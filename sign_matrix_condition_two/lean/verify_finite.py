"""Produce and kernel-check Lean proofs from the paper's sequence certificates."""
import argparse
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
FIRST, LAST = 16, 9998
BATCH = 256


def sequence_proof(j, certificate):
    exponent, words = certificate
    masks = [int(word, 16) for word in words]
    if len(masks) != 4 or any(mask < 0 or mask.bit_length() > j for mask in masks):
        raise ValueError(f"Invalid row encoding at j={j}")
    if not 0 <= exponent <= 12:
        raise ValueError(f"Invalid squaring count at j={j}")

    row_sum = j - 2 * masks[1].bit_count()
    mu = math.isqrt(2*j*256**2 - 1) + 1
    c = (5*j + 4)*256 - 2*mu
    bound = 4*256*j**2 + abs(c - 4*256*row_sum**2) + j*abs(c)
    for _ in range(exponent):
        bound = j * bound**2
    sign_bit = bound.bit_length() + 1
    width = sign_bit + j.bit_length() + 4
    names = [f"{prefix}{j}" for prefix in "ABCD"]
    rows = " ".join(names)
    lines = []
    for name, mask in zip(names, masks):
        # Reversal on Z/jZ fixes the zeroth entry.
        other_bits = f"{mask:0{j}b}"[:-1]
        reverse = (mask & 1) + 2 * int(other_bits[::-1], 2)
        lines.append(f"private def {name} := makeRow {width} {(j-1).bit_length()} {hex(mask)} {hex(reverse)}")
    lines.extend([f"private def out{j} := outputWords {j} {rows} {row_sum} {mu} {exponent} {width} {sign_bit}",
                  f"private theorem row{j} : FiniteEnergy.SequenceWitness {j} := by",
                  f"  apply checkedWordWitness {rows} {row_sum} {mu} {exponent} {width} out{j}.1 out{j}.2 (2^{sign_bit}-1)",
                  "  decide +kernel"])
    return "\n".join(lines) + "\n"


def case_proof(lo, hi):
    if lo == hi:
        return f"(singleInterval {lo} row{lo})"
    mid = (lo + hi) // 2
    left = case_proof(lo, mid)
    right = case_proof(mid + 1, hi)
    return f"(splitInterval (mid := {mid}) {left}\n    {right})"


def write_batch(lo, hi, records):
    lines = ["import SignCond.WordCheck", "namespace SignCond.FiniteWord", "open SignCond.FiniteEnergy",
             "set_option maxRecDepth 100000", "set_option maxHeartbeats 0"]
    lines.extend(sequence_proof(n, records[n]) for n in range(lo, hi + 1))
    lines.extend([f"theorem certified{lo}to{hi} : ∀ (j : ℕ) [NeZero j], {lo} ≤ j → j ≤ {hi} → SequenceWitness j :=",
                  "  " + case_proof(lo, hi), "end SignCond.FiniteWord"])
    return "\n".join(lines) + "\n"


def interval_tree(batches, depth=1):
    indent = "  " * depth
    if len(batches) == 1:
        lo, hi = batches[0]
        return [f"{indent}exact FiniteWord.certified{lo}to{hi} j (by omega) (by omega)"]
    mid = len(batches) // 2
    split = batches[mid - 1][1]
    left = interval_tree(batches[:mid], depth + 1)
    right = interval_tree(batches[mid:], depth + 1)
    left[0] = indent + "· " + left[0].lstrip()
    right[0] = indent + "· " + right[0].lstrip()
    return [f"{indent}by_cases h{split} : j ≤ {split}", *left, *right]


def compile_module(directory, module, source, env):
    path = directory / (module + ".lean")
    output = path.with_suffix(".olean")
    if output.exists() and path.exists() and path.read_text() == source:
        return
    output.unlink(missing_ok=True)
    path.write_text(source)
    with tempfile.TemporaryDirectory(dir=directory) as tmp:
        staged = Path(tmp) / output.name
        subprocess.run([env["FINITE_LEAN"], "-j1", "--root", str(directory), "-o", str(staged), str(path)],
                       cwd=ROOT, env=env, check=True)
        staged.replace(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--first", type=int, default=FIRST)
    parser.add_argument("--last", type=int, default=LAST)
    parser.add_argument("--batch-size", type=int, default=BATCH,
                        help="number of sequence lengths per Lean process (default: %(default)s)")
    options = parser.parse_args()
    if options.batch_size < 1:
        parser.error("The batch size must be positive.")
    lo, hi = options.first, options.last
    if not FIRST <= lo <= hi <= LAST:
        parser.error("Choose a subinterval of 16 through 9998.")
    data = next(p for p in (ROOT.parent / "numerical/certificates_9998.json",
                            ROOT.parent / "code/finite/run/certificates_9998.json") if p.is_file())
    records = {}
    for tag, n, exponent, words in json.loads(data.read_bytes()):
        if tag == "F":
            if n in records:
                raise ValueError(f"Repeated certificate for j={n}")
            records[n] = exponent, words
    full = (lo, hi) == (FIRST, LAST)
    targets = ["SignCond.WordCheck"]
    if full:
        # Build the large matrix-certificate modules sequentially on small machines.
        targets += ["SignCond." + p.stem for p in sorted((ROOT / "SignCond").glob("MatrixCases*.lean"))]
        targets += ["SignCond.FiniteSmall", "SignCond.Paper"]
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "1")
    for target in targets:
        subprocess.run(["lake", "build", target], cwd=ROOT, env=env, check=True)
    lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    prefix = subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip()
    env["FINITE_LEAN"] = str(Path(prefix) / "bin/lean")
    digest = hashlib.sha256()
    for path in sorted([Path(__file__), ROOT / "lean-toolchain", ROOT / "lake-manifest.json",
                        ROOT / "lakefile.toml", ROOT / "Verified.lean", data, *ROOT.glob("SignCond/*.lean")]):
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    directory = ROOT / ".lake/build/finite-proof" / digest.hexdigest()
    directory.mkdir(parents=True, exist_ok=True)
    env["LEAN_PATH"] = str(directory) + os.pathsep + lean_path
    with (directory / ".lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        verify(directory, records, lo, hi, options.batch_size, env)


def verify(directory, records, lo, hi, batch_size, env):
    batches = [(a, min(a + batch_size - 1, hi)) for a in range(lo, hi + 1, batch_size)]
    for a, b in batches:
        module = f"Rows{a}to{b}"
        compile_module(directory, module, write_batch(a, b, records), env)
        print(f"Kernel-checked sequence lengths {a} through {b}", flush=True)
    module = "VerifiedSequenceRange" if (lo, hi) == (FIRST, LAST) else f"Verified{lo}to{hi}"
    compile_module(directory, module, range_source(lo, hi, batches), env)
    if (lo, hi) == (FIRST, LAST):
        compile_module(directory, "Verified", (ROOT / "Verified.lean").read_text(), env)
        module = "Verified"
    print(directory / (module + ".olean"))


def range_source(lo, hi, batches):
    lines = [*(f"import Rows{a}to{b}" for a, b in batches),
             "namespace SignCond", "set_option maxHeartbeats 0", "set_option maxRecDepth 100000",
             f"theorem checkedSequences (j : ℕ) [NeZero j] (hl : {lo} ≤ j) (hh : j ≤ {hi}) : FiniteEnergy.SequenceWitness j := by",
             *interval_tree(batches), "#print axioms checkedSequences", "end SignCond"]
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    main()
