# On the condition number of sign matrices

[Paper](paper.pdf) · [Lean theorem statements](lean/SignCond/Paper.lean)

The least spectral condition number of an order-n sign matrix is strictly below 2 except at order 3, where it equals 2.

## What Lean proves

The final declaration for Theorem 1 is in the `SignCond` namespace. [Lean source](lean/Verified.lean)

```lean
theorem verifiedMain :
    (∀ n : ℕ, 1 ≤ n → ∃ A : Matrix (Fin n) (Fin n) ℝ, IsSign A ∧ CondLe A 2 ∧
      (n ≠ 3 → CondLt2 A)) ∧ ∀ A : Matrix (Fin 3) (Fin 3) ℝ, IsSign A →
      ∀ c : ℝ, 0 ≤ c → CondLe A c → 2 ≤ c :=
  Paper.thm_main verifiedFinite
```

**In words.** For every positive integer $n$, there exists a real $n\times n$ matrix $A$ with entries $+1$ or $-1$ and spectral condition number at most $2$. The same witness has condition number strictly below $2$ whenever $n\ne 3$. In dimension $3$, the second half says that for **every** sign matrix and **every** nonnegative $c$ satisfying the condition-number bound, $c\ge 2$. Combined with existence at $n=3$, this gives the exact optimum there.

Lean expresses these bounds using $G=AA^\top$. In `CondLe A c`, some real $t>0$ satisfies $tI\preceq G\preceq c^2tI$. In `CondLt2 A`, some real $t>0$ satisfies $tI\preceq G\prec 4tI$. Here $X\preceq Y$ means $Y-X$ is positive semidefinite, and $X\prec Y$ means the difference is positive definite. The paper’s singular-value interpretation follows because the eigenvalues of $G$ are the squared singular values of $A$. [Definitions of `IsSign` and `CondLe`](lean/SignCond/Basic.lean) · [Definition of `CondLt2`](lean/SignCond/CriterionTau.lean)

### How Proposition 13 enters the proof

The last line of `verifiedMain` passes `verifiedFinite` to `Paper.thm_main`. The latter takes Proposition 13 as an argument. The certificate replay supplies both halves of that argument in Lean, so `verifiedMain` itself has no finite-range hypothesis. [Conditional theorem](lean/SignCond/Paper.lean) · [Completed proof](lean/Verified.lean)

```lean
theorem verifiedFinite : PropFiniteTau :=
  ⟨checkedSequences, finiteSmallMatrices⟩
```

Here is the proposition those two proofs establish, verbatim. [Lean definition](lean/SignCond/HypothesesTau.lean)

```lean
def PropFiniteTau : Prop :=
  (∀ (j : ℕ) [NeZero j], 16 ≤ j → j ≤ 9998 →
    ∃ (a b c d : ZMod j → ℝ) (s : ℕ), IsSignVec a ∧ IsSignVec b ∧ IsSignVec c ∧ IsSignVec d ∧
      vsum a = -(s : ℝ) ∧ vsum b = s ∧ vsum c = s ∧ vsum d = s ∧ 1 ≤ s ∧
      (2 * (s : ℝ) - 2) ^ 2 ≤ 2 * j ∧ 2 * (j : ℝ) ≤ (2 * s + 2) ^ 2 ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
        (Real.sqrt (2 * j) + 2) ^ 2 ≤ energy a b c d ℓ ∧
          energy a b c d ℓ < (2 * Real.sqrt (2 * j) - 2) ^ 2) ∧
  (∀ n : ℕ, Odd n → n ≤ 63 → n ≠ 3 →
    ∃ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ), IsSign A ∧ 0 < t ∧
      (A * Aᵀ - (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((4 * (t : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A * Aᵀ).PosDef)
```

1. **`checkedSequences` proves Proposition 13(1).** Lean’s $j$ is the paper’s $M$, the sequence length. For each of the 9,983 lengths from 16 through 9,998, there is one quadruple $a,b,c,d$ that works at **every** nonzero frequency. Each sequence is a function on residues modulo $j$ (`ZMod j → ℝ`) with values in $\{-1,1\}$. Its sum is given by `vsum`. The four sums are $(-s,s,s,s)$ for an integer $s\ge1$ satisfying $(2s-2)^2\le 2j\le(2s+2)^2$. Write $\rho=\sqrt{2j}$. For every $1\le\ell<j$, the paper’s $E_\ell$ is Lean’s `energy a b c d ℓ`, the sum of the squared magnitudes of the four unnormalized Fourier coefficients. For each sequence $x$, the coefficient is $\widehat{x}(\ell)=\sum_{v=0}^{j-1}x(v)e^{2\pi i\ell v/j}$. The certified interval is $(\rho+2)^2\le E_\ell<(2\rho-2)^2$, including the lower endpoint and excluding the upper. [Sequence and Fourier definitions](lean/SignCond/Defs.lean)

   **A witness you can read from the data.** The length-16 record contains the hexadecimal masks `c4d7`, `b254`, `e622`, `7a0c` in $a,b,c,d$ order. Bit $v$ specifies entry $v$, starting with the least significant bit at $v=0$. A set bit gives $-1$ and a clear bit gives $+1$. The masks have 9, 7, 7 and 7 set bits, giving sums $(-2,2,2,2)$. Thus $s=2$. For these same four sequences, Lean certifies the energy bounds for all 15 frequencies from 1 to 15 using exact cyclic-convolution inequalities. [Certificate data](numerical/certificates_9998.json) · [Replay script](lean/verify_finite.py) · [Fourier bound](lean/SignCond/FiniteEnergy.lean)

2. **`finiteSmallMatrices` proves Proposition 13(2).** For each of the 31 odd orders $n\le63$ other than $3$, there is a sign matrix $A$ and a **rational** $t>0$ with $tI\preceq AA^\top\prec4tI$. The casts `(t : ℝ)` put that rational scale into the real matrix inequalities. The data file also contains an order-3 record. Proposition 13 excludes it because the strict condition-number bound fails there. [Small-matrix proof](lean/SignCond/FiniteSmall.lean)

The two families serve different roles in Theorem 1. For a small odd order other than $3$, the proof uses the matrix from the second clause directly. For an odd order $n=4M+\beta$ with $\beta\in\{1,3\}$ and $16\le M\le9998$, it takes the four sequences from the first clause and uses them in the paper’s bordered matrix construction. For example, the length-16 quadruple supplies the sequence input for orders 65 and 67. Proposition 12 supplies the construction for $M\ge9999$. [Lean proof of the finite construction and odd-order cases](lean/SignCond/MainTau.lean)

## Lean verification

With Elan installed, run from this directory:

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The project pins Lean and Mathlib to v4.20.0. The labels in `Paper.lean` correspond to the numbered results in the paper. For the matching lemma, Lean checks the eigenvectors and the remaining invariant plane, and the paper gives the dimension count.

Some individual arguments differ. For orders 12, 24, 48 and their subsequent doublings, the manuscript doubles its order-6 witness, while Lean doubles an order-12 Hadamard matrix.

The five exact small-order values are also proved in Lean. For the finite proposition itself, run the following command from `lean/`:

```sh
python3 verify_finite.py
```

Python reads the existing sequence data and emits Lean proof terms. Lean checks the integer certificates and derives the bounds at every nonzero Fourier frequency. Separate Lean certificates establish both Gram inequalities for all required odd matrix orders. The final module, [Verified.lean](lean/Verified.lean), assembles `SignCond.verifiedFinite : PropFiniteTau`, applies it to the main theorem, and prints the axioms for both results. Completed batches are cached under `.lake/build/finite-proof/`. For a short run, use `python3 verify_finite.py --first 16 --last 23`.

The full replay checked all 9,983 sequence lengths. Lean reported exactly `propext`, `Classical.choice`, and `Quot.sound` for both `SignCond.verifiedFinite` and `SignCond.verifiedMain`.

## Computational verification

From this directory, using Python 3.10 or later with assertions enabled:

```sh
cd numerical
python3 verify.py certificates_9998.json 9998
```

The last argument enables the coverage check for all 9,983 quadruples and 32 small matrices. The verifier uses only the standard library and takes about an hour on the original machine. A successful run prints `All certificates verified.`

For floating-point spot checks, install NumPy and run from the same numerical directory:

```sh
python3 full_matrix_check.py
python3 large_orders_check.py freq 9999 10001 1
```

The first checks the block construction on small matrices. The second checks every Fourier frequency for the first three large-order construction parameters, with both border sizes.
