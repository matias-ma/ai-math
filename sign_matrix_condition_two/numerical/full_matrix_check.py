"""Chair's direct check of the construction lemma on full matrices (floating point, small orders).

For random sign rows and random masks in the right sign pools it builds the bordered,
repaired Goethals-Seidel matrix X entry by entry and checks, without using the lemma:
  1. X has entries +-1;
  2. the Goethals-Seidel identity Z Z^T = I_4 (x) (AA^T + BB^T + CC^T + DD^T), exactly;
  3. the constant sector and every frequency sector reduce X, the constant sector is the
     matrix K of the lemma, and on the sector of frequency l all singular values of the
     repaired array lie in [sqrt(E_l) - delta_l, sqrt(E_l) + delta_l];
  4. the singular values of X are exactly those of K together with those of the sectors.
"""
import sys

import numpy as np

V = {1: np.ones((4, 1)), 3: np.array([[1, 1, 1], [-1, 1, -1], [1, -1, -1], [-1, -1, 1]], float)}
G = {1: np.ones((1, 1)), 3: np.array([[1, 1, 1], [-1, 1, 1], [-1, -1, 1]], float)}
H = np.array([[-1, 1, 1, 1], [-1, -1, -1, 1], [-1, 1, -1, -1], [-1, -1, 1, -1]], float)
O = H / 2
PI = np.array([[-1, 0, 0, 0], [0, 0, 0, 1], [0, 1, 0, 0], [0, 0, 1, 0]], float)


def quat(r):
    r0, r1, r2, r3 = r
    return np.array([[r0, r1, r2, r3], [-r1, r0, -r3, r2], [-r2, r3, r0, -r1], [-r3, -r2, r1, r0]], float)


def circ(x):
    j = len(x)
    idx = (np.arange(j)[None, :] - np.arange(j)[:, None]) % j
    return np.asarray(x)[idx]


def gs_array(a, b, c, d):
    j = len(a)
    R = np.zeros((j, j), dtype=np.int64)
    R[(-np.arange(j)) % j, np.arange(j)] = 1
    A, B, C, D = (circ(x).astype(np.int64) for x in (a, b, c, d))
    Z = np.block([[A, B @ R, C @ R, D @ R],
                  [-B @ R, A, -D.T @ R, C.T @ R],
                  [-C @ R, D.T @ R, A, -B.T @ R],
                  [-D @ R, -C.T @ R, B.T @ R, A]])
    return Z, (A, B, C, D)


def build_matrix(rows, masks, border):
    """masks = (S0, S1, S2, S3) for the blocks (0,0), (1,3), (2,1), (3,2)."""
    a, b, c, d = rows
    j = len(a)
    e = 2 - border
    Z, _ = gs_array(a, b, c, d)
    Y = Z.copy()
    u = np.arange(j)
    for x in masks[0]:
        assert a[x] == e
        assert (Y[u, (u + x) % j] == e).all()
        Y[u, (u + x) % j] *= -1
    for (bi, bj, seq, S) in ((1, 3, c, masks[1]), (2, 1, d, masks[2]), (3, 2, b, masks[3])):
        for x in S:
            assert seq[x] == -e
            assert (Y[bi * j + u, bj * j + (x - u) % j] == -e).all()
            Y[bi * j + u, bj * j + (x - u) % j] *= -1
    U = -O @ V[border]
    one = np.ones((j, 1))
    X = np.block([[Y.astype(float), np.kron(U, one)], [np.kron(V[border].T, one.T), G[border]]])
    assert (np.abs(X) == 1).all()
    return X, Z, Y


def check_lemma(rows, masks, border, tol=1e-8):
    a, b, c, d = rows
    j = len(a)
    e = 2 - border
    X, Z, Y = build_matrix(rows, masks, border)
    n = 4 * j + border
    # 2. Goethals-Seidel identity, exact integers
    A, B, C, D = (circ(x).astype(np.int64) for x in rows)
    M = A @ A.T + B @ B.T + C @ C.T + D @ D.T
    assert (Z @ Z.T == np.kron(np.eye(4, dtype=np.int64), M)).all()
    # 3. sectors
    sv_pred = []
    w = np.exp(2j * np.pi * np.arange(j) / j)
    spec = sum(np.abs(np.fft.fft(np.array(x, float))) ** 2 for x in rows)
    k = len(masks[0])
    # constant sector
    Qc = np.zeros((n, 4 + border))
    for i in range(4):
        Qc[i * j:(i + 1) * j, i] = 1 / np.sqrt(j)
    for i in range(border):
        Qc[4 * j + i, 4 + i] = 1
    K = Qc.T @ X @ Qc
    assert np.abs(X @ Qc - Qc @ K).max() < tol and np.abs(X.T @ Qc - Qc @ K.T).max() < tol
    U = -O @ V[border]
    Kform = np.block([[quat([sum(x) for x in rows]) + 2 * k * e * PI, np.sqrt(j) * U],
                      [np.sqrt(j) * V[border].T, G[border]]])
    assert np.abs(K - Kform).max() < tol
    sv_pred += list(np.linalg.svd(K, compute_uv=False))
    worst = 0.0
    for l in range(1, j // 2 + 1):
        cols = []
        for i in range(4):
            for vec in ((w ** l).real, (w ** l).imag):
                if np.abs(vec).max() < 1e-12:
                    continue
                full = np.zeros(4 * j)
                full[i * j:(i + 1) * j] = vec / np.linalg.norm(vec)
                cols.append(full)
        Q = np.array(cols).T
        Yl = Q.T @ Y @ Q
        assert np.abs(Y @ Q - Q @ Yl).max() < tol and np.abs(Y.T @ Q - Q @ Yl.T).max() < tol
        sv = np.linalg.svd(Yl, compute_uv=False)
        ind = [np.zeros(j) for _ in range(4)]
        for t in range(4):
            ind[t][list(masks[t])] = 1
        delta = 2 * max(abs(np.fft.fft(v)[l]) for v in ind)
        root = np.sqrt(spec[l])
        assert sv.min() > root - delta - tol and sv.max() < root + delta + tol
        worst = max(worst, (np.abs(sv - root)).max() / delta) if k else worst
        sv_pred += list(sv)
    # 4. spectrum of X
    sv_X = np.sort(np.linalg.svd(X, compute_uv=False))
    assert len(sv_pred) == n and np.abs(np.sort(sv_pred) - sv_X).max() < 1e-7
    return sv_X.min(), sv_X.max(), worst


def random_tests(seed=0, trials=40):
    rng = np.random.default_rng(seed)
    for t in range(trials):
        j = int(rng.integers(9, 31))
        border = int(rng.choice([1, 3]))
        e = 2 - border
        while True:
            rows = [list(rng.choice([-1, 1], size=j)) for _ in range(4)]
            a, b, c, d = rows
            pools = [[x for x in range(j) if a[x] == e], [x for x in range(j) if c[x] == -e],
                     [x for x in range(j) if d[x] == -e], [x for x in range(j) if b[x] == -e]]
            k = int(rng.integers(0, 5))
            if all(len(p) >= k for p in pools):
                break
        masks = [list(rng.choice(p, size=k, replace=False)) for p in pools]
        lo, hi, used = check_lemma(rows, masks, border)
        print(f"trial {t:2d}: j={j:2d} border={border} k={k}  sv in [{lo:.3f},{hi:.3f}]  "
              f"largest |sv - sqrt(E)|/delta = {used:.3f}")
    print("Construction lemma structure confirmed on all trials.")


if __name__ == "__main__":
    random_tests()
