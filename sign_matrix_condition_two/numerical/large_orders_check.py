"""Numerical checks of the construction for large orders (Proposition "large", j >= 9999).

Written from the statements in the paper, independently of the proofs.  Not part of the proof.

  G      Golay lengths 2^i * {1, 10, 26, 100}, without 1
  l      largest element of G with l^2 <= j + eps, eps = j mod 2;  s = l - eps
  rows   -(P|Phi), (P|-Phi), (Q|Psi), (Q|-Psi): the regular Golay pair of length l^2 (first entry deleted if
         eps = 1) and the tails Phi_r, Psi_r of length r = j - l^2 + eps defined by one recursion
  alpha  the even integer nearest to rho = sqrt(2j);  k = s - alpha/2;  tau = (3 rho + alpha)/4
  masks  any k positions of the right sign if alpha >= rho; if alpha < rho, k positions with |S^(l)| <= k - 3/8
         (drawn at random until the bound holds)
Claim: all singular values of X lie in [tau, 2 tau).

Usage:
  python large_orders_check.py golay              exact: the Golay pairs and the regular pairs used
  python large_orders_check.py tails RMAX         tails of length 2, 4, ..., RMAX: zero sums; energy on a 16x grid
  python large_orders_check.py envelope RMAX      the recursion M_r <= 8g + 8eta + 16eta sqrt(g) + 4M_m of the proof
  python large_orders_check.py scalars JMAX       every j in [9999, JMAX] and samples up to 10^12: the hypotheses
                                                  of the lemmas and the constant block K, both borders
  python large_orders_check.py freq LO HI STEP    the sequences and masks themselves: every nonzero frequency
"""
import sys
from functools import lru_cache
from math import isqrt, sqrt

import numpy as np

signs = lambda w: [1 if ch == "+" else -1 for ch in w]
A10, B10 = signs("+++++-+--+"), signs("++--+++-+-")
A26, B26 = signs("++++-++--+-+-+--+-+++--+++"), signs("++++-++--+-+++++-+---++---")
NET = sorted({g << i for g in (1, 10, 26, 100) for i in range(40)} - {1})


def is_golay(a, b):
    n = len(a)
    return all(sum(a[v] * a[v + u] + b[v] * b[v + u] for v in range(n - u)) == 0 for u in range(1, n))


def square(a, b):
    """Lemma "square": the regular pair of length l^2 from a Golay pair of length l."""
    l = len(a)
    u = [(x + y) // 2 for x, y in zip(a, b)]
    v = [(x - y) // 2 for x, y in zip(a, b)]
    p = [u[x] * b[y] + v[x] * a[l - 1 - y] for y in range(l) for x in range(l)]
    q = [u[x] * a[y] - v[x] * b[l - 1 - y] for y in range(l) for x in range(l)]
    return p, q


@lru_cache(None)
def golay(g):
    """The fixed Golay pair of length g, for g = 1 or g in G."""
    if g == 1:
        return (1,), (1,)
    if g == 10:
        return tuple(A10), tuple(B10)
    if g == 26:
        return tuple(A26), tuple(B26)
    if g == 100:
        return tuple(map(tuple, square(A10, B10)))
    p, q = golay(g // 2)
    return p + q, p + tuple(-x for x in q)


def net_floor(w):
    return max(g for g in NET[:200] if g <= w)


@lru_cache(None)
def tail(r):
    """The pair (Phi_r, Psi_r) of the paper."""
    assert r >= 0 and r % 2 == 0
    if r == 0:
        return (), ()
    if r == 2:
        return (1, -1), (1, -1)
    eta = (r // 2) % 2
    w = r // 2 - eta
    g = net_floor(w)
    p, q = golay(g)
    u, v = tail(w - g)
    anti = lambda a: tuple(y for x in a for y in (x, -x))
    same = lambda a: tuple(y for x in a for y in (x, x))
    return anti(p) + same(u) + ((-1, 1) if eta else ()), anti(q) + same(v) + ((1, -1) if eta else ())


def check_golay():
    for g in (1, 2, 4, 8, 10, 16, 20, 26, 32, 40, 52, 64, 80, 100, 104, 128, 160, 200, 208):
        p, q = golay(g)
        assert len(p) == len(q) == g and is_golay(p, q) and p[0] == q[0] == 1, g
    for l in (2, 4, 10, 16, 26):
        p, q = square(*golay(l))
        assert is_golay(p, q) and sum(p) == sum(q) == l and p[0] == q[0] == 1, l
    for l in (100, 104, 128, 160, 200, 208, 256):          # sums and first coefficients only (lengths up to 65536)
        p, q = square(*golay(l))
        assert sum(p) == sum(q) == l and p[0] == q[0] == 1 and set(p) | set(q) == {1, -1}
    print("Golay pairs of the listed lengths: exact; regular pairs: sums l, first coefficients 1")


def check_tails(rmax):
    worst = (0.0, 0)
    for r in range(2, rmax + 1, 2):
        p, q = tail(r)
        assert len(p) == len(q) == r and sum(p) == sum(q) == 0 and set(p) | set(q) == {1, -1}
        size = 1 << (16 * r - 1).bit_length()
        en = np.abs(np.fft.rfft(np.array(p, float), size)) ** 2 + np.abs(np.fft.rfft(np.array(q, float), size)) ** 2
        assert en.max() <= min(7.5 * r, 6 * r + 400) + 1e-6, (r, en.max())
        worst = max(worst, (en.max() / (6 * r), r))
    print(f"tails: r = 2..{rmax}: zero sums; energy <= min(15r/2, 6r+400) on a 16x grid; "
          f"largest energy/(6r) = {worst[0]:.4f} at r = {worst[1]}")


def check_envelope(rmax):
    M = {0: 0.0, 2: 8.0, 6: 40.0}
    worst = (-1e18, 0)
    for r in range(4, rmax + 1, 2):
        if r not in M:
            eta = (r // 2) % 2
            w = r // 2 - eta
            g = net_floor(w)
            m = w - g
            assert (g >= 32 or m <= 4) and (g >= 64 or m <= 10) and (g < 32 or 4 * m <= g) and (g < 64 or 4 * m <= g - 8)
            M[r] = 8 * g + 8 * eta + 16 * eta * sqrt(g) + 4 * M[m]
        assert M[r] <= 7.5 * r + 1e-9 and M[r] <= 6 * r + 400 + 1e-9, (r, M[r])
        worst = max(worst, (M[r] - 6 * r, r))
    print(f"envelope: r <= {rmax}: M_r <= min(15r/2, 6r+400); largest M_r - 6r = {worst[0]:.2f} at r = {worst[1]}")


def params(j):
    eps = j % 2
    l = net_floor(isqrt(j + eps))
    s = l - eps
    h = isqrt(j // 2)
    m = h + (1 if (2 * h + 1) ** 2 < 2 * j else 0)       # alpha = 2m is the even integer nearest to sqrt(2j)
    rho = sqrt(2 * j)
    alpha = 2 * m
    return l, eps, s, s - m, rho, alpha, 2 * m * m < j, (3 * rho + alpha) / 4


H = np.array([[-1, 1, 1, 1], [-1, -1, -1, 1], [-1, 1, -1, -1], [-1, -1, 1, -1]], float)
PI = np.array([[-1, 0, 0, 0], [0, 0, 0, 1], [0, 1, 0, 0], [0, 0, 1, 0]], float)
V = {1: np.ones((4, 1)), 3: np.array([[1, 1, 1], [-1, 1, -1], [1, -1, -1], [-1, -1, 1]], float)}
G = {1: np.ones((1, 1)), 3: np.array([[1, 1, 1], [-1, 1, 1], [-1, -1, 1]], float)}


def K_matrix(j, s, k, beta):
    U = -(H / 2) @ V[beta]
    return np.block([[s * H - 2 * k * (beta - 2) * PI, np.sqrt(j) * U], [np.sqrt(j) * V[beta].T, G[beta]]])


def check_scalars(jmax):
    worst = dict(freq_lo=9e9, freq_hi=9e9, K_lo=9e9, K_hi=9e9, k_min=9e9)
    js = list(range(9999, jmax + 1))
    rng = np.random.default_rng(5)
    js += [int(x) for x in np.unique((10 ** rng.uniform(np.log10(jmax), 12, 20000)).astype(np.int64))]
    for j in js:
        l, eps, s, k, rho, alpha, select, tau = params(j)
        lp = min(g for g in NET if g > l)
        assert l >= 100 and 4 * lp <= 5 * l and l * l <= j + eps < lp * lp
        assert abs(alpha - rho) < 1 and 0 < k <= s and 2 * k <= j - s
        top = 12 * j - 8 * s * s + 800
        assert top < 8 * j and 8 * 33 * 33 * j < (j - s) ** 2          # every sign pool has Fourier bias < 1/33
        if select:
            assert k >= 13 and j <= 196 * k * k, (j, k)
            worst["k_min"] = min(worst["k_min"], k)
        dmax = 2 * k - 0.75 if select else 2 * k
        worst["freq_lo"] = min(worst["freq_lo"], 2 * s - dmax - tau)
        worst["freq_hi"] = min(worst["freq_hi"], 2 * tau - sqrt(top) - dmax)
        assert 2 * s - dmax >= tau - 1e-9 and sqrt(top) + dmax < 2 * tau, j
        for beta in (1, 3):
            sv = np.linalg.svd(K_matrix(j, s, k, beta), compute_uv=False)
            worst["K_lo"] = min(worst["K_lo"], sv.min() - tau)
            worst["K_hi"] = min(worst["K_hi"], 2 * tau - sv.max())
            assert sv.min() > tau and sv.max() < 2 * tau, (j, beta)
    print(f"scalars: {len(js)} values of j from 9999 to {max(js)}: all hypotheses hold; smallest margins",
          {a: round(float(b), 4) for a, b in worst.items()})


def rows_for(j):
    l, eps, s = params(j)[:3]
    p, q = square(*golay(l))
    p, q = p[eps:], q[eps:]
    u, v = (list(x) for x in tail(j - l * l + eps))
    neg = lambda a: [-x for x in a]
    return [np.array(x) for x in (neg(p + u), p + neg(u), q + v, q + neg(v))]


def check_freq(lo, hi, step):
    rng = np.random.default_rng(13)
    worst = dict(lo=9e9, hi=9e9, deficit=9e9, bias=0.0)
    draws = redraws = 0
    for j in range(lo, hi + 1, step):
        l, eps, s, k, rho, alpha, select, tau = params(j)
        rows = rows_for(j)
        assert all(len(x) == j for x in rows) and [int(x.sum()) for x in rows] == [-s, s, s, s]
        en = sum(np.abs(np.fft.rfft(x.astype(float))) ** 2 for x in rows)
        assert en[1:].min() >= 4 * s * s - 1e-6 and en[1:].max() <= 12 * j - 8 * s * s + 800 + 1e-6
        for beta in (1, 3):
            sig = beta - 2
            delta = np.zeros(j // 2 + 1)
            for row, sign in ((0, -sig), (2, sig), (3, sig), (1, sig)):
                pool = np.flatnonzero(rows[row] == sign)
                worst["bias"] = max(worst["bias"],
                                    np.abs(np.fft.rfft((rows[row] == sign).astype(float)))[1:].max() / len(pool))
                while True:
                    S = rng.choice(pool, k, replace=False) if select else pool[:k]
                    ind = np.zeros(j)
                    ind[S] = 1
                    f = np.abs(np.fft.rfft(ind))
                    draws += 1
                    if not select or f[1:].max() <= k - 0.375:
                        break
                    redraws += 1
                if select:
                    worst["deficit"] = min(worst["deficit"], k - 0.375 - f[1:].max())
                delta = np.maximum(delta, 2 * f)
            root = np.sqrt(en[1:])
            a, b = (root - delta[1:] - tau).min(), (2 * tau - delta[1:] - root).min()
            worst["lo"], worst["hi"] = min(worst["lo"], a), min(worst["hi"], b)
            assert a > -1e-7 and b > 0, (j, beta, a, b)
            sv = np.linalg.svd(K_matrix(j, s, k, beta), compute_uv=False)
            assert sv.min() > tau and sv.max() < 2 * tau
    print(f"freq: j in [{lo},{hi}] step {step}: every frequency and the constant block lie in [tau, 2 tau);",
          {a: round(float(b), 4) for a, b in worst.items()}, f"masks drawn {draws}, redrawn {redraws}")


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "golay":
        check_golay()
    elif cmd == "tails":
        check_tails(int(sys.argv[2]))
    elif cmd == "envelope":
        check_envelope(int(sys.argv[2]))
    elif cmd == "scalars":
        check_scalars(int(sys.argv[2]))
    elif cmd == "freq":
        check_freq(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
