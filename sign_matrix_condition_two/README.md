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

**In words.** Every positive dimension admits a sign matrix with spectral condition number at most $2$. In every dimension other than $3$, the same matrix has condition number strictly below $2$. In dimension $3$, the first half gives a matrix that reaches the bound, and the second half proves that no sign matrix can do better. The variable $c$ is a proposed upper bound. If it works for any order-three sign matrix and $c\ge 0$, then $c\ge 2$.

### Reading the definitions in Theorem 1

`IsSign`, `CondLe`, and `CondLt2` are definitions in this project. In the theorem, `Matrix (Fin n) (Fin n) ℝ` is a real matrix whose rows and columns are indexed from $0$ through $n-1$. The definitions below use a generic index type, also called `n`. The annotations `[Fintype n]` and `[DecidableEq n]` let Lean enumerate those indices and test them for equality.

**Sign entries.** `IsSign A` checks each individual entry. Both quantifiers range over indices, and `∨` means “or.” [Source](lean/SignCond/Basic.lean)

```lean
def IsSign (A : Matrix n n ℝ) : Prop := ∀ i j, A i j = 1 ∨ A i j = -1
```

**An upper bound that allows equality.** Set $G=AA^\top$. In the code, `Aᵀ` is the transpose, the matrix `1` is the identity $I$, and `•` is scalar multiplication. `CondLe A c` asks for one positive real scale $t$ such that $G-tI$ and $c^2tI-G$ are both positive semidefinite. Thus every eigenvalue of $G$ lies in the closed interval $[t,c^2t]$. [Source](lean/SignCond/Basic.lean)

```lean
def CondLe [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (c : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ (A * Aᵀ - t • (1 : Matrix n n ℝ)).PosSemidef ∧
    ((c ^ 2 * t) • (1 : Matrix n n ℝ) - A * Aᵀ).PosSemidef
```

**A strict upper bound of two.** `CondLt2 A` still allows an eigenvalue equal to $t$ at the lower end. At the upper end it requires `(4tI - G).PosDef`, so every eigenvalue of $G$ is **strictly less** than $4t$. [Source](lean/SignCond/CriterionTau.lean)

```lean
def CondLt2 (A : Matrix n n ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ (A * Aᵀ - t • (1 : Matrix n n ℝ)).PosSemidef ∧
    ((4 * t) • (1 : Matrix n n ℝ) - A * Aᵀ).PosDef
```

**What makes the inequality strict?** These are the underlying definitions in Mathlib v4.20.0. For a real matrix, `M.IsHermitian` means $M^\top=M$. The expression `star x ⬝ᵥ (M *ᵥ x)` is the real quadratic form $x^\top Mx$. Semidefiniteness allows this to equal zero. Definiteness requires it to be positive for every **nonzero** vector. [Mathlib source](https://github.com/leanprover-community/mathlib4/blob/v4.20.0/Mathlib/LinearAlgebra/Matrix/PosDef.lean)

```lean
def PosSemidef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, 0 ≤ star x ⬝ᵥ (M *ᵥ x)

def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x)
```

**Why these are condition-number bounds.** Lean proves the displayed Gram-matrix predicates. The paper translates them into singular values using $\lambda_{\min}(G)=\sigma_{\min}(A)^2$ and $\lambda_{\max}(G)=\sigma_{\max}(A)^2$. The positive lower bound makes $A$ invertible. For $c\ge0$, the closed interval gives $\kappa_2(A)^2=\lambda_{\max}(G)/\lambda_{\min}(G)\le c^2$. The half-open interval gives $\kappa_2(A)^2<4$. Conversely, for an invertible matrix take $t=\sigma_{\min}(A)^2$ to recover the corresponding Gram bounds from the condition number. This last translation is the mathematical interpretation of the Lean statement. [Paper](paper.pdf)

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

#### The sequence definitions used above

**Entries and sums.** In the first clause of `PropFiniteTau`, `[NeZero j]` supplies $j\ne0$, and `ZMod j → ℝ` assigns one real entry to each residue modulo $j$. `IsSignVec` restricts each entry to $+1$ or $-1$, and `vsum` adds all $j$ entries once. [Source](lean/SignCond/Defs.lean)

```lean
def IsSignVec (x : ZMod j → ℝ) : Prop := ∀ v, x v = 1 ∨ x v = -1

def vsum (x : ZMod j → ℝ) : ℝ := ∑ v, x v
```

**Fourier coefficients and energy.** `omega j` is the complex root of unity $e^{2\pi i/j}$. In `hat x ℓ`, `v.val` is the representative of the residue $v$ between $0$ and $j-1$. Lean sums the entries with the positive-exponent Fourier weights, with no normalization factor. `energy` then adds the squared complex magnitudes for the **same four sequences** at the **same frequency**. Proposition 13 constrains frequencies $1$ through $j-1$. The separate sum conditions specify their coefficients at frequency zero. [Source](lean/SignCond/Defs.lean)

```lean
noncomputable def omega (j : ℕ) : ℂ := exp (2 * π * I / j)

noncomputable def hat (x : ZMod j → ℝ) (ℓ : ℕ) : ℂ := ∑ v : ZMod j, (x v : ℂ) * omega j ^ (ℓ * v.val)

noncomputable def energy (a b c d : ZMod j → ℝ) (ℓ : ℕ) : ℝ :=
  ‖hat a ℓ‖ ^ 2 + ‖hat b ℓ‖ ^ 2 + ‖hat c ℓ‖ ^ 2 + ‖hat d ℓ‖ ^ 2
```

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
