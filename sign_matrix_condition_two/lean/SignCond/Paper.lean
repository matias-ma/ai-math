import SignCond.MainTau
import SignCond.SquareLift
import SignCond.Power
import SignCond.SmallMain

/-!
# The paper, result by result

One Lean statement per numbered result of `../paper/main.tex` (version of 21 Nov 2026), in the
paper's order, named by the paper's label. Each docstring quotes the paper's statement (LaTeX
source). The proofs are calls to the development in the other files. Notation is that of
`SignCond/Defs.lean`.

One input is verified in the paper by a program, not by hand: Proposition `prop:finite`. It is the
named proposition `PropFiniteTau` (`SignCond/HypothesesTau.lean`, here `prop_finite`) and enters
Theorem `thm:main` as an explicit hypothesis. The separate certificate replay in
`Verified.lean` supplies this argument to obtain `SignCond.verifiedMain`.

Section `sec:small` (exact values of `h(n)` for `n ∈ {7, 9, 10, 13, 14}`): Theorem `thm:small`
(right after `thm_main`) and Lemmas `lem:tools`, `lem:matching` (at the end, after `lem_power`) are
proved. `h(n) = c` is `HVal n c` (`SmallTools.lean`); Lemma `lem:matching` is stated as the
decomposition of its proof (see its docstring).

Condition numbers: `κ(A) ≤ 2` is `CondLe A 2`, the paper's window `tI ⪯ AAᵀ ⪯ 4tI` for some
`t > 0`, and `κ(A) < 2` is `CondLt2 A`, the window `tI ⪯ AAᵀ ≺ 4tI` (Section 2: "All of our bounds
on condition numbers are obtained in this form"). `WindowAt M τ` is `τ²I ⪯ MMᵀ ≺ 4τ²I`.
-/

open Matrix Complex Kronecker
open scoped Real

namespace SignCond.Paper

open SignCond

/-- **Theorem `thm:main`.** "For every integer `n\ge1`, there is an `n\times n` sign matrix `A` with
`\kappa(A)\le2`, and with `\kappa(A)<2` if `n\ne3`. Consequently, `\sup_{n\ge1}h(n)=2`, and
`h(n)=2` only for `n=3`."

The first conjunct is the first sentence (with `κ(A) < 2` as `CondLt2 A`, which gives `h(n) < 2`
for `n ≠ 3`). The second conjunct is the lower bound `h(3) ≥ 2`: no `3 × 3` sign matrix satisfies
the window of any ratio `c < 2`. Proved from the hypothesis `PropFiniteTau` (`prop_finite`). -/
theorem thm_main (hFinite : PropFiniteTau) :
    (∀ n : ℕ, 1 ≤ n → ∃ A : Matrix (Fin n) (Fin n) ℝ, IsSign A ∧ CondLe A 2 ∧
        (n ≠ 3 → CondLt2 A)) ∧
      ∀ A : Matrix (Fin 3) (Fin 3) ℝ, IsSign A → ∀ c : ℝ, 0 ≤ c → CondLe A c → 2 ≤ c :=
  ⟨main_theorem_tau hFinite, fun A hA c hc h =>
    condLe_three_sharp A hA (condLe_det_ne_zero_tau h) c hc h⟩

/-- **Theorem `thm:small`.** "We have
`h(7)=\sqrt3,\qquad h(9)=\frac{1+\sqrt{41}}4,\qquad h(10)=\frac32,`
`\qquad h(13)=\frac5{2\sqrt3},\qquad h(14)=\sqrt{\frac{13}6}`."

`h(n) = c` is `HVal n c`: some `n × n` sign matrix satisfies the window of ratio `c` (`κ(A) ≤ c`),
and every `n × n` sign matrix satisfying the window of a ratio `c' ≥ 0` has `c ≤ c'`. -/
theorem thm_small : HVal 7 (Real.sqrt 3) ∧ HVal 9 ((1 + Real.sqrt 41) / 4) ∧ HVal 10 (3 / 2) ∧
    HVal 13 (5 / (2 * Real.sqrt 3)) ∧ HVal 14 (Real.sqrt (13 / 6)) :=
  SignCond.thm_small

/-- **Lemma `lem:double`.** "Let `A` be a sign matrix and let
`W_2=\begin{pmatrix}1&1\\1&-1\end{pmatrix}`. Then `W_2\otimes A` is a sign matrix with
`\kappa(W_2\otimes A)=\kappa(A)`."

`κ(W₂ ⊗ A) = κ(A)` is stated as: for every `c`, `W₂ ⊗ A` satisfies the window of ratio `c` iff `A`
does, and `W₂ ⊗ A` satisfies the strict window of ratio `2` iff `A` does. -/
theorem lem_double {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : IsSign A) :
    IsSign (W2 ⊗ₖ A) ∧ (∀ c : ℝ, CondLe (W2 ⊗ₖ A) c ↔ CondLe A c) ∧
      (CondLt2 (W2 ⊗ₖ A) ↔ CondLt2 A) :=
  ⟨isSign_kronecker hA, condLe_kronecker_iff A, condLt2_kronecker_iff A⟩

/-- **Lemma `lem:three`.** "Every invertible `3\times3` sign matrix `A` satisfies `\kappa(A)=2`."

Stated as: `A` satisfies the window of ratio `2`, and of no ratio `c < 2`. -/
theorem lem_three (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsSign A) (hdet : A.det ≠ 0) :
    CondLe A 2 ∧ ∀ c : ℝ, 0 ≤ c → CondLe A c → 2 ≤ c :=
  ⟨condLe_three A hA hdet, condLe_three_sharp A hA hdet⟩

/-- **Lemma `lem:GS`.** "The matrix `Z` in \eqref{eq:GS} satisfies
`ZZ^\top=I_4\otimes\left(AA^\top+BB^\top+CC^\top+DD^\top\right)`." (`A = C(a)`, …, `D = C(d)`.) -/
theorem lem_GS {j : ℕ} [NeZero j] (a b c d : ZMod j → ℝ) :
    Zgs a b c d * (Zgs a b c d)ᵀ =
      (1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ
        (circ a * (circ a)ᵀ + circ b * (circ b)ᵀ + circ c * (circ c)ᵀ + circ d * (circ d)ᵀ) :=
  gs_identity_circ a b c d

/-- **Lemma `lem:criterion`.** "Let `a,b,c,d` be sign sequences of length `j` with sums
`\mathbf{s}=(s_0,s_1,s_2,s_3)`, let `S_0,\dots,S_3` be masks of size `k` satisfying
\eqref{eq:pools}, and let `X` be the matrix in \eqref{eq:X}. Put
`\delta_\ell=2\max_i|\widehat{S_i}(\ell)|`, and let
`K=\begin{pmatrix}\mathcal{Q}(\mathbf{s})-2k\sigma\Pi&\sqrt{j}\,U_\beta\\\sqrt{j}\,V_\beta^\top&
G_\beta\end{pmatrix}`. Let `\tau>0`, and suppose that `\tau^2I\preceq KK^\top\prec4\tau^2I` and that
`\tau+\delta_\ell\le\sqrt{E_\ell}<2\tau-\delta_\ell` for `1\le\ell<j` \eqref{eq:window}. Then
`\tau^2I\preceq XX^\top\prec4\tau^2I`. In particular, `\kappa(X)<2`."

(`k` is a natural number and `\mathbf{s}` is written `(vsum a, vsum b, vsum c, vsum d)`; the
hypotheses "sign sequences" and eq. `pools` are kept but not needed for the window.) -/
theorem lem_criterion {j : ℕ} [NeZero j] (β : ℕ) (hβ : β = 1 ∨ β = 3) (a b c d : ZMod j → ℝ)
    (ha : IsSignVec a) (hb : IsSignVec b) (hc : IsSignVec c) (hd : IsSignVec d)
    (S : Fin 4 → Finset (ZMod j)) (k : ℕ) (hS : ∀ i, (S i).card = k)
    (hpools : Pools (sigmaOf β) a b c d S) (τ : ℝ) (hτ : 0 < τ)
    (hK : WindowAt (Kmat β ![vsum a, vsum b, vsum c, vsum d] k j) τ)
    (hwin : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      τ + deltaL S ℓ ≤ Real.sqrt (energy a b c d ℓ) ∧
        Real.sqrt (energy a b c d ℓ) < 2 * τ - deltaL S ℓ) :
    WindowAt (Xmat β a b c d S) τ ∧ CondLt2 (Xmat β a b c d S) :=
  lem_criterion_tau β hβ a b c d ha hb hc hd S k hS hpools τ hτ hK hwin

/-- **Lemma `lem:sector`.** "Let `j\ge1` and `s\ge k\ge0` be integers, and suppose that
`\mathbf{s}=(-s,s,s,s)`. Put `t=2j`, `\alpha=2(s-k)`, and `\gamma=2(s+k)`, and for `\nu\in\{1,4\}`
let `p_\nu(x)=x^2-(\alpha^2+4t+\nu)x+4t^2+4t\alpha+\nu\alpha^2`. Let `\tau>0` with
`\tfrac12t+1<\tau^2\le2t`. Suppose that `\tau\le\gamma<2\tau`, and that `p_\nu(\tau^2)\ge0` and
`p_\nu(4\tau^2)>0` for `\nu\in\{1,4\}`. Then `\tau^2I\preceq KK^\top\prec4\tau^2I` for both
`\beta=1` and `\beta=3`."

(`s, k` are natural numbers; `t` is written out as `2j`; `p_ν` is `pnu j α ν`.) -/
theorem lem_sector {j s k : ℕ} (hj : 1 ≤ j) (hks : k ≤ s) (τ : ℝ) (hτ : 0 < τ)
    (hτlo : 2 * (j : ℝ) / 2 + 1 < τ ^ 2) (hτhi : τ ^ 2 ≤ 2 * (2 * (j : ℝ)))
    (hγ1 : τ ≤ 2 * ((s : ℝ) + k)) (hγ2 : 2 * ((s : ℝ) + k) < 2 * τ)
    (hp : ∀ ν : ℝ, (ν = 1 ∨ ν = 4) →
      0 ≤ pnu j (2 * ((s : ℝ) - k)) ν (τ ^ 2) ∧ 0 < pnu j (2 * ((s : ℝ) - k)) ν (4 * τ ^ 2)) :
    WindowAt (Kmat 1 ![-(s : ℝ), s, s, s] k j) τ ∧ WindowAt (Kmat 3 ![-(s : ℝ), s, s, s] k j) τ :=
  lem_sector_tau hj hks τ hτ hτlo hτhi hγ1 hγ2 hp

/-- **Lemma `lem:scales`.** "Let `t=2j` and `\rho=\sqrt{t}`, let `\alpha` be a real number, and let
`p_\nu` be as in Lemma `lem:sector`, for `\nu\in\{1,4\}`.
1. If `j\ge5` and `0\le\alpha\le\rho`, then `p_\nu(\rho^2)\ge0` and `p_\nu(4\rho^2)>0`.
2. If `\rho\ge14` and `|\alpha-\rho|<1`, then `\tau=\tfrac14(3\rho+\alpha)` satisfies
   `p_\nu(\tau^2)>0` and `p_\nu(4\tau^2)>0`." -/
theorem lem_scales (j : ℕ) (α : ℝ) :
    (5 ≤ j → 0 ≤ α → α ≤ Real.sqrt (2 * j) → ∀ ν : ℝ, (ν = 1 ∨ ν = 4) →
      0 ≤ pnu j α ν (Real.sqrt (2 * j) ^ 2) ∧ 0 < pnu j α ν (4 * Real.sqrt (2 * j) ^ 2)) ∧
    (14 ≤ Real.sqrt (2 * j) → |α - Real.sqrt (2 * j)| < 1 → ∀ ν : ℝ, (ν = 1 ∨ ν = 4) →
      0 < pnu j α ν (((3 * Real.sqrt (2 * j) + α) / 4) ^ 2) ∧
        0 < pnu j α ν (4 * ((3 * Real.sqrt (2 * j) + α) / 4) ^ 2)) :=
  SignCond.lem_scales j α

/-- **Lemma `lem:square`.** "Let `(A,B)` be a Golay pair of length `l`, and put
`U=\tfrac12(A+B)` and `V=\tfrac12(A-B)`. Then `P(z)=U(z)B(z^l)+V(z)A^{\mathrm{rev}}(z^l)`,
`Q(z)=U(z)A(z^l)-V(z)B^{\mathrm{rev}}(z^l)` form a regular Golay pair of length `l^2`. If
`A_0=B_0=1`, then `P_0=Q_0=1`." -/
theorem lem_square {l : ℕ} (A B : Fin l → ℤ) (h : IsGolayPair A B) :
    (∀ z : ℂ, peval (golaySquare A B).1 z = (peval A z + peval B z) / 2 * peval B (z ^ l) +
      (peval A z - peval B z) / 2 * peval (seqRev A) (z ^ l)) ∧
    (∀ z : ℂ, peval (golaySquare A B).2 z = (peval A z + peval B z) / 2 * peval A (z ^ l) -
      (peval A z - peval B z) / 2 * peval (seqRev B) (z ^ l)) ∧
    IsRegular l (golaySquare A B).1 (golaySquare A B).2 ∧
    (coeff A 0 = 1 → coeff B 0 = 1 →
      coeff (golaySquare A B).1 0 = 1 ∧ coeff (golaySquare A B).2 0 = 1) := by
  refine ⟨golaySquare_peval_fst h.1 h.2.1, golaySquare_peval_snd h.1 h.2.1,
    golaySquare_regular h, fun hA hB => ?_⟩
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl; simp [coeff] at hA
  · exact lem_square_first hl A B h hA hB

/-- **Lemma `lem:rows`.** "Let `l\ge4` be even, and let `(P,Q)` be a regular Golay pair of length
`l^2` with `P_0=Q_0=1`. Let `j\ge1` and `\varepsilon\in\{0,1\}` with `\varepsilon\equiv j\pmod2`,
and suppose that `l^2\le j+\varepsilon`. Let `\widetilde{P}` and `\widetilde{Q}` be obtained from
`P` and `Q` by deleting the first coefficient when `\varepsilon=1`, and put `s=l-\varepsilon` and
`r=j-l^2+\varepsilon`. Let `\Phi` and `\Psi` be sign sequences of length `r` with
`\Phi(1)=\Psi(1)=0` and `|\Phi(z)|^2+|\Psi(z)|^2\le6r+400` for all `|z|=1` \eqref{eq:tail}. Then
the sequences `a=-(\widetilde{P}|\Phi)`, `b=\widetilde{P}|{-\Phi}`, `c=\widetilde{Q}|\Psi`,
`d=\widetilde{Q}|{-\Psi}` have length `j` and sums `(-s,s,s,s)`, and their energies satisfy
`4s^2\le E_\ell\le12j-8s^2+800` for all `\ell`."

(`Φ, Ψ` are `R, T`; eq. `tail` is `TailCond400`; `\widetilde{P}` is `dropFirst ε P` inside
`rowsSeqs`; `hlen` is the arithmetic identity `(l² - ε) + r = j`, which follows from the other
hypotheses and is needed to type the sequences as having length `j`; "`P_0 = 1`" is
`coeff P 0 = 1`.) -/
theorem lem_rows {l j ε : ℕ} [NeZero j] (hl : 4 ≤ l) (hle : Even l) (P Q : Fin (l ^ 2) → ℤ)
    (hreg : IsRegular l P Q) (hP0 : coeff P 0 = 1) (hQ0 : coeff Q 0 = 1)
    (hε : ε = 0 ∨ ε = 1) (hεj : ε % 2 = j % 2) (hlj : l ^ 2 ≤ j + ε)
    (hlen : l ^ 2 - ε + (j + ε - l ^ 2) = j) (R T : Fin (j + ε - l ^ 2) → ℤ)
    (hR : IsSignSeq R) (hT : IsSignSeq T) (htail : TailCond400 R T) :
    let s : ℝ := (l : ℝ) - ε
    let abcd := rowsSeqs hlen P Q R T
    (vsum (toVec abcd.1) = -s ∧ vsum (toVec abcd.2.1) = s ∧ vsum (toVec abcd.2.2.1) = s ∧
        vsum (toVec abcd.2.2.2) = s) ∧
      ∀ ℓ : ℕ, 4 * s ^ 2 ≤ energy (toVec abcd.1) (toVec abcd.2.1) (toVec abcd.2.2.1)
          (toVec abcd.2.2.2) ℓ ∧
        energy (toVec abcd.1) (toVec abcd.2.1) (toVec abcd.2.2.1) (toVec abcd.2.2.2) ℓ ≤
          12 * j - 8 * s ^ 2 + 800 :=
  lem_rows_rule hl hle P Q hreg hP0 hQ0 hε hεj hlj hlen R T hR hT htail

/-- **Lemma `lem:tails`.** "For every even `r\ge0`, the sequences `\Phi_r` and `\Psi_r` satisfy
\eqref{eq:tail}."

`Φ_r, Ψ_r` are the sequences of eq. `tailrule` (`tailPhi r`, `tailPsi r` in `TailsRule.lean`,
defined by the paper's recursion), typed at length `r` as `tailPhi' r`, `tailPsi' r`; that they
are sign sequences is part of the conclusion (the paper states it with the definition). -/
theorem lem_tails (r : ℕ) (hr : Even r) :
    IsSignSeq (tailPhi' r) ∧ IsSignSeq (tailPsi' r) ∧ TailCond400 (tailPhi' r) (tailPsi' r) :=
  lem_tails_rule r hr

/-- **Lemma `lem:select`.** "Let `\mathcal{P}\subset\ZZ/j\ZZ` be a set of `N` elements, and let `k`
be an integer with `13\le k\le N` and `j\le196k^2`. Suppose that `|\widehat{\mathcal{P}}(\ell)|\le
N/33` for `1\le\ell<j`. Then there is a set `S\subset\mathcal{P}` of size `k` with
`|\widehat{S}(\ell)|\le k-\tfrac38` for `1\le\ell<j`."

Here `\widehat{S}(\ell)=\sum_{x\in S}\omega^{\ell x}` is `∑ x ∈ S, chi (ℓ * x)` with
`chi u = ω^u` (`Fourier.lean`), and `1 ≤ ℓ < j` is `ℓ : ZMod j`, `ℓ ≠ 0`; `N` is `P.card`. -/
theorem lem_select {j : ℕ} [NeZero j] (P : Finset (ZMod j)) (k : ℕ)
    (hk : 13 ≤ k) (hkP : k ≤ P.card) (hj : j ≤ 196 * k ^ 2)
    (hP : ∀ ℓ : ZMod j, ℓ ≠ 0 → ‖∑ x ∈ P, chi (ℓ * x)‖ ≤ (P.card : ℝ) / 33) :
    ∃ S : Finset (ZMod j), S ⊆ P ∧ S.card = k ∧
      ∀ ℓ : ZMod j, ℓ ≠ 0 → ‖∑ x ∈ S, chi (ℓ * x)‖ ≤ (k : ℝ) - 3 / 8 :=
  SignCond.lem_select P k hk hkP hj hP

/-- **Proposition `prop:large`.** "For every `j\ge9999` and each `\beta\in\{1,3\}`, there are a sign
matrix `X` of order `4j+\beta` and a number `\tau>0` with `\tau^2I\preceq XX^\top\prec4\tau^2I`."
No hypotheses. -/
theorem prop_large : ∀ j : ℕ, 9999 ≤ j → ∀ β : ℕ, (β = 1 ∨ β = 3) →
    ∃ X : Matrix (Fin (4 * j + β)) (Fin (4 * j + β)) ℝ, IsSign X ∧
      ∃ τ : ℝ, 0 < τ ∧ WindowAt X τ :=
  prop_large_tau

/-- **Proposition `prop:finite`** (computational hypothesis; the statement is `PropFiniteTau` in
`HypothesesTau.lean`). "1. For every `16\le j\le9998` there are sign sequences `a,b,c,d` of length
`j` with sums `(-s,s,s,s)`, where `s\ge1` is an integer with `(2s-2)^2\le2j\le(2s+2)^2`, such that,
with `\rho=\sqrt{2j}`, `(\rho+2)^2\le E_\ell<(2\rho-2)^2` for `1\le\ell<j`. 2. For every odd
`n\le63` with `n\ne3` there are an `n\times n` sign matrix `A` and a rational number `t>0` with
`tI\preceq AA^\top\prec4tI`." -/
abbrev prop_finite : Prop := PropFiniteTau

/-- **Lemma `lem:power`.** "Let `q\in\ZZ^j` be indexed by `\ZZ/j\ZZ`, and let `q^{*k}` denote its
`k`-fold cyclic convolution. Then, for every `\ell` and every `k\ge1`,
`|\widehat{q}(\ell)|\le\left(\sum_{t}\left|(q^{*k})_t\right|\right)^{1/k}`." -/
theorem lem_power {j : ℕ} [NeZero j] (q : ZMod j → ℤ) (ℓ k : ℕ) (hk : 1 ≤ k) :
    ‖hat (fun v => (q v : ℝ)) ℓ‖ ≤ (∑ t, |(convPow q k t : ℝ)|) ^ ((1 : ℝ) / k) :=
  power_bound q ℓ k hk

/-- **Lemma `lem:tools`.** "1. If two rows of `A` have numbers of entries `-1` of the same parity,
then their inner product is congruent to `n` modulo `4`. 2. For all nonzero `v,w\in\RR^n`, we have
`\kappa(A)^2\ge\dfrac{v^\top Gv}{v^\top v}\cdot\dfrac{w^\top w}{w^\top Gw}`. In particular,
`\kappa(A)^2\ge\lambda_{\max}(B)/\lambda_{\min}(B)` for every principal submatrix `B` of `G`, and
`\kappa(A)^2\ge(n+|g|)/(n-|g|)` for every off-diagonal entry `g` of `G`."

`A` is an `n × n` sign matrix and `G = AAᵀ`; `negCount A i` is the number of entries `-1` in row
`i`. Part 2 is stated for every `c` with `κ(A) ≤ c` (`CondLe A c`) in the multiplied-out form
`(vᵀGv)(wᵀw) ≤ c²(wᵀGw)(vᵀv)` (with `wᵀGw > 0`); the statement about `λ_max(B)/λ_min(B)` is the same
inequality for the principal submatrices `G.submatrix f f` (`f` injective) at arbitrary vectors,
and the last statement is `n + |g| ≤ c²(n - |g|)` (with `|g| < n`). -/
theorem lem_tools {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSign A) :
    (∀ i j : Fin n, negCount A i % 2 = negCount A j % 2 →
      ∃ g : ℤ, (A * Aᵀ) i j = g ∧ g ≡ n [ZMOD 4]) ∧
    ∀ c : ℝ, CondLe A c →
      (∀ v w : Fin n → ℝ, w ≠ 0 → 0 < w ⬝ᵥ ((A * Aᵀ) *ᵥ w) ∧
        (v ⬝ᵥ ((A * Aᵀ) *ᵥ v)) * (w ⬝ᵥ w) ≤ c ^ 2 * (w ⬝ᵥ ((A * Aᵀ) *ᵥ w)) * (v ⬝ᵥ v)) ∧
      (∀ (k : ℕ) (f : Fin k → Fin n), Function.Injective f → ∀ u w : Fin k → ℝ, w ≠ 0 →
        0 < w ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ w) ∧
        (u ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ u)) * (w ⬝ᵥ w) ≤
          c ^ 2 * (w ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ w)) * (u ⬝ᵥ u)) ∧
      (∀ i j : Fin n, i ≠ j → (n : ℝ) + |(A * Aᵀ) i j| ≤ c ^ 2 * (n - |(A * Aᵀ) i j|) ∧
        |(A * Aᵀ) i j| < n) :=
  SignCond.lem_tools A hA

/-- **Lemma `lem:matching`.** "Let `\Gamma` be a graph on `n` vertices that consists of `k\ge1`
disjoint edges and `r=n-2k\ge1` isolated vertices, and let `N` be its adjacency matrix. For real
numbers `x,y,z`, the eigenvalues of `xI+yJ+zN` are `x-z` with multiplicity `k`, `x+z` with
multiplicity `k-1`, `x` with multiplicity `r-1`, and the two roots of
`\lambda^2-(2x+z+ny)\lambda+(x+z)(x+ry)+2kxy`."

The graph is given by an involution `μ` (`μ i ≠ i`: `i` is matched to `μ i`; `μ i = i`: `i` is
isolated), `N = matchAdj μ`, `xI + yJ + zN = matchingMat μ x y z`, `𝟙_E = indE μ`, `𝟙_I = indI μ`.
The statement about eigenvalues and multiplicities is formalised as the decomposition in the
paper's proof: the matrix acts as `x - z` on `e_p - e_{μp}`, as `x + z` on the vectors constant on
each edge, zero on the isolated vertices and with sum zero, as `x` on the vectors supported on the
isolated vertices with sum zero, and on `𝟙_E, 𝟙_I` by the paper's two displayed formulas. Not
formalised: the dimension count, and that the characteristic polynomial of the `2 × 2` matrix is the
displayed quadratic. The hypotheses `k ≥ 1`, `r ≥ 1` are kept but not used. -/
theorem lem_matching {n : ℕ} (μ : Fin n → Fin n) (hμ : ∀ i, μ (μ i) = i) (k : ℕ)
    (hk : (Finset.univ.filter fun i => μ i ≠ i).card = 2 * k) (hk1 : 1 ≤ k)
    (hr1 : 1 ≤ n - 2 * k) (x y z : ℝ) :
    (∀ p, μ p ≠ p → matchingMat μ x y z *ᵥ (Pi.single p 1 - Pi.single (μ p) 1) =
        (x - z) • (Pi.single p 1 - Pi.single (μ p) 1)) ∧
    (∀ u : Fin n → ℝ, (∀ i, u (μ i) = u i) → (∀ i, μ i = i → u i = 0) → ∑ i, u i = 0 →
        matchingMat μ x y z *ᵥ u = (x + z) • u) ∧
    (∀ u : Fin n → ℝ, (∀ i, μ i ≠ i → u i = 0) → ∑ i, u i = 0 →
        matchingMat μ x y z *ᵥ u = x • u) ∧
    matchingMat μ x y z *ᵥ indE μ = (x + z + 2 * k * y) • indE μ + (2 * k * y) • indI μ ∧
    matchingMat μ x y z *ᵥ indI μ =
      (((n - 2 * k : ℕ) : ℝ) * y) • indE μ + (x + ((n - 2 * k : ℕ) : ℝ) * y) • indI μ :=
  SignCond.lem_matching μ hμ k hk hk1 hr1 x y z

end SignCond.Paper
