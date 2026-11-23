import SignCond.RowsPaper
import SignCond.TailsRule

/-!
# Lemma `lem:square` (first coefficients) and Lemma `lem:rows` (new form, tails with `6r + 400`)

* `lem_square_first`: the last sentence of Lemma `lem:square`, "If `A₀ = B₀ = 1`, then
  `P₀ = Q₀ = 1`".
* `coeff_append_left`, `golayG_first`: "Doubling preserves the first coefficients, so all these
  pairs have first coefficients `1`" (the fixed pair `golayG g` of each length `g ∈ 𝒢`).
* `lem_rows_rule`: Lemma `lem:rows` of the rewritten paper, with eq. `tail` in the form
  `|Φ(z)|² + |Ψ(z)|² ≤ 6r + 400` (`TailCond400`) and the conclusion `4s² ≤ E_ℓ ≤ 12j - 8s² + 800`.
  The proof is that of `rows_paper` (`RowsPaper.lean`); the extra `400` in the tail bound becomes
  the extra `800` in the energy bound.
-/

open Complex

namespace SignCond

/-- **Lemma `lem:square`, first coefficients.** "If `A_0=B_0=1`, then `P_0=Q_0=1`." Here `(A, B)`
is a Golay pair of length `l ≥ 1` and `(P, Q) = golaySquare A B`. (The Golay hypothesis is kept to
mirror the paper; the computation `U₀ = 1`, `V₀ = 0`, `P₀ = B₀`, `Q₀ = A₀` does not need it.) -/
theorem lem_square_first {l : ℕ} (hl : 1 ≤ l) (A B : Fin l → ℤ) (_h : IsGolayPair A B)
    (hA : coeff A 0 = 1) (hB : coeff B 0 = 1) :
    coeff (golaySquare A B).1 0 = 1 ∧ coeff (golaySquare A B).2 0 = 1 := by
  have hl0 : 0 < l := hl
  have hA' : A ⟨0, hl0⟩ = 1 := by simpa [coeff, hl0] using hA
  have hB' : B ⟨0, hl0⟩ = 1 := by simpa [coeff, hl0] using hB
  have h0 : 0 < l ^ 2 := by positivity
  have hmod : (Fin.cast (show l ^ 2 = l * l by ring) ⟨0, h0⟩ : Fin (l * l)).modNat = ⟨0, hl0⟩ := by
    ext; simp [Fin.modNat]
  have hdiv : (Fin.cast (show l ^ 2 = l * l by ring) ⟨0, h0⟩ : Fin (l * l)).divNat = ⟨0, hl0⟩ := by
    ext; simp [Fin.divNat]
  have hU : halfSum A B ⟨0, hl0⟩ = 1 := by simp [halfSum, hA', hB']
  have hV : halfDiff A B ⟨0, hl0⟩ = 0 := by simp [halfDiff, hA', hB']
  constructor
  · simp only [coeff, dif_pos h0, golaySquare, Function.comp_apply, sqP]
    rw [hmod, hdiv, hU, hV, hB']; ring
  · simp only [coeff, dif_pos h0, golaySquare, Function.comp_apply, sqQ]
    rw [hmod, hdiv, hU, hV, hA']; ring

theorem coeff_append_left {n m : ℕ} (P : Fin n → ℤ) (Q : Fin m → ℤ) {x : ℕ} (hx : x < n) :
    coeff (Fin.append P Q) x = coeff P x := by
  have hx' : x < n + m := by omega
  simp only [coeff, dif_pos hx, dif_pos hx']
  have : (⟨x, hx'⟩ : Fin (n + m)) = Fin.castAdd m ⟨x, hx⟩ := rfl
  rw [this, Fin.append_left]

theorem coeff_castPair_fst {n m : ℕ} (h : m = n) (p : (Fin n → ℤ) × (Fin n → ℤ)) (x : ℕ) :
    coeff (castPair h p).1 x = coeff p.1 x := coeff_comp_cast h p.1 x

theorem coeff_castPair_snd {n m : ℕ} (h : m = n) (p : (Fin n → ℤ) × (Fin n → ℤ)) (x : ℕ) :
    coeff (castPair h p).2 x = coeff p.2 x := coeff_comp_cast h p.2 x

/-- Paper: "Doubling preserves the first coefficients, so all these pairs have first coefficients
`1`": the fixed Golay pair `golayG g` of each length `g ∈ 𝒢` (and `g = 1`) has `P₀ = Q₀ = 1`. -/
theorem golayG_first : ∀ g : ℕ, (InG g ∨ g = 1) →
    coeff (golayG g).1 0 = 1 ∧ coeff (golayG g).2 0 = 1 := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro hg
  rw [golayG]
  split_ifs with h1 h10 h26 h100 h2
  · rw [coeff_castPair_fst, coeff_castPair_snd]; simp [coeff, golayOne]
  · rw [coeff_castPair_fst, coeff_castPair_snd]; simp [coeff, golayA10, golayB10]
  · rw [coeff_castPair_fst, coeff_castPair_snd]; simp [coeff, golayA26, golayB26]
  · rw [coeff_castPair_fst, coeff_castPair_snd]
    exact lem_square_first (by norm_num) _ _ isGolayPair_10
      (by simp [coeff, golayA10]) (by simp [coeff, golayB10])
  · have hG : InG g := hg.resolve_right h1
    have hh := half_inG hG h10 h26 h100
    have hpos : 0 < g / 2 := by omega
    obtain ⟨e1, -⟩ := ih (g / 2) (by omega) hh.1
    rw [coeff_castPair_fst, coeff_castPair_snd]
    simp only [golayDouble]
    rw [coeff_append_left _ _ hpos, coeff_append_left _ _ hpos]
    exact ⟨e1, e1⟩
  · exfalso
    have hG : InG g := hg.resolve_right h1
    exact h2 (half_inG hG h10 h26 h100).2

/-- **Lemma `lem:rows`** (rewritten paper). "Let `l\ge4` be even, and let `(P,Q)` be a regular
Golay pair of length `l^2` with `P_0=Q_0=1`. Let `j\ge1` and `\varepsilon\in\{0,1\}` with
`\varepsilon\equiv j\pmod2`, and suppose that `l^2\le j+\varepsilon`. Let `\overline{P}` and
`\overline{Q}` be obtained from `P` and `Q` by deleting the first coefficient when
`\varepsilon=1`, and put `s=l-\varepsilon` and `r=j-l^2+\varepsilon`. Let `\Phi` and `\Psi` be sign
sequences of length `r` with \eqref{eq:tail} [`Φ(1) = Ψ(1) = 0` and
`|Φ(z)|² + |Ψ(z)|² ≤ 6r + 400` on `|z| = 1`]. Then the sequences `a=-(\overline{P}|\Phi)`,
`b=\overline{P}|{-\Phi}`, `c=\overline{Q}|\Psi`, `d=\overline{Q}|{-\Psi}` have length `j` and sums
`(-s,s,s,s)`, and their energies satisfy `4s^2\le E_\ell\le12j-8s^2+800` for all `\ell`."

(`hlen` is the arithmetic identity `(l² - ε) + r = j`, as in `Paper.lem_rows`.) -/
theorem lem_rows_rule {l j ε : ℕ} [NeZero j] (hl : 4 ≤ l) (_hle : Even l) (P Q : Fin (l ^ 2) → ℤ)
    (hreg : IsRegular l P Q) (hP0 : coeff P 0 = 1) (hQ0 : coeff Q 0 = 1)
    (hε : ε = 0 ∨ ε = 1) (_hεj : ε % 2 = j % 2) (hlj : l ^ 2 ≤ j + ε)
    (hlen : l ^ 2 - ε + (j + ε - l ^ 2) = j) (R T : Fin (j + ε - l ^ 2) → ℤ)
    (_hR : IsSignSeq R) (_hT : IsSignSeq T) (htail : TailCond400 R T) :
    let s : ℝ := (l : ℝ) - ε
    let abcd := rowsSeqs hlen P Q R T
    (vsum (toVec abcd.1) = -s ∧ vsum (toVec abcd.2.1) = s ∧ vsum (toVec abcd.2.2.1) = s ∧
        vsum (toVec abcd.2.2.2) = s) ∧
      ∀ ℓ : ℕ, 4 * s ^ 2 ≤ energy (toVec abcd.1) (toVec abcd.2.1) (toVec abcd.2.2.1)
          (toVec abcd.2.2.2) ℓ ∧
        energy (toVec abcd.1) (toVec abcd.2.1) (toVec abcd.2.2.1) (toVec abcd.2.2.2) ℓ ≤
          12 * j - 8 * s ^ 2 + 800 := by
  intro s abcd
  obtain ⟨⟨_, _, hG⟩, hP1, hQ1⟩ := hreg
  obtain ⟨hR1, hT1, hRT⟩ := htail
  have hl2 : ε ≤ l ^ 2 := by rcases hε with rfl | rfl <;> nlinarith
  set n := l ^ 2 - ε
  -- the four polynomials
  have ea : ∀ z, peval abcd.1 z = -(peval (dropFirst ε P) z + z ^ n * peval R z) := by
    intro z; simp only [abcd, rowsSeqs]; rw [peval_castLen, peval_neg, peval_append]
  have eb : ∀ z, peval abcd.2.1 z = peval (dropFirst ε P) z - z ^ n * peval R z := by
    intro z; simp only [abcd, rowsSeqs]
    rw [peval_castLen, peval_append, peval_neg, mul_neg, ← sub_eq_add_neg]
  have ec : ∀ z, peval abcd.2.2.1 z = peval (dropFirst ε Q) z + z ^ n * peval T z := by
    intro z; simp only [abcd, rowsSeqs]; rw [peval_castLen, peval_append]
  have ed : ∀ z, peval abcd.2.2.2 z = peval (dropFirst ε Q) z - z ^ n * peval T z := by
    intro z; simp only [abcd, rowsSeqs]
    rw [peval_castLen, peval_append, peval_neg, mul_neg, ← sub_eq_add_neg]
  have dP := peval_dropFirst hε hl2 P
  have dQ := peval_dropFirst hε hl2 Q
  rw [hP0] at dP
  rw [hQ0] at dQ
  have hεR : (ε : ℝ) = 0 ∨ (ε : ℝ) = 1 := by rcases hε with rfl | rfl <;> simp
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun ℓ => ?_⟩
  -- sums
  · apply Complex.ofReal_injective
    rw [vsum_toVec, ea, hR1, mul_zero, add_zero]
    have := dP 1; simp only [one_pow, one_mul] at this
    rw [this, hP1]; simp only [s]; push_cast; ring
  · apply Complex.ofReal_injective
    rw [vsum_toVec, eb, hR1, mul_zero, sub_zero]
    have := dP 1; simp only [one_pow, one_mul] at this
    rw [this, hP1]; simp only [s]; push_cast; ring
  · apply Complex.ofReal_injective
    rw [vsum_toVec, ec, hT1, mul_zero, add_zero]
    have := dQ 1; simp only [one_pow, one_mul] at this
    rw [this, hQ1]; simp only [s]; push_cast; ring
  · apply Complex.ofReal_injective
    rw [vsum_toVec, ed, hT1, mul_zero, sub_zero]
    have := dQ 1; simp only [one_pow, one_mul] at this
    rw [this, hQ1]; simp only [s]; push_cast; ring
  -- energies
  set z := omega j ^ ℓ
  have hz : ‖z‖ = 1 := norm_omega_pow ℓ
  have hzn : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hE : energy (toVec abcd.1) (toVec abcd.2.1) (toVec abcd.2.2.1) (toVec abcd.2.2.2) ℓ =
      2 * (‖peval (dropFirst ε P) z‖ ^ 2 + ‖peval (dropFirst ε Q) z‖ ^ 2) +
        2 * (‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2) := by
    simp only [energy, hat_toVec]
    rw [ea, eb, ec, ed]
    exact rows_energy_identity _ _ _ _ _ hzn
  have nP : ‖peval (dropFirst ε P) z‖ = ‖peval P z - ((ε : ℝ) : ℂ)‖ := by
    have := congrArg norm (dP z)
    rw [norm_mul, norm_pow, hz, one_pow, one_mul] at this
    rw [this]; push_cast; ring_nf
  have nQ : ‖peval (dropFirst ε Q) z‖ = ‖peval Q z - ((ε : ℝ) : ℂ)‖ := by
    have := congrArg norm (dQ z)
    rw [norm_mul, norm_pow, hz, one_pow, one_mul] at this
    rw [this]; push_cast; ring_nf
  have hGz : ‖peval P z‖ ^ 2 + ‖peval Q z‖ ^ 2 = 2 * (l : ℝ) ^ 2 := by
    rw [hG z hz]; push_cast; ring
  have hb := rows_prefix_bounds (peval P z) (peval Q z) (l := (l : ℝ)) (ε := (ε : ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hGz
  have ht := hRT z hz
  have hlR : (3 : ℝ) ≤ l := by exact_mod_cast (by omega : 3 ≤ l)
  have har := rows_arith_le ((j + ε - l ^ 2 : ℕ) : ℝ) hεR hlR
  have hr : ((j + ε - l ^ 2 : ℕ) : ℝ) = j + ε - (l : ℝ) ^ 2 := by
    rw [Nat.cast_sub hlj]; push_cast; ring
  have hj : ((l : ℝ) ^ 2 - ε + ((j + ε - l ^ 2 : ℕ) : ℝ)) = j := by rw [hr]; ring
  rw [hj] at har
  rw [hE, nP, nQ]
  have h0 : 0 ≤ ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 := by positivity
  simp only [s]
  constructor <;> linarith [hb.1, hb.2]

end SignCond
