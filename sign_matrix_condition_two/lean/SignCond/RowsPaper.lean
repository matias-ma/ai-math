import SignCond.Fourier
import SignCond.BasePairs

/-!
# Lemma `lem:rows` for the sequences `a, b, c, d` of length `j` regarded as vectors of `ℝ^j`

* `peval_eq_range`, `coeff_dropFirst`, `peval_dropFirst` (`z^ε P̄(z) = P(z) - ε P₀`);
* `hat_toVec` (`x̂(ℓ) = x(ω^ℓ)` for a sequence of length `j`), `vsum_toVec` (`Σ x = x(1)`);
* `rows_paper`: the lemma.
-/

open Complex

namespace SignCond

theorem coeff_of_lt {n : ℕ} (P : Fin n → ℤ) (i : Fin n) : coeff P i = P i := by
  simp [coeff, i.isLt]

theorem peval_eq_range {n : ℕ} (P : Fin n → ℤ) (z : ℂ) :
    peval P z = ∑ i ∈ Finset.range n, (coeff P i : ℂ) * z ^ i := by
  rw [peval, ← Fin.sum_univ_eq_sum_range (fun i => (coeff P i : ℂ) * z ^ i)]
  exact Finset.sum_congr rfl fun i _ => by rw [coeff_of_lt]

theorem coeff_dropFirst (ε : ℕ) {n : ℕ} (hε : ε ≤ n) (P : Fin n → ℤ) (i : ℕ) :
    coeff (dropFirst ε P) i = coeff P (i + ε) := by
  by_cases hi : i < n - ε
  · simp [coeff, dropFirst, hi, show i + ε < n by omega]
  · simp [coeff, hi, show ¬ (i + ε < n) by omega]

/-- Deleting the first coefficient: `z^ε P̄(z) = P(z) - ε P₀` for `ε ∈ {0, 1}`. -/
theorem peval_dropFirst {ε : ℕ} (hε : ε = 0 ∨ ε = 1) {n : ℕ} (hn : ε ≤ n) (P : Fin n → ℤ)
    (z : ℂ) : z ^ ε * peval (dropFirst ε P) z = peval P z - ε * coeff P 0 := by
  rw [peval_eq_range, peval_eq_range]
  simp_rw [coeff_dropFirst ε hn P]
  rcases hε with rfl | rfl
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ', Nat.add_sub_cancel, Finset.mul_sum]
    simp only [pow_one, Nat.cast_one, one_mul, pow_zero, mul_one, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

variable {j : ℕ} [NeZero j]

/-- Paper: "`x̂(ℓ) = x(ω^ℓ)` when `n = j`". -/
theorem hat_toVec (x : Fin j → ℤ) (ℓ : ℕ) : hat (toVec x) ℓ = peval x (omega j ^ ℓ) := by
  rw [peval_eq_range, hat, ← sum_zmod_val (fun i => (coeff x i : ℂ) * (omega j ^ ℓ) ^ i)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← pow_mul, toVec, coeff, dif_pos (ZMod.val_lt v)]
  push_cast
  rfl

theorem vsum_toVec (x : Fin j → ℤ) : (vsum (toVec x) : ℂ) = peval x 1 := by
  have h := hat_toVec x 0
  simp only [hat, zero_mul, pow_zero, mul_one] at h
  rw [vsum]; push_cast; rw [h]

theorem peval_castLen {m n : ℕ} (h : m = n) (x : Fin m → ℤ) (z : ℂ) :
    peval (castLen h x) z = peval x z := peval_comp_cast h.symm x z

/-- **Lemma `lem:rows`.** -/
theorem rows_paper {l j' ε : ℕ} [NeZero j'] (hl : 4 ≤ l) (_hle : Even l) (P Q : Fin (l ^ 2) → ℤ)
    (hreg : IsRegular l P Q) (hP0 : coeff P 0 = 1) (hQ0 : coeff Q 0 = 1)
    (hε : ε = 0 ∨ ε = 1) (_hεj : ε % 2 = j' % 2) (hlj : l ^ 2 ≤ j' + ε)
    (hlen : l ^ 2 - ε + (j' + ε - l ^ 2) = j') (R T : Fin (j' + ε - l ^ 2) → ℤ)
    (_hR : IsSignSeq R) (_hT : IsSignSeq T) (htail : TailCond R T) :
    let s : ℝ := (l : ℝ) - ε
    let abcd := rowsSeqs hlen P Q R T
    (vsum (toVec abcd.1) = -s ∧ vsum (toVec abcd.2.1) = s ∧ vsum (toVec abcd.2.2.1) = s ∧
        vsum (toVec abcd.2.2.2) = s) ∧
      ∀ ℓ : ℕ, 4 * s ^ 2 ≤ energy (toVec abcd.1) (toVec abcd.2.1) (toVec abcd.2.2.1)
          (toVec abcd.2.2.2) ℓ ∧
        energy (toVec abcd.1) (toVec abcd.2.1) (toVec abcd.2.2.1) (toVec abcd.2.2.2) ℓ ≤
          12 * j' - 8 * s ^ 2 := by
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
  set z := omega j' ^ ℓ
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
  have har := rows_arith_le ((j' + ε - l ^ 2 : ℕ) : ℝ) hεR hlR
  have hr : ((j' + ε - l ^ 2 : ℕ) : ℝ) = j' + ε - (l : ℝ) ^ 2 := by
    rw [Nat.cast_sub hlj]; push_cast; ring
  have hj : ((l : ℝ) ^ 2 - ε + ((j' + ε - l ^ 2 : ℕ) : ℝ)) = j' := by rw [hr]; ring
  rw [hj] at har
  rw [hE, nP, nQ]
  have h0 : 0 ≤ ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 := by positivity
  simp only [s]
  constructor <;> linarith [hb.1, hb.2]

end SignCond
