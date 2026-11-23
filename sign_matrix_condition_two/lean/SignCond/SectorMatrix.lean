import SignCond.SectorK

/-!
# Lemma `lem:sector`: `2jI ⪯ KKᵀ ⪯ 8jI` for both borders

`K1_form`, `K3_form` compute `‖Kᵀx‖²` in the coordinates of the paper's splitting (see
`SectorK.lean`); `sector_window` is the lemma.
-/

open Matrix

namespace SignCond

/-- The window in quadratic-form terms: `2jI ⪯ MMᵀ ⪯ 8jI` iff
`2j‖x‖² ≤ ‖Mᵀx‖² ≤ 8j‖x‖²` for all `x`. -/
theorem window_iff_form {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (j : ℝ) :
    Window M j ↔ ∀ x : n → ℝ, 2 * j * (x ⬝ᵥ x) ≤ (Mᵀ *ᵥ x) ⬝ᵥ (Mᵀ *ᵥ x) ∧
      (Mᵀ *ᵥ x) ⬝ᵥ (Mᵀ *ᵥ x) ≤ 8 * j * (x ⬝ᵥ x) := by
  unfold Window
  have e : (8 * j) = (2 : ℝ) ^ 2 * (2 * j) := by ring
  rw [e, window_iff]

/-- The window gives the condition-number bound: `2jI ⪯ MMᵀ ⪯ 8jI` with `j > 0` implies
`CondLe M 2`, i.e. `κ(M) ≤ 2`. -/
theorem condLe_of_window {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {j : ℝ}
    (hj : 0 < j) (h : Window M j) : CondLe M 2 :=
  ⟨2 * j, by positivity, h.1, by rw [show (2 : ℝ) ^ 2 * (2 * j) = 8 * j by ring]; exact h.2⟩

theorem K1_form (s k : ℝ) (j : ℕ) (x : Fin 4 ⊕ Fin 1 → ℝ) :
    ((Kmat 1 ![-s, s, s, s] k j)ᵀ *ᵥ x) ⬝ᵥ ((Kmat 1 ![-s, s, s, s] k j)ᵀ *ᵥ x) =
      (-(2 * (s - k)) * ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) +
          2 * Real.sqrt j * x (.inr 0)) ^ 2 +
        (2 * Real.sqrt j * ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) + x (.inr 0)) ^ 2 +
        (2 * (s + k)) ^ 2 * (x (.inl 0) ^ 2 + x (.inl 1) ^ 2 + x (.inl 2) ^ 2 + x (.inl 3) ^ 2 -
          ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2) := by
  simp [Kmat, fromBlocks_transpose, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four,
    quat, Pimat, Ub, Omat, Hmat, Vb, Gb, sigmaOf, Matrix.mul_apply]
  ring

theorem K3_form (s k : ℝ) (j : ℕ) (x : Fin 4 ⊕ Fin 3 → ℝ) :
    ((Kmat 3 ![-s, s, s, s] k j)ᵀ *ᵥ x) ⬝ᵥ ((Kmat 3 ![-s, s, s, s] k j)ᵀ *ᵥ x) =
      phi3 (2 * (s - k)) (2 * Real.sqrt j)
          ((x (.inl 0) + x (.inl 1) + x (.inl 2) - x (.inl 3)) / 2)
          ((x (.inl 0) + x (.inl 1) - x (.inl 2) + x (.inl 3)) / 2)
          ((x (.inl 0) - x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2)
          (x (.inr 0)) (x (.inr 1)) (x (.inr 2)) +
        (2 * (s + k)) ^ 2 * ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 := by
  simp [Kmat, fromBlocks_transpose, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four,
    Fin.sum_univ_three, quat, Pimat, Ub, Omat, Hmat, Vb, Gb, sigmaOf, Matrix.mul_apply, phi3]
  ring


/-- **Lemma `lem:sector`.** Let `j ≥ 5`, `s ≥ k ≥ 0` integers, `r = (-s, s, s, s)`, `ρ = √(2j)`,
`α = 2(s-k)`, `γ = 2(s+k)`, `ρ ≤ γ ≤ 2ρ`, and `α ≤ ρ` or (`ρ ≥ 14` and `α ≤ ρ + 2/5`). Then
`2jI ⪯ KKᵀ ⪯ 8jI` for `β = 1` and for `β = 3`. -/
theorem sector_window {j s k : ℕ} (hj : 5 ≤ j) (hks : k ≤ s)
    (hγ1 : Real.sqrt (2 * j) ≤ 2 * ((s : ℝ) + k)) (hγ2 : 2 * ((s : ℝ) + k) ≤ 2 * Real.sqrt (2 * j))
    (hcase : 2 * ((s : ℝ) - k) ≤ Real.sqrt (2 * j) ∨
      (14 ≤ Real.sqrt (2 * j) ∧ 2 * ((s : ℝ) - k) ≤ Real.sqrt (2 * j) + 2 / 5)) :
    Window (Kmat 1 ![-(s : ℝ), s, s, s] k j) j ∧ Window (Kmat 3 ![-(s : ℝ), s, s, s] k j) j := by
  set ρ := Real.sqrt (2 * (j : ℝ)) with hρdef
  set α : ℝ := 2 * ((s : ℝ) - k) with hαdef
  set γ : ℝ := 2 * ((s : ℝ) + k) with hγdef
  set c : ℝ := 2 * Real.sqrt j with hcdef
  have hj5 : (5 : ℝ) ≤ j := by exact_mod_cast hj
  have hksR : (k : ℝ) ≤ s := by exact_mod_cast hks
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hρ2 : ρ ^ 2 = 2 * j := Real.sq_sqrt (by positivity)
  have hc2 : c ^ 2 = 4 * j := by
    rw [hcdef, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ3 : 3 ≤ ρ := by nlinarith
  have hα0 : 0 ≤ α := by rw [hαdef]; linarith
  have hαγ : α ≤ γ := by rw [hαdef, hγdef]; linarith
  have ht : ρ ^ 2 = c ^ 2 / 2 := by rw [hρ2, hc2]; ring
  have hL1 := sector_nonneg hα0 hρ3 hαγ hγ2 hcase (Or.inl rfl)
  have hL4 := sector_nonneg hα0 hρ3 hαγ hγ2 hcase (Or.inr rfl)
  rw [ht] at hL1 hL4
  have H : SectorHyp α c := ⟨hL1.1, hL4.1, hL1.2, hL4.2, by rw [hc2]; linarith⟩
  have hγlo : 2 * (j : ℝ) ≤ γ ^ 2 := by rw [← hρ2]; exact pow_le_pow_left₀ hρ0 hγ1 2
  have hγhi : γ ^ 2 ≤ 8 * (j : ℝ) := by
    have := pow_le_pow_left₀ (by positivity) hγ2 2
    nlinarith
  have hlo : c ^ 2 / 2 = 2 * (j : ℝ) := by rw [hc2]; ring
  have hhi : 2 * c ^ 2 = 8 * (j : ℝ) := by rw [hc2]; ring
  constructor
  · rw [window_iff_form]
    intro x
    have hD := cs4_half (x (.inl 0)) (x (.inl 1)) (x (.inl 2)) (x (.inl 3))
    obtain ⟨b1, b2⟩ := block1_window H ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2)
      (x (.inr 0))
    rw [hlo] at b1
    rw [hhi] at b2
    have hD0 : 0 ≤ x (.inl 0) ^ 2 + x (.inl 1) ^ 2 + x (.inl 2) ^ 2 + x (.inl 3) ^ 2 -
        ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 := by linarith
    have g1 := mul_le_mul_of_nonneg_right hγlo hD0
    have g2 := mul_le_mul_of_nonneg_right hγhi hD0
    have e : x ⬝ᵥ x = (((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 +
        x (.inr 0) ^ 2) + (x (.inl 0) ^ 2 + x (.inl 1) ^ 2 + x (.inl 2) ^ 2 + x (.inl 3) ^ 2 -
        ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2) := by
      simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_one]; ring
    rw [K1_form, e, ← hαdef, ← hγdef, ← hcdef]
    constructor <;> linarith
  · rw [window_iff_form]
    intro x
    obtain ⟨b1, b2⟩ := block3_window H ((x (.inl 0) + x (.inl 1) + x (.inl 2) - x (.inl 3)) / 2)
      ((x (.inl 0) + x (.inl 1) - x (.inl 2) + x (.inl 3)) / 2)
      ((x (.inl 0) - x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) (x (.inr 0)) (x (.inr 1)) (x (.inr 2))
    rw [hlo] at b1
    rw [hhi] at b2
    have g1 := mul_le_mul_of_nonneg_right hγlo
      (sq_nonneg ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2))
    have g2 := mul_le_mul_of_nonneg_right hγhi
      (sq_nonneg ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2))
    have e : x ⬝ᵥ x =
        (((x (.inl 0) + x (.inl 1) + x (.inl 2) - x (.inl 3)) / 2) ^ 2 +
          ((x (.inl 0) + x (.inl 1) - x (.inl 2) + x (.inl 3)) / 2) ^ 2 +
          ((x (.inl 0) - x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 +
          x (.inr 0) ^ 2 + x (.inr 1) ^ 2 + x (.inr 2) ^ 2) +
        ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 := by
      simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three]; ring
    rw [K3_form, e, ← hαdef, ← hγdef, ← hcdef]
    constructor <;> linarith

end SignCond
