import SignCond.DoublingTau

namespace SignCond.FiniteMatrix
open Matrix

variable {n : ℕ}
abbrev QMat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ

/-- An exact rational LDLᵀ factorization certifies positive semidefiniteness over ℝ. -/
theorem psd (M L : QMat n) (d : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i)
    (h : ∀ i j, M i j = ∑ k, L i k * d k * L j k) :
    (M.map (Rat.cast : ℚ → ℝ)).PosSemidef := by
  let B := L.map (Rat.cast : ℚ → ℝ)
  let D := fun i => (d i : ℝ)
  have heq : M.map (Rat.cast : ℚ → ℝ) = B * diagonal D * Bᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, h, Rat.cast_sum, Rat.cast_mul,
      Matrix.mul_diagonal, Matrix.transpose_apply, B, D]
  rw [heq, ← conjTranspose_eq_transpose_of_trivial]
  apply PosSemidef.mul_mul_conjTranspose_same
  exact PosSemidef.diagonal (fun i => by change 0 ≤ (d i : ℝ); exact_mod_cast hd i)


/-- The two rational factorizations bound the Gram matrix at the rational scale t. -/
theorem window (A L U : QMat n) (l u : Fin n → ℚ) (t b : ℚ) (ht : 0 < t)
    (hb : b < 4*t) (hs : ∀ i j, A i j = 1 ∨ A i j = -1)
    (hl : ∀ i, 0 ≤ l i) (hu : ∀ i, 0 ≤ u i)
    (hL : ∀ i j, ((A * Aᵀ) - t • 1) i j = ∑ k, L i k * l k * L j k)
    (hU : ∀ i j, (b • 1 - (A * Aᵀ)) i j = ∑ k, U i k * u k * U j k) :
    ∃ (X : Matrix (Fin n) (Fin n) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
      (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  let X := A.map (Rat.cast : ℚ → ℝ)
  have liftGram (i j : Fin n) : ((A * Aᵀ) i j : ℝ) = (X * Xᵀ) i j := by
    simp [X, Matrix.mul_apply, Matrix.transpose_apply]
  have liftLow : ((A * Aᵀ - t • 1).map (Rat.cast : ℚ → ℝ)) =
      X * Xᵀ - (t : ℝ) • 1 := by
    ext i j; simp [Matrix.sub_apply, Matrix.smul_apply, liftGram, Matrix.one_apply]
    split <;> simp_all
  have liftHigh : ((b • 1 - A * Aᵀ).map (Rat.cast : ℚ → ℝ)) =
      (b : ℝ) • 1 - X * Xᵀ := by
    ext i j; simp [Matrix.sub_apply, Matrix.smul_apply, liftGram, Matrix.one_apply]
    split <;> simp_all
  refine ⟨X, t, ?_, ht, liftLow ▸ psd _ L l hl hL, ?_⟩
  · intro i j
    rcases hs i j with h | h <;> simp [X, h]
  · have h := psd _ U u hu hU
    rw [liftHigh] at h
    have hgap : 0 < 4 * (t : ℝ) - b := by exact_mod_cast (sub_pos.mpr hb)
    have hpos := Matrix.PosDef.posSemidef_add h (posDef_smul_one hgap)
    convert hpos using 1
    rw [sub_smul]
    abel

end SignCond.FiniteMatrix
