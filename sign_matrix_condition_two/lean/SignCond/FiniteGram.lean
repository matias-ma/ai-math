import SignCond.SmallUpper
import Mathlib.LinearAlgebra.Matrix.Gershgorin

namespace SignCond.FiniteGram
open Matrix
variable {n : ℕ}
abbrev IMat (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

theorem psd_of_dominant {M : IMat n} (hs : Mᵀ = M)
    (h : ∀ i, ∑ k ∈ Finset.univ.erase i, |M i k| ≤ M i i) : (toR M).PosSemidef := by
  apply posSemidef_of_eigen (by rw [← toR_transpose, hs])
  intro μ v hv he
  have heig : Module.End.HasEigenvalue (Matrix.toLin' (toR M)) μ := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    exact ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩
  obtain ⟨i,hi⟩ := eigenvalue_mem_ball heig
  rw [mem_closedBall_iff_norm', Real.norm_eq_abs] at hi
  have hh : ∑ k ∈ Finset.univ.erase i, ‖toR M i k‖ ≤ toR M i i := by
    simp only [toR, Matrix.map_apply, Real.norm_eq_abs, ← Int.cast_abs, ← Int.cast_sum]
    exact_mod_cast h i
  linarith [(abs_le.mp hi).2]

/-- Certify a symmetric integer matrix by a Gram factor and a diagonally dominant residual. -/
theorem gram_residual {M B R : IMat n} (h : M = B * Bᵀ + R) (hs : Rᵀ = R)
    (hr : ∀ i, ∑ k ∈ Finset.univ.erase i, |R i k| ≤ R i i) :
    (toR M).PosSemidef := by
  rw [h, toR_add, toR_mul, toR_transpose, ← conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).add (psd_of_dominant hs hr)

theorem strictWindow (A : IMat n) (m a b : ℤ) (hm : 0 < m) (ha : 0 < a) (hb : b < 4*a)
    (hs : ∀ i j, A i j = 1 ∨ A i j = -1)
    (hL : (toR (m • (A * Aᵀ) - a • 1)).PosSemidef)
    (hU : (toR (b • 1 - m • (A * Aᵀ))).PosSemidef) :
    ∃ (X : Matrix (Fin n) (Fin n) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
      (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  have hmr : 0 < (m:ℝ) := by exact_mod_cast hm
  have hgap : 0 < 4*(a:ℝ) - b := by exact_mod_cast sub_pos.mpr hb
  simp only [toR_sub,toR_smul,toR_mul,toR_transpose,toR_one] at hL hU
  refine ⟨toR A,(a:ℚ)/m,isSign_toR hs, div_pos (by exact_mod_cast ha) (by exact_mod_cast hm), ?_, ?_⟩
  · apply (posSemidef_smul_iff hmr).mp
    simpa [smul_sub, smul_smul, show (m:ℝ)*(a/m)=a by field_simp] using hL
  · have hu := Matrix.PosDef.posSemidef_add hU (posDef_smul_one hgap)
    rw [sub_smul] at hu
    apply (posDef_smul_iff (by simp [transpose_smul,transpose_mul]) hmr).mp
    push_cast
    rw [smul_sub,smul_smul,show (m:ℝ)*(4*(a/m))=4*a by field_simp]
    convert hu using 1 <;> abel

end SignCond.FiniteGram
