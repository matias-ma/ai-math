import SignCond.MatrixCases15To27
import SignCond.MatrixCases29To37
import SignCond.MatrixCases39To45
import SignCond.MatrixCases47To51
import SignCond.MatrixCases53To55
import SignCond.MatrixCases57To59
import SignCond.MatrixCases61To61
import SignCond.MatrixCases63To63
import SignCond.FiniteSmallCases

namespace SignCond
open Matrix

theorem finiteSmallMatrices (n : ℕ) (hodd : Odd n) (hmax : n ≤ 63) (hne : n ≠ 3) :
    ∃ (X : Matrix (Fin n) (Fin n) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
      (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  obtain ⟨k,hk⟩ := hodd
  have cases : n = 1 ∨ n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 11 ∨ n = 13 ∨ n = 15 ∨ n = 17 ∨ n = 19 ∨ n = 21 ∨ n = 23 ∨ n = 25 ∨ n = 27 ∨ n = 29 ∨ n = 31 ∨ n = 33 ∨ n = 35 ∨ n = 37 ∨ n = 39 ∨ n = 41 ∨ n = 43 ∨ n = 45 ∨ n = 47 ∨ n = 49 ∨ n = 51 ∨ n = 53 ∨ n = 55 ∨ n = 57 ∨ n = 59 ∨ n = 61 ∨ n = 63 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact FiniteMatrix.Order1.witness
  · exact FiniteMatrix.Order5.witness
  · exact FiniteMatrix.Order7.witness
  · exact FiniteMatrix.Order9.witness
  · exact FiniteMatrix.Order11.witness
  · exact FiniteMatrix.Order13.witness
  · exact FiniteGram.Order15.witness
  · exact FiniteGram.Order17.witness
  · exact FiniteGram.Order19.witness
  · exact FiniteGram.Order21.witness
  · exact FiniteGram.Order23.witness
  · exact FiniteGram.Order25.witness
  · exact FiniteGram.Order27.witness
  · exact FiniteGram.Order29.witness
  · exact FiniteGram.Order31.witness
  · exact FiniteGram.Order33.witness
  · exact FiniteGram.Order35.witness
  · exact FiniteGram.Order37.witness
  · exact FiniteGram.Order39.witness
  · exact FiniteGram.Order41.witness
  · exact FiniteGram.Order43.witness
  · exact FiniteGram.Order45.witness
  · exact FiniteGram.Order47.witness
  · exact FiniteGram.Order49.witness
  · exact FiniteGram.Order51.witness
  · exact FiniteGram.Order53.witness
  · exact FiniteGram.Order55.witness
  · exact FiniteGram.Order57.witness
  · exact FiniteGram.Order59.witness
  · exact FiniteGram.Order61.witness
  · exact FiniteGram.Order63.witness

end SignCond
