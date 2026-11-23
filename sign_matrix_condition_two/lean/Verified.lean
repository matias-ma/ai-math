import VerifiedSequenceRange
import SignCond.FiniteSmall
import SignCond.Paper

namespace SignCond

/-- The two finite families in Proposition prop:finite. -/
theorem verifiedFinite : PropFiniteTau :=
  ⟨checkedSequences, finiteSmallMatrices⟩

/-- The main theorem, with both finite families supplied. -/
theorem verifiedMain :
    (∀ n : ℕ, 1 ≤ n → ∃ A : Matrix (Fin n) (Fin n) ℝ, IsSign A ∧ CondLe A 2 ∧
      (n ≠ 3 → CondLt2 A)) ∧ ∀ A : Matrix (Fin 3) (Fin 3) ℝ, IsSign A →
      ∀ c : ℝ, 0 ≤ c → CondLe A c → 2 ≤ c :=
  Paper.thm_main verifiedFinite

#print axioms verifiedFinite
#print axioms verifiedMain

end SignCond
