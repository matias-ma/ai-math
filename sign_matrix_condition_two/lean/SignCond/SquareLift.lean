import SignCond.BasePairs

/-!
# The polynomial identities defining the square (Lemma `lem:square`) and the lift (Lemma `lem:lift`)

`golaySquare` and `golayLift` are defined by their coefficients; these lemmas show they are the
polynomials of the paper.
-/

namespace SignCond

theorem golaySquare_peval_fst {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B)
    (z : ℂ) : peval (golaySquare A B).1 z = (peval A z + peval B z) / 2 * peval B (z ^ l) +
      (peval A z - peval B z) / 2 * peval (seqRev A) (z ^ l) := by
  simp only [golaySquare]
  rw [peval_comp_cast, peval_sqP]
  have e1 : peval (halfSum A B) z = (peval A z + peval B z) / 2 := by
    rw [← peval_halfSum hA hB z]; ring
  have e2 : peval (halfDiff A B) z = (peval A z - peval B z) / 2 := by
    rw [← peval_halfDiff hA hB z]; ring
  rw [e1, e2]

theorem golaySquare_peval_snd {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B)
    (z : ℂ) : peval (golaySquare A B).2 z = (peval A z + peval B z) / 2 * peval A (z ^ l) -
      (peval A z - peval B z) / 2 * peval (seqRev B) (z ^ l) := by
  simp only [golaySquare]
  rw [peval_comp_cast, peval_sqQ]
  have e1 : peval (halfSum A B) z = (peval A z + peval B z) / 2 := by
    rw [← peval_halfSum hA hB z]; ring
  have e2 : peval (halfDiff A B) z = (peval A z - peval B z) / 2 := by
    rw [← peval_halfDiff hA hB z]; ring
  rw [e1, e2]

theorem golayLift_peval {n : ℕ} (P Q : Fin n → ℤ) (z : ℂ) :
    peval (golayLift (P, Q)).1 z = (1 + z ^ 2) * peval P (z ^ 4) + (z - z ^ 3) * peval Q (z ^ 4) ∧
      peval (golayLift (P, Q)).2 z = (1 - z ^ 2) * peval P (z ^ 4) + (z + z ^ 3) * peval Q (z ^ 4) := by
  simp only [golayLift]
  rw [peval_comp_cast, peval_comp_cast, peval_liftP, peval_liftQ]
  exact ⟨rfl, rfl⟩

end SignCond
