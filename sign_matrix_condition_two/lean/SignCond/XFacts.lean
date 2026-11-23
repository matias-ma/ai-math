import SignCond.Criterion

/-!
# `X` is a sign matrix of order `4j + β`

Paper: "The matrix we study is the sign matrix of order `4j + β` `X = …`" — the masks condition
eq. `pools` makes `Z + F` the array with the masked entries negated (`Xmat_isSign`). The window is
invariant under relabelling (`window_reindex`), which transports `X` to `Fin (4j + β)`
(`exists_fin_window`).
-/

open Matrix

namespace SignCond

theorem sign_neg {x : ℝ} (h : x = 1 ∨ x = -1) : -x = 1 ∨ -x = -1 := by
  rcases h with rfl | rfl <;> norm_num

theorem mask_add {x σ : ℝ} {j : ℕ} {S : Finset (ZMod j)} {t : ZMod j} (hx : x = 1 ∨ x = -1)
    (hσ : σ = 1 ∨ σ = -1) (hm : t ∈ S → x = -σ) : x + 2 * σ * ind S t = 1 ∨ x + 2 * σ * ind S t = -1 := by
  unfold ind
  split_ifs with h
  · rw [hm h]; rcases hσ with rfl | rfl <;> norm_num
  · simpa using hx

theorem mask_sub {x σ : ℝ} {j : ℕ} {S : Finset (ZMod j)} {t : ZMod j} (hx : x = 1 ∨ x = -1)
    (hσ : σ = 1 ∨ σ = -1) (hm : t ∈ S → x = σ) : x - 2 * σ * ind S t = 1 ∨ x - 2 * σ * ind S t = -1 := by
  unfold ind
  split_ifs with h
  · rw [hm h]; rcases hσ with rfl | rfl <;> norm_num
  · simpa using hx

variable {j : ℕ} [NeZero j]

/-- With eq. `pools`, `X` is a sign matrix. -/
theorem Xmat_isSign {β : ℕ} (hβ : β = 1 ∨ β = 3) {a b c d : ZMod j → ℝ}
    (ha : IsSignVec a) (hb : IsSignVec b) (hc : IsSignVec c) (hd : IsSignVec d)
    {S : Fin 4 → Finset (ZMod j)} (hP : Pools (sigmaOf β) a b c d S) :
    IsSign (Xmat β a b c d S) := by
  have hσ : sigmaOf β = 1 ∨ sigmaOf β = -1 := by
    rcases hβ with rfl | rfl <;> simp [sigmaOf] <;> norm_num
  obtain ⟨p0, p1, p2, p3⟩ := hP
  rintro (⟨q, u⟩ | e) (⟨p, v⟩ | e')
  · rw [Xmat, fromBlocks_apply₁₁, ZF_apply]
    fin_cases q <;> fin_cases p <;>
      simp only [kern1, kern2, kern3, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        Pi.neg_apply, Pi.zero_apply, smul_eq_mul, add_zero, zero_add] <;>
      first
      | exact ha _ | exact hb _ | exact hc _ | exact hd _
      | exact sign_neg (ha _) | exact sign_neg (hb _) | exact sign_neg (hc _) | exact sign_neg (hd _)
      | exact mask_add (ha _) hσ (p0 _)
      | exact mask_sub (hc _) hσ (p1 _) | exact mask_sub (hd _) hσ (p2 _)
      | exact mask_sub (hb _) hσ (p3 _)
  · rw [Xmat, fromBlocks_apply₁₂, of_apply]
    rcases hβ with rfl | rfl <;> fin_cases q <;> fin_cases e' <;>
      simp [Ub, Omat, Hmat, Vb, quat, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  · rw [Xmat, fromBlocks_apply₂₁, of_apply]
    rcases hβ with rfl | rfl <;> fin_cases p <;> fin_cases e <;> simp [Vb]
  · rw [Xmat, fromBlocks_apply₂₂]
    rcases hβ with rfl | rfl <;> fin_cases e <;> fin_cases e' <;> simp [Gb]

omit [NeZero j] in
theorem window_reindex {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {M : Matrix n n ℝ} (e : n ≃ m) {t : ℝ} (h : Window M t) : Window (reindex e e M) t := by
  obtain ⟨h1, h2⟩ := h
  have hG : reindex e e M * (reindex e e M)ᵀ = (M * Mᵀ).submatrix e.symm e.symm := by
    rw [reindex_apply, transpose_submatrix, submatrix_mul_equiv]
  have e1 : reindex e e M * (reindex e e M)ᵀ - (2 * t) • (1 : Matrix m m ℝ) =
      (M * Mᵀ - (2 * t) • (1 : Matrix n n ℝ)).submatrix e.symm e.symm := by
    rw [hG]; ext i k; simp [Matrix.one_apply, e.symm.injective.eq_iff]
  have e2 : (8 * t) • (1 : Matrix m m ℝ) - reindex e e M * (reindex e e M)ᵀ =
      ((8 * t) • (1 : Matrix n n ℝ) - M * Mᵀ).submatrix e.symm e.symm := by
    rw [hG]; ext i k; simp [Matrix.one_apply, e.symm.injective.eq_iff]
  exact ⟨e1 ▸ h1.submatrix e.symm, e2 ▸ h2.submatrix e.symm⟩

theorem card_index (β : ℕ) : Fintype.card ((Fin 4 × ZMod j) ⊕ Fin β) = 4 * j + β := by
  simp [Fintype.card_sum, Fintype.card_prod, ZMod.card]

/-- A sign matrix in the window, indexed by `(Fin 4 × ℤ/jℤ) ⊕ Fin β`, gives one of order `4j + β`. -/
theorem exists_fin_window {β : ℕ} {X : Matrix ((Fin 4 × ZMod j) ⊕ Fin β) ((Fin 4 × ZMod j) ⊕ Fin β) ℝ}
    (hX : IsSign X) (hW : Window X j) :
    ∃ A : Matrix (Fin (4 * j + β)) (Fin (4 * j + β)) ℝ, IsSign A ∧ Window A j := by
  let e := Fintype.equivFinOfCardEq (card_index (j := j) β)
  exact ⟨reindex e e X, isSign_reindex e hX, window_reindex e hW⟩

theorem isSignVec_toVec {x : Fin j → ℤ} (hx : IsSignSeq x) : IsSignVec (toVec x) := by
  intro v
  rcases hx ⟨v.val, ZMod.val_lt v⟩ with h | h <;> simp [toVec, h]

end SignCond
