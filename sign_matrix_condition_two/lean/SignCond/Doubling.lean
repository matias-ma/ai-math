import SignCond.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Lemma 1 (doubling)

Paper: *Let `A` be a sign matrix and `W₂ = [[1, 1], [1, -1]]`. Then `W₂ ⊗ A` is a sign
matrix with `κ(W₂ ⊗ A) = κ(A)`.* Proof: `(W₂ ⊗ A)(W₂ ⊗ A)ᵀ = 2 I ⊗ A Aᵀ`.

* `isSign_kronecker`: `W₂ ⊗ A` is a sign matrix.
* `gram_kronecker`: `(W₂ ⊗ A)(W₂ ⊗ A)ᵀ = 2 • (1 ⊗ A Aᵀ)`.
* `condLe_kronecker_iff`: `CondLe (W₂ ⊗ A) c ↔ CondLe A c` for every real `c`.
* `exists_doubling`: iterating, from an `m × m` example to a `2 ^ a * m` one.
-/

open Matrix Kronecker

namespace SignCond

/-- The `2 × 2` Hadamard matrix `W₂ = [[1, 1], [1, -1]]`. -/
noncomputable def W2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

variable {n : Type*}

theorem isSign_kronecker {A : Matrix n n ℝ} (hA : IsSign A) : IsSign (W2 ⊗ₖ A) := by
  rintro ⟨i, k⟩ ⟨j, l⟩
  rw [kronecker_apply]
  rcases hA k l with h | h <;> rw [h] <;> fin_cases i <;> fin_cases j <;> norm_num [W2]

theorem W2_mul_transpose : W2 * W2ᵀ = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [W2, mul_apply, Fin.sum_univ_two, one_apply]

variable [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem gram_kronecker (A : Matrix n n ℝ) :
    (W2 ⊗ₖ A) * (W2 ⊗ₖ A)ᵀ = (2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (A * Aᵀ)) := by
  rw [← kroneckerMap_transpose, ← mul_kronecker_mul, W2_mul_transpose, smul_kronecker]

omit [DecidableEq n] in
/-- `1 ⊗ M` is positive semidefinite exactly when `M` is. -/
theorem posSemidef_one_kronecker_iff (M : Matrix n n ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ M).PosSemidef ↔ M.PosSemidef := by
  constructor
  · intro h
    have h0 := h.submatrix (fun k : n => ((0 : Fin 2), k))
    have he : ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ M).submatrix (fun k : n => ((0 : Fin 2), k))
        (fun k : n => ((0 : Fin 2), k)) = M := by
      ext k l
      simp
    rwa [he] at h0
  · intro h
    obtain ⟨B, rfl⟩ := posSemidef_iff_eq_conjTranspose_mul_self.1 h
    have hB : (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (Bᴴ * B) =
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ B)ᴴ * ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ B) := by
      simp only [conjTranspose_eq_transpose_of_trivial]
      rw [← kroneckerMap_transpose, ← mul_kronecker_mul, transpose_one, one_mul]
    rw [hB]
    exact posSemidef_conjTranspose_mul_self _

omit [Fintype n] [DecidableEq n] in
theorem one_kronecker_sub (X Y : Matrix n n ℝ) :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (X - Y) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ X - (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ Y := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [mul_sub]

/-- Lower edge of the window: `G₂ - (2t) • 1 = 2 • (1 ⊗ (G - t • 1))`. -/
theorem kronecker_window_lower (A : Matrix n n ℝ) (t : ℝ) :
    (W2 ⊗ₖ A) * (W2 ⊗ₖ A)ᵀ - (2 * t) • (1 : Matrix (Fin 2 × n) (Fin 2 × n) ℝ) =
      (2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (A * Aᵀ - t • (1 : Matrix n n ℝ))) := by
  rw [gram_kronecker, one_kronecker_sub, kronecker_smul, one_kronecker_one, smul_sub, smul_smul]

/-- Upper edge of the window: `(c² (2t)) • 1 - G₂ = 2 • (1 ⊗ ((c² t) • 1 - G))`. -/
theorem kronecker_window_upper (A : Matrix n n ℝ) (c t : ℝ) :
    (c ^ 2 * (2 * t)) • (1 : Matrix (Fin 2 × n) (Fin 2 × n) ℝ) - (W2 ⊗ₖ A) * (W2 ⊗ₖ A)ᵀ =
      (2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ ((c ^ 2 * t) • (1 : Matrix n n ℝ) - A * Aᵀ)) := by
  rw [gram_kronecker, one_kronecker_sub, kronecker_smul, one_kronecker_one, smul_sub, smul_smul,
    show (2 : ℝ) * (c ^ 2 * t) = c ^ 2 * (2 * t) by ring]

/-- **Lemma 1, condition number.** For every real `c`, the Gram window of ratio `c ^ 2`
exists for `W₂ ⊗ A` exactly when it exists for `A` (the window parameter doubles). -/
theorem condLe_kronecker_iff (A : Matrix n n ℝ) (c : ℝ) :
    CondLe (W2 ⊗ₖ A) c ↔ CondLe A c := by
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, s = 2 * t := ⟨s / 2, by ring⟩
    rw [kronecker_window_lower, posSemidef_smul_iff two_pos,
      posSemidef_one_kronecker_iff] at h1
    rw [kronecker_window_upper, posSemidef_smul_iff two_pos,
      posSemidef_one_kronecker_iff] at h2
    exact ⟨t, by linarith, h1, h2⟩
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨2 * t, by positivity, ?_, ?_⟩
    · rw [kronecker_window_lower, posSemidef_smul_iff two_pos, posSemidef_one_kronecker_iff]
      exact h1
    · rw [kronecker_window_upper, posSemidef_smul_iff two_pos, posSemidef_one_kronecker_iff]
      exact h2

/-- One doubling step, both properties at once. -/
theorem isSign_condLe_kronecker {A : Matrix n n ℝ} {c : ℝ} (hA : IsSign A) (hc : CondLe A c) :
    IsSign (W2 ⊗ₖ A) ∧ CondLe (W2 ⊗ₖ A) c :=
  ⟨isSign_kronecker hA, (condLe_kronecker_iff A c).2 hc⟩

/-- **Lemma 1, iterated.** If an `m × m` sign matrix satisfies `CondLe · c`, then so does
some `(2 ^ a * m) × (2 ^ a * m)` sign matrix, for every `a`. -/
theorem exists_doubling {c : ℝ} {m : ℕ}
    (h : ∃ A : Matrix (Fin m) (Fin m) ℝ, IsSign A ∧ CondLe A c) (a : ℕ) :
    ∃ A : Matrix (Fin (2 ^ a * m)) (Fin (2 ^ a * m)) ℝ, IsSign A ∧ CondLe A c := by
  induction a with
  | zero =>
    obtain ⟨A, hA, hc⟩ := h
    let e : Fin m ≃ Fin (2 ^ 0 * m) := finCongr (by ring)
    exact ⟨reindex e e A, isSign_reindex e hA, condLe_reindex e hc⟩
  | succ a ih =>
    obtain ⟨A, hA, hc⟩ := ih
    let e : Fin 2 × Fin (2 ^ a * m) ≃ Fin (2 ^ (a + 1) * m) :=
      finProdFinEquiv.trans (finCongr (by ring))
    obtain ⟨hA', hc'⟩ := isSign_condLe_kronecker hA hc
    exact ⟨reindex e e (W2 ⊗ₖ A), isSign_reindex e hA', condLe_reindex e hc'⟩

end SignCond
