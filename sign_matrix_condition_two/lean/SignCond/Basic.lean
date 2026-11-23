import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Sign matrices and condition-number windows

* `IsSign A`: every entry of the real square matrix `A` is `1` or `-1`.
* `CondLe A c`: the Gram matrix `A * Aᵀ` lies in a Loewner window of ratio `c ^ 2`,
  i.e. `t • 1 ≤ A * Aᵀ ≤ (c ^ 2 * t) • 1` for some `t > 0`.

`condLe_iff` restates `CondLe` without the Loewner order:
`t ‖x‖² ≤ ‖Aᵀ x‖² ≤ c² t ‖x‖²` for every vector `x`.
The lemmas `isSign_reindex` and `condLe_reindex` show that both notions are
invariant under a simultaneous relabelling of rows and columns.
-/

open Matrix

namespace SignCond

variable {n m : Type*}

/-- A real square matrix all of whose entries are `1` or `-1`. -/
def IsSign (A : Matrix n n ℝ) : Prop := ∀ i j, A i j = 1 ∨ A i j = -1

/-- `CondLe A c`: the Gram matrix of `A` lies in a window of ratio `c ^ 2`, i.e. there is `t > 0` with
`t • 1 ≤ A * Aᵀ ≤ (c ^ 2 * t) • 1` in the Loewner order. For `c ≥ 1` this says that `A` is invertible with
condition number at most `c` in the spectral norm. -/
def CondLe [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (c : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ (A * Aᵀ - t • (1 : Matrix n n ℝ)).PosSemidef ∧
    ((c ^ 2 * t) • (1 : Matrix n n ℝ) - A * Aᵀ).PosSemidef

section Fintype

variable [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- For a real symmetric matrix, positive semidefiniteness is nonnegativity of the
quadratic form `x ↦ x ⬝ᵥ (M *ᵥ x)`. -/
theorem posSemidef_iff_of_transpose_eq {M : Matrix n n ℝ} (hM : Mᵀ = M) :
    M.PosSemidef ↔ ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  have hH : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hM
  simp only [PosSemidef, hH, true_and, star_trivial]

omit [DecidableEq n] in
theorem transpose_eq_of_posSemidef {M : Matrix n n ℝ} (hM : M.PosSemidef) : Mᵀ = M := by
  have h := hM.1
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

omit [DecidableEq n] in
theorem posSemidef_smul {M : Matrix n n ℝ} (hM : M.PosSemidef) {r : ℝ} (hr : 0 ≤ r) :
    (r • M).PosSemidef := by
  have hT := transpose_eq_of_posSemidef hM
  rw [posSemidef_iff_of_transpose_eq (by rw [transpose_smul, hT])]
  intro x
  rw [smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
  exact mul_nonneg hr ((posSemidef_iff_of_transpose_eq hT).1 hM x)

omit [DecidableEq n] in
theorem posSemidef_smul_iff {M : Matrix n n ℝ} {r : ℝ} (hr : 0 < r) :
    (r • M).PosSemidef ↔ M.PosSemidef := by
  refine ⟨fun h => ?_, fun h => posSemidef_smul h hr.le⟩
  have := posSemidef_smul h (inv_nonneg.2 hr.le)
  rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this

omit [DecidableEq n] in
/-- The Gram matrix `A * Aᵀ` is symmetric. -/
theorem transpose_gram (A : Matrix n n ℝ) : (A * Aᵀ)ᵀ = A * Aᵀ := by
  rw [transpose_mul, transpose_transpose]

omit [DecidableEq n] in
/-- The quadratic form of the Gram matrix: `xᵀ (A Aᵀ) x = ‖Aᵀ x‖²`. -/
theorem dotProduct_gram_mulVec (A : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((A * Aᵀ) *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]

/-- **Bridging lemma.** The two Loewner inequalities `t • 1 ≤ A * Aᵀ ≤ (c ^ 2 * t) • 1`
hold exactly when `t ‖x‖² ≤ ‖Aᵀ x‖² ≤ c ^ 2 t ‖x‖²` for every real vector `x`
(squared Euclidean norms written as dot products). -/
theorem window_iff (A : Matrix n n ℝ) (t c : ℝ) :
    ((A * Aᵀ - t • (1 : Matrix n n ℝ)).PosSemidef ∧
      ((c ^ 2 * t) • (1 : Matrix n n ℝ) - A * Aᵀ).PosSemidef) ↔
    ∀ x : n → ℝ, t * (x ⬝ᵥ x) ≤ (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) ∧
      (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) ≤ c ^ 2 * t * (x ⬝ᵥ x) := by
  have h1 : (A * Aᵀ - t • (1 : Matrix n n ℝ))ᵀ = A * Aᵀ - t • (1 : Matrix n n ℝ) := by
    rw [transpose_sub, transpose_gram, transpose_smul, transpose_one]
  have h2 : ((c ^ 2 * t) • (1 : Matrix n n ℝ) - A * Aᵀ)ᵀ =
      (c ^ 2 * t) • (1 : Matrix n n ℝ) - A * Aᵀ := by
    rw [transpose_sub, transpose_gram, transpose_smul, transpose_one]
  rw [posSemidef_iff_of_transpose_eq h1, posSemidef_iff_of_transpose_eq h2]
  simp only [sub_mulVec, smul_mulVec_assoc, one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, dotProduct_gram_mulVec, sub_nonneg]
  exact ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

/-- `CondLe A c` in elementary terms: for some `t > 0`,
`√t ‖x‖ ≤ ‖Aᵀ x‖ ≤ c √t ‖x‖` for every real vector `x` (stated with squared norms). -/
theorem condLe_iff (A : Matrix n n ℝ) (c : ℝ) :
    CondLe A c ↔ ∃ t : ℝ, 0 < t ∧ ∀ x : n → ℝ, t * (x ⬝ᵥ x) ≤ (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) ∧
      (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) ≤ c ^ 2 * t * (x ⬝ᵥ x) := by
  simp only [CondLe, window_iff]

/-! ### Invariance under relabelling rows and columns simultaneously -/

omit [Fintype n] [DecidableEq n] in
theorem isSign_reindex {A : Matrix n n ℝ} (e : n ≃ m) (hA : IsSign A) :
    IsSign (reindex e e A) :=
  fun i j => hA (e.symm i) (e.symm j)

theorem condLe_reindex [Fintype m] [DecidableEq m] {A : Matrix n n ℝ} (e : n ≃ m) {c : ℝ}
    (hA : CondLe A c) : CondLe (reindex e e A) c := by
  obtain ⟨t, ht, h1, h2⟩ := hA
  have hG : reindex e e A * (reindex e e A)ᵀ = (A * Aᵀ).submatrix e.symm e.symm := by
    rw [reindex_apply, transpose_submatrix, submatrix_mul_equiv]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hG, ← submatrix_one_equiv (α := ℝ) e.symm]
    exact h1.submatrix e.symm
  · rw [hG, ← submatrix_one_equiv (α := ℝ) e.symm]
    exact h2.submatrix e.symm

theorem condLe_reindex_iff [Fintype m] [DecidableEq m] {A : Matrix n n ℝ} (e : n ≃ m) {c : ℝ} :
    CondLe (reindex e e A) c ↔ CondLe A c := by
  refine ⟨fun h => ?_, condLe_reindex e⟩
  simpa using condLe_reindex e.symm h

end Fintype

end SignCond
