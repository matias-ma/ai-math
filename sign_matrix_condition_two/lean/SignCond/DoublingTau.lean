import SignCond.CriterionTau
import SignCond.Doubling

/-!
# Strict doubling and the explicit matrices of orders 2, 6 and 12

Paper, proof of Theorem `thm:main` (end of Section `sec:computation`): even orders `2^i m` come
from Lemma `lem:double` applied to a matrix of odd order `m ≥ 5`, to `W₂` (`m = 1`), to the matrix
`A₆` (`n = 6`), or to a Hadamard matrix of order `12` (`n = 3·2^i`, `i ≥ 2`).

* `condLt2_kronecker_iff`: `κ(W₂ ⊗ A) < 2 ⟺ κ(A) < 2` (strict form of Lemma `lem:double`).
* `exists_doubling_lt`: iterating it.
* `condLt2_W2`, `isSign_A6`/`condLt2_A6`, `isSign_H12`/`H12_mul_transpose`/`condLt2_H12`.

The Gram identities of the explicit matrices are checked over `ℤ` by `decide` (`A6z`, `H12z`) and
transported to `ℝ` by the cast `toR`.
-/

open Matrix Kronecker

namespace SignCond

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem posDef_smul_iff {M : Matrix n n ℝ} (hM : Mᵀ = M) {r : ℝ} (hr : 0 < r) :
    (r • M).PosDef ↔ M.PosDef := by
  have hT : (r • M)ᵀ = r • M := by rw [transpose_smul, hM]
  rw [posDef_iff_of_transpose_eq hT, posDef_iff_of_transpose_eq hM]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
  exact ⟨fun h => pos_of_mul_pos_right h hr.le, fun h => mul_pos hr h⟩

/-- `c • 1` is positive definite for `c > 0`. -/
theorem posDef_smul_one {c : ℝ} (hc : 0 < c) : (c • (1 : Matrix n n ℝ)).PosDef := by
  rw [posDef_smul_iff (by rw [transpose_one]) hc]
  exact PosDef.one

omit [DecidableEq n] in
/-- If `X` is symmetric and `X * X = c • X` with `c > 0`, then `X = c⁻¹ • XᵀX` is positive
semidefinite. -/
theorem posSemidef_of_mul_self_eq {X : Matrix n n ℝ} (hT : Xᵀ = X) {c : ℝ} (hc : 0 < c)
    (hX : X * X = c • X) : X.PosSemidef := by
  have hH : Xᴴ = X := by rw [conjTranspose_eq_transpose_of_trivial, hT]
  have : X = c⁻¹ • (Xᴴ * X) := by
    rw [hH, hX, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rw [this]
  exact posSemidef_smul (posSemidef_conjTranspose_mul_self X) (inv_nonneg.2 hc.le)

/-- `CondLt2` from an exact Gram identity `A Aᵀ = c • 1`, `c > 0`. -/
theorem condLt2_of_gram_eq {A : Matrix n n ℝ} {c : ℝ} (hc : 0 < c)
    (h : A * Aᵀ = c • (1 : Matrix n n ℝ)) : CondLt2 A := by
  refine ⟨c, hc, ?_, ?_⟩
  · rw [h, sub_self]; exact PosSemidef.zero
  · rw [h, ← sub_smul]
    exact posDef_smul_one (by linarith)

end General

/-! ### Strict doubling -/

section Doubling

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem quad_one_kronecker (N : Matrix n n ℝ) (y : Fin 2 × n → ℝ) :
    y ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ N) *ᵥ y) =
      (fun k => y (0, k)) ⬝ᵥ (N *ᵥ fun k => y (0, k)) +
        (fun k => y (1, k)) ⬝ᵥ (N *ᵥ fun k => y (1, k)) := by
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, kronecker_apply,
    one_apply_eq, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), one_mul, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]

omit [DecidableEq n] in
/-- `1 ⊗ M` is positive definite exactly when `M` is (`M` symmetric). -/
theorem posDef_one_kronecker_iff {M : Matrix n n ℝ} (hM : Mᵀ = M) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ M).PosDef ↔ M.PosDef := by
  have hT : ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ M)ᵀ = (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ M := by
    rw [← kroneckerMap_transpose, transpose_one, hM]
  rw [posDef_iff_of_transpose_eq hT, posDef_iff_of_transpose_eq hM]
  constructor
  · intro h x hx
    set y : Fin 2 × n → ℝ := fun p => if p.1 = 0 then x p.2 else 0 with hy
    have hy0 : y ≠ 0 := by
      intro h0
      apply hx
      funext k
      have := congrFun h0 (0, k)
      simpa [hy] using this
    have := h y hy0
    rw [quad_one_kronecker] at this
    have e0 : (fun k => y (0, k)) = x := by funext k; simp [hy]
    have e1 : (fun k => y (1, k)) = 0 := by funext k; simp [hy]
    rw [e0, e1, mulVec_zero, dotProduct_zero, add_zero] at this
    exact this
  · intro h y hy
    rw [quad_one_kronecker]
    have hnn : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
      intro x
      by_cases hx : x = 0
      · rw [hx, mulVec_zero, dotProduct_zero]
      · exact (h x hx).le
    by_cases h0 : (fun k => y (0, k)) = 0
    · have h1 : (fun k => y (1, k)) ≠ 0 := by
        intro h1
        apply hy
        funext ⟨i, k⟩
        fin_cases i
        · exact congrFun h0 k
        · exact congrFun h1 k
      exact add_pos_of_nonneg_of_pos (hnn _) (h _ h1)
    · exact add_pos_of_pos_of_nonneg (h _ h0) (hnn _)

theorem kronecker_window_upper_lt (A : Matrix n n ℝ) (t : ℝ) :
    (4 * (2 * t)) • (1 : Matrix (Fin 2 × n) (Fin 2 × n) ℝ) - (W2 ⊗ₖ A) * (W2 ⊗ₖ A)ᵀ =
      (2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ ((4 * t) • (1 : Matrix n n ℝ) - A * Aᵀ)) := by
  rw [gram_kronecker, one_kronecker_sub, kronecker_smul, one_kronecker_one, smul_sub, smul_smul,
    show (2 : ℝ) * (4 * t) = 4 * (2 * t) by ring]

theorem upper_symm (A : Matrix n n ℝ) (c : ℝ) :
    (c • (1 : Matrix n n ℝ) - A * Aᵀ)ᵀ = c • (1 : Matrix n n ℝ) - A * Aᵀ := by
  rw [transpose_sub, transpose_smul, transpose_one, transpose_gram]

/-- **Lemma `lem:double`, strict form.** `κ(W₂ ⊗ A) < 2` iff `κ(A) < 2`. -/
theorem condLt2_kronecker_iff (A : Matrix n n ℝ) : CondLt2 (W2 ⊗ₖ A) ↔ CondLt2 A := by
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, s = 2 * t := ⟨s / 2, by ring⟩
    rw [kronecker_window_lower, posSemidef_smul_iff two_pos,
      posSemidef_one_kronecker_iff] at h1
    rw [kronecker_window_upper_lt, posDef_smul_iff (by
        rw [← kroneckerMap_transpose, transpose_one, upper_symm]) two_pos,
      posDef_one_kronecker_iff (upper_symm A _)] at h2
    exact ⟨t, by linarith, h1, h2⟩
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨2 * t, by positivity, ?_, ?_⟩
    · rw [kronecker_window_lower, posSemidef_smul_iff two_pos, posSemidef_one_kronecker_iff]
      exact h1
    · rw [kronecker_window_upper_lt, posDef_smul_iff (by
          rw [← kroneckerMap_transpose, transpose_one, upper_symm]) two_pos,
        posDef_one_kronecker_iff (upper_symm A _)]
      exact h2

omit [DecidableEq n] in
theorem posDef_submatrix_equiv' {m : Type*} [Fintype m] {M : Matrix n n ℝ} (hM : Mᵀ = M)
    (e : n ≃ m) (h : M.PosDef) : (M.submatrix e.symm e.symm).PosDef := by
  rw [posDef_iff_of_transpose_eq (by rw [transpose_submatrix, hM])]
  rw [posDef_iff_of_transpose_eq hM] at h
  intro x hx
  rw [submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm]
  refine h _ fun h0 => hx ?_
  funext i
  simpa using congrFun h0 (e.symm i)

/-- `CondLt2` is invariant under relabelling rows and columns simultaneously. -/
theorem condLt2_reindex {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix n n ℝ} (e : n ≃ m)
    (h : CondLt2 A) : CondLt2 (reindex e e A) := by
  obtain ⟨t, ht, h1, h2⟩ := h
  have hG : reindex e e A * (reindex e e A)ᵀ = (A * Aᵀ).submatrix e.symm e.symm := by
    rw [reindex_apply, transpose_submatrix, submatrix_mul_equiv]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hG, ← submatrix_one_equiv (α := ℝ) e.symm]
    exact h1.submatrix e.symm
  · have e2 : (4 * t) • (1 : Matrix m m ℝ) - (A * Aᵀ).submatrix e.symm e.symm =
        ((4 * t) • (1 : Matrix n n ℝ) - A * Aᵀ).submatrix e.symm e.symm := by
      ext i k
      simp only [sub_apply, smul_apply, submatrix_apply, one_apply, EmbeddingLike.apply_eq_iff_eq]
    rw [hG, e2]
    exact posDef_submatrix_equiv' (upper_symm A _) e h2

end Doubling

/-- **Lemma `lem:double`, strict form, iterated.** If an `m × m` sign matrix has `κ < 2`, then so
does some sign matrix of order `2 ^ a * m`, for every `a`. -/
theorem exists_doubling_lt {m : ℕ}
    (h : ∃ A : Matrix (Fin m) (Fin m) ℝ, IsSign A ∧ CondLt2 A) (a : ℕ) :
    ∃ A : Matrix (Fin (2 ^ a * m)) (Fin (2 ^ a * m)) ℝ, IsSign A ∧ CondLt2 A := by
  induction a with
  | zero =>
    obtain ⟨A, hA, hc⟩ := h
    let e : Fin m ≃ Fin (2 ^ 0 * m) := finCongr (by ring)
    exact ⟨reindex e e A, isSign_reindex e hA, condLt2_reindex e hc⟩
  | succ a ih =>
    obtain ⟨A, hA, hc⟩ := ih
    let e : Fin 2 × Fin (2 ^ a * m) ≃ Fin (2 ^ (a + 1) * m) :=
      finProdFinEquiv.trans (finCongr (by ring))
    exact ⟨reindex e e (W2 ⊗ₖ A), isSign_reindex e (isSign_kronecker hA),
      condLt2_reindex e ((condLt2_kronecker_iff A).2 hc)⟩

/-! ### Integer matrices -/

section Int

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An integer matrix as a real matrix. -/
noncomputable def toR (M : Matrix n n ℤ) : Matrix n n ℝ := M.map (Int.cast : ℤ → ℝ)

omit [DecidableEq n] in
theorem toR_gram (M : Matrix n n ℤ) : toR M * (toR M)ᵀ = toR (M * Mᵀ) := by
  unfold toR
  rw [← transpose_map, show (Int.cast : ℤ → ℝ) = ⇑(Int.castRingHom ℝ) from rfl, Matrix.map_mul]

omit [Fintype n] [DecidableEq n] in
theorem isSign_toR {M : Matrix n n ℤ} (h : ∀ i j, M i j = 1 ∨ M i j = -1) : IsSign (toR M) := by
  intro i j
  rcases h i j with h | h <;> simp [toR, h]

omit [DecidableEq n] in
theorem toR_mul (M N : Matrix n n ℤ) : toR (M * N) = toR M * toR N := by
  unfold toR
  rw [show (Int.cast : ℤ → ℝ) = ⇑(Int.castRingHom ℝ) from rfl, Matrix.map_mul]

omit [Fintype n] [DecidableEq n] in
theorem toR_smul (M : Matrix n n ℤ) (c : ℤ) : toR (c • M) = (c : ℝ) • toR M := by
  ext i j; simp [toR]

omit [Fintype n] [DecidableEq n] in
theorem toR_transpose (M : Matrix n n ℤ) : toR Mᵀ = (toR M)ᵀ := by
  unfold toR; rw [transpose_map]

omit [Fintype n] [DecidableEq n] in
theorem toR_sub (M N : Matrix n n ℤ) : toR (M - N) = toR M - toR N := by
  ext i j; simp [toR]

omit [Fintype n] in
theorem toR_one : toR (1 : Matrix n n ℤ) = 1 := by
  unfold toR; exact Matrix.map_one _ Int.cast_zero Int.cast_one

omit [Fintype n] in
theorem toR_sub_smul_one (M : Matrix n n ℤ) (c : ℤ) :
    toR (M - c • 1) = toR M - (c : ℝ) • (1 : Matrix n n ℝ) := by
  rw [toR_sub, toR_smul, toR_one]

omit [Fintype n] in
theorem toR_smul_one_sub (M : Matrix n n ℤ) (c : ℤ) :
    toR (c • 1 - M) = (c : ℝ) • (1 : Matrix n n ℝ) - toR M := by
  rw [toR_sub, toR_smul, toR_one]

omit [DecidableEq n] in
/-- A symmetric integer matrix `X` with `X * X = c • X`, `c > 0`, is positive semidefinite over
`ℝ`. -/
theorem posSemidef_toR {X : Matrix n n ℤ} (hT : Xᵀ = X) {c : ℤ} (hc : 0 < c)
    (hX : X * X = c • X) : (toR X).PosSemidef := by
  refine posSemidef_of_mul_self_eq (c := (c : ℝ)) (by rw [← toR_transpose, hT])
    (by exact_mod_cast hc) ?_
  rw [← toR_mul, hX, toR_smul]

end Int

/-! ### `W₂` -/

theorem condLt2_W2 : CondLt2 W2 := condLt2_of_gram_eq two_pos W2_mul_transpose

theorem isSign_W2 : IsSign W2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [W2]

/-! ### The matrix `A₆` -/

/-- The integer matrix `A₆` of the paper (proof of Theorem `thm:main`); rows
`++----`, `---+--`, `-+-++-`, `+-+-+-`, `+--+++`, `----++` (`+ = 1`, `- = -1`). -/
def A6z : Matrix (Fin 6) (Fin 6) ℤ := !![
   1,  1, -1, -1, -1, -1;
  -1, -1, -1,  1, -1, -1;
  -1,  1, -1,  1,  1, -1;
   1, -1,  1, -1,  1, -1;
   1, -1, -1,  1,  1,  1;
  -1, -1, -1, -1,  1,  1]

/-- Paper: `A_6=\begin{pmatrix}1&1&-1&-1&-1&-1\\-1&-1&-1&1&-1&-1\\-1&1&-1&1&1&-1\\
1&-1&1&-1&1&-1\\1&-1&-1&1&1&1\\-1&-1&-1&-1&1&1\end{pmatrix}`, as a real matrix. -/
noncomputable def A6 : Matrix (Fin 6) (Fin 6) ℝ := toR A6z

theorem A6z_sign : ∀ i j, A6z i j = 1 ∨ A6z i j = -1 := by decide

/-- `X = A₆A₆ᵀ - 4I` satisfies `X² = 6X` (so `A₆A₆ᵀ` has eigenvalues `4` and `10`). -/
theorem A6z_lower : (A6z * A6zᵀ - (4 : ℤ) • 1) * (A6z * A6zᵀ - (4 : ℤ) • 1) =
    (6 : ℤ) • (A6z * A6zᵀ - (4 : ℤ) • 1) := by decide

/-- `Y = 10I - A₆A₆ᵀ` satisfies `Y² = 6Y`. -/
theorem A6z_upper : ((10 : ℤ) • 1 - A6z * A6zᵀ) * ((10 : ℤ) • 1 - A6z * A6zᵀ) =
    (6 : ℤ) • ((10 : ℤ) • 1 - A6z * A6zᵀ) := by decide

theorem A6z_lower_symm : (A6z * A6zᵀ - (4 : ℤ) • 1)ᵀ = A6z * A6zᵀ - (4 : ℤ) • 1 := by decide

theorem A6z_upper_symm : ((10 : ℤ) • 1 - A6z * A6zᵀ)ᵀ = (10 : ℤ) • 1 - A6z * A6zᵀ := by decide

theorem isSign_A6 : IsSign A6 := isSign_toR A6z_sign

/-- `4I ⪯ A₆A₆ᵀ ⪯ 10I`. -/
theorem A6_window :
    (A6 * A6ᵀ - (4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef ∧
      ((10 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - A6 * A6ᵀ).PosSemidef := by
  have h1 := posSemidef_toR A6z_lower_symm (by norm_num) A6z_lower
  have h2 := posSemidef_toR A6z_upper_symm (by norm_num) A6z_upper
  rw [toR_sub_smul_one, ← toR_gram] at h1
  rw [toR_smul_one_sub, ← toR_gram] at h2
  push_cast at h1 h2
  exact ⟨h1, h2⟩

/-- `κ(A₆) < 2`, with `t = 3`: `3I ⪯ A₆A₆ᵀ ≺ 12I`. -/
theorem condLt2_A6 : CondLt2 A6 := by
  obtain ⟨h1, h2⟩ := A6_window
  refine ⟨3, by norm_num, ?_, ?_⟩
  · have e : A6 * A6ᵀ - (3 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) =
        (A6 * A6ᵀ - (4 : ℝ) • 1) + 1 := by
      rw [show (4 : ℝ) = 3 + 1 by norm_num, add_smul, one_smul]; abel
    rw [e]
    exact h1.add PosSemidef.one
  · have e : (4 * 3 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - A6 * A6ᵀ =
        ((10 : ℝ) • 1 - A6 * A6ᵀ) + (2 : ℝ) • 1 := by
      rw [show (4 * 3 : ℝ) = 10 + 2 by norm_num, add_smul]; abel
    rw [e]
    exact PosDef.posSemidef_add h2 (posDef_smul_one two_pos)

/-! ### A Hadamard matrix of order `12` -/

/-- A Hadamard matrix of order `12` (Paley's construction for `q = 11`: the first row is `𝟙ᵀ`, the
first column below it is `-𝟙`, and the remaining `11 × 11` block is `I + Q` with
`Q_{uv} = (\frac{v-u}{11})` the Legendre symbol). -/
def H12z : Matrix (Fin 12) (Fin 12) ℤ := !![
   1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1;
  -1,  1,  1, -1,  1,  1,  1, -1, -1, -1,  1, -1;
  -1, -1,  1,  1, -1,  1,  1,  1, -1, -1, -1,  1;
  -1,  1, -1,  1,  1, -1,  1,  1,  1, -1, -1, -1;
  -1, -1,  1, -1,  1,  1, -1,  1,  1,  1, -1, -1;
  -1, -1, -1,  1, -1,  1,  1, -1,  1,  1,  1, -1;
  -1, -1, -1, -1,  1, -1,  1,  1, -1,  1,  1,  1;
  -1,  1, -1, -1, -1,  1, -1,  1,  1, -1,  1,  1;
  -1,  1,  1, -1, -1, -1,  1, -1,  1,  1, -1,  1;
  -1,  1,  1,  1, -1, -1, -1,  1, -1,  1,  1, -1;
  -1, -1,  1,  1,  1, -1, -1, -1,  1, -1,  1,  1;
  -1,  1, -1,  1,  1,  1, -1, -1, -1,  1, -1,  1]

/-- The Hadamard matrix `H12z` as a real matrix. -/
noncomputable def H12 : Matrix (Fin 12) (Fin 12) ℝ := toR H12z

theorem H12z_sign : ∀ i j, H12z i j = 1 ∨ H12z i j = -1 := by decide

set_option maxRecDepth 10000 in
theorem H12z_mul_transpose : H12z * H12zᵀ = (12 : ℤ) • 1 := by decide

theorem isSign_H12 : IsSign H12 := isSign_toR H12z_sign

/-- `H₁₂ H₁₂ᵀ = 12 I`. -/
theorem H12_mul_transpose : H12 * H12ᵀ = (12 : ℝ) • (1 : Matrix (Fin 12) (Fin 12) ℝ) := by
  have h := congrArg toR H12z_mul_transpose
  rw [← toR_gram, toR_smul, toR_one] at h
  unfold H12
  rw [h]
  norm_num

theorem condLt2_H12 : CondLt2 H12 := condLt2_of_gram_eq (by norm_num) H12_mul_transpose

end SignCond
