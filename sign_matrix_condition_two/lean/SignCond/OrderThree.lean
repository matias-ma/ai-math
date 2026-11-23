import SignCond.Basic

/-!
# Lemma 2 (order three)

Paper: *Every invertible `3 × 3` sign matrix `A` satisfies `κ(A) = 2`.*
(Its Gram matrix has eigenvalues `1, 4, 4`.)

* `gram_three`: `(A Aᵀ - 1)(A Aᵀ - 4) = 0` for every invertible `3 × 3` sign matrix.
* `condLe_three`: such an `A` satisfies `CondLe A 2` (window `t = 1`).
* `condLe_three_sharp`: no `c` with `0 ≤ c < 2` works.
* `isSign_A3`, `det_A3`: an explicit invertible `3 × 3` sign matrix exists.

The finite check behind `gram_three` is `sign_core`: a case split over the
`2 ^ 9 = 512` sign patterns, each settled by `norm_num` (kernel-checked arithmetic
on numerals; no `native_decide`).
-/

open Matrix

namespace SignCond

/-- The finite check. For nine signs with nonzero `3 × 3` determinant, the three
off-diagonal Gram entries `p, q, r` are `±1` and satisfy `p + q r = q + p r = r + p q = 0`. -/
theorem sign_core (a b c d e f g h i : ℝ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1)
    (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hg : g = 1 ∨ g = -1) (hh : h = 1 ∨ h = -1) (hi : i = 1 ∨ i = -1)
    (hdet : a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g ≠ 0) :
    (a * d + b * e + c * f) ^ 2 = 1 ∧ (a * g + b * h + c * i) ^ 2 = 1 ∧
    (d * g + e * h + f * i) ^ 2 = 1 ∧
    (a * d + b * e + c * f) + (a * g + b * h + c * i) * (d * g + e * h + f * i) = 0 ∧
    (a * g + b * h + c * i) + (a * d + b * e + c * f) * (d * g + e * h + f * i) = 0 ∧
    (d * g + e * h + f * i) + (a * d + b * e + c * f) * (a * g + b * h + c * i) = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;> rcases hi with rfl | rfl <;>
    norm_num at hdet ⊢

/-- The polynomial identity for a symmetric `3 × 3` matrix with diagonal `3`. -/
theorem window_poly (p q r : ℝ) (hp : p ^ 2 = 1) (hq : q ^ 2 = 1) (hr : r ^ 2 = 1)
    (h1 : p + q * r = 0) (h2 : q + p * r = 0) (h3 : r + p * q = 0) :
    (!![3, p, q; p, 3, r; q, r, 3] - 1) * (!![3, p, q; p, 3, r; q, r, 3] - (4 : ℝ) • 1) =
      (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, one_apply] <;>
    first
    | linear_combination hp + hq
    | linear_combination hp + hr
    | linear_combination hq + hr
    | linear_combination h1
    | linear_combination h2
    | linear_combination h3

theorem sign_mul_self {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsSign A) (i j : Fin 3) :
    A i j * A i j = 1 := by
  rcases hA i j with h | h <;> rw [h] <;> norm_num

/-- The Gram matrix of a `3 × 3` sign matrix: diagonal `3`, off-diagonal row inner products. -/
theorem gram_three_eq {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsSign A) :
    A * Aᵀ = !![3, A 0 0 * A 1 0 + A 0 1 * A 1 1 + A 0 2 * A 1 2,
        A 0 0 * A 2 0 + A 0 1 * A 2 1 + A 0 2 * A 2 2;
      A 0 0 * A 1 0 + A 0 1 * A 1 1 + A 0 2 * A 1 2, 3,
        A 1 0 * A 2 0 + A 1 1 * A 2 1 + A 1 2 * A 2 2;
      A 0 0 * A 2 0 + A 0 1 * A 2 1 + A 0 2 * A 2 2,
        A 1 0 * A 2 0 + A 1 1 * A 2 1 + A 1 2 * A 2 2, 3] := by
  have s := sign_mul_self hA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;>
    first
    | ring1
    | linear_combination s 0 0 + s 0 1 + s 0 2
    | linear_combination s 1 0 + s 1 1 + s 1 2
    | linear_combination s 2 0 + s 2 1 + s 2 2

/-- **Lemma 2, Gram identity.** The Gram matrix `G = A Aᵀ` of an invertible `3 × 3`
sign matrix satisfies `(G - 1)(G - 4) = 0`, so its eigenvalues lie in `{1, 4}`. -/
theorem gram_three (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsSign A) (hdet : A.det ≠ 0) :
    (A * Aᵀ - 1) * (A * Aᵀ - (4 : ℝ) • 1) = 0 := by
  rw [det_fin_three] at hdet
  obtain ⟨hp, hq, hr, h1, h2, h3⟩ := sign_core _ _ _ _ _ _ _ _ _ (hA 0 0) (hA 0 1) (hA 0 2)
    (hA 1 0) (hA 1 1) (hA 1 2) (hA 2 0) (hA 2 1) (hA 2 2) hdet
  rw [gram_three_eq hA]
  exact window_poly _ _ _ hp hq hr h1 h2 h3

/-- Diagonal entries of the Gram matrix of a `3 × 3` sign matrix are `3`. -/
theorem gram_three_diag {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsSign A) (i : Fin 3) :
    (A * Aᵀ) i i = 3 := by
  have s := sign_mul_self hA
  rw [mul_apply, Fin.sum_univ_three]
  simp only [transpose_apply, s]
  norm_num

/-- If `X` is symmetric and `X * X = 3 • X`, then `X = (1/3) • Xᵀ X` is positive semidefinite. -/
theorem posSemidef_of_mul_self {X : Matrix (Fin 3) (Fin 3) ℝ} (hT : Xᵀ = X)
    (hX : X * X = (3 : ℝ) • X) : X.PosSemidef := by
  have hH : Xᴴ = X := by rw [conjTranspose_eq_transpose_of_trivial, hT]
  have : X = (1 / 3 : ℝ) • (Xᴴ * X) := by
    rw [hH, hX, smul_smul]
    norm_num
  rw [this]
  exact posSemidef_smul (posSemidef_conjTranspose_mul_self X) (by norm_num)

/-- A symmetric `G` with `(G - 1)(G - 4) = 0` lies in the window `1 ≤ G ≤ 4`:
`G - 1 = (G - 1)² / 3` and `4 - G = (4 - G)² / 3`. -/
theorem window_of_quadratic (G : Matrix (Fin 3) (Fin 3) ℝ) (hGT : Gᵀ = G)
    (h : (G - 1) * (G - (4 : ℝ) • 1) = 0) :
    (G - (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef ∧
      (((2 : ℝ) ^ 2 * 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - G).PosSemidef := by
  have hZ : G - (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = (G - 1) - (3 : ℝ) • 1 := by
    rw [show (4 : ℝ) = 1 + 3 by norm_num, add_smul, one_smul]
    abel
  have hXX : (G - 1) * (G - 1) = (3 : ℝ) • (G - 1) := by
    rw [hZ, mul_sub, Matrix.mul_smul, mul_one, sub_eq_zero] at h
    exact h
  have hXT : (G - 1)ᵀ = G - 1 := by rw [transpose_sub, hGT, transpose_one]
  refine ⟨?_, ?_⟩
  · rw [one_smul]
    exact posSemidef_of_mul_self hXT hXX
  · have hY : ((2 : ℝ) ^ 2 * 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - G =
        (3 : ℝ) • 1 - (G - 1) := by
      rw [show (2 : ℝ) ^ 2 * 1 = 1 + 3 by norm_num, add_smul, one_smul]
      abel
    rw [hY]
    generalize G - 1 = X at hXX hXT ⊢
    apply posSemidef_of_mul_self
    · rw [transpose_sub, transpose_smul, transpose_one, hXT]
    · rw [sub_mul, mul_sub, mul_sub, hXX]
      simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_sub, smul_smul]
      abel

/-- **Lemma 2, condition number.** Every invertible `3 × 3` sign matrix satisfies
`CondLe A 2`, with window `t = 1`: `1 ≤ A Aᵀ ≤ 4` in the Loewner order. -/
theorem condLe_three (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsSign A) (hdet : A.det ≠ 0) :
    CondLe A 2 :=
  ⟨1, one_pos, window_of_quadratic (A * Aᵀ) (transpose_gram A) (gram_three A hA hdet)⟩

/-- Spectral sharpness (no symmetry needed): if `(G - 1)(G - 4) = 0` and `G 0 0 = 3`, then
`G` has an eigenvector for `1` and one for `4`, so a window `t • 1 ≤ G ≤ (c ^ 2 t) • 1`
forces `t ≤ 1` and `4 ≤ c ^ 2 t`, hence `2 ≤ c` when `0 ≤ c`. -/
theorem sharp_of_quadratic (G : Matrix (Fin 3) (Fin 3) ℝ)
    (h : (G - 1) * (G - (4 : ℝ) • 1) = 0) (hd : G 0 0 = 3) (c t : ℝ) (hc : 0 ≤ c)
    (h1 : (G - t • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef)
    (h2 : ((c ^ 2 * t) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - G).PosSemidef) : 2 ≤ c := by
  have hcomm : (G - (4 : ℝ) • 1) * (G - 1) = 0 := by
    rw [← h]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    abel
  -- `v`, the first column of `G - 4`, is an eigenvector of `G` for the eigenvalue `1`.
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → ℝ, v = (G - (4 : ℝ) • 1) *ᵥ Pi.single 0 1 := ⟨_, rfl⟩
  have hv0 : v 0 = -1 := by
    rw [hv, mulVec_single_one]
    show (G - (4 : ℝ) • 1) 0 0 = -1
    rw [sub_apply, smul_apply, one_apply_eq, hd, smul_eq_mul]
    norm_num
  have hGv : G *ᵥ v = v := by
    have : (G - 1) *ᵥ v = 0 := by rw [hv, mulVec_mulVec, h, zero_mulVec]
    rwa [sub_mulVec, one_mulVec, sub_eq_zero] at this
  -- `w`, the first column of `G - 1`, is an eigenvector of `G` for the eigenvalue `4`.
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → ℝ, w = (G - 1) *ᵥ Pi.single 0 1 := ⟨_, rfl⟩
  have hw0 : w 0 = 2 := by
    rw [hw, mulVec_single_one]
    show (G - 1) 0 0 = 2
    rw [sub_apply, one_apply_eq, hd]
    norm_num
  have hGw : G *ᵥ w = (4 : ℝ) • w := by
    have : (G - (4 : ℝ) • 1) *ᵥ w = 0 := by rw [hw, mulVec_mulVec, hcomm, zero_mulVec]
    rwa [sub_mulVec, smul_mulVec_assoc, one_mulVec, sub_eq_zero] at this
  have hvv : 0 < v ⬝ᵥ v := by
    simp only [dotProduct, Fin.sum_univ_three, hv0]
    nlinarith [mul_self_nonneg (v 1), mul_self_nonneg (v 2)]
  have hww : 0 < w ⬝ᵥ w := by
    simp only [dotProduct, Fin.sum_univ_three, hw0]
    nlinarith [mul_self_nonneg (w 1), mul_self_nonneg (w 2)]
  have q1 := h1.2 v
  have q2 := h2.2 w
  rw [star_trivial, sub_mulVec, smul_mulVec_assoc, one_mulVec, hGv, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at q1
  rw [star_trivial, sub_mulVec, smul_mulVec_assoc, one_mulVec, hGw, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at q2
  have ht1 : t ≤ 1 := by nlinarith
  have h4 : 4 ≤ c ^ 2 * t := by nlinarith
  have hc2 : 4 ≤ c ^ 2 := by nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.2 ht1)]
  nlinarith

/-- **Lemma 2, sharpness.** For an invertible `3 × 3` sign matrix no window of ratio
`c ^ 2 < 4` exists: both eigenvalues `1` and `4` of `A Aᵀ` occur. -/
theorem condLe_three_sharp (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsSign A) (hdet : A.det ≠ 0)
    (c : ℝ) (hc : 0 ≤ c) (hcond : CondLe A c) : 2 ≤ c := by
  obtain ⟨t, -, h1, h2⟩ := hcond
  exact sharp_of_quadratic (A * Aᵀ) (gram_three A hA hdet) (gram_three_diag hA 0) c t hc h1 h2

/-! ### Existence: the statement is not vacuous -/

/-- An explicit invertible `3 × 3` sign matrix. -/
noncomputable def A3 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, -1; 1, -1, 1; 1, -1, -1]

theorem isSign_A3 : IsSign A3 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [A3]

theorem det_A3 : A3.det = 4 := by
  rw [det_fin_three]
  norm_num [A3, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem exists_three :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, IsSign A ∧ A.det ≠ 0 ∧ CondLe A 2 :=
  ⟨A3, isSign_A3, by rw [det_A3]; norm_num,
    condLe_three A3 isSign_A3 (by rw [det_A3]; norm_num)⟩

end SignCond
