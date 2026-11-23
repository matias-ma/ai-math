import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The constant sector (scalar and `2 × 2` content of Lemma `lem:sector`)

Paper, proof of Lemma `lem:sector`: the matrix `M` splits into the `2 × 2` blocks
`B_y = [[-α, √(2t)], [√(2t), 1 + i y]]` with `y ∈ {0, √3, -√3}`, `ν = 1 + y² ∈ {1, 4}`, and
`t I ⪯ B_y B_y^* ⪯ 4 t I` follows from `L_ν ≥ 0`, `U_ν ≥ 0`, where
`L_ν = (ν - t) α² + 4 t α + t (t - ν)` and `U_ν = (ν - 4t) α² + 4 t α + 4 t (t - ν)`.

* `sectorL ν t α`, `sectorU ν t α`: the polynomials `L_ν`, `U_ν`.
* `sectorEntryL`, `sectorEntryU`: the determinants written with the entries
  (`(α² + t)(t + ν) - 2t((1-α)² + y²) = L_ν` and the same for `U_ν`).
* `sectorBlock t α y = B_y`; `sectorBlock_gram` computes `B_y B_y^*`;
  `det_sectorBlock_sub`, `det_sub_sectorBlock` give `det (B_y B_y^* - t I) = L_ν` and
  `det (4 t I - B_y B_y^*) = U_ν`.
* `sectorU_one`, `sectorL_eq`: `U_1 = U_4 + 3(4t - α²)` and `L_ν = U_ν/4 + 3tα + 3να²/4`.
* `sectorU_four_rho`, `sectorU_four_rho_add`: the two evaluations with `t = ρ²`.
* `sector_nonneg`: the conclusion `L_ν ≥ 0`, `U_ν ≥ 0` for `ν ∈ {1, 4}`.
* `herm_form_nonneg`, `posSemidef_fin_two`: a Hermitian `2 × 2` matrix with positive lower right
  entry and nonnegative determinant is positive semidefinite.
* `sectorBlock_window`: `t I ⪯ B_y B_y^* ⪯ 4 t I` (both differences positive semidefinite) under the
  hypotheses of the lemma.
-/

open Complex Matrix ComplexConjugate
open scoped ComplexOrder

namespace SignCond

/-- `L_ν = (ν - t) α² + 4 t α + t (t - ν)`. -/
noncomputable def sectorL (ν t α : ℝ) : ℝ := (ν - t) * α ^ 2 + 4 * t * α + t * (t - ν)

/-- `U_ν = (ν - 4t) α² + 4 t α + 4 t (t - ν)`. -/
noncomputable def sectorU (ν t α : ℝ) : ℝ := (ν - 4 * t) * α ^ 2 + 4 * t * α + 4 * t * (t - ν)

/-! ### The determinants in terms of the entries -/

theorem sectorEntryL (ν t α y : ℝ) (hy : y ^ 2 = ν - 1) :
    (α ^ 2 + t) * (t + ν) - 2 * t * ((1 - α) ^ 2 + y ^ 2) = sectorL ν t α := by
  rw [hy, sectorL]; ring

theorem sectorEntryU (ν t α y : ℝ) (hy : y ^ 2 = ν - 1) :
    (2 * t - α ^ 2) * (2 * t - ν) - 2 * t * ((1 - α) ^ 2 + y ^ 2) = sectorU ν t α := by
  rw [hy, sectorU]; ring

/-! ### The `2 × 2` block `B_y` -/

/-- `B_y = [[-α, √(2t)], [√(2t), 1 + i y]]`. -/
noncomputable def sectorBlock (t α y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(α : ℂ), (√(2 * t) : ℂ); (√(2 * t) : ℂ), 1 + y * I]

theorem sectorBlock_gram {t : ℝ} (ht : 0 ≤ t) (α y : ℝ) :
    sectorBlock t α y * (sectorBlock t α y)ᴴ =
      !![((α ^ 2 + 2 * t : ℝ) : ℂ), (√(2 * t) : ℂ) * (1 - α - y * I);
        (√(2 * t) : ℂ) * (1 - α + y * I), ((2 * t + (1 + y ^ 2) : ℝ) : ℂ)] := by
  have hr : √(2 * t) * √(2 * t) = 2 * t := Real.mul_self_sqrt (by linarith)
  unfold sectorBlock
  generalize √(2 * t) = r at hr ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply] <;>
    apply Complex.ext <;> simp [sq] <;> nlinarith [hr]

theorem det_sectorBlock_sub {ν t : ℝ} (ht : 0 ≤ t) (α : ℝ) {y : ℝ} (hy : y ^ 2 = ν - 1) :
    (sectorBlock t α y * (sectorBlock t α y)ᴴ - (t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
      (sectorL ν t α : ℂ) := by
  have hr : √(2 * t) * √(2 * t) = 2 * t := Real.mul_self_sqrt (by linarith)
  rw [sectorBlock_gram ht, Matrix.det_fin_two]
  generalize √(2 * t) = r at hr ⊢
  obtain rfl : ν = y ^ 2 + 1 := by linarith
  obtain rfl : t = r * r / 2 := by linarith
  apply Complex.ext <;> simp [sectorL, sq] <;> ring

theorem det_sub_sectorBlock {ν t : ℝ} (ht : 0 ≤ t) (α : ℝ) {y : ℝ} (hy : y ^ 2 = ν - 1) :
    ((4 * t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - sectorBlock t α y * (sectorBlock t α y)ᴴ).det =
      (sectorU ν t α : ℂ) := by
  have hr : √(2 * t) * √(2 * t) = 2 * t := Real.mul_self_sqrt (by linarith)
  rw [sectorBlock_gram ht, Matrix.det_fin_two]
  generalize √(2 * t) = r at hr ⊢
  obtain rfl : ν = y ^ 2 + 1 := by linarith
  obtain rfl : t = r * r / 2 := by linarith
  apply Complex.ext <;> simp [sectorU, sq] <;> ring

/-- The lower right entries of `B_y B_y^* - t I` and `4 t I - B_y B_y^*` are `t + ν` and `2t - ν`. -/
theorem sectorBlock_lowerRight {ν t : ℝ} (ht : 0 ≤ t) (α : ℝ) {y : ℝ} (hy : y ^ 2 = ν - 1) :
    (sectorBlock t α y * (sectorBlock t α y)ᴴ - (t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 =
        ((t + ν : ℝ) : ℂ) ∧
      ((4 * t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - sectorBlock t α y * (sectorBlock t α y)ᴴ) 1 1 =
        ((2 * t - ν : ℝ) : ℂ) := by
  rw [sectorBlock_gram ht]
  obtain rfl : ν = y ^ 2 + 1 := by linarith
  constructor <;> simp <;> ring

/-! ### Algebraic relations and evaluations -/

theorem sectorU_one (t α : ℝ) : sectorU 1 t α = sectorU 4 t α + 3 * (4 * t - α ^ 2) := by
  unfold sectorU; ring

theorem sectorL_eq (ν t α : ℝ) :
    sectorL ν t α = sectorU ν t α / 4 + 3 * t * α + 3 / 4 * ν * α ^ 2 := by
  unfold sectorL sectorU; ring

theorem sectorU_four_rho (ρ : ℝ) : sectorU 4 (ρ ^ 2) ρ = 4 * ρ ^ 2 * (ρ - 3) := by
  unfold sectorU; ring

theorem sectorU_four_rho_add (ρ : ℝ) :
    25 * sectorU 4 (ρ ^ 2) (ρ + 2 / 5) =
      4 * (5 * (ρ - 14) ^ 3 + 141 * (ρ - 14) ^ 2 + 1028 * (ρ - 14) + 480) := by
  unfold sectorU; ring

theorem sectorU_four_zero (t : ℝ) : sectorU 4 t 0 = 4 * t * (t - 4) := by
  unfold sectorU; ring

/-- Concavity of `U_4` in `α` (for `t ≥ 1`), as an exact interpolation identity:
`b U_4(α) = (b - α) U_4(0) + α U_4(b) + 4 (t - 1) b α (b - α)`. -/
theorem sectorU_four_interp (t α b : ℝ) :
    b * sectorU 4 t α =
      (b - α) * sectorU 4 t 0 + α * sectorU 4 t b + 4 * (t - 1) * b * α * (b - α) := by
  unfold sectorU; ring

/-- `U_4(α) ≥ 0` on `[0, b]` when `U_4(0) ≥ 0`, `U_4(b) ≥ 0` and `t ≥ 1`. -/
theorem sectorU_four_nonneg_of_endpoints {t α b : ℝ} (ht : 1 ≤ t) (hα : 0 ≤ α) (hαb : α ≤ b)
    (h0 : 0 ≤ sectorU 4 t 0) (hb : 0 ≤ sectorU 4 t b) : 0 ≤ sectorU 4 t α := by
  rcases eq_or_lt_of_le (hα.trans hαb) with hb0 | hb0
  · obtain rfl : α = 0 := by linarith
    exact h0
  have key := sectorU_four_interp t α b
  have h1 : 0 ≤ (b - α) * sectorU 4 t 0 := mul_nonneg (by linarith) h0
  have h2 : 0 ≤ α * sectorU 4 t b := mul_nonneg hα hb
  have h3 : 0 ≤ 4 * (t - 1) * b * α * (b - α) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * (t - 1)) hb0.le) hα)
      (by linarith : (0 : ℝ) ≤ b - α)
    linarith
  by_contra hneg
  push_neg at hneg
  nlinarith

/-- The conclusion of the proof of Lemma `lem:sector`: under its hypotheses on `α = 2(s-k)`,
`γ = 2(s+k)` and `ρ`, `t = ρ²`, we have `L_ν ≥ 0` and `U_ν ≥ 0` for `ν ∈ {1, 4}`.
(The paper's `j ≥ 5` gives `ρ = √(2j) ≥ 3`; `t ≥ 4` follows from `ρ ≥ 3`.) -/
theorem sector_nonneg {ρ α γ ν : ℝ} (hα : 0 ≤ α) (hρ : 3 ≤ ρ) (hαγ : α ≤ γ) (hγ : γ ≤ 2 * ρ)
    (hcase : α ≤ ρ ∨ (14 ≤ ρ ∧ α ≤ ρ + 2 / 5)) (hν : ν = 1 ∨ ν = 4) :
    0 ≤ sectorL ν (ρ ^ 2) α ∧ 0 ≤ sectorU ν (ρ ^ 2) α := by
  have ht1 : 1 ≤ ρ ^ 2 := by nlinarith
  have h0 : 0 ≤ sectorU 4 (ρ ^ 2) 0 := by
    rw [sectorU_four_zero]
    have : 0 ≤ ρ ^ 2 - 4 := by nlinarith
    positivity
  have hU4 : 0 ≤ sectorU 4 (ρ ^ 2) α := by
    rcases hcase with h | ⟨h14, h⟩
    · refine sectorU_four_nonneg_of_endpoints ht1 hα h h0 ?_
      rw [sectorU_four_rho]; have : 0 ≤ ρ - 3 := by linarith
      positivity
    · refine sectorU_four_nonneg_of_endpoints ht1 hα h h0 ?_
      have e := sectorU_four_rho_add ρ
      have hv : 0 ≤ ρ - 14 := by linarith
      have : 0 ≤ 5 * (ρ - 14) ^ 3 + 141 * (ρ - 14) ^ 2 + 1028 * (ρ - 14) + 480 := by positivity
      linarith
  have hU1 : 0 ≤ sectorU 1 (ρ ^ 2) α := by
    rw [sectorU_one]
    have : α ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
    linarith
  have hU : 0 ≤ sectorU ν (ρ ^ 2) α := by rcases hν with rfl | rfl <;> assumption
  refine ⟨?_, hU⟩
  rw [sectorL_eq]
  have hν0 : 0 ≤ ν := by rcases hν with rfl | rfl <;> norm_num
  positivity

/-! ### Hermitian `2 × 2` matrices -/

/-- If `q > 0` and `p q - |w|² ≥ 0`, the Hermitian form of `[[p, w], [w̄, q]]` is nonnegative:
`p |x|² + 2 Re(w x̄ y) + q |y|² ≥ 0`. -/
theorem herm_form_nonneg {p q : ℝ} (w : ℂ) (hq : 0 < q) (hdet : 0 ≤ p * q - normSq w) (x y : ℂ) :
    0 ≤ p * normSq x + 2 * (w * conj x * y).re + q * normSq y := by
  have key : q * (p * normSq x + 2 * (w * conj x * y).re + q * normSq y) =
      normSq (q * y + conj w * x) + (p * q - normSq w) * normSq x := by
    simp only [normSq_apply, mul_re, mul_im, add_re, add_im, conj_re, conj_im, ofReal_re,
      ofReal_im]
    ring
  have h1 := normSq_nonneg (q * y + conj w * x)
  have h2 := mul_nonneg hdet (normSq_nonneg x)
  by_contra hneg
  push_neg at hneg
  nlinarith

/-- A Hermitian `2 × 2` matrix `[[p, w], [w̄, q]]` with `q > 0` and determinant `p q - |w|² ≥ 0` is
positive semidefinite. -/
theorem posSemidef_fin_two {p q : ℝ} (w : ℂ) (hq : 0 < q) (hdet : 0 ≤ p * q - normSq w) :
    (!![(p : ℂ), w; conj w, (q : ℂ)]).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have h := herm_form_nonneg w hq hdet (x 0) (x 1)
    rw [Complex.nonneg_iff]
    simp only [dotProduct, mulVec, Fin.sum_univ_two, Pi.star_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, RCLike.star_def]
    constructor
    · simp only [normSq_apply, mul_re, mul_im, add_re, add_im, conj_re, conj_im, ofReal_re,
        ofReal_im] at h ⊢
      nlinarith [h]
    · simp only [mul_re, mul_im, add_re, add_im, conj_re, conj_im, ofReal_re, ofReal_im]
      ring

/-- A Hermitian `2 × 2` complex matrix with positive real lower right entry and nonnegative
real determinant is positive semidefinite. -/
theorem posSemidef_of_det {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.IsHermitian)
    (h11 : 0 < (M 1 1).re) (hdet : 0 ≤ M.det.re) : M.PosSemidef := by
  have h00 : M 0 0 = ((M 0 0).re : ℂ) := by
    have := hM.apply 0 0
    apply Complex.ext <;> simp
    have h := congrArg Complex.im this
    simp at h; linarith
  have h11' : M 1 1 = ((M 1 1).re : ℂ) := by
    have := hM.apply 1 1
    apply Complex.ext <;> simp
    have h := congrArg Complex.im this
    simp at h; linarith
  have h10 : M 1 0 = conj (M 0 1) := (hM.apply 1 0).symm
  have hMeq : M = !![((M 0 0).re : ℂ), M 0 1; conj (M 0 1), ((M 1 1).re : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← h00, ← h11', h10]
  rw [hMeq]
  refine posSemidef_fin_two _ h11 ?_
  rw [Matrix.det_fin_two, h00, h11', h10] at hdet
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, conj_re, conj_im] at hdet
  rw [normSq_apply]
  linarith

/-! ### The window `t I ⪯ B_y B_y^* ⪯ 4 t I` -/

/-- `t I ⪯ B_y B_y^* ⪯ 4 t I` as soon as `L_ν ≥ 0`, `U_ν ≥ 0`, `t + ν > 0` and `2t - ν > 0`
(the paper: "a Hermitian `2 × 2` matrix with a positive lower right entry and a nonnegative
determinant is positive semidefinite"). -/
theorem sectorBlock_window_of {ν t α y : ℝ} (ht : 0 ≤ t) (hy : y ^ 2 = ν - 1)
    (htν : 0 < t + ν) (hνt : 0 < 2 * t - ν) (hL : 0 ≤ sectorL ν t α) (hU : 0 ≤ sectorU ν t α) :
    (sectorBlock t α y * (sectorBlock t α y)ᴴ - (t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef ∧
      ((4 * t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        sectorBlock t α y * (sectorBlock t α y)ᴴ).PosSemidef := by
  obtain ⟨h1, h2⟩ := sectorBlock_lowerRight ht α hy
  constructor
  · refine posSemidef_of_det ?_ ?_ ?_
    · simp [IsHermitian, conjTranspose_sub, conjTranspose_mul, conjTranspose_smul]
    · rw [h1, ofReal_re]; exact htν
    · rw [det_sectorBlock_sub ht α hy, ofReal_re]; exact hL
  · refine posSemidef_of_det ?_ ?_ ?_
    · simp [IsHermitian, conjTranspose_sub, conjTranspose_mul, conjTranspose_smul]
    · rw [h2, ofReal_re]; exact hνt
    · rw [det_sub_sectorBlock ht α hy, ofReal_re]; exact hU

/-- The `2 × 2` content of Lemma `lem:sector`: with `t = ρ²`, `ν = 1 + y² ∈ {1, 4}`, `α ≥ 0`,
`ρ ≥ 3`, `α ≤ γ ≤ 2ρ`, and `α ≤ ρ` or (`ρ ≥ 14` and `α ≤ ρ + 2/5`), the block `B_y` satisfies
`t I ⪯ B_y B_y^* ⪯ 4 t I`. -/
theorem sectorBlock_window {ρ α γ y : ℝ} (hα : 0 ≤ α) (hρ : 3 ≤ ρ) (hαγ : α ≤ γ)
    (hγ : γ ≤ 2 * ρ) (hcase : α ≤ ρ ∨ (14 ≤ ρ ∧ α ≤ ρ + 2 / 5)) (hy : y ^ 2 = 0 ∨ y ^ 2 = 3) :
    (sectorBlock (ρ ^ 2) α y * (sectorBlock (ρ ^ 2) α y)ᴴ -
        ((ρ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef ∧
      ((4 * (ρ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        sectorBlock (ρ ^ 2) α y * (sectorBlock (ρ ^ 2) α y)ᴴ).PosSemidef := by
  have hν : 1 + y ^ 2 = 1 ∨ 1 + y ^ 2 = 4 := by
    rcases hy with h | h <;> [left; right] <;> linarith
  obtain ⟨hL, hU⟩ := sector_nonneg hα hρ hαγ hγ hcase hν
  have ht : 9 ≤ ρ ^ 2 := by nlinarith
  have hν4 : 1 + y ^ 2 ≤ 4 := by rcases hν with h | h <;> linarith
  exact sectorBlock_window_of (by linarith) (by ring) (by positivity) (by linarith) hL hU

end SignCond
