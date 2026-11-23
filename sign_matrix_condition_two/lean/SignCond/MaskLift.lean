import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round

/-!
# Lifting masks (Lemma `lem:masklift`)

For a finite set `S` of naturals, `pS S z = ∑ x ∈ S, z ^ x`, and `maskLift S = 4S ∪ (4S + 1)`.

* `maskLift_disjoint`, `card_maskLift`: the two halves are disjoint, so `|S'| = 2|S|`.
* `pS_maskLift`: `p_{S'}(z) = (1 + z) p_S(z⁴)`.
* `norm_one_add_lt`: if `z` is within `δ ≤ 1/16` of `i`, `-1` or `-i` then `|1 + z| < 3/2`
  (via `√2 < 23/16`).
* `norm_exp_sub_exp_le`: `|e^{ia} - e^{ib}| ≤ |a - b|` (chord ≤ arc).
* `masklift`: the lemma, with `z = e^{iθ}`.
-/

open Complex
open scoped Real

namespace SignCond

/-- `p_S(z) = ∑_{x ∈ S} z^x`. -/
noncomputable def pS (S : Finset ℕ) (z : ℂ) : ℂ := ∑ x ∈ S, z ^ x

/-- `S' = 4S ∪ (4S + 1)`. -/
def maskLift (S : Finset ℕ) : Finset ℕ := S.image (4 * ·) ∪ S.image (4 * · + 1)

theorem maskLift_disjoint (S : Finset ℕ) :
    Disjoint (S.image (4 * ·)) (S.image (4 * · + 1)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_image] at ha hb
  obtain ⟨x, -, rfl⟩ := ha
  obtain ⟨y, -, hy⟩ := hb
  omega

theorem card_maskLift (S : Finset ℕ) : (maskLift S).card = 2 * S.card := by
  rw [maskLift, Finset.card_union_of_disjoint (maskLift_disjoint S),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by omega)]
  ring

/-- `p_{S'}(z) = (1 + z) p_S(z⁴)`. -/
theorem pS_maskLift (S : Finset ℕ) (z : ℂ) : pS (maskLift S) z = (1 + z) * pS S (z ^ 4) := by
  rw [pS, maskLift, Finset.sum_union (maskLift_disjoint S),
    Finset.sum_image (fun a _ b _ h => by simpa using h),
    Finset.sum_image (fun a _ b _ h => by omega), pS, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pow_succ, pow_mul]
  ring

/-- Trivial bound `|p_S(w)| ≤ |S|` on the unit circle. -/
theorem norm_pS_le (S : Finset ℕ) {w : ℂ} (hw : ‖w‖ = 1) : ‖pS S w‖ ≤ S.card := by
  calc ‖pS S w‖ ≤ ∑ x ∈ S, ‖w ^ x‖ := norm_sum_le _ _
    _ = S.card := by simp [norm_pow, hw]

/-- If `|1 + ζ|² ≤ 2` and `|z - ζ| ≤ 1/16` then `|1 + z| < 3/2`, because `√2 < 23/16`. -/
theorem norm_one_add_lt_of {z ζ : ℂ} (hζ : ‖1 + ζ‖ ^ 2 ≤ 2) (hz : ‖z - ζ‖ ≤ 1 / 16) :
    ‖1 + z‖ < 3 / 2 := by
  have h1 : ‖1 + ζ‖ < 23 / 16 := by
    nlinarith [norm_nonneg (1 + ζ)]
  calc ‖1 + z‖ = ‖(1 + ζ) + (z - ζ)‖ := by ring_nf
    _ ≤ ‖1 + ζ‖ + ‖z - ζ‖ := norm_add_le _ _
    _ < 3 / 2 := by linarith

/-- The analytic step of Lemma `lem:masklift`: if `z` is within `δ ≤ 1/16` of one of `i`, `-1`,
`-i`, then `|1 + z| < 3/2`. (`|z| = 1` is not needed.) -/
theorem norm_one_add_lt {z ζ : ℂ} {δ : ℝ} (hζ : ζ = I ∨ ζ = -1 ∨ ζ = -I) (hz : ‖z - ζ‖ ≤ δ)
    (hδ : δ ≤ 1 / 16) : ‖1 + z‖ < 3 / 2 := by
  refine norm_one_add_lt_of ?_ (hz.trans hδ)
  rw [Complex.sq_norm]
  rcases hζ with rfl | rfl | rfl <;> simp [normSq_apply] <;> norm_num

/-- `|e^{ix} - 1| ≤ |x|`. -/
theorem norm_exp_mul_I_sub_one_le (x : ℝ) : ‖exp (x * I) - 1‖ ≤ |x| := by
  have key : normSq (exp ((x : ℂ) * I) - 1) = 2 - 2 * Real.cos x := by
    rw [normSq_apply]
    simp only [sub_re, sub_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, one_re, one_im]
    linear_combination Real.sin_sq_add_cos_sq x
  have hc : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hsq : ‖exp ((x : ℂ) * I) - 1‖ ^ 2 ≤ |x| ^ 2 := by
    rw [Complex.sq_norm, sq_abs, key]
    linarith
  nlinarith [norm_nonneg (exp ((x : ℂ) * I) - 1), abs_nonneg x]

/-- Chord ≤ arc: `|e^{ia} - e^{ib}| ≤ |a - b|`. -/
theorem norm_exp_sub_exp_le (a b : ℝ) : ‖exp (a * I) - exp (b * I)‖ ≤ |a - b| := by
  have e : exp (a * I) - exp (b * I) = exp (b * I) * (exp (((a - b : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact norm_exp_mul_I_sub_one_le _

/-- Lemma `lem:masklift`. Let `S` have `q` elements, `J ≥ 32`, `η ≤ q/4` (the paper also assumes `η > 0`;
it is not needed), and
`|p_S(e^{iθ})| ≤ q - η` for `2π/J ≤ |θ| ≤ π`. Then `S' = 4S ∪ (4S+1)` satisfies
`|p_{S'}(e^{iθ})| ≤ 2q - 2η` for `2π/(4J) ≤ |θ| ≤ π`. -/
theorem masklift (S : Finset ℕ) {J η : ℝ} (hJ : 32 ≤ J) (hηq : η ≤ S.card / 4)
    (h : ∀ θ : ℝ, 2 * π / J ≤ |θ| → |θ| ≤ π → ‖pS S (exp (θ * I))‖ ≤ S.card - η)
    (θ : ℝ) (hθ1 : 2 * π / (4 * J) ≤ |θ|) (hθ2 : |θ| ≤ π) :
    ‖pS (maskLift S) (exp (θ * I))‖ ≤ 2 * S.card - 2 * η := by
  set q : ℝ := (S.card : ℝ)
  have hJ0 : 0 < J := by linarith
  rw [pS_maskLift, norm_mul, ← Complex.exp_nat_mul]
  -- reduce `4θ` to `φ ∈ [-π, π]`: `4θ = φ + 2π n`
  set n : ℤ := round (4 * θ / (2 * π))
  set φ : ℝ := 4 * θ - 2 * π * n
  have hφ : |φ| ≤ π := by
    have hr := abs_sub_round (4 * θ / (2 * π))
    have : φ = 2 * π * (4 * θ / (2 * π) - n) := by
      simp only [φ]; field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith [Real.pi_pos]
  have hexp : exp ((4 : ℕ) * (θ * I)) = exp (φ * I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨n, by simp only [φ]; push_cast; ring⟩
  rw [hexp]
  have hz1 : ‖1 + exp (θ * I)‖ ≤ 2 := by
    calc ‖1 + exp (θ * I)‖ ≤ ‖(1 : ℂ)‖ + ‖exp (θ * I)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_exp_ofReal_mul_I]; norm_num
  have hq0 : 0 ≤ q := by positivity
  by_cases hfar : 2 * π / J ≤ |φ|
  · -- far from `0` modulo `2π` after multiplying by 4
    have h1 := h φ hfar hφ
    calc ‖1 + exp (θ * I)‖ * ‖pS S (exp (φ * I))‖ ≤ 2 * (q - η) :=
          mul_le_mul hz1 h1 (norm_nonneg _) (by norm_num)
      _ = 2 * q - 2 * η := by ring
  · -- `z` is close to `e^{i n π / 2}` with `n ∈ {±1, ±2}`
    push_neg at hfar
    have hπJ : π / (2 * J) ≤ π / 64 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
    have hdist : |θ - n * π / 2| < π / (2 * J) := by
      have : θ - n * π / 2 = φ / 4 := by simp only [φ]; ring
      rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      calc |φ| / 4 < 2 * π / J / 4 := by linarith
        _ = π / (2 * J) := by field_simp; ring
    have hθ1' : π / (2 * J) ≤ |θ| := by
      calc π / (2 * J) = 2 * π / (4 * J) := by field_simp; ring
        _ ≤ |θ| := hθ1
    have hn0 : n ≠ 0 := by
      intro hn
      rw [hn] at hdist
      simp at hdist
      linarith
    have hn2 : |(n : ℝ)| ≤ 2 := by
      have h3 : |(n : ℝ) * π / 2| < π + π / 64 := by
        have := abs_sub_abs_le_abs_sub θ (n * π / 2)
        have := abs_sub_comm θ (n * π / 2)
        have := abs_sub_abs_le_abs_sub (n * π / 2) θ
        linarith
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h3
      have : |(n : ℝ)| < 2 + 1 / 32 := by nlinarith [Real.pi_pos]
      have hi : |n| < 3 := by
        have : (|n| : ℝ) < 3 := by linarith
        exact_mod_cast this
      have : |n| ≤ 2 := by omega
      exact_mod_cast this
    -- `|1 + ζ|² = 2 + 2 cos(nπ/2) ≤ 2`
    set ζ := exp (((n * π / 2 : ℝ) : ℂ) * I)
    have hcos : Real.cos (n * π / 2) ≤ 0 := by
      have hn' : n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2 := by
        have : |n| ≤ 2 := by exact_mod_cast hn2
        have := abs_le.mp this
        omega
      rcases hn' with h | h | h | h <;> rw [h]
      · push_cast
        rw [show (-2 : ℝ) * π / 2 = -π by ring, Real.cos_neg, Real.cos_pi]; norm_num
      · push_cast
        rw [show (-1 : ℝ) * π / 2 = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
      · push_cast
        rw [show (1 : ℝ) * π / 2 = π / 2 by ring, Real.cos_pi_div_two]
      · push_cast
        rw [show (2 : ℝ) * π / 2 = π by ring, Real.cos_pi]; norm_num
    have hζ : ‖1 + ζ‖ ^ 2 ≤ 2 := by
      rw [Complex.sq_norm, normSq_apply]
      simp only [ζ, add_re, add_im, one_re, one_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
      nlinarith [Real.sin_sq_add_cos_sq (n * π / 2)]
    have hzζ : ‖exp (θ * I) - ζ‖ ≤ 1 / 16 := by
      calc ‖exp (θ * I) - ζ‖ ≤ |θ - n * π / 2| := norm_exp_sub_exp_le _ _
        _ ≤ π / 64 := by linarith
        _ ≤ 1 / 16 := by linarith [Real.pi_le_four]
    have hlt := norm_one_add_lt_of hζ hzζ
    have hp := norm_pS_le S (norm_exp_ofReal_mul_I φ)
    calc ‖1 + exp (θ * I)‖ * ‖pS S (exp (φ * I))‖ ≤ 3 / 2 * q :=
          mul_le_mul hlt.le hp (norm_nonneg _) (by norm_num)
      _ ≤ 2 * q - 2 * η := by linarith

end SignCond
