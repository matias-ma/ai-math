import SignCond.Fourier
import SignCond.Maclaurin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.BigOperators

/-!
# Lemma `lem:select`: a `k`-subset with small Fourier coefficients

If `P ⊆ ℤ/jℤ` has all nontrivial Fourier sums at most `|P|/33`, `13 ≤ k ≤ |P|` and `j ≤ 196 k²`,
then some `k`-subset `S ⊆ P` has `|Σ_{x∈S} χ(ℓx)| ≤ k - 3/8` for every `ℓ ≠ 0`.

Proof (as in the paper). For a direction `h ∈ {0,…,k}` put `u_h = exp(i(π - 2πh/k))`,
`c_{ℓ,h}(x) = Re(u_h χ(ℓx))` and `w_{ℓ,h}(x) = ((1 + c_{ℓ,h}(x))/2)^3 ∈ [0,1]`.

* Step 1 (`exists_dir`, `bad_prod`): if `|Σ_{x∈S} χ(ℓx)| > k - 3/8` with `|S| = k`, some direction
  gives `Σ_S c > k - 4/5`, hence (Weierstrass product inequality `one_sub_sum_le_prod`)
  `Π_S w_{ℓ,h} > (3/5)^3 = 27/125`.
* Step 2 (`cube_re`, `sum_wt_good`, `sum_wt_any`): `((1 + Re z)/2)^3 = (10 + 15 Re z + 6 Re z² + Re z³)/32`
  for `|z| = 1`, so the mean of `w_{ℓ,h}` over `P` is at most `1/3` when `ℓ, 2ℓ, 3ℓ ≠ 0`, and at most
  `17/33` for every `ℓ ≠ 0` (using `t³ ≤ t`).
* Step 3: Maclaurin's inequality (`SignCond.maclaurin_le`, file `Maclaurin.lean`).
* Step 4: by conjugate symmetry only `ℓ` in `half j = {ℓ : 0 < ℓ.val, 2ℓ.val ≤ j}` (at most `98k²`
  elements, at most two of them with `2ℓ = 0` or `3ℓ = 0`) are needed; summing over all `k`-subsets,
  `C(N,k)·27/125 < C(N,k)·(k+1)(98k²·3^{-k} + 2(17/33)^k) ≤ C(N,k)·27/125` is a contradiction
  (`numeric_final`).

(Our direction set has `k+1` elements, `h = 0` and `h = k` giving the same direction; this costs a
factor `(k+1)/k` that the numerical margin absorbs.)
-/

open Complex ComplexConjugate Finset
open scoped Real

namespace SignCond

/-! ### Directions -/

/-- The direction `u_h = exp(i(π - 2πh/k))`. -/
noncomputable def rot (k h : ℕ) : ℂ := exp (((π - 2 * π * h / k : ℝ) : ℂ) * I)

theorem norm_rot (k h : ℕ) : ‖rot k h‖ = 1 := norm_exp_ofReal_mul_I _

/-- Every complex number is within angle `π/k` of one of the directions `u_0, …, u_k`. -/
theorem exists_dir (k : ℕ) (hk : 0 < k) (z : ℂ) :
    ∃ h ∈ range (k + 1), ‖z‖ * (1 - (π / k) ^ 2 / 2) ≤ (rot k h * z).re := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hθ1 := neg_pi_lt_arg z
  have hθ2 := arg_le_pi z
  have hpi := Real.pi_pos
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (arg z + π) * k / (2 * π) := ⟨_, rfl⟩
  have hr := abs_sub_round x
  rw [abs_le] at hr
  generalize hrdef : round x = r at hr
  have hx0 : 0 < x := by
    rw [hx]; have : 0 < arg z + π := by linarith
    positivity
  have hxk : x ≤ k := by
    rw [hx, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * π - (arg z + π)) hkpos.le]
  have hr0 : 0 ≤ r := by
    have h1 : ((-1 : ℤ) : ℝ) < r := by push_cast; linarith [hr.1, hr.2]
    have h2 : (-1 : ℤ) < r := by exact_mod_cast h1
    omega
  have hrk : r ≤ k := by
    have h1 : (r : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; linarith [hr.1, hr.2]
    have h2 : r < (k : ℤ) + 1 := by exact_mod_cast h1
    omega
  refine ⟨r.toNat, ?_, ?_⟩
  · rw [mem_range]; omega
  · have hcast : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by
      have := Int.toNat_of_nonneg hr0
      exact_mod_cast this
    have hre : (rot k r.toNat * z).re = ‖z‖ * Real.cos (π - 2 * π * (r.toNat : ℕ) / k + arg z) := by
      conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
      rw [rot, mul_left_comm, ← exp_add, re_ofReal_mul]
      rw [show ((π - 2 * π * ((r.toNat : ℕ) : ℝ) / k : ℝ) : ℂ) * I + (arg z : ℂ) * I
          = ((π - 2 * π * ((r.toNat : ℕ) : ℝ) / k + arg z : ℝ) : ℂ) * I by push_cast; ring]
      rw [exp_ofReal_mul_I_re]
    rw [hre, hcast]
    have hdev : π - 2 * π * (r : ℝ) / k + arg z = (2 * π / k) * (x - r) := by
      rw [hx]; field_simp; ring
    have hcos := Real.one_sub_sq_div_two_le_cos (x := π - 2 * π * (r : ℝ) / k + arg z)
    have hsq : (π - 2 * π * (r : ℝ) / k + arg z) ^ 2 ≤ (π / k) ^ 2 := by
      rw [hdev]
      have h4 : (x - r) ^ 2 ≤ 1 / 4 := by
        nlinarith [mul_nonneg (by linarith [hr.1] : (0 : ℝ) ≤ x - r + 1 / 2)
          (by linarith [hr.2] : (0 : ℝ) ≤ 1 / 2 - (x - r))]
      calc (2 * π / k * (x - r)) ^ 2 = (2 * π / k) ^ 2 * (x - r) ^ 2 := by ring
        _ ≤ (2 * π / k) ^ 2 * (1 / 4) := by gcongr
        _ = (π / k) ^ 2 := by ring
    have hc : 1 - (π / k) ^ 2 / 2 ≤ Real.cos (π - 2 * π * (r : ℝ) / k + arg z) := by linarith
    exact mul_le_mul_of_nonneg_left hc (norm_nonneg z)

/-- The numerical part of Step 1: `(k - 3/8)(1 - π²/(2k²)) > k - 4/5` for `k ≥ 13`. -/
theorem step1_numeric (k : ℕ) (hk : 13 ≤ k) (A B : ℝ) (hA : (k : ℝ) - 3 / 8 < A)
    (hB : A * (1 - (π / k) ^ 2 / 2) ≤ B) : (k : ℝ) - 4 / 5 < B := by
  have hkr : (13 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  set q := (π / k) ^ 2 / 2 with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq_eq : q * (2 * (k : ℝ) ^ 2) = π ^ 2 := by rw [hqdef]; field_simp; ring
  have hpi2 : π ^ 2 < 9.93 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h1 : q * (2 * (k : ℝ) ^ 2) < 9.93 := by rw [hq_eq]; exact hpi2
  have h2 : q * k * 26 ≤ q * (2 * (k : ℝ) ^ 2) := by
    have : (26 : ℝ) * k ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hq0]
  have h3 : q * 338 ≤ q * (2 * (k : ℝ) ^ 2) := by
    have : (338 : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hq0
  have hq1 : 0 < 1 - q := by linarith
  have h4 : ((k : ℝ) - 3 / 8) * (1 - q) < A * (1 - q) := mul_lt_mul_of_pos_right hA hq1
  nlinarith

/-! ### The Weierstrass product inequality and the cube identity -/

/-- `Π aᵢ ≥ 1 - Σ (1 - aᵢ)` for `aᵢ ∈ [0,1]`. -/
theorem one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ x ∈ s, 0 ≤ a x) (h1 : ∀ x ∈ s, a x ≤ 1) :
    1 - ∑ x ∈ s, (1 - a x) ≤ ∏ x ∈ s, a x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [sum_insert hb, prod_insert hb]
    have h0b := h0 b (mem_insert_self b s)
    have h1b := h1 b (mem_insert_self b s)
    have ih' := ih (fun x hx => h0 x (mem_insert_of_mem hx))
      (fun x hx => h1 x (mem_insert_of_mem hx))
    have hD : 0 ≤ ∑ x ∈ s, (1 - a x) :=
      sum_nonneg fun x hx => by linarith [h1 x (mem_insert_of_mem hx)]
    have e1 : a b * (1 - ∑ x ∈ s, (1 - a x)) ≤ a b * ∏ x ∈ s, a x :=
      mul_le_mul_of_nonneg_left ih' h0b
    have e2 : 0 ≤ (1 - a b) * ∑ x ∈ s, (1 - a x) := mul_nonneg (by linarith) hD
    nlinarith [e1, e2]

/-- `((1 + cos θ)/2)^3 = (10 + 15 cos θ + 6 cos 2θ + cos 3θ)/32`, for `z = e^{iθ}`. -/
theorem cube_re (z : ℂ) (hz : ‖z‖ = 1) :
    ((1 + z.re) / 2) ^ 3 = (10 + 15 * z.re + 6 * (z ^ 2).re + (z ^ 3).re) / 32 := by
  have h : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  have e2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two]; simp only [Complex.mul_re]; ring
  have e3 : (z ^ 3).re = z.re ^ 3 - 3 * z.re * z.im ^ 2 := by
    rw [show z ^ 3 = z * z * z by ring]; simp only [Complex.mul_re, Complex.mul_im]; ring
  rw [e2, e3]
  linear_combination ((6 + 3 * z.re) / 32) * h

/-! ### The weights -/

section weights

variable {j : ℕ} [NeZero j]

/-- `c_{ℓ,h}(x) = Re(u_h χ(ℓx))`. -/
noncomputable def cdir (k h : ℕ) (ℓ x : ZMod j) : ℝ := (rot k h * chi (ℓ * x)).re

/-- `w_{ℓ,h}(x) = ((1 + c_{ℓ,h}(x))/2)^3`. -/
noncomputable def wt (k h : ℕ) (ℓ x : ZMod j) : ℝ := ((1 + cdir k h ℓ x) / 2) ^ 3

theorem abs_cdir_le (k h : ℕ) (ℓ x : ZMod j) : |cdir k h ℓ x| ≤ 1 := by
  have := Complex.abs_re_le_norm (rot k h * chi (ℓ * x))
  rwa [norm_mul, norm_rot, norm_chi, one_mul] at this

theorem half_cdir_nonneg (k h : ℕ) (ℓ x : ZMod j) : 0 ≤ (1 + cdir k h ℓ x) / 2 := by
  have := abs_le.1 (abs_cdir_le k h ℓ x); linarith

theorem half_cdir_le_one (k h : ℕ) (ℓ x : ZMod j) : (1 + cdir k h ℓ x) / 2 ≤ 1 := by
  have := abs_le.1 (abs_cdir_le k h ℓ x); linarith

theorem wt_nonneg (k h : ℕ) (ℓ x : ZMod j) : 0 ≤ wt k h ℓ x :=
  pow_nonneg (half_cdir_nonneg k h ℓ x) 3

omit [NeZero j] in
theorem sum_cdir (k h : ℕ) (ℓ : ZMod j) (S : Finset (ZMod j)) :
    ∑ x ∈ S, cdir k h ℓ x = (rot k h * ∑ x ∈ S, chi (ℓ * x)).re := by
  rw [mul_sum, re_sum]; rfl

omit [NeZero j] in
theorem re_rot_pow_sum_le (k h m : ℕ) (ℓ' : ZMod j) (P : Finset (ZMod j)) :
    ∑ x ∈ P, (rot k h ^ m * chi (ℓ' * x)).re ≤ ‖∑ x ∈ P, chi (ℓ' * x)‖ := by
  rw [← re_sum, ← mul_sum]
  refine (Complex.re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, norm_pow, norm_rot, one_pow, one_mul]

/-- Step 2, the generic case: if `ℓ, 2ℓ, 3ℓ` all have small sums, the mean of `w_{ℓ,h}` is `≤ 1/3`. -/
theorem sum_wt_good (P : Finset (ZMod j)) (k h : ℕ) (ℓ : ZMod j)
    (h1 : ‖∑ x ∈ P, chi (ℓ * x)‖ ≤ (P.card : ℝ) / 33)
    (h2 : ‖∑ x ∈ P, chi ((2 * ℓ) * x)‖ ≤ (P.card : ℝ) / 33)
    (h3 : ‖∑ x ∈ P, chi ((3 * ℓ) * x)‖ ≤ (P.card : ℝ) / 33) :
    ∑ x ∈ P, wt k h ℓ x ≤ 1 / 3 * P.card := by
  have hpt : ∀ x, wt k h ℓ x = (10 + 15 * (rot k h ^ 1 * chi (ℓ * x)).re
      + 6 * (rot k h ^ 2 * chi ((2 * ℓ) * x)).re + (rot k h ^ 3 * chi ((3 * ℓ) * x)).re) / 32 := by
    intro x
    have hz : ‖rot k h * chi (ℓ * x)‖ = 1 := by rw [norm_mul, norm_rot, norm_chi, one_mul]
    rw [wt, cdir, cube_re _ hz, pow_one]
    have e2 : (rot k h * chi (ℓ * x)) ^ 2 = rot k h ^ 2 * chi ((2 * ℓ) * x) := by
      rw [mul_pow, pow_two (chi _), ← chi_add, show ℓ * x + ℓ * x = (2 * ℓ) * x by ring]
    have e3 : (rot k h * chi (ℓ * x)) ^ 3 = rot k h ^ 3 * chi ((3 * ℓ) * x) := by
      rw [mul_pow, pow_three (chi _), ← chi_add, ← chi_add,
        show ℓ * x + (ℓ * x + ℓ * x) = (3 * ℓ) * x by ring]
    rw [e2, e3]
  rw [sum_congr rfl (fun x _ => hpt x), ← sum_div, sum_add_distrib, sum_add_distrib,
    sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, nsmul_eq_mul]
  have t1 := re_rot_pow_sum_le k h 1 ℓ P
  have t2 := re_rot_pow_sum_le k h 2 (2 * ℓ) P
  have t3 := re_rot_pow_sum_le k h 3 (3 * ℓ) P
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- Step 2, every `ℓ ≠ 0`: the mean of `w_{ℓ,h}` is at most `17/33`. -/
theorem sum_wt_any (P : Finset (ZMod j)) (k h : ℕ) (ℓ : ZMod j)
    (h1 : ‖∑ x ∈ P, chi (ℓ * x)‖ ≤ (P.card : ℝ) / 33) :
    ∑ x ∈ P, wt k h ℓ x ≤ 17 / 33 * P.card := by
  have hpt : ∀ x ∈ P, wt k h ℓ x ≤ 1 / 2 + cdir k h ℓ x / 2 := by
    intro x _
    have a0 := half_cdir_nonneg k h ℓ x
    have a1 := half_cdir_le_one k h ℓ x
    have : ((1 + cdir k h ℓ x) / 2) ^ 3 ≤ (1 + cdir k h ℓ x) / 2 := by
      have hsq : ((1 + cdir k h ℓ x) / 2) ^ 2 ≤ 1 := by nlinarith
      calc ((1 + cdir k h ℓ x) / 2) ^ 3
          = (1 + cdir k h ℓ x) / 2 * ((1 + cdir k h ℓ x) / 2) ^ 2 := by ring
        _ ≤ (1 + cdir k h ℓ x) / 2 * 1 := mul_le_mul_of_nonneg_left hsq a0
        _ = (1 + cdir k h ℓ x) / 2 := mul_one _
    rw [wt]; linarith
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_div, sum_cdir]
  have t1 := re_rot_pow_sum_le k h 1 ℓ P
  rw [pow_one, ← re_sum, ← mul_sum] at t1
  linarith

/-! ### Step 1: a bad set has a large product -/

theorem bad_prod (S : Finset (ZMod j)) (k : ℕ) (hk : 13 ≤ k) (hS : S.card = k) (ℓ : ZMod j)
    (hbad : (k : ℝ) - 3 / 8 < ‖∑ x ∈ S, chi (ℓ * x)‖) :
    ∃ h ∈ range (k + 1), (27 / 125 : ℝ) < ∏ x ∈ S, wt k h ℓ x := by
  obtain ⟨h, hh, hdir⟩ := exists_dir k (by omega) (∑ x ∈ S, chi (ℓ * x))
  refine ⟨h, hh, ?_⟩
  have hc : (k : ℝ) - 4 / 5 < ∑ x ∈ S, cdir k h ℓ x := by
    rw [sum_cdir]; exact step1_numeric k hk _ _ hbad hdir
  have hW := one_sub_sum_le_prod S (fun x => (1 + cdir k h ℓ x) / 2)
    (fun x _ => half_cdir_nonneg k h ℓ x) (fun x _ => half_cdir_le_one k h ℓ x)
  have hdef : ∑ x ∈ S, (1 - (1 + cdir k h ℓ x) / 2) = ((k : ℝ) - ∑ x ∈ S, cdir k h ℓ x) / 2 := by
    rw [sum_congr rfl (fun x _ => show 1 - (1 + cdir k h ℓ x) / 2 = 1 / 2 - cdir k h ℓ x / 2 by ring),
      sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_div, hS]
    ring
  simp only at hW
  rw [hdef] at hW
  have hp : (3 / 5 : ℝ) < ∏ x ∈ S, (1 + cdir k h ℓ x) / 2 := by linarith
  have hw : ∏ x ∈ S, wt k h ℓ x = (∏ x ∈ S, (1 + cdir k h ℓ x) / 2) ^ 3 := by
    rw [← prod_pow]; rfl
  rw [hw]
  calc (27 / 125 : ℝ) = (3 / 5) ^ 3 := by norm_num
    _ < (∏ x ∈ S, (1 + cdir k h ℓ x) / 2) ^ 3 := by gcongr

end weights

/-! ### Step 4: symmetry and counting -/

section counting

variable {j : ℕ} [NeZero j]

theorem norm_sum_chi_neg (S : Finset (ZMod j)) (ℓ : ZMod j) :
    ‖∑ x ∈ S, chi (-ℓ * x)‖ = ‖∑ x ∈ S, chi (ℓ * x)‖ := by
  rw [show (∑ x ∈ S, chi (-ℓ * x)) = conj (∑ x ∈ S, chi (ℓ * x)) by
    rw [map_sum]; refine sum_congr rfl fun x _ => ?_; rw [neg_mul, chi_neg]]
  exact Complex.norm_conj _

variable (j) in
/-- `{ℓ : 0 < ℓ.val ≤ j/2}`. -/
def half : Finset (ZMod j) := univ.filter (fun ℓ => 0 < ℓ.val ∧ 2 * ℓ.val ≤ j)

theorem mem_half {ℓ : ZMod j} : ℓ ∈ half j ↔ 0 < ℓ.val ∧ 2 * ℓ.val ≤ j := by
  simp [half]

theorem ne_zero_of_mem_half {ℓ : ZMod j} (h : ℓ ∈ half j) : ℓ ≠ 0 := by
  rw [mem_half] at h
  intro h0; rw [h0, ZMod.val_zero] at h; omega

theorem mem_half_of_ne {ℓ : ZMod j} (hℓ : ℓ ≠ 0) : ℓ ∈ half j ∨ -ℓ ∈ half j := by
  have hv : 0 < ℓ.val := by
    rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact hℓ
  have hlt := ZMod.val_lt ℓ
  rw [mem_half, mem_half, ZMod.neg_val, if_neg hℓ]
  omega

theorem card_half : 2 * (half j).card ≤ j := by
  have : (half j).card ≤ j / 2 := by
    rw [← card_image_of_injective _ (ZMod.val_injective j)]
    calc ((half j).image ZMod.val).card ≤ (Icc 1 (j / 2)).card := card_le_card (by
          intro v hv
          rw [mem_image] at hv
          obtain ⟨ℓ, hℓ, rfl⟩ := hv
          rw [mem_half] at hℓ
          rw [mem_Icc]; omega)
      _ = j / 2 := by simp
  omega

theorem val_eq_of_two_mul_eq_zero {ℓ : ZMod j} (hℓ : ℓ ∈ half j) (h : (2 : ZMod j) * ℓ = 0) :
    2 * ℓ.val = j := by
  rw [mem_half] at hℓ
  have hc : ((2 * ℓ.val : ℕ) : ZMod j) = 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]; exact h
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨c, hc⟩ := hc
  have hjpos : 0 < j := Nat.pos_of_ne_zero (NeZero.ne j)
  have hc1 : c ≤ 1 := by
    have : j * c ≤ j * 1 := by omega
    exact Nat.le_of_mul_le_mul_left this hjpos
  interval_cases c <;> omega

theorem val_eq_of_three_mul_eq_zero {ℓ : ZMod j} (hℓ : ℓ ∈ half j) (h : (3 : ZMod j) * ℓ = 0) :
    3 * ℓ.val = j := by
  rw [mem_half] at hℓ
  have hc : ((3 * ℓ.val : ℕ) : ZMod j) = 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]; exact h
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨c, hc⟩ := hc
  have hjpos : 0 < j := Nat.pos_of_ne_zero (NeZero.ne j)
  have hc1 : c ≤ 1 := by
    have : j * c < j * 2 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  interval_cases c <;> omega

/-- At most two `ℓ ∈ half j` have `2ℓ = 0` or `3ℓ = 0`. -/
theorem card_exceptional :
    ((half j).filter (fun ℓ => ¬ ((2 : ZMod j) * ℓ ≠ 0 ∧ (3 : ZMod j) * ℓ ≠ 0))).card ≤ 2 := by
  have hsub : (half j).filter (fun ℓ => ¬ ((2 : ZMod j) * ℓ ≠ 0 ∧ (3 : ZMod j) * ℓ ≠ 0)) ⊆
      univ.filter (fun ℓ : ZMod j => 2 * ℓ.val = j) ∪ univ.filter (fun ℓ : ZMod j => 3 * ℓ.val = j) := by
    intro ℓ hℓ
    rw [mem_filter] at hℓ
    rw [mem_union, mem_filter, mem_filter]
    by_cases h2 : (2 : ZMod j) * ℓ = 0
    · exact Or.inl ⟨mem_univ _, val_eq_of_two_mul_eq_zero hℓ.1 h2⟩
    · have h3 : (3 : ZMod j) * ℓ = 0 := by
        by_contra h3; exact hℓ.2 ⟨h2, h3⟩
      exact Or.inr ⟨mem_univ _, val_eq_of_three_mul_eq_zero hℓ.1 h3⟩
  have hA : (univ.filter (fun ℓ : ZMod j => 2 * ℓ.val = j)).card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    rw [mem_filter] at ha hb
    exact ZMod.val_injective j (by omega)
  have hB : (univ.filter (fun ℓ : ZMod j => 3 * ℓ.val = j)).card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    rw [mem_filter] at ha hb
    exact ZMod.val_injective j (by omega)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ 2 := by omega

end counting

/-! ### The numerical inequality -/

theorem numeric_A (k : ℕ) (hk : 13 ≤ k) :
    ((k : ℝ) + 1) * (17 / 33) ^ k ≤ 14 * (17 / 33) ^ 13 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : (0 : ℝ) ≤ (17 / 33) ^ k := by positivity
    have hkr : (13 : ℝ) ≤ k := by exact_mod_cast hk
    have : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [this, pow_succ]
    have h1 : ((k : ℝ) + 2) * (17 / 33) ≤ (k : ℝ) + 1 := by linarith
    calc ((k : ℝ) + 2) * ((17 / 33) ^ k * (17 / 33))
        = (((k : ℝ) + 2) * (17 / 33)) * (17 / 33) ^ k := by ring
      _ ≤ ((k : ℝ) + 1) * (17 / 33) ^ k := mul_le_mul_of_nonneg_right h1 hp
      _ ≤ _ := ih

theorem numeric_B (k : ℕ) (hk : 13 ≤ k) :
    ((k : ℝ) + 1) * (k : ℝ) ^ 2 * (1 / 3) ^ k ≤ 14 * 13 ^ 2 * (1 / 3) ^ 13 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : (0 : ℝ) ≤ (1 / 3) ^ k := by positivity
    have hkr : (13 : ℝ) ≤ k := by exact_mod_cast hk
    have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [this, pow_succ]
    have h1 : ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1) ^ 2 * (1 / 3) ≤ ((k : ℝ) + 1) * (k : ℝ) ^ 2 := by
      nlinarith
    calc ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1) ^ 2 * ((1 / 3) ^ k * (1 / 3))
        = (((k : ℝ) + 1 + 1) * ((k : ℝ) + 1) ^ 2 * (1 / 3)) * (1 / 3) ^ k := by ring
      _ ≤ (((k : ℝ) + 1) * (k : ℝ) ^ 2) * (1 / 3) ^ k := mul_le_mul_of_nonneg_right h1 hp
      _ ≤ _ := ih

/-- `(k+1)(98k²·3^{-k} + 2(17/33)^k) ≤ 27/125` for `k ≥ 13`. -/
theorem numeric_final (k : ℕ) (hk : 13 ≤ k) :
    ((k : ℝ) + 1) * (98 * (k : ℝ) ^ 2 * (1 / 3) ^ k + 2 * (17 / 33) ^ k) ≤ 27 / 125 := by
  have hA := numeric_A k hk
  have hB := numeric_B k hk
  have e : ((k : ℝ) + 1) * (98 * (k : ℝ) ^ 2 * (1 / 3) ^ k + 2 * (17 / 33) ^ k)
      = 98 * (((k : ℝ) + 1) * (k : ℝ) ^ 2 * (1 / 3) ^ k) + 2 * (((k : ℝ) + 1) * (17 / 33) ^ k) := by
    ring
  rw [e]
  have hnum : 98 * (14 * 13 ^ 2 * (1 / 3 : ℝ) ^ 13) + 2 * (14 * (17 / 33 : ℝ) ^ 13) ≤ 27 / 125 := by
    norm_num
  linarith

/-! ### The lemma -/

/-- **Lemma `lem:select`.** -/
theorem lem_select {j : ℕ} [NeZero j] (P : Finset (ZMod j)) (k : ℕ)
    (hk : 13 ≤ k) (hkP : k ≤ P.card) (hj : j ≤ 196 * k ^ 2)
    (hP : ∀ ℓ : ZMod j, ℓ ≠ 0 → ‖∑ x ∈ P, chi (ℓ * x)‖ ≤ (P.card : ℝ) / 33) :
    ∃ S : Finset (ZMod j), S ⊆ P ∧ S.card = k ∧
      ∀ ℓ : ZMod j, ℓ ≠ 0 → ‖∑ x ∈ S, chi (ℓ * x)‖ ≤ (k : ℝ) - 3 / 8 := by
  by_contra hcon
  push_neg at hcon
  have hPne : P.Nonempty := by rw [← card_pos]; omega
  set N := P.card with hN
  set M : ZMod j → ℝ := fun ℓ =>
    if (2 : ZMod j) * ℓ ≠ 0 ∧ (3 : ZMod j) * ℓ ≠ 0 then 1 / 3 else 17 / 33 with hM
  set F : Finset (ZMod j) → ℝ := fun S =>
    ∑ ℓ ∈ half j, ∑ h ∈ range (k + 1), ∏ x ∈ S, wt k h ℓ x with hF
  have hnn : ∀ (S : Finset (ZMod j)) (ℓ : ZMod j) (h : ℕ), 0 ≤ ∏ x ∈ S, wt k h ℓ x :=
    fun S ℓ h => prod_nonneg fun x _ => wt_nonneg k h ℓ x
  -- every `k`-subset of `P` is bad, so `F S > 27/125`
  have hFS : ∀ S ∈ P.powersetCard k, (27 / 125 : ℝ) < F S := by
    intro S hS
    rw [mem_powersetCard] at hS
    obtain ⟨ℓ, hℓ0, hℓ⟩ := hcon S hS.1 hS.2
    obtain ⟨ℓ', hℓ'R, hℓ'⟩ : ∃ ℓ' ∈ half j, (k : ℝ) - 3 / 8 < ‖∑ x ∈ S, chi (ℓ' * x)‖ := by
      rcases mem_half_of_ne hℓ0 with h | h
      · exact ⟨ℓ, h, hℓ⟩
      · exact ⟨-ℓ, h, by rw [norm_sum_chi_neg]; exact hℓ⟩
    obtain ⟨h, hh, hprod⟩ := bad_prod S k hk hS.2 ℓ' hℓ'
    calc (27 / 125 : ℝ) < ∏ x ∈ S, wt k h ℓ' x := hprod
      _ ≤ ∑ h ∈ range (k + 1), ∏ x ∈ S, wt k h ℓ' x :=
          single_le_sum (f := fun h => ∏ x ∈ S, wt k h ℓ' x) (fun h _ => hnn S ℓ' h) hh
      _ ≤ F S :=
          single_le_sum (f := fun ℓ => ∑ h ∈ range (k + 1), ∏ x ∈ S, wt k h ℓ x)
            (fun ℓ _ => sum_nonneg fun h _ => hnn S ℓ h) hℓ'R
  have hlow : (N.choose k : ℝ) * (27 / 125) < ∑ S ∈ P.powersetCard k, F S := by
    have := sum_lt_sum_of_nonempty (powersetCard_nonempty.2 hkP) hFS
    rwa [sum_const, card_powersetCard, nsmul_eq_mul] at this
  have hswap : ∑ S ∈ P.powersetCard k, F S =
      ∑ ℓ ∈ half j, ∑ h ∈ range (k + 1), esum (wt k h ℓ) P k := by
    simp only [hF, esum]
    rw [sum_comm]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [sum_comm]
  have hup : ∀ ℓ ∈ half j, ∀ h, esum (wt k h ℓ) P k ≤ (N.choose k : ℝ) * M ℓ ^ k := by
    intro ℓ hℓ h
    have hℓ0 := ne_zero_of_mem_half hℓ
    apply maclaurin_le _ P hPne (fun x _ => wt_nonneg k h ℓ x) (M ℓ)
    simp only [hM]
    split_ifs with hc
    · exact sum_wt_good P k h ℓ (hP ℓ hℓ0) (hP _ hc.1) (hP _ hc.2)
    · exact sum_wt_any P k h ℓ (hP ℓ hℓ0)
  have hMpt : ∀ ℓ ∈ half j, M ℓ ^ k ≤ (1 / 3 : ℝ) ^ k +
      (if ¬ ((2 : ZMod j) * ℓ ≠ 0 ∧ (3 : ZMod j) * ℓ ≠ 0) then (17 / 33 : ℝ) ^ k else 0) := by
    intro ℓ _
    simp only [hM]
    split_ifs <;> linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) k]
  have hMsum : ∑ ℓ ∈ half j, M ℓ ^ k ≤ ((half j).card : ℝ) * (1 / 3) ^ k + 2 * (17 / 33) ^ k := by
    refine (sum_le_sum hMpt).trans ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter, sum_const, nsmul_eq_mul]
    have hE : (((half j).filter (fun ℓ => ¬ ((2 : ZMod j) * ℓ ≠ 0 ∧ (3 : ZMod j) * ℓ ≠ 0))).card : ℝ)
        ≤ 2 := by exact_mod_cast card_exceptional
    have hp : (0 : ℝ) ≤ (17 / 33) ^ k := by positivity
    nlinarith
  have hR : ((half j).card : ℝ) ≤ 98 * (k : ℝ) ^ 2 := by
    have h1 := card_half (j := j)
    have h2 : 2 * (half j).card ≤ 196 * k ^ 2 := le_trans h1 hj
    have h3 : (half j).card ≤ 98 * k ^ 2 := by omega
    exact_mod_cast h3
  have hC0 : (0 : ℝ) ≤ (N.choose k : ℝ) := by positivity
  have hupper : ∑ S ∈ P.powersetCard k, F S ≤ (N.choose k : ℝ) * (27 / 125) := by
    rw [hswap]
    calc ∑ ℓ ∈ half j, ∑ h ∈ range (k + 1), esum (wt k h ℓ) P k
        ≤ ∑ ℓ ∈ half j, ∑ h ∈ range (k + 1), (N.choose k : ℝ) * M ℓ ^ k :=
          sum_le_sum fun ℓ hℓ => sum_le_sum fun h _ => hup ℓ hℓ h
      _ = (N.choose k : ℝ) * (((k : ℝ) + 1) * ∑ ℓ ∈ half j, M ℓ ^ k) := by
          simp only [sum_const, card_range, nsmul_eq_mul, mul_sum]
          refine sum_congr rfl fun ℓ _ => ?_
          push_cast; ring
      _ ≤ (N.choose k : ℝ) * (((k : ℝ) + 1) *
            (98 * (k : ℝ) ^ 2 * (1 / 3) ^ k + 2 * (17 / 33) ^ k)) := by
          gcongr
          refine hMsum.trans ?_
          have hp : (0 : ℝ) ≤ (1 / 3) ^ k := by positivity
          nlinarith
      _ ≤ (N.choose k : ℝ) * (27 / 125) := by
          gcongr
          exact numeric_final k hk
  linarith

end SignCond
