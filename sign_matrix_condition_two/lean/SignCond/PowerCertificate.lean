import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The convolution-power certificate

Paper: *Let `q ∈ ℤ^j` be indexed by `ℤ/jℤ`, and let `q^{*k}` denote its `k`-fold cyclic
convolution. Then for every `ℓ` and every `k ≥ 1`,
`|q̂(ℓ)| ≤ (∑_t |(q^{*k})_t|)^{1/k}`, where `q̂(ℓ) = ∑_v q_v ω^{ℓ v}`, `ω = e^{2πi/j}`.*

We do not fix `ω`: everything holds for any `z : ℂ` with `z ^ j = 1` (for the paper,
`z = ω ^ ℓ`; see `exp_pow_eq_one` and `fourier_le_of_certificate`).

* `ev q z = ∑ v, q v * z ^ v.val` (`v.val ∈ {0, …, j - 1}` is the representative of `v`).
* `conv p q t = ∑ u, p u * q (t - u)`, cyclic convolution on `ℤ/jℤ`.
* `convPow q k`: `convPow q 0 = delta` (the unit, `delta t = if t = 0 then 1 else 0`) and
  `convPow q (k + 1) = conv (convPow q k) q`; so `convPow q 1 = q` (`convPow_one`).

Main results: `ev_conv`, `ev_convPow`, `norm_ev_le`, `norm_ev_pow_le` (the lemma),
`norm_ev_le_of_certificate` (the form the verifier uses), `convPow_two_mul` and
`convPow_two_pow_succ` (the squaring step), `squarings_eq_convPow`,
`norm_ev_le_of_squarings` (the verifier's loop), `fourier_le_of_certificate` (`ω = e^{2πi/j}`).
-/

open Complex
open scoped Real

namespace SignCond

variable {j : ℕ} [NeZero j]

/-- Evaluation of `q : ℤ/jℤ → ℤ` at `z`: `ev q z = ∑ v, q v * z ^ v.val`. For `z = ω ^ ℓ`
with `ω = e^{2πi/j}` this is the discrete Fourier coefficient `q̂(ℓ)`. -/
noncomputable def ev (q : ZMod j → ℤ) (z : ℂ) : ℂ := ∑ v : ZMod j, (q v : ℂ) * z ^ v.val

/-- Cyclic convolution on `ℤ/jℤ`: `conv p q t = ∑ u, p u * q (t - u)`. -/
def conv (p q : ZMod j → ℤ) (t : ZMod j) : ℤ := ∑ u : ZMod j, p u * q (t - u)

/-- The unit for `conv`: `delta t = 1` if `t = 0` and `0` otherwise. -/
def delta (t : ZMod j) : ℤ := if t = 0 then 1 else 0

/-- Convolution powers: `convPow q 0 = delta`, `convPow q (k + 1) = conv (convPow q k) q`. -/
def convPow (q : ZMod j → ℤ) : ℕ → ZMod j → ℤ
  | 0 => delta
  | k + 1 => conv (convPow q k) q

theorem convPow_zero (q : ZMod j → ℤ) : convPow q 0 = delta := rfl

theorem convPow_succ (q : ZMod j → ℤ) (k : ℕ) :
    convPow q (k + 1) = conv (convPow q k) q := rfl

/-! ### Algebra of `conv` -/

theorem delta_conv (q : ZMod j → ℤ) : conv delta q = q := by
  funext t
  simp [conv, delta]

theorem conv_delta (q : ZMod j → ℤ) : conv q delta = q := by
  funext t
  simp [conv, delta, sub_eq_zero]

theorem convPow_one (q : ZMod j → ℤ) : convPow q 1 = q := by
  rw [convPow_succ, convPow_zero, delta_conv]

theorem conv_assoc (p q r : ZMod j → ℤ) : conv (conv p q) r = conv p (conv q r) := by
  funext t
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight v) _ _ fun u => ?_
  rw [Equiv.subRight_apply, show t - v - (u - v) = t - u by ring, mul_assoc]

theorem conv_comm (p q : ZMod j → ℤ) : conv p q = conv q p := by
  funext t
  refine Fintype.sum_equiv (Equiv.subLeft t) _ _ fun u => ?_
  rw [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]

theorem convPow_add (q : ZMod j → ℤ) (m k : ℕ) :
    convPow q (m + k) = conv (convPow q m) (convPow q k) := by
  induction k with
  | zero => rw [Nat.add_zero, convPow_zero, conv_delta]
  | succ k ih => rw [← Nat.add_assoc, convPow_succ, ih, conv_assoc, convPow_succ]

/-- **Squaring step.** `q^{*2k} = q^{*k} * q^{*k}`. -/
theorem convPow_two_mul (q : ZMod j → ℤ) (k : ℕ) :
    convPow q (2 * k) = conv (convPow q k) (convPow q k) := by
  rw [two_mul, convPow_add]

/-- **Squaring step, iterated form.** `q^{*2^(p+1)} = q^{*2^p} * q^{*2^p}`. -/
theorem convPow_two_pow_succ (q : ZMod j → ℤ) (p : ℕ) :
    convPow q (2 ^ (p + 1)) = conv (convPow q (2 ^ p)) (convPow q (2 ^ p)) := by
  rw [pow_succ, mul_comm, convPow_two_mul]

/-- `p` exact squarings starting from `q`, as the verifier computes them. -/
def squarings (q : ZMod j → ℤ) : ℕ → ZMod j → ℤ
  | 0 => q
  | p + 1 => conv (squarings q p) (squarings q p)

/-- `p` squarings compute the `2 ^ p`-fold convolution power. -/
theorem squarings_eq_convPow (q : ZMod j → ℤ) (p : ℕ) : squarings q p = convPow q (2 ^ p) := by
  induction p with
  | zero => rw [squarings, pow_zero, convPow_one]
  | succ p ih => rw [squarings, ih, convPow_two_pow_succ]

/-! ### Evaluation at a `j`-th root of unity -/

/-- If `z ^ j = 1`, then `z ^ (u + w).val = z ^ u.val * z ^ w.val` for `u, w : ℤ/jℤ`. -/
theorem pow_val_add {z : ℂ} (hz : z ^ j = 1) (u w : ZMod j) :
    z ^ (u + w).val = z ^ u.val * z ^ w.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (u.val + w.val) j, pow_add, pow_mul, hz, one_pow, one_mul]

/-- **Convolution becomes multiplication.** `ev (p * q) z = ev p z * ev q z` when `z ^ j = 1`. -/
theorem ev_conv (p q : ZMod j → ℤ) {z : ℂ} (hz : z ^ j = 1) :
    ev (conv p q) z = ev p z * ev q z := by
  simp only [ev, conv, Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight u) _ _ fun t => ?_
  rw [Equiv.subRight_apply]
  conv_lhs => rw [show t = u + (t - u) by ring, pow_val_add hz, add_sub_cancel_left]
  ring

theorem ev_delta (z : ℂ) : ev (delta : ZMod j → ℤ) z = 1 := by
  simp [ev, delta]

/-- `ev (q^{*k}) z = (ev q z) ^ k` when `z ^ j = 1`. -/
theorem ev_convPow (q : ZMod j → ℤ) {z : ℂ} (hz : z ^ j = 1) (k : ℕ) :
    ev (convPow q k) z = ev q z ^ k := by
  induction k with
  | zero => rw [convPow_zero, ev_delta, pow_zero]
  | succ k ih => rw [convPow_succ, ev_conv _ _ hz, ih, pow_succ]

/-- `‖ev q z‖ ≤ ∑ t, |q t|` when `z ^ j = 1` (then `‖z‖ = 1`). -/
theorem norm_ev_le (q : ZMod j → ℤ) {z : ℂ} (hz : z ^ j = 1) :
    ‖ev q z‖ ≤ ∑ t, |(q t : ℝ)| := by
  have hz1 : ‖z‖ = 1 := norm_eq_one_of_pow_eq_one hz (NeZero.ne j)
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_))
  rw [norm_mul, norm_pow, hz1, one_pow, mul_one, norm_intCast]

/-- **The lemma (power form).** For every `k` (including `k = 0`, where both sides are `1`),
`‖ev q z‖ ^ k ≤ ∑ t, |q^{*k}_t|` when `z ^ j = 1`. -/
theorem norm_ev_pow_le (q : ZMod j → ℤ) {z : ℂ} (hz : z ^ j = 1) (k : ℕ) :
    ‖ev q z‖ ^ k ≤ ∑ t, |(convPow q k t : ℝ)| := by
  rw [← norm_pow, ← ev_convPow q hz]
  exact norm_ev_le _ hz

/-- **The certificate.** If `∑ t, |q^{*k}_t| ≤ R ^ k` with `k ≥ 1` and `R ≥ 0`,
then `‖ev q z‖ ≤ R` for every `z` with `z ^ j = 1`. -/
theorem norm_ev_le_of_certificate (q : ZMod j → ℤ) {z : ℂ} (hz : z ^ j = 1) {k : ℕ}
    (hk : 1 ≤ k) {R : ℝ} (hR0 : 0 ≤ R) (hcert : ∑ t, |(convPow q k t : ℝ)| ≤ R ^ k) :
    ‖ev q z‖ ≤ R :=
  le_of_pow_le_pow_left₀ (by omega) hR0 ((norm_ev_pow_le q hz k).trans hcert)

/-- **The certificate, integer form** (exactly what the verifier checks): if the integer
inequality `∑ t, |q^{*k}_t| ≤ R ^ k` holds with `k ≥ 1` and `R ≥ 0`, then
`‖ev q z‖ ≤ R` for every `z` with `z ^ j = 1`. -/
theorem norm_ev_le_of_certificate_int (q : ZMod j → ℤ) {z : ℂ} (hz : z ^ j = 1) {k : ℕ}
    (hk : 1 ≤ k) {R : ℤ} (hR0 : 0 ≤ R) (hcert : ∑ t, |convPow q k t| ≤ R ^ k) :
    ‖ev q z‖ ≤ R := by
  refine norm_ev_le_of_certificate q hz hk (Int.cast_nonneg.2 hR0) ?_
  exact_mod_cast hcert

/-- **The certificate after `p` squarings** (the verifier's loop: `p` times
`q ← q * q`, `R ← R * R`, then check `∑ t, |q t| ≤ R`): if
`∑ t, |squarings q p t| ≤ R ^ (2 ^ p)` with `R ≥ 0`, then `‖ev q z‖ ≤ R` whenever `z ^ j = 1`. -/
theorem norm_ev_le_of_squarings (q : ZMod j → ℤ) {z : ℂ} (hz : z ^ j = 1) (p : ℕ) {R : ℤ}
    (hR0 : 0 ≤ R) (hcert : ∑ t, |squarings q p t| ≤ R ^ (2 ^ p)) :
    ‖ev q z‖ ≤ R := by
  rw [squarings_eq_convPow] at hcert
  exact norm_ev_le_of_certificate_int q hz (Nat.one_le_two_pow) hR0 hcert

/-! ### The paper's normalisation `ω = e^{2πi/j}` -/

/-- `ω ^ ℓ` is a `j`-th root of unity for `ω = e^{2πi/j}`. -/
theorem exp_pow_eq_one (ℓ : ℕ) : (exp (2 * π * I / j) ^ ℓ) ^ j = 1 := by
  have hj : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne j)
  have h : exp (2 * π * I / j) ^ j = 1 := by
    rw [← exp_nat_mul, show (j : ℂ) * (2 * π * I / j) = 2 * π * I by field_simp,
      exp_two_pi_mul_I]
  rw [← pow_mul, mul_comm ℓ j, pow_mul, h, one_pow]

/-- **The paper's statement.** With `ω = e^{2πi/j}` and
`q̂(ℓ) = ev q (ω ^ ℓ) = ∑ v, q v ω^{ℓ v}`: if `∑ t, |q^{*k}_t| ≤ R ^ k` (integers, `k ≥ 1`,
`R ≥ 0`), then `|q̂(ℓ)| ≤ R`. -/
theorem fourier_le_of_certificate (q : ZMod j → ℤ) (ℓ : ℕ) {k : ℕ} (hk : 1 ≤ k) {R : ℤ}
    (hR0 : 0 ≤ R) (hcert : ∑ t, |convPow q k t| ≤ R ^ k) :
    ‖ev q (exp (2 * π * I / j) ^ ℓ)‖ ≤ R :=
  norm_ev_le_of_certificate_int q (exp_pow_eq_one ℓ) hk hR0 hcert

end SignCond
