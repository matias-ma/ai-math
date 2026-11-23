import SignCond.Defs

/-!
# Lemma `lem:power` with the paper's `q̂(ℓ)` and the `k`-th root

`PowerCertificate.lean` proves `|q̂(ℓ)|^k ≤ Σ_t |(q^{*k})_t|` (`norm_ev_pow_le`); here we take the
`k`-th root, as in the paper.
-/

open Complex
open scoped Real

namespace SignCond

theorem hat_int_eq_ev {j : ℕ} [NeZero j] (q : ZMod j → ℤ) (ℓ : ℕ) :
    hat (fun v => (q v : ℝ)) ℓ = ev q (omega j ^ ℓ) := by
  unfold hat ev
  refine Finset.sum_congr rfl fun v _ => ?_
  push_cast
  rw [pow_mul]

theorem power_bound {j : ℕ} [NeZero j] (q : ZMod j → ℤ) (ℓ k : ℕ) (hk : 1 ≤ k) :
    ‖hat (fun v => (q v : ℝ)) ℓ‖ ≤ (∑ t, |(convPow q k t : ℝ)|) ^ ((1 : ℝ) / k) := by
  rw [hat_int_eq_ev]
  have hz : (omega j ^ ℓ) ^ j = 1 := exp_pow_eq_one ℓ
  have h := norm_ev_pow_le q hz k
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  calc ‖ev q (omega j ^ ℓ)‖ = (‖ev q (omega j ^ ℓ)‖ ^ k) ^ ((1 : ℝ) / k) := by
        rw [one_div, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hk0,
          Real.rpow_one]
    _ ≤ (∑ t, |(convPow q k t : ℝ)|) ^ ((1 : ℝ) / k) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)

end SignCond
