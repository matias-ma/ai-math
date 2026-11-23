import SignCond.Fourier
import SignCond.Power

namespace SignCond
namespace FiniteEnergy

variable {j : ℕ} [NeZero j]

def corr (x : ZMod j → ℤ) (t : ZMod j) : ℤ :=
  ∑ u, x (u + t) * x u

def realRow (x : ZMod j → ℤ) (u : ZMod j) : ℝ := x u

private theorem transform_corr (x : ZMod j → ℤ) (ℓ : ℕ) :
    ev (corr x) (omega j ^ ℓ) = ((‖hat (realRow x) ℓ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← hat_int_eq_ev, hat_eq_dft, hat_eq_dft, ofReal_normSq_eq, ← dft_cx_neg,
    ← dft_conv3]
  congr 1
  funext t
  simp [cx, corr, realRow]

def centered (a b c d : ZMod j → ℤ) (s μ : ℤ) (t : ZMod j) : ℤ :=
  let C := (5 * (j : ℤ) + 4) * 256 - 2 * μ
  j * 256 * (corr a t + corr b t + corr c t + corr d t) +
    (C - 4 * 256 * s ^ 2) - j * C * delta t

private theorem transform_centered (a b c d : ZMod j → ℤ) (s μ : ℤ)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hlt : ℓ < j) :
    ev (centered a b c d s μ) (omega j ^ ℓ) =
      ((j * (256 * energy (realRow a) (realRow b) (realRow c) (realRow d) ℓ -
        ((5 * (j : ℝ) + 4) * 256 - 2 * μ)) : ℝ) : ℂ) := by
  have hne : (ℓ : ZMod j) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hv
    omega
  have hsum : ∑ t : ZMod j, (omega j ^ ℓ) ^ t.val = 0 := by
    simpa [chi_mul_val, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, hne] using
      sum_chi_mul (ℓ : ZMod j)
  have hd := ev_delta (j := j) (omega j ^ ℓ)
  have ha := transform_corr a ℓ
  have hb := transform_corr b ℓ
  have hc := transform_corr c ℓ
  have he := transform_corr d ℓ
  unfold ev at hd ha hb hc he ⊢
  simp only [centered, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_pow, add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, hd, mul_one]
  push_cast [energy]
  push_cast at ha hb hc he
  linear_combination (j : ℂ) * 256 * ha + j * 256 * hb + j * 256 * hc + j * 256 * he

/-- A cyclic-squaring certificate implies the two spectral inequalities in PropFiniteTau. -/
theorem bounds (a b c d : ZMod j → ℤ) (s μ : ℤ) (p : ℕ)
    (hμ : 256 * Real.sqrt (2 * j) ≤ μ)
    (hr : 0 ≤ 3 * (j : ℤ) * 256 - 6 * μ - 8)
    (hcert : ∑ t, |squarings (centered a b c d s μ) p t| ≤
      ((j : ℤ) * (3 * j * 256 - 6 * μ - 8)) ^ (2 ^ p))
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hlt : ℓ < j) :
    (Real.sqrt (2 * j) + 2)^2 ≤ energy (realRow a) (realRow b) (realRow c) (realRow d) ℓ ∧
    energy (realRow a) (realRow b) (realRow c) (realRow d) ℓ < (2 * Real.sqrt (2 * j) - 2)^2 := by
  have h := norm_ev_le_of_squarings _ (exp_pow_eq_one ℓ) p
    (mul_nonneg (Int.natCast_nonneg j) hr) hcert
  rw [← omega, transform_centered _ _ _ _ _ _ hℓ hlt, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (Nat.cast_nonneg j)] at h
  push_cast at h
  have hj : 0 < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne j)
  have habs := abs_le.mp ((mul_le_mul_left hj).mp h)
  have hs := Real.sq_sqrt (show 0 ≤ (2 * j : ℝ) by positivity)
  constructor <;> nlinarith [habs.1, habs.2]

end FiniteEnergy
end SignCond
