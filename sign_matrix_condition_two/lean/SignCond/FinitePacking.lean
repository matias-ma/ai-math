import SignCond.Fourier
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Integer radix arithmetic for cyclic convolution certificates. -/
namespace SignCond.FinitePacking

/-- Little-endian polynomial evaluation at the integer base B. -/
def pack (B : ℤ) (v : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => v 0 + B * pack B (fun i => v (i+1)) n

theorem pack_zero_digits {B : ℤ} (hB : 1 < B) {n : ℕ} {v : ℕ → ℤ}
    (hv : ∀ i < n, |v i| < B) (h : pack B v n = 0) : ∀ i < n, v i = 0 := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pack] at h
    have hdiv : B ∣ v 0 := ⟨-pack B (fun i => v (i+1)) n, by linarith⟩
    have hz : v 0 = 0 := by
      have hw := hv 0 (by omega)
      rcases hdiv with ⟨k,hk⟩
      rw [hk,abs_mul, abs_of_pos (by omega : 0 < B)] at hw
      have : |k| < 1 := by
        by_contra! hge
        nlinarith [mul_nonneg (show 0 ≤ B by omega) (sub_nonneg.mpr hge)]
      have : k = 0 := abs_eq_zero.mp (by have := abs_nonneg k; omega)
      simp [hk,this]
    rw [hz, zero_add] at h
    have ht := (mul_eq_zero.mp h).resolve_left (by omega)
    intro i hi
    cases i with
    | zero => exact hz
    | succ i => exact ih (v := fun i => v (i+1)) (fun k hk => hv (k+1) (by omega)) ht i (by omega)

theorem pack_abs_lt {B : ℤ} (hB : 1 < B) {n : ℕ} (hn : 0 < n) {v : ℕ → ℤ}
    (hv : ∀ i < n, |v i| < B-1) : |pack B v n| < B^n-1 := by
  induction n generalizing v with
  | zero => omega
  | succ n ih =>
    rw [pack, pow_succ]
    have h0 := hv 0 (by omega)
    cases n with
    | zero => simpa [pack] using h0
    | succ n =>
      have ht := ih (by omega) (v := fun i => v (i+1)) (fun k hk => hv (k+1) (by omega))
      have H := abs_add_le (v 0) (B * pack B (fun i => v (i+1)) (n+1))
      rw [abs_mul,abs_of_pos (by omega : 0 < B)] at H
      nlinarith [mul_lt_mul_of_pos_left ht (show 0 < B by omega)]

/-- Zero modulo Bⁿ−1 detects a zero vector when the digits fit strictly inside the radix. -/
theorem digits_zero_of_modEq {B : ℤ} (hB : 1 < B) {n : ℕ} (hn : 0 < n) {v : ℕ → ℤ}
    (hv : ∀ i < n, |v i| < B-1) (h : pack B v n ≡ 0 [ZMOD B^n-1]) :
    ∀ i < n, v i = 0 := by
  have hlt := pack_abs_lt hB hn hv
  have hd := Int.modEq_zero_iff_dvd.mp h
  have hz : pack B v n = 0 := by
    by_contra H
    have := Int.le_of_dvd (abs_pos.mpr H) ((dvd_abs _ _).mpr hd)
    omega
  exact pack_zero_digits hB (fun i hi => (hv i hi).trans (by omega)) hz

end SignCond.FinitePacking

namespace SignCond.FinitePacking
open Finset

theorem pack_sum (B : ℤ) (v : ℕ → ℤ) (n : ℕ) :
    pack B v n = ∑ k ∈ range n, v k * B^k := by
  induction n generalizing v with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, ih, sum_range_succ', mul_sum]
    simp_rw [pow_succ]
    ring_nf

variable {j : ℕ} [NeZero j]
def packed (B : ℕ) (x : ZMod j → ℤ) : ℤ := pack B (fun i => x i) j

theorem packed_sum (B : ℕ) (x : ZMod j → ℤ) :
    packed B x = ∑ i, x i * (B:ℤ)^i.val := by
  rw [packed, pack_sum, ← sum_zmod_val]
  simp

omit [NeZero j] in
private theorem root (B : ℕ) (hB : 1 < B) : (B : ZMod (B^j-1))^j = 1 := by
  have hpow : 1 ≤ B^j := Nat.one_le_pow _ _ (by omega)
  rw [← Nat.cast_pow]
  have h := ZMod.natCast_self (B^j-1)
  rw [Nat.cast_sub hpow,Nat.cast_one,sub_eq_zero] at h
  exact h

private theorem pow_add_mod {R : Type*} [CommRing R] {z : R} (hz : z^j=1)
    (u w : ZMod j) : z ^ (u+w).val = z ^ u.val * z ^ w.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (u.val + w.val) j, pow_add, pow_mul, hz, one_pow, one_mul]

theorem packed_conv (B : ℕ) (hB : 1 < B) (x y : ZMod j → ℤ) :
    ((packed B (conv x y) : ℤ) : ZMod (B^j-1)) =
      ((packed B x : ℤ) : ZMod (B^j-1)) * ((packed B y : ℤ) : ZMod (B^j-1)) := by
  simp only [packed_sum,conv,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight u) _ _ fun t => ?_
  rw [Equiv.subRight_apply]
  conv_lhs => rw [show t = u + (t-u) by ring, pow_add_mod (root B hB), add_sub_cancel_left]
  ring

theorem packed_inj (B : ℕ) (hB : 1 < B) (v w : ZMod j → ℤ)
    (hd : ∀ i, |v i - w i| < (B:ℤ)-1)
    (h : ((packed B v : ℤ) : ZMod (B^j-1)) = (packed B w : ℤ)) : v = w := by
  have hp : packed B (fun i => v i - w i) = packed B v - packed B w := by
    simp [packed_sum, sub_mul, Finset.sum_sub_distrib]
  have hz : ((packed B (fun i => v i - w i) : ℤ) : ZMod (B^j-1)) = 0 := by
    rw [hp,Int.cast_sub,h,sub_self]
  have H := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),Nat.cast_pow,Nat.cast_one] at H
  have h0 := digits_zero_of_modEq (B := (B:ℤ)) (by exact_mod_cast hB)
    (Nat.pos_of_ne_zero (NeZero.ne j)) (v := fun k => v k - w k)
    (fun i _ => hd _) (Int.modEq_zero_iff_dvd.mpr H)
  funext i
  have hi := h0 i.val (ZMod.val_lt i)
  simpa using sub_eq_zero.mp hi

/-- Bound the coefficients after p cyclic squarings of a length-j integer vector. -/
def majorant (j : ℕ) (C : ℕ) : ℕ → ℕ
  | 0 => C
  | p+1 => j * (majorant j C p)^2

theorem squarings_abs_le (x : ZMod j → ℤ) (C : ℕ) (hx : ∀ i, |x i| ≤ (C:ℤ))
    (p : ℕ) (t : ZMod j) : |squarings x p t| ≤ majorant j C p := by
  induction p generalizing t with
  | zero => exact hx t
  | succ p ih =>
    rw [squarings, conv]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _i : ZMod j, (majorant j C p : ℤ)^2 := Finset.sum_le_sum fun i _ => by
        rw [abs_mul,pow_two]
        exact mul_le_mul (ih _) (ih _) (abs_nonneg _) (by positivity)
      _ = _ := by simp [majorant, nsmul_eq_mul]

theorem packed_squarings (B : ℕ) (hB : 1 < B) (x : ZMod j → ℤ) (p : ℕ) :
    ((packed B (squarings x p) : ℤ) : ZMod (B^j-1)) =
      ((packed B x : ℤ) : ZMod (B^j-1)) ^ (2^p) := by
  induction p with
  | zero => simp [squarings]
  | succ p ih => rw [squarings, packed_conv B hB, ih, pow_succ 2, pow_mul, pow_two]

/-- A single exact modular power identifies all coefficients of the cyclic power.
The two magnitude bounds guarantee uniqueness of the signed radix digits. -/
theorem squarings_eq_of_packed (B C D p : ℕ) (hB : 1 < B) (x y : ZMod j → ℤ)
    (hx : ∀ i, |x i| ≤ (C:ℤ)) (hy : ∀ i, |y i| ≤ (D:ℤ))
    (hwidth : majorant j C p + D + 1 < B)
    (hcode : ((packed B x : ℤ) : ZMod (B^j-1)) ^ (2^p) = (packed B y : ℤ)) :
    squarings x p = y := by
  apply packed_inj B hB
  · intro i
    have hs := squarings_abs_le x C hx p i
    have h := abs_sub (squarings x p i) (y i)
    have hw : (majorant j C p : ℤ) + D + 1 < B := by exact_mod_cast hwidth
    linarith [hy i]
  · rw [packed_squarings B hB, hcode]

end SignCond.FinitePacking
