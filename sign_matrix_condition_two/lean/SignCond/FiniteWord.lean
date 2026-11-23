import SignCond.PackedEnergy

namespace SignCond.FiniteWord
open SignCond.FinitePacking Finset

/-- A length-n word of radix-B digits all equal to one. -/
def ones (B n : ℕ) := (B^n-1)/(B-1)

theorem ones_sum {B : ℕ} (hb : 1 < B) (n : ℕ) : ones B n = ∑ i ∈ range n, B^i := by
  unfold ones
  have h := geom_sum_mul_of_one_le (show 1 ≤ B by omega) n
  rw [← h, Nat.mul_div_cancel _ (by omega)]

private theorem ones_succ {B : ℕ} (hb : 1 < B) (n : ℕ) :
    ones B (n+1) = 1 + B*ones B n := by
  simp [ones_sum hb, sum_range_succ', pow_succ, Finset.mul_sum, mul_comm,add_comm]

private theorem digit_div (B E k i : ℕ) : digit B (E/B^k) i = digit B E (k+i) := by
  simp [digit,pow_add,Nat.div_div_eq_div_mul]

theorem digit_const {B c : ℕ} (hb : 1 < B) (hc : c < B) {n i : ℕ} (hi : i < n) :
    digit B (c*ones B n) i = c := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      rw [show c*ones B (n+1) = c+B*(c*ones B n) by rw [ones_succ hb]; ring]
      simp [digit,Nat.mod_eq_of_lt hc]
    | succ i =>
      rw [show c*ones B (n+1) = c + B*(c*ones B n) by rw [ones_succ hb]; ring,
        show i+1=1+i by omega, ← digit_div, pow_one]
      simp [Nat.add_mul_div_left _ _ (by omega : 0 < B),Nat.div_eq_of_lt hc,ih (by omega : i<n)]

private theorem digit_and (w X Y i : ℕ) :
    digit (2^w) (X &&& Y) i = digit (2^w) X i &&& digit (2^w) Y i := by
  simp only [digit, ← pow_mul, ← Nat.shiftRight_eq_div_pow,Nat.shiftRight_and_distrib,Nat.and_mod_two_pow]

theorem bounded_digits {w c n X : ℕ} (hb : 1 < 2^w) (hc : c < 2^w)
    (h : X &&& (c*ones (2^w) n) = X) {i : ℕ} (hi : i < n) :
    digit (2^w) X i ≤ c := by
  have eq := congrArg (fun x => digit (2^w) x i) h
  change digit (2^w) (X &&& _) i = _ at eq
  rw [digit_and,digit_const hb hc hi] at eq
  exact eq.symm.trans_le (Nat.and_le_right (n := digit (2^w) X i))

private theorem pack_mod (B n : ℕ) (f : ℕ → ℤ) :
    pack B f n ≡ (∑ i ∈ range n, f i) [ZMOD (B:ℤ)-1] := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, sum_range_succ']
    have hB : (B:ℤ) ≡ 1 [ZMOD (B:ℤ)-1] := by
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-1,by ring⟩
    simpa [add_comm] using (Int.ModEq.refl (f 0)).add (hB.mul (ih (fun i => f (i+1))))

theorem sum_digits {B n X c : ℕ} (hB : 1 < B) (hX : X<B^n)
    (hc : ∀ i<n, digit B X i ≤ c) (hw : n*c < B-1) :
    ∑ i ∈ range n, digit B X i = X%(B-1) := by
  have h := pack_mod B n (fun i => (digit B X i : ℤ))
  rw [pack_digits B (by omega) X n hX] at h
  have hb : ∑ i ∈ range n, digit B X i < B-1 := by
    refine lt_of_le_of_lt ?_ hw
    simpa using sum_le_sum (s := range n) (g := fun _ => c) (fun i hi => hc i (mem_range.mp hi))
  have H : X ≡ (∑ i ∈ range n, digit B X i) [MOD B-1] := by
    apply (Int.natCast_modEq_iff).mp
    simpa [Nat.cast_sub (by omega : 1≤B)] using h
  change X % (B-1) = _ at H
  simpa [Nat.mod_eq_of_lt hb] using H.symm

end SignCond.FiniteWord
