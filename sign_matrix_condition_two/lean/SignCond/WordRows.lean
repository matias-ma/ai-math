import SignCond.FiniteWord
namespace SignCond.FiniteWord
open SignCond.FinitePacking SignCond.FiniteEnergy Finset
variable {j : ℕ} [NeZero j]

def bits (j B X : ℕ) [NeZero j] (i : ZMod j) : ℤ := digit B X i.val

theorem packed_bits {B X : ℕ} (hb : 0 < B) (hX : X < B^j) :
    packed B (bits j B X) = X := by
  rw [packed_sum,← pack_digits B hb X j hX,pack_sum]
  exact sum_zmod_val (fun i => (digit B X i : ℤ)*(B:ℤ)^i)

theorem sum_bits {B X c : ℕ} (hb : 1 < B) (hX : X < B^j)
    (hc : ∀ i < j, digit B X i ≤ c) (hw : j*c < B-1) :
    ∑ i, bits j B X i = (X%(B-1) : ℕ) := by
  have hh := sum_digits hb hX hc hw
  rw [show (∑ i, bits j B X i) = ∑ i ∈ range j, (digit B X i:ℤ) from sum_zmod_val (fun i => (digit B X i : ℤ))]
  exact_mod_cast hh

theorem packed_ones {B : ℕ} (hb : 1 < B) :
    packed B (fun _ : ZMod j => (1:ℤ)) = ones B j := by
  rw [packed_sum,ones_sum hb]
  simp only [one_mul,Nat.cast_sum,Nat.cast_pow]
  exact sum_zmod_val (fun i => (B:ℤ)^i)

structure BitWord (j w X : ℕ) : Prop where
  size : X < (2^w)^j
  sparse : X &&& ones (2^w) j = X

theorem bit_values {w X : ℕ} (hb : 1 < 2^w) (h : BitWord j w X) (i : ZMod j) :
    bits j (2^w) X i = 0 ∨ bits j (2^w) X i = 1 := by
  have ht := bounded_digits (c := 1) hb hb (by simpa using h.sparse) (ZMod.val_lt i)
  unfold bits; omega

private theorem pack_first {B : ℕ} (hb : 0 < B) (x : ZMod j → ℤ) :
    packed B x % B = (x 0) % B := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne j)
  unfold packed
  generalize h : (fun i : ℕ => x (i : ZMod j)) = v
  conv_lhs => rw [hn,pack,Int.add_mul_emod_self_left]
  have hh := congrFun h 0
  simpa [← hh]

theorem reverse_of_product {w X Y : ℕ} (B : ℕ) (hB : B = 2^w) (hb : 1 < B)
    (hj : j < B-1) (hx : BitWord j w X) (hy : BitWord j w Y)
    (hs : X%(B-1) = Y%(B-1))
    (hdot : ((X*Y)% (B^j-1)) % B = X%(B-1)) :
    ∀ i : ZMod j, bits j B Y (-i) = bits j B X i := by
  subst B
  let B := 2^w
  let x := bits j B X
  let y := bits j B Y
  have hx01 (i) : x i = 0 ∨ x i = 1 := bit_values hb hx i
  have hy01 (i) : y i = 0 ∨ y i = 1 := bit_values hb hy i
  have hsumX : ∑ i, x i = (X%(B-1):ℕ) :=
    sum_bits (c := 1) hb hx.size (fun i hi => bounded_digits hb hb (by simpa using hx.sparse) hi) (by simpa using hj)
  have hsumY : ∑ i, y i = (Y%(B-1):ℕ) :=
    sum_bits (c := 1) hb hy.size (fun i hi => bounded_digits hb hb (by simpa using hy.sparse) hi) (by simpa using hj)
  let z := conv x y
  have hprod (i t : ZMod j) : 0 ≤ x i * y (t-i) ∧ x i * y (t-i) ≤ 1 := by
    rcases hx01 i with h|h <;> rcases hy01 (t-i) with k|k <;> simp [h,k]
  have hz (t : ZMod j) : 0 ≤ z t ∧ z t ≤ j := by
    constructor
    · exact sum_nonneg (fun i _ => (hprod i t).1)
    · calc
        _ ≤ ∑ _i : ZMod j, (1:ℤ) := sum_le_sum fun i _ => (hprod i t).2
        _ = _ := by simp
  have hmod : (packed B z : ZMod (B^j-1)) = ((X*Y:ℕ) : ZMod (B^j-1)) := by
    rw [packed_conv _ hb,packed_bits (by omega) hx.size,packed_bits (by omega) hy.size]
    push_cast; rfl
  have hz0 : 0 ≤ packed B z := by rw [packed_sum]; exact sum_nonneg fun i _ => mul_nonneg (hz i).1 (by positivity)
  have hzlt : packed B z < (B^j-1:ℕ) := by
    have h := pack_abs_lt (B := (B:ℤ)) (by exact_mod_cast hb) (Nat.pos_of_ne_zero (NeZero.ne j))
      (v := fun k => z k) (fun i _ => by rw [abs_of_nonneg (hz _).1]; have := (hz (i:ZMod j)).2; omega)
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),Nat.cast_pow,Nat.cast_one]
    exact (le_abs_self _).trans_lt h
  have hzval : packed B z = (((X*Y)%(B^j-1):ℕ):ℤ) := by
    have hh : packed B z ≡ ((X*Y:ℕ):ℤ) [ZMOD ((B^j-1:ℕ):ℤ)] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
      simpa only [Int.cast_natCast] using hmod
    change packed B z % ((B^j-1:ℕ):ℤ) = _ at hh
    rw [Int.emod_eq_of_lt hz0 hzlt, ← Int.natCast_mod] at hh
    exact hh
  have hdot' : z 0 = (X%(B-1):ℕ) := by
    have h := pack_first (by omega : 0 < B) z
    rw [hzval,Int.emod_eq_of_lt (hz 0).1 (by have := (hz 0).2; omega)] at h
    rw [← Int.natCast_mod] at h
    exact h.symm.trans (congrArg (fun u : ℕ => (u:ℤ)) hdot)
  have hnorm : ∑ i, (x i - y (-i))^2 = 0 := by
    have hpt (i : ZMod j) : (x i - y (-i))^2 = x i + y (-i) - 2*(x i*y (-i)) := by
      rcases hx01 i with h|h <;> rcases hy01 (-i) with k|k <;> simp [h,k]
    have hyrev : (∑ i, y (-i)) = ∑ i, y i := Fintype.sum_equiv (Equiv.neg _) _ _ (by simp)
    have hxy : (∑ i, x i*y (-i)) = z 0 := by simp [z,conv]
    simp only [hpt,sum_sub_distrib,sum_add_distrib,← Finset.mul_sum,hyrev,hxy,hsumX,hsumY,hdot',hs]
    rw [show X%(B-1)=Y%(B-1) from hs]
    ring
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (x k - y (-k)))).mp hnorm i (mem_univ _)
  change y (-i) = x i
  nlinarith

end SignCond.FiniteWord
