import SignCond.WordRows

namespace SignCond.FiniteWord
open FiniteEnergy FinitePacking Finset
variable {j : ℕ} [NeZero j]

structure Row where
  x : ℕ
  y : ℕ

def Row.seq (r : Row) (j B : ℕ) [NeZero j] (i : ZMod j) : ℤ := 1 - 2*bits j B r.x i

structure Row.Check (r : Row) (j w : ℕ) (sum : ℤ) : Prop where
  xword : BitWord j w r.x
  yword : BitWord j w r.y
  sameCount : r.x%(2^w-1) = r.y%(2^w-1)
  dot : ((r.x*r.y)%((2^w)^j-1))%(2^w) = r.x%(2^w-1)
  total : (j:ℤ) - 2*((r.x%(2^w-1):ℕ):ℤ) = sum

def Row.code (r : Row) (B j : ℕ) : ℤ :=
  ((ones B j : ℤ)-2*r.x)*((ones B j : ℤ)-2*r.y)

theorem Row.spec (r : Row) {w : ℕ} {s : ℤ} (hb : 1 < 2^w) (hj : j < 2^w-1)
    (h : r.Check j w s) :
    IsSignVec (realRow (r.seq j (2^w))) ∧ (∑ i, r.seq j (2^w) i = s) ∧
    packedCorr (2^w) (r.seq j (2^w)) = r.code (2^w) j := by
  let B := 2^w
  have hval := bit_values hb h.xword
  have hrev := reverse_of_product B rfl hb hj h.xword h.yword h.sameCount h.dot
  have hsum := sum_bits (c := 1) hb h.xword.size
    (fun i hi => bounded_digits hb hb (by simpa using h.xword.sparse) hi) (by simpa using hj)
  have hc (f : ZMod j → ℤ) : packed B (fun i => 1-2*f i) = (ones B j : ℤ)-2*packed B f := by
    rw [← packed_ones hb]
    simp [B,packed_sum,sub_mul,mul_assoc,Finset.sum_sub_distrib,Finset.mul_sum]
  constructor
  · intro i
    rcases hval i with h0|h0 <;> simp [realRow,Row.seq,h0]
  constructor
  · simpa only [Row.seq,sum_sub_distrib,← Finset.mul_sum,hsum,sum_const,card_univ,ZMod.card,nsmul_eq_mul,
      mul_one] using h.total
  · have he : (fun i => r.seq j B (-i)) = fun i => 1-2*bits j B r.y i := by
      funext i
      simpa [Row.seq] using congrArg (fun k : ℤ => 1-2*k) (hrev (-i)).symm
    change packed B (r.seq j B) * packed B (fun i => r.seq j B (-i)) = r.code B j
    rw [he]
    change packed B (fun i => 1-2*bits j B r.x i) * packed B (fun i => 1-2*bits j B r.y i) = _
    rw [hc,hc,packed_bits (by omega : 0 < B) h.xword.size,packed_bits (by omega : 0 < B) h.yword.size]
    rfl

/-- The two nonnegative output words jointly bound the absolute coefficient sum. -/
theorem word_norm {w P N cap : ℕ} (hb : 1 < 2^w) (hc : cap < 2^w) (hw : j*cap < 2^w-1)
    (hp : P < (2^w)^j) (hn : N < (2^w)^j)
    (hpMask : P &&& (cap*ones (2^w) j) = P) (hnMask : N &&& (cap*ones (2^w) j) = N) :
    (∀ i, |bits j (2^w) P i - bits j (2^w) N i| ≤ (cap:ℤ)) ∧
    (∑ i, |bits j (2^w) P i - bits j (2^w) N i| ≤ ((P%(2^w-1) + N%(2^w-1):ℕ):ℤ)) := by
  have h1 := fun i hi => bounded_digits hb hc hpMask (i := i) hi
  have h2 := fun i hi => bounded_digits hb hc hnMask (i := i) hi
  have hp0 (X : ℕ) (i : ZMod j) : 0 ≤ bits j (2^w) X i := Int.natCast_nonneg _
  constructor
  · intro i
    have hp' := h1 i.val (ZMod.val_lt i)
    have hn' := h2 i.val (ZMod.val_lt i)
    unfold bits
    rw [abs_le]; omega
  · calc
      _ ≤ ∑ i, (bits j (2^w) P i + bits j (2^w) N i) := sum_le_sum fun i _ => by
        simpa [abs_of_nonneg (hp0 _ _)] using abs_sub (bits j (2^w) P i) (bits j (2^w) N i)
      _ = _ := by rw [sum_add_distrib,sum_bits hb hp h1 hw,sum_bits hb hn h2 hw,Nat.cast_add]

end SignCond.FiniteWord
