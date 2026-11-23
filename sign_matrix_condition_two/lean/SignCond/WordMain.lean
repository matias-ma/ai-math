import SignCond.WordCertificate
namespace SignCond.FiniteWord
open FiniteEnergy FinitePacking Finset
private theorem centerBoundRows {j : ℕ} [NeZero j] (a b c d : ZMod j → ℤ) (s μ : ℕ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (hc : ∀ i, |c i| ≤ 1) (hd : ∀ i, |d i| ≤ 1)
    (i : ZMod j) :
    |centered a b c d s μ i| ≤ coeffBound j s μ := by
  have hab (x y z w : ℤ) : |x+y+z+w| ≤ |x|+|y|+|z|+|w| := by
    linarith [abs_add_le x y, abs_add_le (x+y) z, abs_add_le (x+y+z) w]
  have h4 : |corr a i + corr b i + corr c i +
      corr d i| ≤ 4*(j:ℤ) := by
    linarith [hab (corr a i) (corr b i) (corr c i)
      (corr d i), corr_bound a ha i, corr_bound b hb i, corr_bound c hc i, corr_bound d hd i]
  unfold centered coeffBound
  push_cast
  refine (abs_sub _ _).trans ?_
  apply (add_le_add_right (abs_add_le _ _) _).trans
  simp only [abs_mul,abs_of_nonneg (Int.natCast_nonneg j),abs_of_pos (by decide : (0:ℤ)<256),
    Int.natCast_natAbs]
  have hh : |delta i| ≤ 1 := by unfold delta; split <;> norm_num
  nlinarith [mul_le_mul_of_nonneg_left h4 (show 0 ≤ (j:ℤ)*256 by positivity),
    mul_le_mul_of_nonneg_left hh (show 0 ≤ (j:ℤ)*|(5*(j:ℤ)+4)*256-2*μ| by positivity)]

def quadCode (A B C D : Row) (j base s μ : ℕ) : ℤ :=
  let c : ℤ := (5*(j:ℤ)+4)*256-2*μ
  j*256*(A.code base j+B.code base j+C.code base j+D.code base j) +
    (c-4*256*(s:ℤ)^2)*(ones base j)-j*c

theorem wordWitness {j : ℕ} [NeZero j] (A B C D : Row) (s μ p w P N cap : ℕ)
    (hb : 1 < 2^w) (hj : j < 2^w-1)
    (ha : A.Check j w (-(s:ℤ))) (hb' : B.Check j w s) (hc : C.Check j w s) (hd : D.Check j w s)
    (hs : 1≤s) (hs1 : (2*(s:ℤ)-2)^2 ≤ 2*j) (hs2 : 2*(j:ℤ) ≤ (2*s+2)^2)
    (hm : (2*j)*256^2 ≤ μ^2) (hr : 0 ≤ 3*(j:ℤ)*256-6*μ-8)
    (hw : majorant j (coeffBound j s μ) p + cap + 1 < 2^w)
    (hcap : j*cap < 2^w-1) (hP : P < (2^w)^j) (hN : N < (2^w)^j)
    (hpm : P &&& (cap*ones (2^w) j) = P) (hnm : N &&& (cap*ones (2^w) j) = N)
    (hPow : ((quadCode A B C D j (2^w) s μ : ℤ) : ZMod ((2^w)^j-1))^(2^p) =
            (P : ZMod ((2^w)^j-1)) - N)
    (hNorm : ((P%(2^w-1) + N%(2^w-1):ℕ):ℤ) ≤ ((j:ℤ)*(3*j*256-6*μ-8))^(2^p)) :
    SequenceWitness j := by
  let base := 2^w
  obtain ⟨hA,sA,cA⟩ := A.spec hb hj ha
  obtain ⟨hB,sB,cB⟩ := B.spec hb hj hb'
  obtain ⟨hC,sC,cC⟩ := C.spec hb hj hc
  obtain ⟨hD,sD,cD⟩ := D.spec hb hj hd
  have hsum (r : Row) : vsum (realRow (r.seq j base)) = ((∑ i, r.seq j base i : ℤ):ℝ) := by
    simp [vsum,realRow]
  refine ⟨_,_,_,_,s,hA,hB,hC,hD,?_,?_,?_,?_,hs,?_,?_,?_⟩
  · rw [hsum,sA]; push_cast; rfl
  · rw [hsum,sB]; norm_cast
  · rw [hsum,sC]; norm_cast
  · rw [hsum,sD]; norm_cast
  · exact_mod_cast hs1
  · exact_mod_cast hs2
  intro ℓ hℓ hlt
  apply bounds _ _ _ _ s μ p _ hr _ hℓ hlt
  · push_cast
    rw [← le_div_iff₀' (by norm_num : (0:ℝ)<256), Real.sqrt_le_iff]
    constructor
    · positivity
    · have h : (2*(j:ℝ))*256^2 ≤ (μ:ℝ)^2 := by exact_mod_cast hm
      nlinarith
  · let out := fun i => bits j base P i - bits j base N i
    have hout := word_norm hb (by omega : cap<2^w) hcap hP hN hpm hnm
    suffices squarings (centered (A.seq j base) (B.seq j base) (C.seq j base) (D.seq j base) s μ) p = out by
      rw [this]; exact hout.2.trans hNorm
    refine squarings_eq_of_packed base (coeffBound j s μ) cap p hb _ out ?_ hout.1 hw ?_
    · intro i
      apply centerBoundRows
      · intro k
        rcases bit_values hb ha.xword k with h|h <;> unfold Row.seq <;> rw [h] <;> decide
      · intro k
        rcases bit_values hb hb'.xword k with h|h <;> unfold Row.seq <;> rw [h] <;> decide
      · intro k
        rcases bit_values hb hc.xword k with h|h <;> unfold Row.seq <;> rw [h] <;> decide
      · intro k
        rcases bit_values hb hd.xword k with h|h <;> unfold Row.seq <;> rw [h] <;> decide
    · have ho : packed base out = (P:ℤ)-N := by
        unfold out; simp only [packed_sum,sub_mul,sum_sub_distrib]
        rw [← packed_sum, ← packed_sum, packed_bits (by omega : 0<base) hP, packed_bits (by omega : 0<base) hN]
      rw [ho]
      dsimp only [base]
      rw [centerCode_eq _ hb]
      simpa only [centerCode,cA,cB,cC,cD,packed_ones hb,quadCode,Int.cast_sub,Int.cast_natCast] using hPow

end SignCond.FiniteWord
