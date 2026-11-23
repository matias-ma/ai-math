import SignCond.FinitePacking
import SignCond.FiniteSequence

namespace SignCond.FiniteEnergy
open FinitePacking
variable {j : ℕ} [NeZero j]

private theorem corr_eq_conv (x : ZMod j → ℤ) :
    corr x = conv x (fun u => x (-u)) := by
  funext t
  unfold corr conv
  refine Fintype.sum_equiv (Equiv.addRight t) _ _ fun u => ?_
  change x (u+t) * x u = x (u+t) * x (-(t-(u+t)))
  congr 2 <;> abel

private theorem packed_corr (B : ℕ) (hB : 1 < B) (x : ZMod j → ℤ) :
    ((packed B (corr x) : ℤ) : ZMod (B^j-1)) =
      ((packed B x : ℤ) : ZMod (B^j-1)) * (packed B (fun u => x (-u)) : ℤ) := by
  rw [corr_eq_conv, packed_conv B hB]

def packedCorr (B : ℕ) (x : ZMod j → ℤ) : ℤ :=
  packed B x * packed B (fun u => x (-u))

def centerCode (B : ℕ) (a b c d : ZMod j → ℤ) (s μ : ℤ) : ℤ :=
  let C := (5*(j:ℤ)+4)*256 - 2*μ
  j*256*(packedCorr B a + packedCorr B b + packedCorr B c + packedCorr B d) +
    (C - 4*256*s^2) * packed B (fun _ : ZMod j => 1) - j*C

theorem centerCode_eq (B : ℕ) (hB : 1 < B) (a b c d : ZMod j → ℤ) (s μ : ℤ) :
    ((packed B (centered a b c d s μ) : ℤ) : ZMod (B^j-1)) =
    (centerCode B a b c d s μ : ℤ) := by
  have hdelta : packed B (delta : ZMod j → ℤ) = 1 := by simp [packed_sum, delta, ite_mul]
  have h :
      packed B (centered a b c d s μ) =
      j * 256 * (packed B (corr a) + packed B (corr b) + packed B (corr c) + packed B (corr d)) +
      (((5*(j:ℤ)+4)*256-2*μ)-4*256*s^2) * packed B (fun _ : ZMod j => 1) -
      j * ((5*(j:ℤ)+4)*256-2*μ) := by
    rw [packed_sum] at hdelta
    simp only [packed_sum,centered,add_mul,sub_mul,mul_assoc,Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum,one_mul,hdelta,mul_one]
  rw [h]
  simp only [centerCode,packedCorr,Int.cast_sub,Int.cast_add,Int.cast_mul,packed_corr B hB]

theorem corr_bound (x : ZMod j → ℤ) (hx : ∀ u, |x u| ≤ 1) (t : ZMod j) :
    |corr x t| ≤ (j:ℤ) := by
  unfold corr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _u : ZMod j, (1:ℤ) := Finset.sum_le_sum fun u _ => by
      rw [abs_mul]; simpa using mul_le_mul (hx (u+t)) (hx u) (abs_nonneg _) (by decide : (0:ℤ) ≤ 1)
    _ = _ := by simp

end SignCond.FiniteEnergy

namespace SignCond.FinitePacking
variable {j : ℕ} [NeZero j]

def digit (B E i : ℕ) : ℕ := E / B^i % B

private theorem digit_succ (B E i : ℕ) : digit B E (i+1) = digit B (E/B) i := by
  simp [digit,Nat.div_div_eq_div_mul,pow_succ,mul_comm]

theorem pack_digits (B : ℕ) (hb : 0 < B) (E n : ℕ) (hE : E < B^n) :
    pack (B:ℤ) (fun i => digit B E i) n = (E:ℤ) := by
  induction n generalizing E with
  | zero => have : E = 0 := by simpa using hE
            simp [this,pack]
  | succ n ih =>
    have ht : E/B < B^n := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [pow_succ] using hE)
    simp only [pack,digit_succ,ih _ ht]
    simpa [digit] using (show (↑(E % B) : ℤ) + B*(E/B : ℕ) = E by exact_mod_cast Nat.mod_add_div E B)

theorem packed_shifted_digits (B E bias : ℕ) (hb : 0 < B) (hE : E < B^j) :
    packed B (fun i : ZMod j => (digit B E i.val : ℤ) - bias) =
      E - (bias:ℤ)*packed B (fun _ : ZMod j => 1) := by
  have hpack : packed B (fun i : ZMod j => (digit B E i.val : ℤ)) = E := by
    rw [packed_sum, ← pack_digits B hb E j hE,pack_sum]
    exact sum_zmod_val (fun k => (digit B E k : ℤ) * (B:ℤ)^k)
  rw [← hpack]
  simp [packed_sum,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]


end SignCond.FinitePacking

namespace SignCond.FiniteEnergy
open FinitePacking

def coeffBound (j s μ : ℕ) : ℕ :=
  let C : ℤ := (5*(j:ℤ)+4)*256-2*μ
  j*256*(4*j) + (C-4*256*(s:ℤ)^2).natAbs + j*C.natAbs

private theorem centerBound {j : ℕ} [NeZero j] (a b c d s μ : ℕ) (i : ZMod j) :
    |centered (signRow j a) (signRow j b) (signRow j c) (signRow j d) s μ i| ≤ coeffBound j s μ := by
  have hrow (v : ℕ) (k : ZMod j) : |signRow j v k| ≤ 1 := by
    unfold signRow
    split <;> norm_num
  have hc (v : ℕ) := corr_bound (signRow j v) (hrow v) i
  have hab (x y z w : ℤ) : |x+y+z+w| ≤ |x|+|y|+|z|+|w| := by
    linarith [abs_add_le x y, abs_add_le (x+y) z, abs_add_le (x+y+z) w]
  have h4 : |corr (signRow j a) i + corr (signRow j b) i + corr (signRow j c) i +
      corr (signRow j d) i| ≤ 4*(j:ℤ) := by
    linarith [hab (corr (signRow j a) i) (corr (signRow j b) i) (corr (signRow j c) i)
      (corr (signRow j d) i), hc a, hc b, hc c, hc d]
  unfold centered coeffBound
  push_cast
  refine (abs_sub _ _).trans ?_
  apply (add_le_add_right (abs_add_le _ _) _).trans
  simp only [abs_mul,abs_of_nonneg (Int.natCast_nonneg j),abs_of_pos (by decide : (0:ℤ)<256),
    Int.natCast_natAbs]
  have hh : |delta i| ≤ 1 := by unfold delta; split <;> norm_num
  nlinarith [mul_le_mul_of_nonneg_left h4 (show 0 ≤ (j:ℤ)*256 by positivity),
    mul_le_mul_of_nonneg_left hh (show 0 ≤ (j:ℤ)*|(5*(j:ℤ)+4)*256-2*μ| by positivity)]

/-- The integer output is decoded into signed radix digits. -/
def output (j B E : ℕ) [NeZero j] (i : ZMod j) : ℤ :=
  (digit B E i.val : ℤ) - ((B/2:ℕ):ℤ)

theorem witnessPacked {j : ℕ} [NeZero j] (a b c d s μ p B E : ℕ)
    (hs : 1 ≤ s)
    (hs1 : (2*(s:ℤ)-2)^2 ≤ 2*j) (hs2 : 2*(j:ℤ) ≤ (2*s+2)^2)
    (ha : ∑ i, signRow j a i = -(s:ℤ)) (hb : ∑ i, signRow j b i = (s:ℤ))
    (hc : ∑ i, signRow j c i = (s:ℤ)) (hd : ∑ i, signRow j d i = (s:ℤ))
    (hm : (2*j)*256^2 ≤ μ^2) (hr : 0 ≤ 3*(j:ℤ)*256-6*μ-8)
    (hB : 1 < B) (hE : E < B^j)
    (hw : majorant j (coeffBound j s μ) p + (B/2+1) + 1 < B)
    (hcode : (centerCode B (signRow j a) (signRow j b) (signRow j c) (signRow j d) s μ ^ (2^p) -
       (E - (B/2:ℕ)*packed B (fun _ : ZMod j => 1))) % (B^j-1:ℕ) = (0:ℤ))
    (habs : ∑ i, |output j B E i| ≤ ((j:ℤ)*(3*j*256-6*μ-8))^(2^p)) : SequenceWitness j := by
  apply witness a b c d s μ p hs hs1 hs2 ha hb hc hd hm hr
  rw [squarings_eq_of_packed B (coeffBound j s μ) (B/2+1) p hB _ (output j B E)
    (centerBound a b c d s μ) _ hw _]
  · exact habs
  · intro i
    have ht : digit B E i.val < B := Nat.mod_lt _ (by omega)
    unfold output
    rw [abs_le]
    push_cast
    omega
  · rw [centerCode_eq _ hB]
    have hy := packed_shifted_digits (j := j) B E (B/2) (by omega) hE
    have H : packed B (output j B E) = E - ((B/2:ℕ):ℤ) * packed B (fun _ : ZMod j => 1) := by
      exact hy
    rw [H, ← Int.cast_pow, ← sub_eq_zero, ← Int.cast_sub,ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero hcode

end SignCond.FiniteEnergy
