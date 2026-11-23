import SignCond.FiniteEnergy

namespace SignCond.FiniteEnergy

def signRow (j mask : ℕ) [NeZero j] (t : ZMod j) : ℤ :=
  if mask.testBit t.val then -1 else 1

def SequenceWitness (j : ℕ) [NeZero j] : Prop :=
  ∃ (a b c d : ZMod j → ℝ) (s : ℕ), IsSignVec a ∧ IsSignVec b ∧ IsSignVec c ∧
    IsSignVec d ∧ vsum a = -(s : ℝ) ∧ vsum b = s ∧ vsum c = s ∧ vsum d = s ∧ 1 ≤ s ∧
    (2 * (s : ℝ) - 2)^2 ≤ 2 * j ∧ 2 * (j : ℝ) ≤ (2*s+2)^2 ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      (Real.sqrt (2*j) + 2)^2 ≤ energy a b c d ℓ ∧
      energy a b c d ℓ < (2 * Real.sqrt (2*j) - 2)^2

private theorem row_sign (j mask : ℕ) [NeZero j] : IsSignVec (realRow (signRow j mask)) := by
  intro i
  simp only [realRow, signRow]
  split <;> norm_num

theorem witness {j : ℕ} [NeZero j] (a b c d : ℕ) (s μ p : ℕ)
    (hs : 1 ≤ s)
    (hs1 : (2 * (s : ℤ) - 2)^2 ≤ 2*j) (hs2 : 2*(j : ℤ) ≤ (2*s+2)^2)
    (ha : ∑ i, signRow j a i = -(s : ℤ)) (hb : ∑ i, signRow j b i = (s : ℤ))
    (hc : ∑ i, signRow j c i = (s : ℤ)) (hd : ∑ i, signRow j d i = (s : ℤ))
    (hm : (2*j)*256^2 ≤ μ^2)
    (hr : 0 ≤ 3*(j : ℤ)*256 - 6*μ - 8)
    (hcert : ∑ t, |squarings (centered (signRow j a) (signRow j b) (signRow j c) (signRow j d) s μ) p t| ≤
      ((j : ℤ) * (3*j*256 - 6*μ - 8))^(2^p)) : SequenceWitness j := by
  have hsum (v : ℕ) : vsum (realRow (signRow j v)) = ((∑ i, signRow j v i : ℤ) : ℝ) := by
    simp [vsum, realRow]
  refine ⟨_, _, _, _, s, row_sign j a, row_sign j b, row_sign j c, row_sign j d,
    ?_, ?_, ?_, ?_, hs, ?_, ?_, ?_⟩
  · rw [hsum, ha]; push_cast; rfl
  · rw [hsum, hb]; norm_cast
  · rw [hsum, hc]; norm_cast
  · rw [hsum, hd]; norm_cast
  · exact_mod_cast hs1
  · exact_mod_cast hs2
  · intro ℓ hℓ hlt
    refine bounds _ _ _ _ s μ p ?_ hr hcert hℓ hlt
    push_cast
    rw [← le_div_iff₀' (by norm_num : (0:ℝ) < 256), Real.sqrt_le_iff]
    constructor
    · positivity
    · have h : (2*(j:ℝ))*256^2 ≤ (μ:ℝ)^2 := by exact_mod_cast hm
      nlinarith

end SignCond.FiniteEnergy
