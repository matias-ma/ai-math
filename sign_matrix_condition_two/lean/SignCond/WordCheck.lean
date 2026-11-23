import SignCond.WordReplay

namespace SignCond.FiniteWord
open FiniteEnergy FinitePacking

instance {j w X : ℕ} : Decidable (BitWord j w X) :=
  decidable_of_iff (_ ∧ _) ⟨fun ⟨a,b⟩ => ⟨a,b⟩, fun h => ⟨h.size,h.sparse⟩⟩

instance {r : Row} {j w : ℕ} {s : ℤ} : Decidable (r.Check j w s) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨a,b,c,d,e⟩ => ⟨a,b,c,d,e⟩, fun h => ⟨h.xword,h.yword,h.sameCount,h.dot,h.total⟩⟩

theorem checkedWordWitness {j : ℕ} [NeZero j] (A B C D : Row) (s μ p w P N cap : ℕ)
    (h : 1 < 2^w ∧
      j < 2^w-1 ∧
      A.Check j w (-(s:ℤ)) ∧
      B.Check j w s ∧
      C.Check j w s ∧
      D.Check j w s ∧
      1≤s ∧
      (2*(s:ℤ)-2)^2 ≤ 2*j ∧
      2*(j:ℤ) ≤ (2*s+2)^2 ∧
      (2*j)*256^2 ≤ μ^2 ∧
      0 ≤ 3*(j:ℤ)*256-6*μ-8 ∧
      majorant j (coeffBound j s μ) p + cap + 1 < 2^w ∧
      j*cap < 2^w-1 ∧
      P < (2^w)^j ∧
      N < (2^w)^j ∧
      P &&& (cap*ones (2^w) j) = P ∧
      N &&& (cap*ones (2^w) j) = N ∧
      ((quadCode A B C D j (2^w) s μ : ℤ) : ZMod ((2^w)^j-1))^(2^p) =
            (P : ZMod ((2^w)^j-1)) - N ∧
      ((P%(2^w-1) + N%(2^w-1):ℕ):ℤ) ≤ ((j:ℤ)*(3*j*256-6*μ-8))^(2^p)) : SequenceWitness j := by
  obtain ⟨hb,hj,ha,hb',hc,hd,hs,hs1,hs2,hm,hr,hw,hcap,hP,hN,hpm,hnm,hPow,hNorm⟩ := h
  exact wordWitness A B C D s μ p w P N cap hb hj ha hb' hc hd hs hs1 hs2 hm hr hw hcap hP hN hpm hnm hPow hNorm

theorem singleInterval (n : ℕ) [NeZero n] (p : SequenceWitness n) :
    ∀ (j : ℕ) [NeZero j], n ≤ j → j ≤ n → SequenceWitness j := by
  intro j _ lo hi
  obtain rfl := Nat.le_antisymm lo hi
  exact p

theorem splitInterval {lo mid hi : ℕ}
    (left : ∀ (j : ℕ) [NeZero j], lo ≤ j → j ≤ mid → SequenceWitness j)
    (right : ∀ (j : ℕ) [NeZero j], mid+1 ≤ j → j ≤ hi → SequenceWitness j) :
    ∀ (j : ℕ) [NeZero j], lo ≤ j → j ≤ hi → SequenceWitness j := by
  intro j _ hl hh
  by_cases h : j ≤ mid
  · exact left j hl h
  · exact right j (by omega) hh

end SignCond.FiniteWord
