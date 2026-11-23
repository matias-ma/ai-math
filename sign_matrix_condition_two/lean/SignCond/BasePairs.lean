import SignCond.Defs

/-!
# Golay pairs: casts, doubling, square, lift, the base pairs `(P^{(λ)}, Q^{(λ)})`, lifted pairs and
their common pools

* `IsGolayPair` is preserved by reindexing along `Fin.cast`, doubling, Lemma `lem:square`, `Q ↦ Q^rev`
  and the lift; hence every base pair is a regular Golay pair (`basePair_regular`) and so is every
  lifted pair (`liftedPair_regular`).
* `coeff` is unchanged by `Fin.cast`; the lift copies `P_x, Q_x` to positions `4x, 4x+1`
  (`coeff_golayLift`), so the common pool of the lift contains `4𝒫 ∪ (4𝒫+1)` (`pool_golayLift`).
-/

open Complex

namespace SignCond

/-! ### Casts -/

theorem peval_comp_cast {n m : ℕ} (h : m = n) (P : Fin n → ℤ) (z : ℂ) :
    peval (P ∘ Fin.cast h) z = peval P z := by
  subst h; rfl

theorem isSignSeq_comp_cast {n m : ℕ} (h : m = n) {P : Fin n → ℤ} (hP : IsSignSeq P) :
    IsSignSeq (P ∘ Fin.cast h) := fun _ => hP _

theorem isGolayPair_comp_cast {n m : ℕ} (h : m = n) {P Q : Fin n → ℤ} (hPQ : IsGolayPair P Q) :
    IsGolayPair (P ∘ Fin.cast h) (Q ∘ Fin.cast h) := by
  subst h; exact hPQ

theorem coeff_comp_cast {n m : ℕ} (h : m = n) (P : Fin n → ℤ) (x : ℕ) :
    coeff (P ∘ Fin.cast h) x = coeff P x := by
  subst h; rfl

theorem pool_comp_cast (σ : ℤ) {n m : ℕ} (h : m = n) (P Q : Fin n → ℤ) :
    pool σ (P ∘ Fin.cast h) (Q ∘ Fin.cast h) = pool σ P Q := by
  subst h; rfl

/-! ### Doubling, square, reversal, lift -/

theorem isGolayPair_double {n : ℕ} {p : (Fin n → ℤ) × (Fin n → ℤ)} (h : IsGolayPair p.1 p.2) :
    IsGolayPair (golayDouble p).1 (golayDouble p).2 := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨s1, s2⟩ := isSignSeq_double h1 h2
  exact ⟨s1, s2, isGolay_double h3⟩

theorem golayDoubleIter_zero {n : ℕ} (p : (Fin n → ℤ) × (Fin n → ℤ)) :
    golayDoubleIter 0 p = (p.1 ∘ Fin.cast (by ring), p.2 ∘ Fin.cast (by ring)) := rfl

theorem golayDoubleIter_succ (k : ℕ) {n : ℕ} (p : (Fin n → ℤ) × (Fin n → ℤ)) :
    golayDoubleIter (k + 1) p =
      ((golayDouble (golayDoubleIter k p)).1 ∘ Fin.cast (by ring),
        (golayDouble (golayDoubleIter k p)).2 ∘ Fin.cast (by ring)) := rfl

theorem isGolayPair_doubleIter (k : ℕ) {n : ℕ} {p : (Fin n → ℤ) × (Fin n → ℤ)}
    (h : IsGolayPair p.1 p.2) : IsGolayPair (golayDoubleIter k p).1 (golayDoubleIter k p).2 := by
  induction k with
  | zero => rw [golayDoubleIter_zero]; dsimp only; exact isGolayPair_comp_cast _ h
  | succ k ih =>
    rw [golayDoubleIter_succ]; dsimp only; exact isGolayPair_comp_cast _ (isGolayPair_double ih)

/-- Lemma `lem:square` for `golaySquare`: a regular Golay pair of length `l²`. -/
theorem golaySquare_regular {l : ℕ} {A B : Fin l → ℤ} (h : IsGolayPair A B) :
    IsRegular l (golaySquare A B).1 (golaySquare A B).2 := by
  obtain ⟨hA, hB, hG⟩ := h
  simp only [IsRegular, golaySquare]
  refine ⟨isGolayPair_comp_cast _ ⟨isSignSeq_sqP hA hB, isSignSeq_sqQ hA hB, isGolay_sq hA hB hG⟩,
    ?_, ?_⟩
  · rw [peval_comp_cast, sqP_one hA hB hG]
  · rw [peval_comp_cast, sqQ_one hA hB hG]

theorem isRegular_rev {l : ℕ} {P Q : Fin (l ^ 2) → ℤ} (h : IsRegular l P Q) :
    IsRegular l P (seqRev Q) := by
  obtain ⟨⟨hP, hQ, hG⟩, h1, h2⟩ := h
  exact ⟨⟨hP, isSignSeq_rev hQ, isGolay_rev hG⟩, h1, by rw [peval_rev_one, h2]⟩

theorem isGolayPair_lift {n : ℕ} {p : (Fin n → ℤ) × (Fin n → ℤ)} (h : IsGolayPair p.1 p.2) :
    IsGolayPair (golayLift p).1 (golayLift p).2 := by
  obtain ⟨hP, hQ, hG⟩ := h
  simp only [golayLift]
  exact isGolayPair_comp_cast _ ⟨isSignSeq_liftP hP hQ, isSignSeq_liftQ hP hQ, isGolay_lift hG⟩

theorem golayLift_one {n : ℕ} (p : (Fin n → ℤ) × (Fin n → ℤ)) :
    peval (golayLift p).1 1 = 2 * peval p.1 1 ∧ peval (golayLift p).2 1 = 2 * peval p.2 1 := by
  simp only [golayLift]
  rw [peval_comp_cast, peval_comp_cast, liftP_one, liftQ_one]
  exact ⟨rfl, rfl⟩

/-- The lift copies `P_x`, `Q_x` to positions `4x` and `4x + 1`. -/
theorem coeff_golayLift {n : ℕ} (p : (Fin n → ℤ) × (Fin n → ℤ)) (x : ℕ) (hx : x < n) :
    coeff (golayLift p).1 (4 * x) = coeff p.1 x ∧ coeff (golayLift p).2 (4 * x) = coeff p.1 x ∧
      coeff (golayLift p).1 (4 * x + 1) = coeff p.2 x ∧
      coeff (golayLift p).2 (4 * x + 1) = coeff p.2 x := by
  obtain ⟨h1, h2, h3, h4⟩ := lift_coefficients p.1 p.2 ⟨x, hx⟩
  have a1 : 4 * x < 4 * n := by omega
  have a2 : 4 * x + 1 < 4 * n := by omega
  simp only [golayLift, coeff, Function.comp_apply, dif_pos a1, dif_pos a2, dif_pos hx]
  exact ⟨h1, h2, h3, h4⟩

theorem pool_golayLift (σ : ℤ) {n : ℕ} (p : (Fin n → ℤ) × (Fin n → ℤ)) :
    maskLift (pool σ p.1 p.2) ⊆ pool σ (golayLift p).1 (golayLift p).2 := by
  intro y hy
  simp only [maskLift, Finset.mem_union, Finset.mem_image] at hy
  have key : ∀ x ∈ pool σ p.1 p.2, x < n ∧ coeff p.1 x = σ ∧ coeff p.2 x = σ := by
    intro x hx
    simp only [pool, Finset.mem_filter, Finset.mem_range] at hx
    exact hx
  rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;> obtain ⟨hxn, hP, hQ⟩ := key x hx <;>
    obtain ⟨c1, c2, c3, c4⟩ := coeff_golayLift p x hxn <;>
    simp only [pool, Finset.mem_filter, Finset.mem_range]
  · exact ⟨by omega, by rw [c1, hP], by rw [c2, hP]⟩
  · exact ⟨by omega, by rw [c3, hQ], by rw [c4, hQ]⟩

/-! ### The base pairs -/

theorem isGolayPair_one : IsGolayPair golayOne.1 golayOne.2 :=
  ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun z _ => by simp [golayOne, peval]; norm_num⟩

theorem isGolayPair_10 : IsGolayPair golayA10 golayB10 :=
  ⟨by unfold IsSignSeq golayA10; decide, by unfold IsSignSeq golayB10; decide, isGolay_10⟩

theorem isGolayPair_26 : IsGolayPair golayA26 golayB26 :=
  ⟨by unfold IsSignSeq golayA26; decide, by unfold IsSignSeq golayB26; decide, isGolay_26⟩

theorem basePair_64 : basePair 64 =
    golaySquare (golayDoubleIter 6 golayOne).1 (golayDoubleIter 6 golayOne).2 := rfl

theorem basePair_80 : basePair 80 =
    ((golaySquare (golayDoubleIter 3 (golayA10, golayB10)).1
        (golayDoubleIter 3 (golayA10, golayB10)).2).1,
      seqRev (golaySquare (golayDoubleIter 3 (golayA10, golayB10)).1
        (golayDoubleIter 3 (golayA10, golayB10)).2).2) := rfl

theorem basePair_100 : basePair 100 =
    golaySquare (golaySquare golayA10 golayB10).1 (golaySquare golayA10 golayB10).2 := rfl

theorem basePair_104 : basePair 104 =
    golaySquare (golayDoubleIter 2 (golayA26, golayB26)).1
      (golayDoubleIter 2 (golayA26, golayB26)).2 := rfl

/-- Paper: "all four pairs are regular Golay pairs". -/
theorem basePair_regular (lam : ℕ) (hlam : lam ∈ ({64, 80, 100, 104} : Finset ℕ)) :
    IsRegular lam (basePair lam).1 (basePair lam).2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlam
  rcases hlam with rfl | rfl | rfl | rfl
  · rw [basePair_64]
    exact golaySquare_regular (isGolayPair_doubleIter 6 isGolayPair_one)
  · rw [basePair_80]
    exact isRegular_rev (golaySquare_regular (isGolayPair_doubleIter 3 (p := (golayA10, golayB10))
      isGolayPair_10))
  · rw [basePair_100]
    exact golaySquare_regular (golaySquare_regular isGolayPair_10).1
  · rw [basePair_104]
    exact golaySquare_regular (isGolayPair_doubleIter 2 (p := (golayA26, golayB26))
      isGolayPair_26)

/-! ### Lifted pairs -/

theorem liftedPair_zero (lam : ℕ) :
    liftedPair lam 0 = ((basePair lam).1 ∘ Fin.cast (by ring), (basePair lam).2 ∘ Fin.cast (by ring)) :=
  rfl

theorem liftedPair_succ (lam h : ℕ) :
    liftedPair lam (h + 1) =
      ((golayLift (liftedPair lam h)).1 ∘ Fin.cast (by ring),
        (golayLift (liftedPair lam h)).2 ∘ Fin.cast (by ring)) := rfl

/-- Paper: "It is a regular Golay pair of length `(2^h λ)²`." -/
theorem liftedPair_regular (lam : ℕ) (hlam : lam ∈ ({64, 80, 100, 104} : Finset ℕ)) (h : ℕ) :
    IsRegular (2 ^ h * lam) (liftedPair lam h).1 (liftedPair lam h).2 := by
  induction h with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := basePair_regular lam hlam
    rw [liftedPair_zero]
    dsimp only
    refine ⟨isGolayPair_comp_cast _ h1, ?_, ?_⟩
    · rw [peval_comp_cast, h2]; simp
    · rw [peval_comp_cast, h3]; simp
  | succ h ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨l1, l2⟩ := golayLift_one (liftedPair lam h)
    rw [liftedPair_succ]
    dsimp only
    refine ⟨isGolayPair_comp_cast _ (isGolayPair_lift h1), ?_, ?_⟩
    · rw [peval_comp_cast, l1, h2]; push_cast; ring
    · rw [peval_comp_cast, l2, h3]; push_cast; ring

/-- With eq. `liftcoefficients`: if `P^{(λ)}_0 = Q^{(λ)}_0 = 1` then `P^{(λ,h)}_0 = Q^{(λ,h)}_0 = 1`. -/
theorem liftedPair_coeff_zero (lam h : ℕ) (hpos : 0 < lam) (h1 : coeff (basePair lam).1 0 = 1)
    (h2 : coeff (basePair lam).2 0 = 1) :
    coeff (liftedPair lam h).1 0 = 1 ∧ coeff (liftedPair lam h).2 0 = 1 := by
  induction h with
  | zero =>
    rw [liftedPair_zero]; dsimp only
    rw [coeff_comp_cast, coeff_comp_cast]; exact ⟨h1, h2⟩
  | succ h ih =>
    rw [liftedPair_succ]; dsimp only
    rw [coeff_comp_cast, coeff_comp_cast]
    have hpos' : 0 < (2 ^ h * lam) ^ 2 := by positivity
    obtain ⟨c1, c2, -, -⟩ := coeff_golayLift (liftedPair lam h) 0 hpos'
    simp only [mul_zero] at c1 c2
    rw [c1, c2]
    exact ⟨ih.1, ih.1⟩

/-- The lifted seed `S^{(h)}`: `S ↦ 4S ∪ (4S + 1)` applied `h` times. -/
def maskLiftIter (S : Finset ℕ) : ℕ → Finset ℕ
  | 0 => S
  | h + 1 => maskLift (maskLiftIter S h)

theorem card_maskLiftIter (S : Finset ℕ) (h : ℕ) : (maskLiftIter S h).card = 2 ^ h * S.card := by
  induction h with
  | zero => simp [maskLiftIter]
  | succ h ih => rw [maskLiftIter, card_maskLift, ih]; ring

theorem pool_liftedPair (σ : ℤ) (lam : ℕ) (h : ℕ) :
    maskLiftIter (pool σ (basePair lam).1 (basePair lam).2) h ⊆
      pool σ (liftedPair lam h).1 (liftedPair lam h).2 := by
  induction h with
  | zero => rw [liftedPair_zero]; dsimp only; rw [pool_comp_cast]; rfl
  | succ h ih =>
    rw [liftedPair_succ]; dsimp only; rw [pool_comp_cast, maskLiftIter]
    exact (maskLift_mono ih).trans (pool_golayLift σ _)
where
  maskLift_mono {A B : Finset ℕ} (hAB : A ⊆ B) : maskLift A ⊆ maskLift B := by
    intro y hy
    simp only [maskLift, Finset.mem_union, Finset.mem_image] at hy ⊢
    rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact Or.inl ⟨x, hAB hx, rfl⟩
    · exact Or.inr ⟨x, hAB hx, rfl⟩

theorem maskLiftIter_mono {A B : Finset ℕ} (hAB : A ⊆ B) (h : ℕ) :
    maskLiftIter A h ⊆ maskLiftIter B h := by
  induction h with
  | zero => exact hAB
  | succ h ih => exact pool_liftedPair.maskLift_mono ih

theorem zero_not_mem_maskLiftIter {S : Finset ℕ} (hS : 0 ∉ S) (h : ℕ) : 0 ∉ maskLiftIter S h := by
  induction h with
  | zero => exact hS
  | succ h ih =>
    simp only [maskLiftIter, maskLift, Finset.mem_union, Finset.mem_image, not_or, not_exists,
      not_and]
    refine ⟨fun x hx h0 => ?_, fun x _ h0 => by omega⟩
    have : x = 0 := by omega
    exact ih (this ▸ hx)

end SignCond
