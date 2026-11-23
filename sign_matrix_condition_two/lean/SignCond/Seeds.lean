import SignCond.Defs

/-!
# Lemma `lem:seeds`, parts 2 and 3 (first half): finite checks by kernel evaluation

The memberships `S_q^σ ⊆ 𝒫_σ(P^{(λ)}, Q^{(λ)})` and the first coefficients
`P^{(λ)}_0 = Q^{(λ)}_0 = 1` are checked by `decide +kernel` (evaluation in Lean's kernel; no
`native_decide`). Memberships are evaluated coefficient by coefficient (`mem_pool_of_coeff`), which
needs only the `7` or `9` coefficients involved. The pool sizes (`≥ 992`) need all `λ²` coefficients
and exceeded the memory budget of this machine; they are the named hypothesis `LemSeedsPools`
in `Paper.lean`.
-/

namespace SignCond

theorem mem_pool_of_coeff {σ : ℤ} (hσ : σ ≠ 0) {n : ℕ} {P Q : Fin n → ℤ} {x : ℕ}
    (hP : coeff P x = σ) (hQ : coeff Q x = σ) : x ∈ pool σ P Q := by
  have hx : x < n := by
    by_contra h; simp [coeff, h] at hP; exact hσ hP.symm
  simp only [pool, Finset.mem_filter, Finset.mem_range]
  exact ⟨hx, hP, hQ⟩

theorem subset_pool_of_coeff {σ : ℤ} (hσ : σ ≠ 0) {n : ℕ} {P Q : Fin n → ℤ} {S : Finset ℕ}
    (h : ∀ x ∈ S, coeff P x = σ ∧ coeff Q x = σ) : S ⊆ pool σ P Q :=
  fun x hx => mem_pool_of_coeff hσ (h x hx).1 (h x hx).2

set_option maxRecDepth 100000

theorem seeds_coeff_64 : coeff (basePair 64).1 0 = 1 ∧ coeff (basePair 64).2 0 = 1 := by
  decide +kernel
theorem seeds_coeff_80 : coeff (basePair 80).1 0 = 1 ∧ coeff (basePair 80).2 0 = 1 := by
  decide +kernel
theorem seeds_coeff_100 : coeff (basePair 100).1 0 = 1 ∧ coeff (basePair 100).2 0 = 1 := by
  decide +kernel
theorem seeds_coeff_104 : coeff (basePair 104).1 0 = 1 ∧ coeff (basePair 104).2 0 = 1 := by
  decide +kernel

theorem seeds_mem_64_m :
    ∀ x ∈ seedSet 7 (-1), coeff (basePair 64).1 x = -1 ∧ coeff (basePair 64).2 x = -1 := by
  decide +kernel
theorem seeds_mem_64_p :
    ∀ x ∈ seedSet 7 1, coeff (basePair 64).1 x = 1 ∧ coeff (basePair 64).2 x = 1 := by
  decide +kernel
theorem seeds_mem_80_m :
    ∀ x ∈ seedSet 9 (-1), coeff (basePair 80).1 x = -1 ∧ coeff (basePair 80).2 x = -1 := by
  decide +kernel
theorem seeds_mem_80_p :
    ∀ x ∈ seedSet 9 1, coeff (basePair 80).1 x = 1 ∧ coeff (basePair 80).2 x = 1 := by
  decide +kernel
theorem seeds_mem_100_m :
    ∀ x ∈ seedSet 9 (-1), coeff (basePair 100).1 x = -1 ∧ coeff (basePair 100).2 x = -1 := by
  decide +kernel
theorem seeds_mem_100_p :
    ∀ x ∈ seedSet 9 1, coeff (basePair 100).1 x = 1 ∧ coeff (basePair 100).2 x = 1 := by
  decide +kernel
theorem seeds_mem_104_m :
    ∀ x ∈ seedSet 9 (-1), coeff (basePair 104).1 x = -1 ∧ coeff (basePair 104).2 x = -1 := by
  decide +kernel
theorem seeds_mem_104_p :
    ∀ x ∈ seedSet 9 1, coeff (basePair 104).1 x = 1 ∧ coeff (basePair 104).2 x = 1 := by
  decide +kernel

/-- `q = 7` for `λ = 64` and `q = 9` otherwise. -/
def seedSize (lam : ℕ) : ℕ := if lam = 64 then 7 else 9

/-- Lemma `lem:seeds`, part 2. -/
theorem seeds_part2 (σ : ℤ) (hσ : σ = -1 ∨ σ = 1) (lam : ℕ)
    (hlam : lam ∈ ({64, 80, 100, 104} : Finset ℕ)) :
    seedSet (seedSize lam) σ ⊆ pool σ (basePair lam).1 (basePair lam).2 := by
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlam
  apply subset_pool_of_coeff hσ0
  rcases hlam with rfl | rfl | rfl | rfl <;> rcases hσ with rfl | rfl
  · exact seeds_mem_64_m
  · exact seeds_mem_64_p
  · exact seeds_mem_80_m
  · exact seeds_mem_80_p
  · exact seeds_mem_100_m
  · exact seeds_mem_100_p
  · exact seeds_mem_104_m
  · exact seeds_mem_104_p

/-- Lemma `lem:seeds`, part 3 (first coefficients). -/
theorem seeds_part3_coeff (lam : ℕ) (hlam : lam ∈ ({64, 80, 100, 104} : Finset ℕ)) :
    coeff (basePair lam).1 0 = 1 ∧ coeff (basePair lam).2 0 = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlam
  rcases hlam with rfl | rfl | rfl | rfl
  · exact seeds_coeff_64
  · exact seeds_coeff_80
  · exact seeds_coeff_100
  · exact seeds_coeff_104

end SignCond
