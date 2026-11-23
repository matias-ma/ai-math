import SignCond.SmallUpper

/-!
# Section `sec:small`, paragraph "Order 10": `h(10) = 3/2`

Paper: "Suppose that `\kappa(A)^2<\tfrac94`. At least five rows of `A` have numbers of entries `-1`
of the same parity. By Lemma `lem:tools`, their inner products are congruent to `2` modulo `4`, and
`|g|=6` would give `\kappa(A)^2\ge4`. So these inner products are `\pm2`. [...] In every case
`\kappa(A)^2\ge\tfrac94`, a contradiction. Thus `h(10)\ge\tfrac32`."

Formalisation.
* `exists_five_same_parity`: five rows with numbers of `-1` of the same parity (pigeonhole).
* Their inner products are `±2` (Lemma `lem:tools`; `|g| = 6` gives `16 ≤ 4c²`, and `|g| = 10`
  contradicts `|g| < n`).
* `five_switch`: negate rows (switching, `rayleighLe_switch`) so that the first of the five rows has
  inner product `2` with the other four (the paper's normalisation).
* `five_core`: the remaining six inner products give `2⁶ = 64` patterns. The paper's case analysis
  (balanced/unbalanced triples; principal submatrices with spectra `{8, 18}`,
  `{10 ± 2√5, 8, 12}`, `{4, 12}`) is replaced by an integer certificate checked by `decide`
  (`cert10`): for every pattern, one of seven pairs `(v, w)` of integer vectors satisfies
  `9 (wᵀGw)(vᵀv) ≤ 4 (vᵀGv)(wᵀw)`. The seven pairs are the paper's test vectors: the balanced case
  `v = Σ eᵢ`, and vectors supported on four of the five rows for the unbalanced cases.
-/

open Matrix

namespace SignCond

/-- "At least five rows of `A` have numbers of entries `-1` of the same parity." -/
theorem exists_five_same_parity (A : Matrix (Fin 10) (Fin 10) ℝ) :
    ∃ f : Fin 5 → Fin 10, Function.Injective f ∧
      ∀ k l, negCount A (f k) % 2 = negCount A (f l) % 2 := by
  have key : ∀ (P : Fin 10 → Prop) [DecidablePred P], 5 ≤ (Finset.univ.filter P).card →
      ∃ f : Fin 5 → Fin 10, Function.Injective f ∧ ∀ k, P (f k) := by
    intro P _ h
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h
    refine ⟨fun k => t.orderEmbOfFin htc k, (t.orderEmbOfFin htc).injective, fun k => ?_⟩
    have := ht (t.orderEmbOfFin_mem htc k)
    simpa using this
  have hcard := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin 10))) (fun i => negCount A i % 2 = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  by_cases hE : 5 ≤ (Finset.univ.filter fun i => negCount A i % 2 = 0).card
  · obtain ⟨f, hf, hP⟩ := key _ hE
    exact ⟨f, hf, fun k l => by rw [hP k, hP l]⟩
  · obtain ⟨f, hf, hP⟩ := key (fun i => ¬ negCount A i % 2 = 0) (by omega)
    exact ⟨f, hf, fun k l => by have := hP k; have := hP l; omega⟩

/-- The normalised Gram matrix of the five rows: diagonal `10`, first row and column `2`, and the
six remaining inner products `z_{kl}`. -/
def M10 (z12 z13 z14 z23 z24 z34 : ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![10, 2, 2, 2, 2;
     2, 10, z12, z13, z14;
     2, z12, 10, z23, z24;
     2, z13, z23, 10, z34;
     2, z14, z24, z34, 10]

/-- Seven pairs `(v, w)` of test vectors. -/
def L10 : List ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  [(![1, 1, 0, 0, 0], ![-1, 1, 1, 1, 1]),
   (![1, 1, 1, 1, 0], ![-1, 0, 0, 1, 1]),
   (![1, 1, 0, 1, 1], ![-1, 0, 1, 1, 0]),
   (![1, 0, 1, 1, 1], ![-1, 1, 0, 1, 0]),
   (![1, 1, 1, 1, 1], ![-1, 1, 1, -1, 1]),
   (![1, 1, 1, 1, 1], ![-1, -1, 0, 1, 1]),
   (![1, 1, 1, 0, 1], ![-1, -1, 1, 1, 1])]

/-- **The integer certificate.** For each of the `64` sign patterns, some pair `(v, w)` of `L10`
satisfies `9 (wᵀMw)(vᵀv) ≤ 4 (vᵀMv)(wᵀw)`. -/
theorem cert10 :
    ∀ z12 ∈ ([2, -2] : List ℤ), ∀ z13 ∈ ([2, -2] : List ℤ), ∀ z14 ∈ ([2, -2] : List ℤ),
    ∀ z23 ∈ ([2, -2] : List ℤ), ∀ z24 ∈ ([2, -2] : List ℤ), ∀ z34 ∈ ([2, -2] : List ℤ),
    ∃ uw ∈ L10, 0 < uw.1 ⬝ᵥ uw.1 ∧ 0 < uw.2 ⬝ᵥ uw.2 ∧
      9 * ((uw.2 ⬝ᵥ (M10 z12 z13 z14 z23 z24 z34 *ᵥ uw.2)) * (uw.1 ⬝ᵥ uw.1)) ≤
        4 * ((uw.1 ⬝ᵥ (M10 z12 z13 z14 z23 z24 z34 *ᵥ uw.1)) * (uw.2 ⬝ᵥ uw.2)) := by
  decide

theorem exists_pm2 {x : ℝ} (h : x = 2 ∨ x = -2) : ∃ z : ℤ, x = z ∧ z ∈ ([2, -2] : List ℤ) := by
  rcases h with rfl | rfl
  · exact ⟨2, by norm_num, by simp⟩
  · exact ⟨-2, by norm_num, by simp⟩

/-- **Five normalised rows.** If the five rows have inner products `±2`, and the first has inner
product `2` with the other four, then `c² ≥ 9/4`. -/
theorem five_core {B : Matrix (Fin 5) (Fin 5) ℝ} {c : ℝ} (hR : RayleighLe B c)
    (hsym : ∀ i j, B i j = B j i) (hdiag : ∀ i, B i i = 10) (h0 : ∀ k, k ≠ 0 → B 0 k = 2)
    (hval : ∀ i j, i ≠ j → B i j = 2 ∨ B i j = -2) : 9 ≤ 4 * c ^ 2 := by
  obtain ⟨z12, e12, m12⟩ := exists_pm2 (hval 1 2 (by decide))
  obtain ⟨z13, e13, m13⟩ := exists_pm2 (hval 1 3 (by decide))
  obtain ⟨z14, e14, m14⟩ := exists_pm2 (hval 1 4 (by decide))
  obtain ⟨z23, e23, m23⟩ := exists_pm2 (hval 2 3 (by decide))
  obtain ⟨z24, e24, m24⟩ := exists_pm2 (hval 2 4 (by decide))
  obtain ⟨z34, e34, m34⟩ := exists_pm2 (hval 3 4 (by decide))
  have f1 := h0 1 (by decide)
  have f2 := h0 2 (by decide)
  have f3 := h0 3 (by decide)
  have f4 := h0 4 (by decide)
  have g1 : B 1 0 = 2 := by rw [hsym]; exact f1
  have g2 : B 2 0 = 2 := by rw [hsym]; exact f2
  have g3 : B 3 0 = 2 := by rw [hsym]; exact f3
  have g4 : B 4 0 = 2 := by rw [hsym]; exact f4
  have e21 : B 2 1 = z12 := by rw [hsym]; exact e12
  have e31 : B 3 1 = z13 := by rw [hsym]; exact e13
  have e41 : B 4 1 = z14 := by rw [hsym]; exact e14
  have e32 : B 3 2 = z23 := by rw [hsym]; exact e23
  have e42 : B 4 2 = z24 := by rw [hsym]; exact e24
  have e43 : B 4 3 = z34 := by rw [hsym]; exact e34
  have hB : B = toR (M10 z12 z13 z14 z23 z24 z34) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toR, M10, hdiag, f1, f2, f3, f4, g1, g2, g3, g4, e12, e13, e14, e23, e24, e34,
        e21, e31, e41, e32, e42, e43]
  obtain ⟨uw, -, hu, hw, hc⟩ := cert10 z12 m12 z13 m13 z14 m14 z23 m23 z24 m24 z34 m34
  have := rayleigh_cert hR _ hB uw.1 uw.2 4 9 (by norm_num) hu hw hc
  push_cast at this
  linarith

/-- **Normalisation.** Paper: "we negate rows so that the first has inner product `2` with the other
four". -/
theorem five_switch {B : Matrix (Fin 5) (Fin 5) ℝ} {c : ℝ} (hR : RayleighLe B c)
    (hsym : ∀ i j, B i j = B j i) (hdiag : ∀ i, B i i = 10)
    (hval : ∀ i j, i ≠ j → B i j = 2 ∨ B i j = -2) : 9 ≤ 4 * c ^ 2 := by
  obtain ⟨s, hs_def⟩ : ∃ s : Fin 5 → ℝ, s = fun k => if k = 0 then 1 else B 0 k / 2 := ⟨_, rfl⟩
  have hs : ∀ k, s k = 1 ∨ s k = -1 := by
    intro k
    by_cases hk : k = 0
    · left; simp [hs_def, hk]
    · rcases hval 0 k (Ne.symm hk) with h | h <;> simp [hs_def, hk, h]
  have hss : ∀ k, s k * s k = 1 := fun k => by rcases hs k with h | h <;> rw [h] <;> norm_num
  refine five_core (rayleighLe_switch hR hs) ?_ ?_ ?_ ?_
  · intro i j
    simp only [of_apply]
    rw [hsym i j]
    ring
  · intro i
    simp only [of_apply]
    rw [hss, hdiag]
    norm_num
  · intro k hk
    simp only [of_apply]
    have h0 : s 0 = 1 := by simp [hs_def]
    have hk' : s k = B 0 k / 2 := by simp [hs_def, hk]
    rw [h0, hk']
    rcases hval 0 k (Ne.symm hk) with h | h <;> rw [h] <;> norm_num
  · intro i j hij
    simp only [of_apply]
    rcases hs i with hi | hi <;> rcases hs j with hj | hj <;>
      rcases hval i j hij with h | h <;> rw [hi, hj, h] <;> norm_num

/-- **Order 10, lower bound.** Every `10 × 10` sign matrix with `κ(A) ≤ c` has `c² ≥ 9/4`. -/
theorem order10_lower {A : Matrix (Fin 10) (Fin 10) ℝ} (hA : IsSign A) {c : ℝ} (h : CondLe A c) :
    9 ≤ 4 * c ^ 2 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf, hpar⟩ := exists_five_same_parity A
  have hR5 := rayleighLe_submatrix (rayleighLe_of_condLe h) hf
  have hsym : ∀ i j, (A * Aᵀ).submatrix f f i j = (A * Aᵀ).submatrix f f j i :=
    fun i j => gram_symm A _ _
  have hdiag : ∀ i, (A * Aᵀ).submatrix f f i i = 10 := fun i => by
    simp only [submatrix_apply]
    rw [gram_diag hA]
    norm_num
  have hval : ∀ i j, i ≠ j →
      (A * Aᵀ).submatrix f f i j = 2 ∨ (A * Aᵀ).submatrix f f i j = -2 := by
    intro i j hij
    obtain ⟨g, hg, hmod⟩ := lem_tools_one hA (f i) (f j) (hpar i j)
    obtain ⟨h1, h2⟩ := rayleigh_pair hR5 hsym hdiag hij
    simp only [submatrix_apply] at h1 h2 ⊢
    rw [hg] at h1 h2 ⊢
    have hg10 : |g| < 10 := by exact_mod_cast h2
    rw [abs_lt] at hg10
    unfold Int.ModEq at hmod
    have : g = -6 ∨ g = -2 ∨ g = 2 ∨ g = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · norm_num at h1
      nlinarith
    · right; norm_num
    · left; norm_num
    · norm_num at h1
      nlinarith
  exact absurd (five_switch hR5 hsym hdiag hval) (not_le.2 hlt)

/-- **Theorem `thm:small`, `h(10) = 3/2`.** `W₂ ⊗ (J₅ - 2I₅)` has `κ ≤ 3/2`, and every `10 × 10` sign
matrix with `κ(A) ≤ c'`, `c' ≥ 0`, has `3/2 ≤ c'`. -/
theorem hval_10 : HVal 10 (3 / 2) := by
  refine ⟨⟨A10, isSign_A10, condLe_A10⟩, fun A hA c' hc' h => ?_⟩
  have := order10_lower hA h
  nlinarith

end SignCond
