import SignCond.SmallTools

/-!
# Section `sec:small`: Lemma `lem:matching`

Paper: "Let `\Gamma` be a graph on `n` vertices that consists of `k\ge1` disjoint edges and
`r=n-2k\ge1` isolated vertices, and let `N` be its adjacency matrix. For real numbers `x,y,z`, the
eigenvalues of `xI+yJ+zN` are `x-z` with multiplicity `k`, `x+z` with multiplicity `k-1`, `x` with
multiplicity `r-1`, and the two roots of `\lambda^2-(2x+z+ny)\lambda+(x+z)(x+ry)+2kxy`."

The graph is described by an involution `μ` of `Fin n`: the vertices with `μ i ≠ i` are matched to
`μ i`, the fixed points are the isolated vertices. The paper's statement about eigenvalues and
multiplicities is its proof's decomposition, which is what is formalised: `xI + yJ + zN` acts as
* `x - z` on `e_p - e_{μ p}` for every matched `p` (these span a space of dimension `k`),
* `x + z` on the vectors constant on each edge, zero on the isolated vertices, with sum zero,
* `x` on the vectors supported on the isolated vertices with sum zero,
* and on the span of `𝟙_E, 𝟙_I` by the `2 × 2` matrix `[[x+z+2ky, ry], [2ky, x+ry]]` (columns are the
  images of `𝟙_E` and `𝟙_I`), whose characteristic polynomial is the displayed quadratic.
The dimension count (that these spaces have dimensions `k, k-1, r-1, 2` and span `ℝⁿ`) is not
formalised; the lower bounds of Section `sec:small` do not use it (they use test vectors).
-/

open Matrix

namespace SignCond

variable {n : ℕ}

/-- The adjacency matrix `N` of the matching given by the involution `μ`. -/
def matchAdj (μ : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if j = μ i ∧ μ i ≠ i then 1 else 0

/-- `xI + yJ + zN`. -/
def matchingMat (μ : Fin n → Fin n) (x y z : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  x • (1 : Matrix (Fin n) (Fin n) ℝ) + y • Matrix.of (fun _ _ => (1 : ℝ)) + z • matchAdj μ

/-- `𝟙_E`, the indicator vector of the matched vertices. -/
def indE (μ : Fin n → Fin n) : Fin n → ℝ := fun i => if μ i ≠ i then 1 else 0

/-- `𝟙_I`, the indicator vector of the isolated vertices. -/
def indI (μ : Fin n → Fin n) : Fin n → ℝ := fun i => if μ i = i then 1 else 0

theorem matchingMat_mulVec (μ : Fin n → Fin n) (x y z : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (matchingMat μ x y z *ᵥ v) i =
      x * v i + y * ∑ j, v j + z * (if μ i ≠ i then v (μ i) else 0) := by
  have h1 : ∑ j, x * (if i = j then (1 : ℝ) else 0) * v j = x * v i := by
    simp [mul_ite, ite_mul, Finset.sum_ite_eq]
  have h2 : ∑ j, y * (1 : ℝ) * v j = y * ∑ j, v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ j, z * (if j = μ i ∧ μ i ≠ i then (1 : ℝ) else 0) * v j =
      z * (if μ i ≠ i then v (μ i) else 0) := by
    by_cases h : μ i = i
    · simp [h]
    · simp [h, mul_ite, ite_mul, Finset.sum_ite_eq']
  simp only [matchingMat, mulVec, dotProduct, add_apply, smul_apply, one_apply, of_apply,
    matchAdj, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  rw [h1, h2, h3]

/-- **Lemma `lem:matching`** (as the decomposition of its proof; see the module docstring). -/
theorem lem_matching (μ : Fin n → Fin n) (hμ : ∀ i, μ (μ i) = i) (k : ℕ)
    (hk : (Finset.univ.filter fun i => μ i ≠ i).card = 2 * k) (_hk1 : 1 ≤ k)
    (_hr1 : 1 ≤ n - 2 * k) (x y z : ℝ) :
    (∀ p, μ p ≠ p → matchingMat μ x y z *ᵥ (Pi.single p 1 - Pi.single (μ p) 1) =
        (x - z) • (Pi.single p 1 - Pi.single (μ p) 1)) ∧
    (∀ u : Fin n → ℝ, (∀ i, u (μ i) = u i) → (∀ i, μ i = i → u i = 0) → ∑ i, u i = 0 →
        matchingMat μ x y z *ᵥ u = (x + z) • u) ∧
    (∀ u : Fin n → ℝ, (∀ i, μ i ≠ i → u i = 0) → ∑ i, u i = 0 →
        matchingMat μ x y z *ᵥ u = x • u) ∧
    matchingMat μ x y z *ᵥ indE μ = (x + z + 2 * k * y) • indE μ + (2 * k * y) • indI μ ∧
    matchingMat μ x y z *ᵥ indI μ =
      (((n - 2 * k : ℕ) : ℝ) * y) • indE μ + (x + ((n - 2 * k : ℕ) : ℝ) * y) • indI μ := by
  have hfix : ∀ i, μ i ≠ i → μ (μ i) ≠ μ i := fun i h e => h (by rw [hμ] at e; exact e.symm)
  have hsumE : ∑ i, indE μ i = 2 * k := by
    simp only [indE, Finset.sum_boole, hk]
    push_cast
    ring
  have hsumI : ∑ i, indI μ i = ((n - 2 * k : ℕ) : ℝ) := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin n))) (fun i => μ i = i)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have : (Finset.univ.filter fun i => ¬ μ i = i).card = 2 * k := hk
    simp only [indI, Finset.sum_boole]
    congr 1
    omega
  refine ⟨fun p hp => ?_, fun u hu1 hu2 hu3 => ?_, fun u hu1 hu2 => ?_, ?_, ?_⟩
  · have hsum : ∑ i, (Pi.single p (1 : ℝ) - Pi.single (μ p) 1 : Fin n → ℝ) i = 0 := by
      simp [Finset.sum_sub_distrib]
    funext i
    rw [matchingMat_mulVec, hsum]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hip : i = p
    · subst hip
      simp [Pi.single_apply, hp, Ne.symm hp, hμ]
      ring
    · by_cases hiq : i = μ p
      · subst hiq
        simp [Pi.single_apply, hp, Ne.symm hp, hμ, hfix p hp]
        ring
      · have h1 : μ i ≠ p := fun e => hiq (by rw [← e, hμ])
        have h2 : μ i ≠ μ p := fun e => hip (by rw [← hμ i, e, hμ])
        simp [Pi.single_apply, hip, hiq, h1, h2]
  · funext i
    rw [matchingMat_mulVec, hu3]
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : μ i = i
    · rw [hu2 i h]
      simp [h]
    · rw [if_pos h, hu1]
      ring
  · funext i
    rw [matchingMat_mulVec, hu2]
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : μ i = i
    · simp [h]
    · rw [if_pos h, hu1 (μ i) (hfix i h), hu1 i h]
      ring
  · funext i
    rw [matchingMat_mulVec, hsumE]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, indE, indI]
    by_cases h : μ i = i
    · simp [h]
      ring
    · simp [h, hfix i h]
      ring
  · funext i
    rw [matchingMat_mulVec, hsumI]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, indE, indI]
    by_cases h : μ i = i
    · simp [h]
      ring
    · simp [h, hfix i h]
      ring

end SignCond
