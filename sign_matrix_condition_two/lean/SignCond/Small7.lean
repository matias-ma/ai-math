import SignCond.SmallUpper

/-!
# Section `sec:small`, paragraph "Order 7": `h(7) = √3`

Paper: "Suppose that `\kappa(A)^2<3`, and negate rows so that every row has an even number of entries
`-1`. The off-diagonal entries of `G` are congruent to `3` modulo `4`. By Lemma `lem:tools`, an entry
with `|g|=5` would give `\kappa(A)^2\ge6`, and `|g|=7` is impossible for an invertible matrix. Hence
every off-diagonal entry is `-1` or `3` [...] If a vertex of `\Gamma` has two neighbours, the
principal submatrix of `G` on these three vertices has eigenvalues `4,4,13` if the neighbours are
adjacent, and `8` and `\tfrac12(13\pm\sqrt{73})` if they are not. [...] Hence `\Gamma` consists of
`k\le3` disjoint edges [...] In every case `\kappa(A)^2\ge3`, a contradiction."

Every eigenvalue comparison is replaced by the Rayleigh form (Lemma `lem:tools`, part 2) at explicit
integer vectors (`rayleigh_cert`):

* `|g| = 5`: `e_i ± e_j` (`rayleigh_pair`: `12 ≤ 2c²`); `|g| = 7` contradicts positivity;
* a vertex `i` with adjacent neighbours `j, k`: `v = e_i+e_j+e_k` (`39/3`), `w = e_j-e_k` (`8/2`);
* a vertex `i` with nonadjacent neighbours `j, k`: `v = 3e_i+2e_j+2e_k` (`183/17`),
  `w = -4e_i+3e_j+3e_k` (`76/34`);
* two disjoint edges `{p,q}, {p',q'}` (this covers `k = 2, 3`): `v = e_p+e_q-e_{p'}-e_{q'}` (`48/4`),
  `w = e_p-e_q` (`8/2`);
* at most one edge, contained in `{p,q}` (this covers `k = 0, 1`): `v = e_a-e_b` for two vertices
  `a, b ∉ {p,q}` (`16/2`), `w = 𝟙` (`𝟙ᵀG𝟙 ≤ 15`, so quotient at most `15/7`).

The case analysis never enumerates graphs: it first shows that no vertex has two neighbours
(`Gram7.no_two`), and then distinguishes "two disjoint edges" from "all edges inside one pair".
-/

open Matrix

namespace SignCond

theorem injective_three {m : Type*} {i j k : m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective ![i, j, k] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

theorem injective_four {m : Type*} {i j k l : m} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : Function.Injective ![i, j, k, l] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- The normalised Gram matrix of order `7` after the first step: symmetric, diagonal `7`,
off-diagonal entries `-1` or `3`, with the Rayleigh form of ratio `c`. -/
structure Gram7 (B : Matrix (Fin 7) (Fin 7) ℝ) (c : ℝ) : Prop where
  ray : RayleighLe B c
  symm : ∀ i j, B i j = B j i
  diag : ∀ i, B i i = 7
  vals : ∀ i j, i ≠ j → B i j = -1 ∨ B i j = 3

namespace Gram7

variable {B : Matrix (Fin 7) (Fin 7) ℝ} {c : ℝ}

/-- **No vertex has two neighbours.** Paper: the principal submatrix on a vertex and two of its
neighbours has eigenvalues `4,4,13` (adjacent neighbours) or `8, ½(13 ± √73)`; both ratios exceed
`3`. -/
theorem no_two (hG : Gram7 B c) (hc : c ^ 2 < 3) {i j k : Fin 7} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (h1 : B i j = 3) (h2 : B i k = 3) : False := by
  have hR := rayleighLe_submatrix hG.ray (injective_three hij hik hjk)
  have h1' : B j i = 3 := by rw [hG.symm]; exact h1
  have h2' : B k i = 3 := by rw [hG.symm]; exact h2
  rcases hG.vals j k hjk with h3 | h3
  · have h3' : B k j = -1 := by rw [hG.symm]; exact h3
    have hM : B.submatrix ![i, j, k] ![i, j, k] = toR !![7, 3, 3; 3, 7, -1; 3, -1, 7] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [toR, hG.diag, h1, h2, h3, h1', h2', h3']
    have := rayleigh_cert hR _ hM ![3, 2, 2] ![-4, 3, 3] 1 3 one_pos (by decide) (by decide)
      (by decide)
    push_cast at this
    linarith
  · have h3' : B k j = 3 := by rw [hG.symm]; exact h3
    have hM : B.submatrix ![i, j, k] ![i, j, k] = toR !![7, 3, 3; 3, 7, 3; 3, 3, 7] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [toR, hG.diag, h1, h2, h3, h1', h2', h3']
    have := rayleigh_cert hR _ hM ![1, 1, 1] ![0, 1, -1] 1 3 one_pos (by decide) (by decide)
      (by decide)
    push_cast at this
    linarith

/-- If `j` is the neighbour of `i`, every other entry of row `i` is `-1`. -/
theorem other_neg (hG : Gram7 B c) (hc : c ^ 2 < 3) {i j k : Fin 7} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (h1 : B i j = 3) : B i k = -1 :=
  (hG.vals i k (Ne.symm hki)).resolve_right fun h2 =>
    hG.no_two hc hij (Ne.symm hki) (Ne.symm hkj) h1 h2

/-- **Two disjoint edges** (the paper's cases `k = 2, 3`): `v = e_p+e_q-e_{p'}-e_{q'}` has quotient
`12` and `w = e_p - e_q` has quotient `4`. -/
theorem two_edges (hG : Gram7 B c) (hc : c ^ 2 < 3) {p q p' q' : Fin 7} (h1 : p ≠ q)
    (h2 : p ≠ p') (h3 : p ≠ q') (h4 : q ≠ p') (h5 : q ≠ q') (h6 : p' ≠ q')
    (hpq : B p q = 3) (hpq' : B p' q' = 3) : False := by
  have hqp : B q p = 3 := by rw [hG.symm]; exact hpq
  have hqp' : B q' p' = 3 := by rw [hG.symm]; exact hpq'
  have a1 : B p p' = -1 := hG.other_neg hc h1 (Ne.symm h2) (Ne.symm h4) hpq
  have a2 : B p q' = -1 := hG.other_neg hc h1 (Ne.symm h3) (Ne.symm h5) hpq
  have a3 : B q p' = -1 := hG.other_neg hc (Ne.symm h1) (Ne.symm h4) (Ne.symm h2) hqp
  have a4 : B q q' = -1 := hG.other_neg hc (Ne.symm h1) (Ne.symm h5) (Ne.symm h3) hqp
  have b1 : B p' p = -1 := by rw [hG.symm]; exact a1
  have b2 : B q' p = -1 := by rw [hG.symm]; exact a2
  have b3 : B p' q = -1 := by rw [hG.symm]; exact a3
  have b4 : B q' q = -1 := by rw [hG.symm]; exact a4
  have hR := rayleighLe_submatrix hG.ray (injective_four h1 h2 h3 h4 h5 h6)
  have hM : B.submatrix ![p, q, p', q'] ![p, q, p', q'] =
      toR !![7, 3, -1, -1; 3, 7, -1, -1; -1, -1, 7, 3; -1, -1, 3, 7] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [toR, hG.diag, hpq, hqp, hpq', hqp', a1, a2, a3, a4, b1, b2, b3, b4]
  have := rayleigh_cert hR _ hM ![1, 1, -1, -1] ![1, -1, 0, 0] 1 3 one_pos (by decide)
    (by decide) (by decide)
  push_cast at this
  linarith

/-- The comparison matrix for "every edge lies inside `{p, q}`": diagonal `7`, entries `3` at
`(p,q), (q,p)`, and `-1` elsewhere. -/
def boundMat (p q : Fin 7) : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.of fun i j => if i = j then 7 else if (i = p ∧ j = q) ∨ (i = q ∧ j = p) then 3 else -1

/-- `𝟙ᵀ M 𝟙 = 49 - 42 + 8 = 15`. -/
theorem sum_boundMat : ∀ p q : Fin 7, p ≠ q → ∑ i, ∑ j, boundMat p q i j = 15 := by decide

theorem exists_two_avoid : ∀ p q : Fin 7, ∃ a b : Fin 7, a ≠ b ∧ a ≠ p ∧ a ≠ q ∧ b ≠ p ∧ b ≠ q := by
  decide

/-- **At most one edge** (the paper's cases `k = 0, 1`): `v = e_a - e_b` with `a, b` outside the
edge has quotient `8`, and `w = 𝟙` has `wᵀGw ≤ 15`, `wᵀw = 7`. -/
theorem at_most_one (hG : Gram7 B c) (hc : c ^ 2 < 3) {p q : Fin 7} (hpq : p ≠ q)
    (hE : ∀ i j, i ≠ j → B i j = 3 → (i = p ∧ j = q) ∨ (i = q ∧ j = p)) : False := by
  obtain ⟨a, b, hab, hap, haq, hbp, hbq⟩ := exists_two_avoid p q
  have hba : B a b = -1 := (hG.vals a b hab).resolve_right fun h => by
    rcases hE a b hab h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hap h1
    · exact haq h1
  have hbound : ∀ i j, B i j ≤ ((boundMat p q i j : ℤ) : ℝ) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [boundMat, hG.diag]
    · rcases hG.vals i j hij with h | h
      · rw [h]; unfold boundMat; simp only [of_apply, if_neg hij]; split_ifs <;> norm_num
      · rcases hE i j hij h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [boundMat, hij, h]
  have hsum : ∑ i, ∑ j, B i j ≤ 15 := by
    calc ∑ i, ∑ j, B i j ≤ ∑ i, ∑ j, ((boundMat p q i j : ℤ) : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hbound i j
      _ = ((∑ i, ∑ j, boundMat p q i j : ℤ) : ℝ) := by push_cast; rfl
      _ = 15 := by rw [sum_boundMat p q hpq]; norm_num
  have hw : (fun _ => (1 : ℝ)) ≠ (0 : Fin 7 → ℝ) := fun h0 => by
    simpa using congrFun h0 0
  obtain ⟨hpos, hle⟩ := hG.ray (extV ![a, b] ![1, -1]) (fun _ => 1) hw
  have hQw : (fun _ => (1 : ℝ)) ⬝ᵥ (B *ᵥ fun _ => 1) = ∑ i, ∑ j, B i j := by
    simp [dotProduct, mulVec]
  have hww : (fun _ => (1 : ℝ)) ⬝ᵥ (fun _ => (1 : ℝ) : Fin 7 → ℝ) = 7 := by
    simp [dotProduct]
  have hQv : extV ![a, b] ![1, -1] ⬝ᵥ (B *ᵥ extV ![a, b] ![1, -1]) = 16 := by
    rw [quad_extV, quad_two, hG.diag, hG.diag, hba, hG.symm b a, hba]
    norm_num
  have hvv : extV ![a, b] ![1, -1] ⬝ᵥ extV ![a, b] ![1, -1] = 2 := by
    rw [norm_extV (injective_two hab)]
    simp [dotProduct, Fin.sum_univ_two]
    norm_num
  rw [hQw, hww, hQv, hvv] at hle
  rw [hQw] at hpos
  nlinarith [sq_nonneg c]

/-- **The order-7 lower bound for the normalised Gram matrix:** `c² ≥ 3`. -/
theorem three_le (hG : Gram7 B c) : 3 ≤ c ^ 2 := by
  by_contra hc
  push_neg at hc
  by_cases hedge : ∃ p q, p ≠ q ∧ B p q = 3
  · obtain ⟨p, q, hpq, h⟩ := hedge
    have hqp : B q p = 3 := by rw [hG.symm]; exact h
    by_cases hother : ∃ i j, i ≠ j ∧ B i j = 3 ∧ ¬((i = p ∧ j = q) ∨ (i = q ∧ j = p))
    · obtain ⟨i, j, hij, h', hn⟩ := hother
      have hji : B j i = 3 := by rw [hG.symm]; exact h'
      push_neg at hn
      obtain ⟨hn1, hn2⟩ := hn
      have hip : i ≠ p := by
        rintro rfl
        exact hG.no_two hc hpq hij (fun e => hn1 rfl e.symm) h h'
      have hiq : i ≠ q := by
        rintro rfl
        exact hG.no_two hc (Ne.symm hpq) hij (fun e => hn2 rfl e.symm) hqp h'
      have hjp : j ≠ p := by
        rintro rfl
        exact hG.no_two hc hpq (Ne.symm hij) (Ne.symm hiq) h hji
      have hjq : j ≠ q := by
        rintro rfl
        exact hG.no_two hc (Ne.symm hpq) (Ne.symm hij) (Ne.symm hip) hqp hji
      exact hG.two_edges hc hpq (Ne.symm hip) (Ne.symm hjp) (Ne.symm hiq) (Ne.symm hjq) hij h h'
    · push_neg at hother
      exact hG.at_most_one hc hpq hother
  · push_neg at hedge
    exact hG.at_most_one hc (show (0 : Fin 7) ≠ 1 by decide) fun i j hij hb =>
      absurd hb (hedge i j hij)

end Gram7

/-- **Order 7, lower bound.** Every `7 × 7` sign matrix with `κ(A) ≤ c` has `c² ≥ 3`. -/
theorem order7_lower {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : IsSign A) {c : ℝ} (h : CondLe A c) :
    3 ≤ c ^ 2 := by
  obtain ⟨A', hA', hc', heven⟩ := exists_even_rows (by norm_num) hA
  have h' := hc' c h
  by_contra hlt
  push_neg at hlt
  have hR := rayleighLe_of_condLe h'
  have hdiag : ∀ i, (A' * A'ᵀ) i i = 7 := fun i => by rw [gram_diag hA']; norm_num
  have vals : ∀ i j, i ≠ j → (A' * A'ᵀ) i j = -1 ∨ (A' * A'ᵀ) i j = 3 := by
    intro i j hij
    obtain ⟨g, hg, hmod⟩ := lem_tools_one hA' i j (by rw [heven i, heven j])
    obtain ⟨h1, h2⟩ := rayleigh_pair hR (gram_symm A') hdiag hij
    rw [hg] at h1 h2 ⊢
    have hg7 : |g| < 7 := by exact_mod_cast h2
    rw [abs_lt] at hg7
    unfold Int.ModEq at hmod
    have : g = -5 ∨ g = -1 ∨ g = 3 := by omega
    rcases this with rfl | rfl | rfl
    · norm_num at h1
      nlinarith
    · left; norm_num
    · right; norm_num
  exact absurd (Gram7.three_le ⟨hR, gram_symm A', hdiag, vals⟩) (not_le.2 hlt)

/-- **Theorem `thm:small`, `h(7) = √3`.** The matrix `A₇` has `κ(A₇) ≤ √3`, and every `7 × 7` sign
matrix with `κ(A) ≤ c'`, `c' ≥ 0`, has `√3 ≤ c'`. -/
theorem hval_7 : HVal 7 (Real.sqrt 3) := by
  refine ⟨⟨A7, isSign_A7, condLe_A7⟩, fun A hA c' hc' h => ?_⟩
  calc Real.sqrt 3 ≤ Real.sqrt (c' ^ 2) := Real.sqrt_le_sqrt (order7_lower hA h)
    _ = c' := Real.sqrt_sq hc'

end SignCond
