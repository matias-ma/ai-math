import SignCond.Small7

/-!
# Section `sec:small`: tools for the orders `9` and `13`

* `exists_inj_extend`: an injective `p : Fin k → Fin n` extends to an injective `f : Fin n → Fin n`
  with `f a = p a` for `a < k` (a relabelling of the rows that puts a given set of rows first).
* `quad_eq_sum`: `vᵀMv = ∑ᵢ ∑ⱼ M i j (vᵢ vⱼ)`.
* `comp_cert`: the paper's "whole-matrix" test vectors. If a set `Λ` of `m` rows (listed by `p`) is
  closed (every row of `Λ` has inner product `1` with every row outside `Λ`), the other off-diagonal
  entries are at most `1`, and the entries on `Λ` form the integer matrix `Kin`, then the quadratic
  form of `G` at a vector `w` that is constant (`= t`) outside `Λ` is at most that of the comparison
  matrix `Kext` (entries `Kin` on `Λ`, diagonal `d`, and `1` elsewhere): "an edge outside `Λ` joins
  two vertices on which `v` takes the same value, further edges can only decrease this quotient".
  A vector `v` supported on `Λ` has the same quadratic form for `G` and `Kext`. An integer
  inequality between the two quotients, checked by `decide`, then bounds `c²` from below.
* `rowsum_ge`: a row with diagonal `d`, one entry `≥ -3` and all other entries `1` has sum at least
  `n + d - 5`.
-/

open Matrix

namespace SignCond

theorem injective_five {m : Type*} {i j k l x : m} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hix : i ≠ x) (hjk : j ≠ k) (hjl : j ≠ l) (hjx : j ≠ x) (hkl : k ≠ l) (hkx : k ≠ x)
    (hlx : l ≠ x) : Function.Injective ![i, j, k, l, x] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

theorem injective_six {m : Type*} {i j k l x y : m} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hix : i ≠ x) (hiy : i ≠ y) (hjk : j ≠ k) (hjl : j ≠ l) (hjx : j ≠ x) (hjy : j ≠ y)
    (hkl : k ≠ l) (hkx : k ≠ x) (hky : k ≠ y) (hlx : l ≠ x) (hly : l ≠ y) (hxy : x ≠ y) :
    Function.Injective ![i, j, k, l, x, y] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- Relabelling: an injective `p : Fin k → Fin n` extends to an injective map `Fin n → Fin n`. -/
theorem exists_inj_extend {n k : ℕ} (hk : k ≤ n) (p : Fin k → Fin n)
    (hp : Function.Injective p) :
    ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ a : Fin k, f (Fin.castLE hk a) = p a := by
  classical
  let F : Fin n → Fin n := fun x => if h : x.val < k then p ⟨x.val, h⟩ else x
  let s : Finset (Fin n) := Finset.univ.filter (fun x => x.val < k)
  have hinj : Set.InjOn F s := by
    intro x hx y hy hxy
    simp only [s, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    simp only [F, dif_pos hx, dif_pos hy] at hxy
    have := hp hxy
    exact Fin.ext (by simpa using congrArg Fin.val this)
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (t := Finset.univ) (by simp)
    (Finset.subset_univ _) hinj
  refine ⟨fun x => (g x : Fin n), fun x y h => g.injective (Subtype.ext h), fun a => ?_⟩
  have := hg (Fin.castLE hk a) (by simp [s])
  show (g (Fin.castLE hk a) : Fin n) = p a
  rw [this]
  simp [F]

theorem quad_eq_sum {m : Type*} [Fintype m] (M : Matrix m m ℝ) (v : m → ℝ) :
    v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, M i j * (v i * v j) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The comparison matrix: `Kin` on the first `m` indices, `d` on the rest of the diagonal, `1`
elsewhere. -/
def Kext {n m : ℕ} (Kin : Matrix (Fin m) (Fin m) ℤ) (d : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if h : i.val < m ∧ j.val < m then Kin ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else if i = j then d else 1

/-- A vector with entries `u` on the first `m` indices and `t` elsewhere. -/
def vext {n m : ℕ} (u : Fin m → ℤ) (t : ℤ) : Fin n → ℤ :=
  fun i => if h : i.val < m then u ⟨i.val, h⟩ else t

/-- **Whole-matrix certificate for a closed set of rows.** See the module docstring. -/
theorem comp_cert {n m : ℕ} (hm : m ≤ n) {B : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hR : RayleighLe B c) (hsym : ∀ i j, B i j = B j i) (d : ℤ) (hdiag : ∀ i, B i i = d)
    (hle : ∀ i j, i ≠ j → B i j ≤ 1)
    (p : Fin m → Fin n) (hp : Function.Injective p) (Kin : Matrix (Fin m) (Fin m) ℤ)
    (hin : ∀ a b, B (p a) (p b) = Kin a b)
    (hclosed : ∀ a x, (∀ b, x ≠ p b) → B (p a) x = 1)
    (vin win : Fin m → ℤ) (t : ℤ) (P Q : ℤ) (hP : 0 < P)
    (hv : 0 < (vext vin 0 : Fin n → ℤ) ⬝ᵥ vext vin 0)
    (hw : 0 < (vext win t : Fin n → ℤ) ⬝ᵥ vext win t)
    (hcert : Q * (((vext win t : Fin n → ℤ) ⬝ᵥ (Kext Kin d *ᵥ vext win t)) *
        ((vext vin 0 : Fin n → ℤ) ⬝ᵥ vext vin 0)) ≤
      P * (((vext vin 0 : Fin n → ℤ) ⬝ᵥ (Kext Kin d *ᵥ vext vin 0)) *
        ((vext win t : Fin n → ℤ) ⬝ᵥ vext win t))) :
    (Q : ℝ) ≤ P * c ^ 2 := by
  obtain ⟨f, hf, hfp⟩ := exists_inj_extend hm p hp
  have hR' := rayleighLe_submatrix hR hf
  set B' := B.submatrix f f with hB'
  -- the rows of `Λ` are the first `m` indices
  have hfin : ∀ (i : Fin n) (h : i.val < m), f i = p ⟨i.val, h⟩ := by
    intro i h
    rw [← hfp]
    rfl
  have hfout : ∀ (j : Fin n), m ≤ j.val → ∀ b, f j ≠ p b := by
    intro j hj b h
    rw [← hfp] at h
    have := congrArg Fin.val (hf h)
    simp at this
    omega
  have hinside : ∀ i j : Fin n, ∀ h : i.val < m ∧ j.val < m,
      B' i j = ((Kext Kin d i j : ℤ) : ℝ) := by
    intro i j h
    simp only [hB', submatrix_apply, Kext, of_apply, dif_pos h]
    rw [hfin i h.1, hfin j h.2, hin]
  have hcross : ∀ i j : Fin n, i.val < m → m ≤ j.val → B' i j = 1 := by
    intro i j hi hj
    simp only [hB', submatrix_apply]
    rw [hfin i hi]
    exact hclosed _ _ (hfout j hj)
  have hK1 : ∀ i j : Fin n, ¬ (i.val < m ∧ j.val < m) → i ≠ j → Kext Kin d i j = 1 := by
    intro i j h hij
    simp [Kext, h, hij]
  -- entrywise comparisons
  have hvE : ∀ i j, B' i j * (((vext vin 0 : Fin n → ℤ) i : ℝ) * ((vext vin 0 : Fin n → ℤ) j : ℝ)) =
      toR (Kext Kin d) i j *
        (((vext vin 0 : Fin n → ℤ) i : ℝ) * ((vext vin 0 : Fin n → ℤ) j : ℝ)) := by
    intro i j
    by_cases h : i.val < m ∧ j.val < m
    · rw [hinside i j h]; rfl
    · have h0 : ((vext vin 0 : Fin n → ℤ) i : ℝ) * ((vext vin 0 : Fin n → ℤ) j : ℝ) = 0 := by
        rcases not_and_or.1 h with h' | h'
        · simp [vext, h']
        · simp [vext, h']
      rw [h0, mul_zero, mul_zero]
  have hwE : ∀ i j, B' i j * (((vext win t : Fin n → ℤ) i : ℝ) * ((vext win t : Fin n → ℤ) j : ℝ)) ≤
      toR (Kext Kin d) i j *
        (((vext win t : Fin n → ℤ) i : ℝ) * ((vext win t : Fin n → ℤ) j : ℝ)) := by
    intro i j
    by_cases h : i.val < m ∧ j.val < m
    · rw [hinside i j h]; rfl
    · by_cases hi : i.val < m
      · have hj : m ≤ j.val := by
          by_contra hj; exact h ⟨hi, by omega⟩
        have hij : i ≠ j := fun e => by subst e; omega
        rw [hcross i j hi hj]
        simp only [toR, map_apply, hK1 i j h hij, Int.cast_one, le_refl]
      · by_cases hj : j.val < m
        · have hij : i ≠ j := fun e => by subst e; exact hi hj
          have : B' i j = 1 := by
            simp only [hB', submatrix_apply]
            rw [hsym]
            exact hcross j i hj (by omega)
          rw [this]
          simp only [toR, map_apply, hK1 i j h hij, Int.cast_one, le_refl]
        · have hwi : ((vext win t : Fin n → ℤ) i : ℝ) = t := by simp [vext, hi]
          have hwj : ((vext win t : Fin n → ℤ) j : ℝ) = t := by simp [vext, hj]
          rw [hwi, hwj]
          by_cases hij : i = j
          · subst hij
            simp [hB', hdiag, toR, Kext, hi]
          · apply mul_le_mul_of_nonneg_right _ (mul_self_nonneg _)
            rw [show toR (Kext Kin d) i j = 1 by simp [toR, hK1 i j h hij]]
            exact hle _ _ (hf.ne hij)
  -- the two quadratic forms
  set V : Fin n → ℝ := fun i => ((vext vin 0 : Fin n → ℤ) i : ℝ)
  set W : Fin n → ℝ := fun i => ((vext win t : Fin n → ℤ) i : ℝ)
  have hQV : V ⬝ᵥ (B' *ᵥ V) = V ⬝ᵥ (toR (Kext Kin d) *ᵥ V) := by
    rw [quad_eq_sum, quad_eq_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hvE i j
  have hQW : W ⬝ᵥ (B' *ᵥ W) ≤ W ⬝ᵥ (toR (Kext Kin d) *ᵥ W) := by
    rw [quad_eq_sum, quad_eq_sum]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hwE i j
  have hWne : W ≠ 0 := by
    intro h0
    have := cast_dotProduct (vext win t : Fin n → ℤ) (vext win t)
    change W ⬝ᵥ W = _ at this
    rw [h0, zero_dotProduct] at this
    have : (((vext win t : Fin n → ℤ) ⬝ᵥ vext win t : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
    simp_all
  obtain ⟨hpos, hle'⟩ := hR' V W hWne
  have cV : V ⬝ᵥ (toR (Kext Kin d) *ᵥ V) =
      (((vext vin 0 : Fin n → ℤ) ⬝ᵥ (Kext Kin d *ᵥ vext vin 0) : ℤ) : ℝ) := cast_quad _ _
  have cW : W ⬝ᵥ (toR (Kext Kin d) *ᵥ W) =
      (((vext win t : Fin n → ℤ) ⬝ᵥ (Kext Kin d *ᵥ vext win t) : ℤ) : ℝ) := cast_quad _ _
  have nV : V ⬝ᵥ V = (((vext vin 0 : Fin n → ℤ) ⬝ᵥ vext vin 0 : ℤ) : ℝ) := cast_dotProduct _ _
  have nW : W ⬝ᵥ W = (((vext win t : Fin n → ℤ) ⬝ᵥ vext win t : ℤ) : ℝ) := cast_dotProduct _ _
  rw [hQV, cV, nV, nW] at hle'
  rw [cW] at hQW
  have hc' : (Q : ℝ) * ((((vext win t : Fin n → ℤ) ⬝ᵥ (Kext Kin d *ᵥ vext win t) : ℤ) : ℝ) *
      (((vext vin 0 : Fin n → ℤ) ⬝ᵥ vext vin 0 : ℤ) : ℝ)) ≤
      (P : ℝ) * ((((vext vin 0 : Fin n → ℤ) ⬝ᵥ (Kext Kin d *ᵥ vext vin 0) : ℤ) : ℝ) *
      (((vext win t : Fin n → ℤ) ⬝ᵥ vext win t : ℤ) : ℝ)) := by exact_mod_cast hcert
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hv' : (0 : ℝ) < (((vext vin 0 : Fin n → ℤ) ⬝ᵥ vext vin 0 : ℤ) : ℝ) := by exact_mod_cast hv
  set a := (((vext vin 0 : Fin n → ℤ) ⬝ᵥ (Kext Kin d *ᵥ vext vin 0) : ℤ) : ℝ)
  set b := (((vext win t : Fin n → ℤ) ⬝ᵥ (Kext Kin d *ᵥ vext win t) : ℤ) : ℝ)
  set vv := (((vext vin 0 : Fin n → ℤ) ⬝ᵥ vext vin 0 : ℤ) : ℝ)
  set ww := (((vext win t : Fin n → ℤ) ⬝ᵥ vext win t : ℤ) : ℝ)
  set q := W ⬝ᵥ (B' *ᵥ W)
  have hb : 0 < b := lt_of_lt_of_le hpos hQW
  have key : (Q : ℝ) * (b * vv) ≤ (P * c ^ 2) * (b * vv) := by
    calc (Q : ℝ) * (b * vv) ≤ P * (a * ww) := hc'
      _ ≤ P * (c ^ 2 * q * vv) := mul_le_mul_of_nonneg_left hle' hP'.le
      _ ≤ P * (c ^ 2 * b * vv) := by
          apply mul_le_mul_of_nonneg_left _ hP'.le
          apply mul_le_mul_of_nonneg_right _ hv'.le
          exact mul_le_mul_of_nonneg_left hQW (sq_nonneg c)
      _ = (P * c ^ 2) * (b * vv) := by ring
  exact le_of_mul_le_mul_right key (mul_pos hb hv')

/-- **Row sums.** A row with diagonal entry `d`, one entry `≥ -3` at `j₀` and all other entries `1`
has sum at least `n + (d - 1) - 4`. -/
theorem rowsum_ge {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (i j0 : Fin n) (hij : j0 ≠ i) (d : ℝ)
    (hd : B i i = d) (h0 : -3 ≤ B i j0) (h1 : ∀ j, j ≠ i → j ≠ j0 → B i j = 1) :
    (n : ℝ) + (d - 1) - 4 ≤ ∑ j, B i j := by
  have hle : ∀ j, (1 + (if j = i then d - 1 else 0) - (if j = j0 then 4 else 0) : ℝ) ≤ B i j := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, if_neg (Ne.symm hij), hd]
      ring_nf
      exact le_refl _
    · by_cases hj0 : j = j0
      · subst hj0
        rw [if_neg hji, if_pos rfl]
        linarith
      · rw [if_neg hji, if_neg hj0, h1 j hji hj0]
        norm_num
  calc (n : ℝ) + (d - 1) - 4 =
        ∑ j, (1 + (if j = i then d - 1 else 0) - (if j = j0 then 4 else 0) : ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          simp
    _ ≤ ∑ j, B i j := Finset.sum_le_sum fun j _ => hle j

theorem injective_eight {m : Type*} {x0 x1 x2 x3 x4 x5 x6 x7 : m}
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h03 : x0 ≠ x3) (h04 : x0 ≠ x4) (h05 : x0 ≠ x5) (h06 : x0 ≠ x6) (h07 : x0 ≠ x7) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h25 : x2 ≠ x5) (h26 : x2 ≠ x6) (h27 : x2 ≠ x7) (h34 : x3 ≠ x4) (h35 : x3 ≠ x5) (h36 : x3 ≠ x6) (h37 : x3 ≠ x7) (h45 : x4 ≠ x5) (h46 : x4 ≠ x6) (h47 : x4 ≠ x7) (h56 : x5 ≠ x6) (h57 : x5 ≠ x7) (h67 : x6 ≠ x7) :
    Function.Injective ![x0, x1, x2, x3, x4, x5, x6, x7] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- Two elements outside the range of an injective `p : Fin k → Fin (k+1)` are equal. -/
theorem eq_of_not_mem_range {n k : ℕ} (hk : k + 1 = n) (p : Fin k → Fin n)
    (hp : Function.Injective p) {x y : Fin n} (hx : ∀ a, x ≠ p a) (hy : ∀ a, y ≠ p a) : x = y := by
  obtain ⟨f, hf, hfp⟩ := exists_inj_extend (by omega) p hp
  have hs := Finite.surjective_of_injective hf
  obtain ⟨i, rfl⟩ := hs x
  obtain ⟨j, rfl⟩ := hs y
  have hi : k ≤ i.val := by
    by_contra h
    exact hx ⟨i.val, by omega⟩ (by rw [← hfp]; rfl)
  have hj : k ≤ j.val := by
    by_contra h
    exact hy ⟨j.val, by omega⟩ (by rw [← hfp]; rfl)
  have : i = j := Fin.ext (by omega)
  rw [this]

/-- The Gram matrix of a graph consisting of the `k` disjoint edges `{2t, 2t+1}` (`t < k`) and
isolated vertices: diagonal `d`, `-3` on the edges, `1` elsewhere. -/
def matchMat (n k : ℕ) (d : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if i = j then d else
    if i.val < 2 * k ∧ j.val < 2 * k ∧ i.val / 2 = j.val / 2 then -3 else 1

/-- **A matching in canonical position.** If the rows `p 0, …, p (2k-1)` are matched in pairs
`{p (2t), p (2t+1)}` (inner product `-3`), every vertex has at most one neighbour, and every edge
has an end among the `p a`, then after a relabelling `G` is `matchMat n k d`. -/
theorem match_sub {n k : ℕ} (hk : 2 * k ≤ n) {B : Matrix (Fin n) (Fin n) ℝ}
    (hsym : ∀ i j, B i j = B j i) (d : ℤ) (hdiag : ∀ i, B i i = d)
    (hvals : ∀ i j, i ≠ j → B i j = 1 ∨ B i j = -3)
    (hdeg : ∀ x y z, B x y = -3 → B x z = -3 → y = z)
    (p : Fin (2 * k) → Fin n) (hp : Function.Injective p)
    (hadj : ∀ a : Fin (2 * k), a.val % 2 = 0 → ∀ h : a.val + 1 < 2 * k,
      B (p a) (p ⟨a.val + 1, h⟩) = -3)
    (hfin : ∀ x y, B x y = -3 → ∃ a, x = p a) :
    ∃ f : Fin n → Fin n, Function.Injective f ∧ B.submatrix f f = toR (matchMat n k d) := by
  obtain ⟨f, hf, hfp⟩ := exists_inj_extend hk p hp
  refine ⟨f, hf, ?_⟩
  have hfin' : ∀ (i : Fin n) (h : i.val < 2 * k), f i = p ⟨i.val, h⟩ := fun i h => by
    rw [← hfp]; rfl
  have hin : ∀ (i : Fin n) (a : Fin (2 * k)), f i = p a → i.val = a.val := by
    intro i a h
    rw [← hfp] at h
    have := congrArg Fin.val (hf h)
    simpa using this
  have hpair : ∀ a b : Fin (2 * k), a ≠ b → a.val / 2 = b.val / 2 → B (p a) (p b) = -3 := by
    intro a b hab hd
    have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
    have ha := a.2
    have hb := b.2
    rcases Nat.mod_two_eq_zero_or_one a.val with h0 | h0
    · have e : b = ⟨a.val + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e]
      exact hadj a h0 _
    · have e : a = ⟨b.val + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hsym, e]
      exact hadj b (by omega) _
  have partner : ∀ a : Fin (2 * k), ∃ a' : Fin (2 * k), a' ≠ a ∧ a'.val / 2 = a.val / 2 := by
    intro a
    have ha := a.2
    rcases Nat.mod_two_eq_zero_or_one a.val with h0 | h0
    · exact ⟨⟨a.val + 1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this,
        by simp; omega⟩
    · exact ⟨⟨a.val - 1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega,
        by simp; omega⟩
  ext i j
  simp only [submatrix_apply, toR, map_apply, matchMat, of_apply]
  by_cases hij : i = j
  · subst hij
    simp [hdiag]
  · rw [if_neg hij]
    split_ifs with h
    · rw [hfin' i h.1, hfin' j h.2.1]
      push_cast
      exact hpair _ _ (fun e => hij (Fin.ext (by simpa using congrArg Fin.val e))) h.2.2
    · push_cast
      refine (hvals _ _ (hf.ne hij)).resolve_right fun hE => h ?_
      obtain ⟨a, ha⟩ := hfin _ _ hE
      have hia := hin i a ha
      obtain ⟨a', ha'ne, ha'⟩ := partner a
      have h2 : B (f i) (p a') = -3 := by
        rw [ha]
        exact hpair a a' (Ne.symm ha'ne) ha'.symm
      have hja := hin j a' (hdeg _ _ _ hE h2)
      have := a.2
      have := a'.2
      exact ⟨by omega, by omega, by omega⟩

end SignCond
