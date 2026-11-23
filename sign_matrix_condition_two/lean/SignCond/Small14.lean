import SignCond.Small10

/-!
# Section `sec:small`, paragraph "Order 14": `h(14) = √(13/6)`

Paper: "Suppose that `\kappa(A)^2<\tfrac{13}6`. At least seven rows of `A` have numbers of entries
`-1` of the same parity. Their inner products are congruent to `2` modulo `4`, and `|g|=6` would give
`\kappa(A)^2\ge\tfrac52`, so they are `\pm2`. We negate rows so that the first of the seven rows has
inner product `2` with the other six, and let `\Gamma` be the graph on these six rows whose edges are
the pairs with inner product `-2`. [...] Hence every four vertices of `\Gamma` induce a graph without
edges or a `P_4`. [...] Hence `\Gamma` has no edge, the principal submatrix on the seven rows is
`12I+2J` with eigenvalues `12` and `26`, and `\kappa(A)^2\ge\tfrac{13}6`, a contradiction."

Formalisation.
* `exists_seven_same_parity`: seven rows with numbers of `-1` of the same parity (pigeonhole).
* Their inner products are `±2` (Lemma `lem:tools`; `|g| = 6` gives `20 ≤ 8c²`, `|g| = 10` gives
  `24 ≤ 4c²`, and `|g| = 14` contradicts `|g| < n`).
* `seven_switch`: negate rows so that the first of the seven has inner product `2` with the others.
* `cert14`: the paper's computation over the `64` graphs on four vertices. A graph on four labelled
  vertices is six Booleans (`true` = inner product `-2`); `ok4` says that it has no edge or is a
  `P₄`. For every other graph, one of `27` pairs `(v, w)` of integer vectors on the five rows (the
  first row and the four) satisfies `13 (wᵀMw)(vᵀv) ≤ 6 (vᵀMv)(wᵀw)`. Checked by `decide`.
* `graph6`: "every four vertices of `Γ` induce a graph without edges or a `P_4`" forces `Γ` to be
  empty. The paper's argument (degrees, connectedness, `P₆`/`C₆` contain `2K₂`) is replaced by a
  check over the `2¹⁵` graphs on six labelled vertices (`decide +kernel`).
* `seven_core`: then all inner products are `2`, and `v = 𝟙` (`182/7 = 26`), `w = e₁ - e₂`
  (`24/2 = 12`) give `c² ≥ 13/6`.
-/

open Matrix

namespace SignCond

/-- "At least seven rows of `A` have numbers of entries `-1` of the same parity." -/
theorem exists_seven_same_parity (A : Matrix (Fin 14) (Fin 14) ℝ) :
    ∃ f : Fin 7 → Fin 14, Function.Injective f ∧
      ∀ k l, negCount A (f k) % 2 = negCount A (f l) % 2 := by
  have key : ∀ (P : Fin 14 → Prop) [DecidablePred P], 7 ≤ (Finset.univ.filter P).card →
      ∃ f : Fin 7 → Fin 14, Function.Injective f ∧ ∀ k, P (f k) := by
    intro P _ h
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h
    refine ⟨fun k => t.orderEmbOfFin htc k, (t.orderEmbOfFin htc).injective, fun k => ?_⟩
    have := ht (t.orderEmbOfFin_mem htc k)
    simpa using this
  have hcard := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin 14))) (fun i => negCount A i % 2 = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  by_cases hE : 7 ≤ (Finset.univ.filter fun i => negCount A i % 2 = 0).card
  · obtain ⟨f, hf, hP⟩ := key _ hE
    exact ⟨f, hf, fun k l => by rw [hP k, hP l]⟩
  · obtain ⟨f, hf, hP⟩ := key (fun i => ¬ negCount A i % 2 = 0) (by omega)
    exact ⟨f, hf, fun k l => by have := hP k; have := hP l; omega⟩

/-! ### Graphs as Booleans -/

/-- The inner product encoded by a Boolean: `true` (an edge of `Γ`) is `-2`, `false` is `2`. -/
def bsgn (b : Bool) : ℤ := if b then -2 else 2

/-- The edge indicator of an inner product `x = ±2`: `true` iff `x = -2`. -/
noncomputable def eb (x : ℝ) : Bool := decide (x = -2)

theorem eq_bsgn {x : ℝ} (h : x = 2 ∨ x = -2) : x = ((bsgn (eb x) : ℤ) : ℝ) := by
  rcases h with rfl | rfl
  · have : eb 2 = false := by simp only [eb, decide_eq_false_iff_not]; norm_num
    rw [this]; simp [bsgn]
  · have : eb (-2) = true := by simp [eb]
    rw [this]; simp [bsgn]

theorem eb_false {x : ℝ} (h : x = 2 ∨ x = -2) (he : eb x = false) : x = 2 :=
  h.resolve_right fun h' => by simp [eb, h'] at he

/-- A graph on four labelled vertices `1, 2, 3, 4` (edges `b_{kl}`) has no edge or is a path `P₄`
(three edges, all degrees `1` or `2`). -/
def ok4 (b12 b13 b14 b23 b24 b34 : Bool) : Bool :=
  let d1 := b12.toNat + b13.toNat + b14.toNat
  let d2 := b12.toNat + b23.toNat + b24.toNat
  let d3 := b13.toNat + b23.toNat + b34.toNat
  let d4 := b14.toNat + b24.toNat + b34.toNat
  (d1 + d2 + d3 + d4 == 0) ||
    (d1 + d2 + d3 + d4 == 6 && (d1 == 1 || d1 == 2) && (d2 == 1 || d2 == 2) &&
      (d3 == 1 || d3 == 2) && (d4 == 1 || d4 == 2))

/-- The principal submatrix of `G` on the first row and four further rows: `12I + 2J` with `-2` on
the edges of `Γ`. -/
def M14 (b12 b13 b14 b23 b24 b34 : Bool) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![14, 2, 2, 2, 2;
     2, 14, bsgn b12, bsgn b13, bsgn b14;
     2, bsgn b12, 14, bsgn b23, bsgn b24;
     2, bsgn b13, bsgn b23, 14, bsgn b34;
     2, bsgn b14, bsgn b24, bsgn b34, 14]

/-- `27` pairs `(v, w)` of test vectors (computed with exact arithmetic). -/
def L14 : List ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  [(![-2, -2, 2, -2, -2], ![-2, 1, 2, 1, 1]),
   (![2, 2, 2, 0, 0], ![-1, 0, 1, 1, 1]),
   (![2, -1, 2, 2, 2], ![2, -2, -1, -1, -1]),
   (![0, 2, -2, 2, -2], ![1, -1, -1, -1, -1]),
   (![1, 1, 2, -1, 2], ![-2, 1, 1, 2, 1]),
   (![0, 2, -2, -2, 2], ![-2, 1, 1, 1, 1]),
   (![1, 1, 2, 2, -1], ![-2, 1, 1, 1, 2]),
   (![2, 2, 1, 2, 0], ![-1, 1, 1, -1, 2]),
   (![2, 1, 1, 2, 1], ![1, -2, -2, 1, 1]),
   (![2, 2, 1, 2, 2], ![1, 1, -2, 1, -2]),
   (![-2, 0, -2, -2, -2], ![-2, 2, 1, 2, -1]),
   (![2, 0, -2, 2, 2], ![-1, 1, 1, 1, 1]),
   (![2, 2, 2, 1, 0], ![-1, 1, -1, 1, 2]),
   (![2, 2, 2, 2, 2], ![-1, 2, -1, -1, 2]),
   (![2, 2, 2, 0, 2], ![-2, 2, 2, 2, -2]),
   (![-2, -2, 0, -2, -2], ![1, 1, -1, -1, -1]),
   (![0, 2, 2, -2, -2], ![-2, 1, 2, 1, 2]),
   (![2, 2, 1, 0, 2], ![1, -1, 1, -2, -1]),
   (![1, 1, 0, 1, 1], ![-1, 1, 2, 1, -1]),
   (![1, 0, 2, 2, 2], ![-1, 2, -1, 1, 1]),
   (![1, 1, 1, 1, 0], ![-1, -1, 1, 1, 2]),
   (![2, 2, 1, 1, 1], ![-1, -1, -1, 2, 2]),
   (![1, 1, 1, 1, 1], ![-1, 2, -1, 2, -1]),
   (![2, 1, 2, 2, 2], ![1, -2, -1, 1, -1]),
   (![1, 1, 0, 1, 1], ![-1, 1, 2, -1, 1]),
   (![-2, -2, -2, 0, -2], ![1, 1, -1, -1, -1]),
   (![-2, -2, -1, -2, -2], ![-1, -1, 2, 2, -1])]

/-- **The computation over the `64` graphs on four vertices.** Paper: "We computed the ratio of its
extreme eigenvalues for each of the `64` graphs on four vertices. It is less than `\tfrac{13}6` only
if the graph has no edge or is a path `P_4`." Here: either the graph has no edge or is a `P₄`, or a
pair of `L14` certifies `13 (wᵀMw)(vᵀv) ≤ 6 (vᵀMv)(wᵀw)`. -/
theorem cert14 : ∀ b12 b13 b14 b23 b24 b34 : Bool, ok4 b12 b13 b14 b23 b24 b34 = true ∨
    ∃ uw ∈ L14, 0 < uw.1 ⬝ᵥ uw.1 ∧ 0 < uw.2 ⬝ᵥ uw.2 ∧
      13 * ((uw.2 ⬝ᵥ (M14 b12 b13 b14 b23 b24 b34 *ᵥ uw.2)) * (uw.1 ⬝ᵥ uw.1)) ≤
        6 * ((uw.1 ⬝ᵥ (M14 b12 b13 b14 b23 b24 b34 *ᵥ uw.1)) * (uw.2 ⬝ᵥ uw.2)) := by
  decide +kernel

/-- **Four vertices.** If the first row has inner product `2` with four further rows, all inner
products are `±2` and `c² < 13/6`, then the graph on the four rows has no edge or is a `P₄`. -/
theorem four14 {B : Matrix (Fin 5) (Fin 5) ℝ} {c : ℝ} (hR : RayleighLe B c)
    (hsym : ∀ i j, B i j = B j i) (hdiag : ∀ i, B i i = 14) (h0 : ∀ k, k ≠ 0 → B 0 k = 2)
    (hval : ∀ i j, i ≠ j → B i j = 2 ∨ B i j = -2) (hc : 6 * c ^ 2 < 13) :
    ok4 (eb (B 1 2)) (eb (B 1 3)) (eb (B 1 4)) (eb (B 2 3)) (eb (B 2 4)) (eb (B 3 4)) = true := by
  have key : ∀ b12 b13 b14 b23 b24 b34 : Bool, B 1 2 = ((bsgn b12 : ℤ) : ℝ) →
      B 1 3 = ((bsgn b13 : ℤ) : ℝ) → B 1 4 = ((bsgn b14 : ℤ) : ℝ) →
      B 2 3 = ((bsgn b23 : ℤ) : ℝ) → B 2 4 = ((bsgn b24 : ℤ) : ℝ) →
      B 3 4 = ((bsgn b34 : ℤ) : ℝ) → ok4 b12 b13 b14 b23 b24 b34 = true := by
    intro b12 b13 b14 b23 b24 b34 e12 e13 e14 e23 e24 e34
    have f1 := h0 1 (by decide)
    have f2 := h0 2 (by decide)
    have f3 := h0 3 (by decide)
    have f4 := h0 4 (by decide)
    have g1 : B 1 0 = 2 := by rw [hsym]; exact f1
    have g2 : B 2 0 = 2 := by rw [hsym]; exact f2
    have g3 : B 3 0 = 2 := by rw [hsym]; exact f3
    have g4 : B 4 0 = 2 := by rw [hsym]; exact f4
    have e21 : B 2 1 = ((bsgn b12 : ℤ) : ℝ) := by rw [hsym]; exact e12
    have e31 : B 3 1 = ((bsgn b13 : ℤ) : ℝ) := by rw [hsym]; exact e13
    have e41 : B 4 1 = ((bsgn b14 : ℤ) : ℝ) := by rw [hsym]; exact e14
    have e32 : B 3 2 = ((bsgn b23 : ℤ) : ℝ) := by rw [hsym]; exact e23
    have e42 : B 4 2 = ((bsgn b24 : ℤ) : ℝ) := by rw [hsym]; exact e24
    have e43 : B 4 3 = ((bsgn b34 : ℤ) : ℝ) := by rw [hsym]; exact e34
    have hB : B = toR (M14 b12 b13 b14 b23 b24 b34) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [toR, M14, hdiag, f1, f2, f3, f4, g1, g2, g3, g4, e12, e13, e14, e23, e24, e34,
          e21, e31, e41, e32, e42, e43]
    rcases cert14 b12 b13 b14 b23 b24 b34 with h | ⟨uw, -, hu, hw, hcert⟩
    · exact h
    · have := rayleigh_cert hR _ hB uw.1 uw.2 6 13 (by norm_num) hu hw hcert
      push_cast at this
      linarith
  exact key _ _ _ _ _ _ (eq_bsgn (hval 1 2 (by decide))) (eq_bsgn (hval 1 3 (by decide)))
    (eq_bsgn (hval 1 4 (by decide))) (eq_bsgn (hval 2 3 (by decide)))
    (eq_bsgn (hval 2 4 (by decide))) (eq_bsgn (hval 3 4 (by decide)))

/-- The check on six vertices: `g6 = true` says "if every four vertices induce no edge or a `P₄`,
then there is no edge". -/
def g6 (e12 e13 e14 e15 e16 e23 e24 e25 e26 e34 e35 e36 e45 e46 e56 : Bool) : Bool :=
  !(ok4 e12 e13 e14 e23 e24 e34 && ok4 e12 e13 e15 e23 e25 e35 && ok4 e12 e13 e16 e23 e26 e36 &&
    ok4 e12 e14 e15 e24 e25 e45 && ok4 e12 e14 e16 e24 e26 e46 && ok4 e12 e15 e16 e25 e26 e56 &&
    ok4 e13 e14 e15 e34 e35 e45 && ok4 e13 e14 e16 e34 e36 e46 && ok4 e13 e15 e16 e35 e36 e56 &&
    ok4 e14 e15 e16 e45 e46 e56 && ok4 e23 e24 e25 e34 e35 e45 && ok4 e23 e24 e26 e34 e36 e46 &&
    ok4 e23 e25 e26 e35 e36 e56 && ok4 e24 e25 e26 e45 e46 e56 && ok4 e34 e35 e36 e45 e46 e56) ||
  !(e12 || e13 || e14 || e15 || e16 || e23 || e24 || e25 || e26 || e34 || e35 || e36 || e45 ||
      e46 || e56)

/-- **Six vertices.** Paper: "Suppose that `\Gamma` has an edge. [...] In both, the first, second,
fourth, and fifth vertices induce two disjoint edges, a contradiction. Hence `\Gamma` has no edge."
Checked over all `2¹⁵` graphs on six labelled vertices. -/
theorem graph6 : ∀ e12 e13 e14 e15 e16 e23 e24 e25 e26 e34 e35 e36 e45 e46 e56 : Bool,
    g6 e12 e13 e14 e15 e16 e23 e24 e25 e26 e34 e35 e36 e45 e46 e56 = true := by
  decide +kernel

theorem graph6_imp {e12 e13 e14 e15 e16 e23 e24 e25 e26 e34 e35 e36 e45 e46 e56 : Bool}
    (h1 : ok4 e12 e13 e14 e23 e24 e34 = true) (h2 : ok4 e12 e13 e15 e23 e25 e35 = true)
    (h3 : ok4 e12 e13 e16 e23 e26 e36 = true) (h4 : ok4 e12 e14 e15 e24 e25 e45 = true)
    (h5 : ok4 e12 e14 e16 e24 e26 e46 = true) (h6 : ok4 e12 e15 e16 e25 e26 e56 = true)
    (h7 : ok4 e13 e14 e15 e34 e35 e45 = true) (h8 : ok4 e13 e14 e16 e34 e36 e46 = true)
    (h9 : ok4 e13 e15 e16 e35 e36 e56 = true) (h10 : ok4 e14 e15 e16 e45 e46 e56 = true)
    (h11 : ok4 e23 e24 e25 e34 e35 e45 = true) (h12 : ok4 e23 e24 e26 e34 e36 e46 = true)
    (h13 : ok4 e23 e25 e26 e35 e36 e56 = true) (h14 : ok4 e24 e25 e26 e45 e46 e56 = true)
    (h15 : ok4 e34 e35 e36 e45 e46 e56 = true) :
    e12 = false ∧ e13 = false ∧ e14 = false ∧ e15 = false ∧ e16 = false ∧ e23 = false ∧
      e24 = false ∧ e25 = false ∧ e26 = false ∧ e34 = false ∧ e35 = false ∧ e36 = false ∧
      e45 = false ∧ e46 = false ∧ e56 = false := by
  have := graph6 e12 e13 e14 e15 e16 e23 e24 e25 e26 e34 e35 e36 e45 e46 e56
  simp only [g6, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Bool.and_self,
    Bool.not_true, Bool.false_or, Bool.not_eq_eq_eq_not, Bool.or_eq_false_iff, and_assoc]
    at this
  exact this

/-- Four of the six rows, together with the first row. -/
theorem sub14 {B : Matrix (Fin 7) (Fin 7) ℝ} {c : ℝ} (hR : RayleighLe B c)
    (hsym : ∀ i j, B i j = B j i) (hdiag : ∀ i, B i i = 14) (h0 : ∀ k, k ≠ 0 → B 0 k = 2)
    (hval : ∀ i j, i ≠ j → B i j = 2 ∨ B i j = -2) (hc : 6 * c ^ 2 < 13) (a b d e : Fin 7)
    (hf : Function.Injective ![0, a, b, d, e]) :
    ok4 (eb (B a b)) (eb (B a d)) (eb (B a e)) (eb (B b d)) (eb (B b e)) (eb (B d e)) = true := by
  have := four14 (B := B.submatrix ![0, a, b, d, e] ![0, a, b, d, e]) (rayleighLe_submatrix hR hf)
    (fun i j => hsym _ _) (fun i => hdiag _)
    (fun k hk => h0 _ fun h => hk (hf (h.trans (rfl : (0 : Fin 7) = ![0, a, b, d, e] 0))))
    (fun i j hij => hval _ _ (hf.ne hij)) hc
  exact this

/-- The Gram matrix `12I + 2J` of seven rows. -/
def M7two : Matrix (Fin 7) (Fin 7) ℤ := Matrix.of fun i j => if i = j then 14 else 2

/-- **Seven normalised rows.** If the seven rows have inner products `±2`, and the first has inner
product `2` with the other six, then `c² ≥ 13/6`. -/
theorem seven_core {B : Matrix (Fin 7) (Fin 7) ℝ} {c : ℝ} (hR : RayleighLe B c)
    (hsym : ∀ i j, B i j = B j i) (hdiag : ∀ i, B i i = 14) (h0 : ∀ k, k ≠ 0 → B 0 k = 2)
    (hval : ∀ i j, i ≠ j → B i j = 2 ∨ B i j = -2) : 13 ≤ 6 * c ^ 2 := by
  by_contra hc'
  have hc : 6 * c ^ 2 < 13 := lt_of_not_le hc'
  have s1234 := sub14 hR hsym hdiag h0 hval hc 1 2 3 4 (by decide)
  have s1235 := sub14 hR hsym hdiag h0 hval hc 1 2 3 5 (by decide)
  have s1236 := sub14 hR hsym hdiag h0 hval hc 1 2 3 6 (by decide)
  have s1245 := sub14 hR hsym hdiag h0 hval hc 1 2 4 5 (by decide)
  have s1246 := sub14 hR hsym hdiag h0 hval hc 1 2 4 6 (by decide)
  have s1256 := sub14 hR hsym hdiag h0 hval hc 1 2 5 6 (by decide)
  have s1345 := sub14 hR hsym hdiag h0 hval hc 1 3 4 5 (by decide)
  have s1346 := sub14 hR hsym hdiag h0 hval hc 1 3 4 6 (by decide)
  have s1356 := sub14 hR hsym hdiag h0 hval hc 1 3 5 6 (by decide)
  have s1456 := sub14 hR hsym hdiag h0 hval hc 1 4 5 6 (by decide)
  have s2345 := sub14 hR hsym hdiag h0 hval hc 2 3 4 5 (by decide)
  have s2346 := sub14 hR hsym hdiag h0 hval hc 2 3 4 6 (by decide)
  have s2356 := sub14 hR hsym hdiag h0 hval hc 2 3 5 6 (by decide)
  have s2456 := sub14 hR hsym hdiag h0 hval hc 2 4 5 6 (by decide)
  have s3456 := sub14 hR hsym hdiag h0 hval hc 3 4 5 6 (by decide)
  obtain ⟨g12, g13, g14, g15, g16, g23, g24, g25, g26, g34, g35, g36, g45, g46, g56⟩ :=
    graph6_imp s1234 s1235 s1236 s1245 s1246 s1256 s1345 s1346 s1356 s1456 s2345 s2346 s2356
      s2456 s3456
  have t12 := eb_false (hval 1 2 (by decide)) g12
  have t13 := eb_false (hval 1 3 (by decide)) g13
  have t14 := eb_false (hval 1 4 (by decide)) g14
  have t15 := eb_false (hval 1 5 (by decide)) g15
  have t16 := eb_false (hval 1 6 (by decide)) g16
  have t23 := eb_false (hval 2 3 (by decide)) g23
  have t24 := eb_false (hval 2 4 (by decide)) g24
  have t25 := eb_false (hval 2 5 (by decide)) g25
  have t26 := eb_false (hval 2 6 (by decide)) g26
  have t34 := eb_false (hval 3 4 (by decide)) g34
  have t35 := eb_false (hval 3 5 (by decide)) g35
  have t36 := eb_false (hval 3 6 (by decide)) g36
  have t45 := eb_false (hval 4 5 (by decide)) g45
  have t46 := eb_false (hval 4 6 (by decide)) g46
  have t56 := eb_false (hval 5 6 (by decide)) g56
  have u12 : B 2 1 = 2 := by rw [hsym]; exact t12
  have u13 : B 3 1 = 2 := by rw [hsym]; exact t13
  have u14 : B 4 1 = 2 := by rw [hsym]; exact t14
  have u15 : B 5 1 = 2 := by rw [hsym]; exact t15
  have u16 : B 6 1 = 2 := by rw [hsym]; exact t16
  have u23 : B 3 2 = 2 := by rw [hsym]; exact t23
  have u24 : B 4 2 = 2 := by rw [hsym]; exact t24
  have u25 : B 5 2 = 2 := by rw [hsym]; exact t25
  have u26 : B 6 2 = 2 := by rw [hsym]; exact t26
  have u34 : B 4 3 = 2 := by rw [hsym]; exact t34
  have u35 : B 5 3 = 2 := by rw [hsym]; exact t35
  have u36 : B 6 3 = 2 := by rw [hsym]; exact t36
  have u45 : B 5 4 = 2 := by rw [hsym]; exact t45
  have u46 : B 6 4 = 2 := by rw [hsym]; exact t46
  have u56 : B 6 5 = 2 := by rw [hsym]; exact t56
  have f1 := h0 1 (by decide)
  have f2 := h0 2 (by decide)
  have f3 := h0 3 (by decide)
  have f4 := h0 4 (by decide)
  have f5 := h0 5 (by decide)
  have f6 := h0 6 (by decide)
  have k1 : B 1 0 = 2 := by rw [hsym]; exact f1
  have k2 : B 2 0 = 2 := by rw [hsym]; exact f2
  have k3 : B 3 0 = 2 := by rw [hsym]; exact f3
  have k4 : B 4 0 = 2 := by rw [hsym]; exact f4
  have k5 : B 5 0 = 2 := by rw [hsym]; exact f5
  have k6 : B 6 0 = 2 := by rw [hsym]; exact f6
  have hB : B = toR M7two := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toR, M7two, hdiag, f1, f2, f3, f4, f5, f6, k1, k2, k3, k4, k5, k6, t12, t13, t14, t15,
        t16, t23, t24, t25, t26, t34, t35, t36, t45, t46, t56, u12, u13, u14, u15, u16, u23, u24,
        u25, u26, u34, u35, u36, u45, u46, u56]
  have := rayleigh_cert hR _ hB ![1, 1, 1, 1, 1, 1, 1] ![0, 1, -1, 0, 0, 0, 0] 6 13 (by norm_num)
    (by decide) (by decide) (by decide)
  push_cast at this
  exact hc' (by linarith)

/-- **Normalisation.** Paper: "We negate rows so that the first of the seven rows has inner product
`2` with the other six". -/
theorem seven_switch {B : Matrix (Fin 7) (Fin 7) ℝ} {c : ℝ} (hR : RayleighLe B c)
    (hsym : ∀ i j, B i j = B j i) (hdiag : ∀ i, B i i = 14)
    (hval : ∀ i j, i ≠ j → B i j = 2 ∨ B i j = -2) : 13 ≤ 6 * c ^ 2 := by
  obtain ⟨s, hs_def⟩ : ∃ s : Fin 7 → ℝ, s = fun k => if k = 0 then 1 else B 0 k / 2 := ⟨_, rfl⟩
  have hs : ∀ k, s k = 1 ∨ s k = -1 := by
    intro k
    by_cases hk : k = 0
    · left; simp [hs_def, hk]
    · rcases hval 0 k (Ne.symm hk) with h | h <;> simp [hs_def, hk, h]
  have hss : ∀ k, s k * s k = 1 := fun k => by rcases hs k with h | h <;> rw [h] <;> norm_num
  refine seven_core (rayleighLe_switch hR hs) ?_ ?_ ?_ ?_
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

/-- **Order 14, lower bound.** Every `14 × 14` sign matrix with `κ(A) ≤ c` has `c² ≥ 13/6`. -/
theorem order14_lower {A : Matrix (Fin 14) (Fin 14) ℝ} (hA : IsSign A) {c : ℝ} (h : CondLe A c) :
    13 ≤ 6 * c ^ 2 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf, hpar⟩ := exists_seven_same_parity A
  have hR7 := rayleighLe_submatrix (rayleighLe_of_condLe h) hf
  have hsym : ∀ i j, (A * Aᵀ).submatrix f f i j = (A * Aᵀ).submatrix f f j i :=
    fun i j => gram_symm A _ _
  have hdiag : ∀ i, (A * Aᵀ).submatrix f f i i = 14 := fun i => by
    simp only [submatrix_apply]
    rw [gram_diag hA]
    norm_num
  have hval : ∀ i j, i ≠ j →
      (A * Aᵀ).submatrix f f i j = 2 ∨ (A * Aᵀ).submatrix f f i j = -2 := by
    intro i j hij
    obtain ⟨g, hg, hmod⟩ := lem_tools_one hA (f i) (f j) (hpar i j)
    obtain ⟨h1, h2⟩ := rayleigh_pair hR7 hsym hdiag hij
    simp only [submatrix_apply] at h1 h2 ⊢
    rw [hg] at h1 h2 ⊢
    have hg14 : |g| < 14 := by exact_mod_cast h2
    rw [abs_lt] at hg14
    unfold Int.ModEq at hmod
    have : g = -10 ∨ g = -6 ∨ g = -2 ∨ g = 2 ∨ g = 6 ∨ g = 10 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num at h1
      nlinarith
    · norm_num at h1
      nlinarith
    · right; norm_num
    · left; norm_num
    · norm_num at h1
      nlinarith
    · norm_num at h1
      nlinarith
  exact absurd (seven_switch hR7 hsym hdiag hval) (not_le.2 hlt)

/-- **Theorem `thm:small`, `h(14) = √(13/6)`.** The matrix `A₁₄` has `κ(A₁₄) ≤ √(13/6)`, and every
`14 × 14` sign matrix with `κ(A) ≤ c'`, `c' ≥ 0`, has `√(13/6) ≤ c'`. -/
theorem hval_14 : HVal 14 (Real.sqrt (13 / 6)) := by
  refine ⟨⟨A14, isSign_A14, condLe_A14⟩, fun A hA c' hc' h => ?_⟩
  have := order14_lower hA h
  calc Real.sqrt (13 / 6) ≤ Real.sqrt (c' ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = c' := Real.sqrt_sq hc'

end SignCond
