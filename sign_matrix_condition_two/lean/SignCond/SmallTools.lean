import SignCond.DoublingTau

/-!
# Section `sec:small`: the exact value `h(n) = c`, and Lemma `lem:tools`

Paper, Section `sec:small` ("Exact values in small dimensions"): "Throughout, `A` is an invertible
sign matrix of order `n` and `G=AA^\top` is its Gram matrix [...] The diagonal entries of `G` are
`n`. Negating a row of `A` does not change `\kappa(A)`, and it negates the corresponding row and
column of `G`."

* `HVal n c`: the paper's `h(n) = c` (some `n × n` sign matrix has `κ ≤ c`, and none has `κ < c`).
* `negCount A i`: the number of entries `-1` in row `i`.
* `gram_entry_formula`: the inner product of rows `i, j` is `n - 2X_i - 2X_j + 4P`, where `X_i` is
  the number of `-1` in row `i` and `P` the number of common positions of `-1`.
* `lem_tools_one` (Lemma `lem:tools`, part 1) and `lem_tools_two` (part 2), combined in `lem_tools`.
* `RayleighLe B c`: the Rayleigh form of part 2 for a symmetric matrix `B`; it passes to principal
  submatrices (`rayleighLe_submatrix`), is invariant under switching (`rayleighLe_switch`), and is
  used through integer test vectors (`rayleigh_cert`) and for pairs of rows (`rayleigh_pair`).
* `isSign_diagonal_mul`, `condLe_diagonal_mul`, `isSign_submatrix_rows`, `condLe_submatrix_rows`:
  negating and permuting rows preserve `IsSign` and `CondLe`.
* `exists_even_rows`: for odd `n`, rows can be negated so that every row has an even number of
  entries `-1`.

No spectral theory is used: every eigenvalue comparison of the paper becomes the Rayleigh form at
explicit vectors.
-/

open Matrix

namespace SignCond

/-- The paper's `h(n) = c`: some `n × n` sign matrix satisfies `κ(A) ≤ c` (the window `CondLe A c`),
and every `n × n` sign matrix satisfying a window of ratio `c' ≥ 0` has `c ≤ c'`. -/
def HVal (n : ℕ) (c : ℝ) : Prop :=
  (∃ A : Matrix (Fin n) (Fin n) ℝ, IsSign A ∧ CondLe A c) ∧
    ∀ A : Matrix (Fin n) (Fin n) ℝ, IsSign A → ∀ c' : ℝ, 0 ≤ c' → CondLe A c' → c ≤ c'

/-! ### Part 1: the inner products modulo `4` -/

section PartOne

variable {n : ℕ}

/-- The number of entries `-1` in row `i` of `A`. -/
noncomputable def negCount (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun k => A i k = -1).card

/-- The number of positions where rows `i` and `j` both have the entry `-1`. -/
noncomputable def negCommon (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun k => A i k = -1 ∧ A j k = -1).card

theorem sign_prod_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSign A) (i j k : Fin n) :
    A i k * A j k = 1 - 2 * (if A i k = -1 then (1 : ℝ) else 0) -
      2 * (if A j k = -1 then (1 : ℝ) else 0) +
      4 * (if A i k = -1 ∧ A j k = -1 then (1 : ℝ) else 0) := by
  rcases hA i k with h1 | h1 <;> rcases hA j k with h2 | h2 <;> simp [h1, h2] <;> norm_num

/-- The inner product of two rows of a sign matrix: `n - 2X_i - 2X_j + 4P`. -/
theorem gram_entry_formula {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSign A) (i j : Fin n) :
    (A * Aᵀ) i j = (((n : ℤ) - 2 * negCount A i - 2 * negCount A j + 4 * negCommon A i j : ℤ) : ℝ) := by
  rw [mul_apply]
  simp only [transpose_apply, sign_prod_eq hA i j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Finset.sum_boole, negCount, negCommon]
  push_cast
  ring

/-- **Lemma `lem:tools`, part 1.** "If two rows of `A` have numbers of entries `-1` of the same
parity, then their inner product is congruent to `n` modulo `4`." The inner product is an integer
`g` with `g ≡ n (mod 4)`. -/
theorem lem_tools_one {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSign A) (i j : Fin n)
    (h : negCount A i % 2 = negCount A j % 2) :
    ∃ g : ℤ, (A * Aᵀ) i j = g ∧ g ≡ n [ZMOD 4] := by
  refine ⟨_, gram_entry_formula hA i j, ?_⟩
  unfold Int.ModEq
  omega

/-- Negating row `i` of a sign matrix replaces the number of its entries `-1` by `n` minus it. -/
theorem negCount_neg_row {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSign A) (i : Fin n) :
    (Finset.univ.filter fun k => -A i k = -1).card + negCount A i = n := by
  have e : (Finset.univ.filter fun k => -A i k = -1) =
      Finset.univ.filter fun k => ¬ (A i k = -1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_eq_iff_eq_neg, neg_neg]
    rcases hA i k with h | h <;> rw [h] <;> norm_num
  rw [e, negCount, add_comm, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ,
    Fintype.card_fin]

/-- The signs that make every row even: `s i = 1` if row `i` has an even number of entries `-1`,
and `s i = -1` otherwise. -/
noncomputable def evenSigns (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  if negCount A i % 2 = 0 then 1 else -1

theorem evenSigns_sq (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    evenSigns A i = 1 ∨ evenSigns A i = -1 := by
  unfold evenSigns; split_ifs <;> simp

/-- Paper: "For odd `n` we may negate rows so that every row has an even number of entries `-1`." -/
theorem negCount_evenSigns {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSign A) (hn : n % 2 = 1)
    (i : Fin n) : negCount (diagonal (evenSigns A) * A) i % 2 = 0 := by
  have hrow : ∀ k, (diagonal (evenSigns A) * A) i k = evenSigns A i * A i k := fun k =>
    diagonal_mul _ _ _ _
  unfold negCount
  simp only [hrow]
  unfold evenSigns
  split_ifs with h
  · simp only [one_mul]; exact h
  · have := negCount_neg_row hA i
    simp only [neg_one_mul]
    omega

end PartOne

/-! ### Negating and permuting rows -/

section Invariance

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Negating rows (multiplying on the left by a diagonal `±1` matrix) preserves `IsSign`. -/
theorem isSign_diagonal_mul {A : Matrix m m ℝ} (hA : IsSign A) {s : m → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1) : IsSign (diagonal s * A) := by
  intro i j
  rw [diagonal_mul]
  rcases hs i with h | h <;> rcases hA i j with h' | h' <;> rw [h, h'] <;> norm_num

/-- Negating rows preserves `CondLe`: `(DA)(DA)ᵀ = D (AAᵀ) D` with `D² = 1`. -/
theorem condLe_diagonal_mul {A : Matrix m m ℝ} {s : m → ℝ} (hs : ∀ i, s i = 1 ∨ s i = -1)
    {c : ℝ} (h : CondLe A c) : CondLe (diagonal s * A) c := by
  obtain ⟨t, ht, h1, h2⟩ := h
  have hss : (fun i => s i * s i) = fun _ => (1 : ℝ) :=
    funext fun i => by rcases hs i with h | h <;> rw [h] <;> norm_num
  have hDD : diagonal s * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, hss, diagonal_one]
  have hDT : (diagonal s)ᴴ = diagonal s := by
    rw [conjTranspose_eq_transpose_of_trivial, diagonal_transpose]
  have hG : diagonal s * A * (diagonal s * A)ᵀ = (diagonal s)ᴴ * (A * Aᵀ) * diagonal s := by
    rw [hDT, transpose_mul, diagonal_transpose, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc]
  have hone : ∀ r : ℝ, r • (1 : Matrix m m ℝ) = (diagonal s)ᴴ * (r • 1) * diagonal s := by
    intro r
    rw [hDT, Matrix.mul_smul, mul_one, Matrix.smul_mul, hDD]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hG, hone t, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact h1.conjTranspose_mul_mul_same _
  · rw [hG, hone (c ^ 2 * t), ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact h2.conjTranspose_mul_mul_same _

omit [Fintype m] [DecidableEq m] in
/-- Permuting rows preserves `IsSign`. -/
theorem isSign_submatrix_rows {A : Matrix m m ℝ} (hA : IsSign A) (σ : Equiv.Perm m) :
    IsSign (A.submatrix σ id) :=
  fun i j => hA (σ i) j

/-- Permuting rows preserves `CondLe`: the Gram matrix becomes `(AAᵀ).submatrix σ σ`. -/
theorem condLe_submatrix_rows {A : Matrix m m ℝ} (σ : Equiv.Perm m) {c : ℝ} (h : CondLe A c) :
    CondLe (A.submatrix σ id) c := by
  obtain ⟨t, ht, h1, h2⟩ := h
  have hG : A.submatrix σ id * (A.submatrix σ id)ᵀ = (A * Aᵀ).submatrix σ σ := by
    rw [transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id]
  have e1 : (A * Aᵀ).submatrix σ σ - t • (1 : Matrix m m ℝ) =
      (A * Aᵀ - t • (1 : Matrix m m ℝ)).submatrix σ σ := by
    ext i j; simp [one_apply]
  have e2 : (c ^ 2 * t) • (1 : Matrix m m ℝ) - (A * Aᵀ).submatrix σ σ =
      ((c ^ 2 * t) • (1 : Matrix m m ℝ) - A * Aᵀ).submatrix σ σ := by
    ext i j; simp [one_apply]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hG, e1]
    exact h1.submatrix σ
  · rw [hG, e2]
    exact h2.submatrix σ

end Invariance

/-- Paper: "For odd `n` we may negate rows so that every row has an even number of entries `-1`":
the normalised matrix is a sign matrix with the same windows, all of whose rows are even. -/
theorem exists_even_rows {n : ℕ} (hn : n % 2 = 1) {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSign A) :
    ∃ A' : Matrix (Fin n) (Fin n) ℝ, IsSign A' ∧ (∀ c, CondLe A c → CondLe A' c) ∧
      ∀ i, negCount A' i % 2 = 0 :=
  ⟨_, isSign_diagonal_mul hA (evenSigns_sq A), fun _ h => condLe_diagonal_mul (evenSigns_sq A) h,
    negCount_evenSigns hA hn⟩

/-! ### Part 2: the Rayleigh form -/

section PartTwo

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The Rayleigh form of Lemma `lem:tools`, part 2, for a matrix `B` (to be the Gram matrix):
`w ⬝ᵥ Bw > 0` for `w ≠ 0`, and `(vᵀBv)(wᵀw) ≤ c² (wᵀBw)(vᵀv)` for all `v` and all `w ≠ 0`. -/
def RayleighLe (B : Matrix m m ℝ) (c : ℝ) : Prop :=
  ∀ v w : m → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (B *ᵥ w) ∧
    (v ⬝ᵥ (B *ᵥ v)) * (w ⬝ᵥ w) ≤ c ^ 2 * (w ⬝ᵥ (B *ᵥ w)) * (v ⬝ᵥ v)

omit [DecidableEq m] in
theorem dotProduct_self_nonneg' (v : m → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

omit [DecidableEq m] in
theorem dotProduct_self_pos' {v : m → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dotProduct_self_nonneg' v) (fun h => hv (dotProduct_self_eq_zero.1 h.symm))

/-- `CondLe A c` gives the Rayleigh form for `G = AAᵀ`: the quotient `vᵀGv / vᵀv` lies between
`t` and `c²t`. -/
theorem rayleighLe_of_condLe {A : Matrix m m ℝ} {c : ℝ} (h : CondLe A c) :
    RayleighLe (A * Aᵀ) c := by
  obtain ⟨t, ht, hx⟩ := (condLe_iff A c).1 h
  intro v w hw
  have hw' := dotProduct_self_pos' hw
  have hvv := dotProduct_self_nonneg' v
  rw [dotProduct_gram_mulVec, dotProduct_gram_mulVec]
  have h1 := (hx v).2
  have h2 := (hx w).1
  refine ⟨lt_of_lt_of_le (mul_pos ht hw') h2, ?_⟩
  calc (Aᵀ *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ v) * (w ⬝ᵥ w) ≤ (c ^ 2 * t * (v ⬝ᵥ v)) * (w ⬝ᵥ w) :=
        mul_le_mul_of_nonneg_right h1 hw'.le
    _ = c ^ 2 * (v ⬝ᵥ v) * (t * (w ⬝ᵥ w)) := by ring
    _ ≤ c ^ 2 * (v ⬝ᵥ v) * ((Aᵀ *ᵥ w) ⬝ᵥ (Aᵀ *ᵥ w)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg c) hvv)
    _ = _ := by ring

/-! #### Vectors supported on a few coordinates -/

/-- The vector of `ℝ^m` with entries `u k` at the positions `f k` (and `0` elsewhere). -/
def extV {k : ℕ} (f : Fin k → m) (u : Fin k → ℝ) : m → ℝ :=
  fun x => ∑ a, if f a = x then u a else 0

theorem sum_mul_extV {k : ℕ} (f : Fin k → m) (g : m → ℝ) (u : Fin k → ℝ) :
    ∑ y, g y * extV f u y = ∑ b, g (f b) * u b := by
  simp only [extV, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem bilin_extV {k : ℕ} (B : Matrix m m ℝ) (f : Fin k → m) (u w : Fin k → ℝ) :
    extV f u ⬝ᵥ (B *ᵥ extV f w) = ∑ a, ∑ b, u a * B (f a) (f b) * w b := by
  have h1 : ∀ x, (B *ᵥ extV f w) x = ∑ b, B x (f b) * w b := fun x => sum_mul_extV f _ w
  rw [dotProduct_comm, dotProduct]
  simp only [h1]
  rw [sum_mul_extV f (fun x => ∑ b, B x (f b) * w b) u]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The quadratic form at `extV f u` is the quadratic form of the principal submatrix on `f`. -/
theorem quad_extV {k : ℕ} (B : Matrix m m ℝ) (f : Fin k → m) (u : Fin k → ℝ) :
    extV f u ⬝ᵥ (B *ᵥ extV f u) = u ⬝ᵥ (B.submatrix f f *ᵥ u) := by
  rw [bilin_extV]
  simp only [dotProduct, mulVec, submatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem norm_extV {k : ℕ} {f : Fin k → m} (hf : Function.Injective f) (u : Fin k → ℝ) :
    extV f u ⬝ᵥ extV f u = u ⬝ᵥ u := by
  have h := bilin_extV (1 : Matrix m m ℝ) f u u
  rw [one_mulVec] at h
  rw [h]
  simp only [one_apply, hf.eq_iff, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]

theorem extV_ne_zero {k : ℕ} {f : Fin k → m} (hf : Function.Injective f) {u : Fin k → ℝ}
    (hu : u ≠ 0) : extV f u ≠ 0 := by
  intro h
  apply hu
  have := norm_extV hf u
  rw [h, zero_dotProduct] at this
  exact dotProduct_self_eq_zero.1 this.symm

/-- **Principal submatrices.** The Rayleigh form passes to every principal submatrix (the paper's
"we apply it to eigenvectors of `B` [...] extended by zero"). -/
theorem rayleighLe_submatrix {B : Matrix m m ℝ} {c : ℝ} (h : RayleighLe B c) {k : ℕ}
    {f : Fin k → m} (hf : Function.Injective f) : RayleighLe (B.submatrix f f) c := by
  intro u w hw
  have := h (extV f u) (extV f w) (extV_ne_zero hf hw)
  rwa [quad_extV, quad_extV, norm_extV hf, norm_extV hf] at this

omit [DecidableEq m] in
/-- **Switching.** Negating rows of `A` negates the corresponding rows and columns of `G`; the
Rayleigh form is invariant. -/
theorem rayleighLe_switch {B : Matrix m m ℝ} {c : ℝ} (h : RayleighLe B c) {s : m → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1) : RayleighLe (Matrix.of fun i j => s i * s j * B i j) c := by
  have hss : ∀ i, s i * s i = 1 := fun i => by rcases hs i with h | h <;> rw [h] <;> norm_num
  have hq : ∀ v : m → ℝ, v ⬝ᵥ ((Matrix.of fun i j => s i * s j * B i j) *ᵥ v) =
      (fun i => s i * v i) ⬝ᵥ (B *ᵥ fun i => s i * v i) := by
    intro v
    simp only [dotProduct, mulVec, of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hn : ∀ v : m → ℝ, (fun i => s i * v i) ⬝ᵥ (fun i => s i * v i) = v ⬝ᵥ v := by
    intro v
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (v i * v i) * hss i
  intro v w hw
  have hw' : (fun i => s i * w i) ≠ 0 := by
    intro h0
    apply hw
    funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply] at this
    have h2 : s i * (s i * w i) = 0 := by rw [this, mul_zero]
    rw [← mul_assoc, hss, one_mul] at h2
    exact h2
  have := h (fun i => s i * v i) (fun i => s i * w i) hw'
  rwa [hn, hn, ← hq, ← hq] at this

/-! #### Integer test vectors -/

omit [DecidableEq m] in
theorem cast_dotProduct (u w : m → ℤ) :
    (fun i => (u i : ℝ)) ⬝ᵥ (fun i => (w i : ℝ)) = ((u ⬝ᵥ w : ℤ) : ℝ) := by
  simp only [dotProduct]
  push_cast
  rfl

omit [DecidableEq m] in
theorem cast_quad (M : Matrix m m ℤ) (u : m → ℤ) :
    (fun i => (u i : ℝ)) ⬝ᵥ (toR M *ᵥ fun i => (u i : ℝ)) = ((u ⬝ᵥ (M *ᵥ u) : ℤ) : ℝ) := by
  simp only [dotProduct, mulVec, toR, map_apply]
  push_cast
  rfl

omit [DecidableEq m] in
/-- **Integer certificates.** If `B = M` is an integer matrix and the integer vectors `u, w ≠ 0`
satisfy `q (wᵀMw)(uᵀu) ≤ p (uᵀMu)(wᵀw)` with `p > 0`, then the Rayleigh form forces `q ≤ p c²`. -/
theorem rayleigh_cert {B : Matrix m m ℝ} {c : ℝ} (h : RayleighLe B c) (M : Matrix m m ℤ)
    (hB : B = toR M) (u w : m → ℤ) (p q : ℤ) (hp : 0 < p) (hu : 0 < u ⬝ᵥ u)
    (hw : 0 < w ⬝ᵥ w)
    (hcert : q * ((w ⬝ᵥ (M *ᵥ w)) * (u ⬝ᵥ u)) ≤ p * ((u ⬝ᵥ (M *ᵥ u)) * (w ⬝ᵥ w))) :
    (q : ℝ) ≤ p * c ^ 2 := by
  have hW : (fun i => (w i : ℝ)) ≠ 0 := by
    intro h0
    have := cast_dotProduct w w
    rw [h0, zero_dotProduct] at this
    have : ((w ⬝ᵥ w : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
    simp_all
  obtain ⟨hpos, hle⟩ := h (fun i => (u i : ℝ)) (fun i => (w i : ℝ)) hW
  rw [hB, cast_quad, cast_quad, cast_dotProduct, cast_dotProduct] at hle
  rw [hB, cast_quad] at hpos
  have hu' : (0 : ℝ) < ((u ⬝ᵥ u : ℤ) : ℝ) := by exact_mod_cast hu
  have hc' : (q : ℝ) * (((w ⬝ᵥ (M *ᵥ w) : ℤ) : ℝ) * ((u ⬝ᵥ u : ℤ) : ℝ)) ≤
      (p : ℝ) * (((u ⬝ᵥ (M *ᵥ u) : ℤ) : ℝ) * ((w ⬝ᵥ w : ℤ) : ℝ)) := by exact_mod_cast hcert
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have key : (q : ℝ) * (((w ⬝ᵥ (M *ᵥ w) : ℤ) : ℝ) * ((u ⬝ᵥ u : ℤ) : ℝ)) ≤
      (p * c ^ 2) * (((w ⬝ᵥ (M *ᵥ w) : ℤ) : ℝ) * ((u ⬝ᵥ u : ℤ) : ℝ)) := by
    calc _ ≤ _ := hc'
      _ ≤ (p : ℝ) * (c ^ 2 * ((w ⬝ᵥ (M *ᵥ w) : ℤ) : ℝ) * ((u ⬝ᵥ u : ℤ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hle hp'.le
      _ = _ := by ring
  exact le_of_mul_le_mul_right key (mul_pos hpos hu')

omit [DecidableEq m] in
/-- The same, with the certificate given as a member of a list of pairs of test vectors (so that a
finite family of patterns can be checked at once by `decide`). -/
theorem rayleigh_cert_list {B : Matrix m m ℝ} {c : ℝ} (h : RayleighLe B c) (M : Matrix m m ℤ)
    (hB : B = toR M) (p q : ℤ) (hp : 0 < p) (L : List ((m → ℤ) × (m → ℤ)))
    (hL : ∃ uw ∈ L, 0 < uw.1 ⬝ᵥ uw.1 ∧ 0 < uw.2 ⬝ᵥ uw.2 ∧
      q * ((uw.2 ⬝ᵥ (M *ᵥ uw.2)) * (uw.1 ⬝ᵥ uw.1)) ≤
        p * ((uw.1 ⬝ᵥ (M *ᵥ uw.1)) * (uw.2 ⬝ᵥ uw.2))) :
    (q : ℝ) ≤ p * c ^ 2 := by
  obtain ⟨⟨u, w⟩, -, hu, hw, hc⟩ := hL
  exact rayleigh_cert h M hB u w p q hp hu hw hc

/-! #### Two rows -/

omit [Fintype m] [DecidableEq m] in
theorem quad_two (B : Matrix m m ℝ) (i j : m) (a b : ℝ) :
    ![a, b] ⬝ᵥ (B.submatrix ![i, j] ![i, j] *ᵥ ![a, b]) =
      a * a * B i i + a * b * B i j + b * a * B j i + b * b * B j j := by
  simp only [dotProduct, mulVec, Fin.sum_univ_two, submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  ring

omit [Fintype m] [DecidableEq m] in
theorem injective_two {i j : m} (hij : i ≠ j) : Function.Injective ![i, j] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- **Two rows.** Paper: "The principal submatrix formed by two rows with inner product `g` has
eigenvalues `n ± g`", so `κ(A)² ≥ (n+|g|)/(n-|g|)`; here `d + |g| ≤ c² (d - |g|)` and `|g| < d`. -/
theorem rayleigh_pair {B : Matrix m m ℝ} {c : ℝ} (h : RayleighLe B c)
    (hsym : ∀ i j, B i j = B j i) {d : ℝ} (hd : ∀ i, B i i = d) {i j : m} (hij : i ≠ j) :
    d + |B i j| ≤ c ^ 2 * (d - |B i j|) ∧ |B i j| < d := by
  have hR := rayleighLe_submatrix h (injective_two hij)
  have two : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] = 2 := by
    simp [dotProduct, Fin.sum_univ_two]; norm_num
  have two' : (![1, -1] : Fin 2 → ℝ) ⬝ᵥ ![1, -1] = 2 := by
    simp [dotProduct, Fin.sum_univ_two]; norm_num
  have ne1 : (![1, 1] : Fin 2 → ℝ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
  have ne2 : (![1, -1] : Fin 2 → ℝ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
  rcases le_or_lt 0 (B i j) with hg | hg
  · obtain ⟨hp, hl⟩ := hR ![1, 1] ![1, -1] ne2
    rw [quad_two, quad_two, two, two', hd, hd, hsym j i] at hl
    rw [quad_two, hd, hd, hsym j i] at hp
    rw [abs_of_nonneg hg]
    constructor <;> nlinarith
  · obtain ⟨hp, hl⟩ := hR ![1, -1] ![1, 1] ne1
    rw [quad_two, quad_two, two, two', hd, hd, hsym j i] at hl
    rw [quad_two, hd, hd, hsym j i] at hp
    rw [abs_of_neg hg]
    constructor <;> nlinarith

end PartTwo

/-- Useful form of the diagonal: the Gram matrix of a sign matrix of order `n` has diagonal `n`. -/
theorem gram_diag {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSign A) (i : Fin n) :
    (A * Aᵀ) i i = n := by
  rw [gram_entry_formula hA]
  simp [negCommon, negCount]
  ring

theorem gram_symm {n : Type*} [Fintype n] (A : Matrix n n ℝ) (i j : n) :
    (A * Aᵀ) i j = (A * Aᵀ) j i := by
  rw [← transpose_apply (A * Aᵀ) j i, transpose_gram]

/-- **Lemma `lem:tools`, part 2.** "For all nonzero `v,w\in\RR^n`, we have
`\kappa(A)^2\ge\dfrac{v^\top Gv}{v^\top v}\cdot\dfrac{w^\top w}{w^\top Gw}`. In particular,
`\kappa(A)^2\ge\lambda_{\max}(B)/\lambda_{\min}(B)` for every principal submatrix `B` of `G`, and
`\kappa(A)^2\ge(n+|g|)/(n-|g|)` for every off-diagonal entry `g` of `G`."

With `κ(A) ≤ c` as `CondLe A c`: the Rayleigh form for `G = AAᵀ` (with `wᵀGw > 0`), the same for
every principal submatrix `G.submatrix f f` (`f` injective; this is the vector form of the
eigenvalue statement), and `n + |g| ≤ c²(n - |g|)`, `|g| < n` for `g = G i j`, `i ≠ j`. -/
theorem lem_tools_two {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSign A) {c : ℝ}
    (h : CondLe A c) :
    (∀ v w : Fin n → ℝ, w ≠ 0 → 0 < w ⬝ᵥ ((A * Aᵀ) *ᵥ w) ∧
      (v ⬝ᵥ ((A * Aᵀ) *ᵥ v)) * (w ⬝ᵥ w) ≤ c ^ 2 * (w ⬝ᵥ ((A * Aᵀ) *ᵥ w)) * (v ⬝ᵥ v)) ∧
    (∀ (k : ℕ) (f : Fin k → Fin n), Function.Injective f → ∀ u w : Fin k → ℝ, w ≠ 0 →
      0 < w ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ w) ∧
      (u ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ u)) * (w ⬝ᵥ w) ≤
        c ^ 2 * (w ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ w)) * (u ⬝ᵥ u)) ∧
    (∀ i j : Fin n, i ≠ j → (n : ℝ) + |(A * Aᵀ) i j| ≤ c ^ 2 * (n - |(A * Aᵀ) i j|) ∧
      |(A * Aᵀ) i j| < n) := by
  have hR := rayleighLe_of_condLe h
  refine ⟨hR, fun k f hf => rayleighLe_submatrix hR hf, fun i j hij => ?_⟩
  refine rayleigh_pair hR (fun i j => ?_) (fun i => ?_) hij
  · exact gram_symm A i j
  · exact gram_diag hA i

/-- **Lemma `lem:tools`.** Both parts (see `lem_tools_one`, `lem_tools_two`). -/
theorem lem_tools {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSign A) :
    (∀ i j : Fin n, negCount A i % 2 = negCount A j % 2 →
      ∃ g : ℤ, (A * Aᵀ) i j = g ∧ g ≡ n [ZMOD 4]) ∧
    ∀ c : ℝ, CondLe A c →
      (∀ v w : Fin n → ℝ, w ≠ 0 → 0 < w ⬝ᵥ ((A * Aᵀ) *ᵥ w) ∧
        (v ⬝ᵥ ((A * Aᵀ) *ᵥ v)) * (w ⬝ᵥ w) ≤ c ^ 2 * (w ⬝ᵥ ((A * Aᵀ) *ᵥ w)) * (v ⬝ᵥ v)) ∧
      (∀ (k : ℕ) (f : Fin k → Fin n), Function.Injective f → ∀ u w : Fin k → ℝ, w ≠ 0 →
        0 < w ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ w) ∧
        (u ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ u)) * (w ⬝ᵥ w) ≤
          c ^ 2 * (w ⬝ᵥ ((A * Aᵀ).submatrix f f *ᵥ w)) * (u ⬝ᵥ u)) ∧
      (∀ i j : Fin n, i ≠ j → (n : ℝ) + |(A * Aᵀ) i j| ≤ c ^ 2 * (n - |(A * Aᵀ) i j|) ∧
        |(A * Aᵀ) i j| < n) :=
  ⟨fun i j h => lem_tools_one hA i j h, fun _ h => lem_tools_two hA h⟩

end SignCond
