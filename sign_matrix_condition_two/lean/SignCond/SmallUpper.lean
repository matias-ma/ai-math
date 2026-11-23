import SignCond.SmallTools

/-!
# Section `sec:small`: the five upper bounds

The matrices `A₇`, `A₉` (Appendix `app:small`), `W₂ ⊗ (J₅ - 2I₅)` (order `10`), the circulant
`A₁₃` and the block matrix `A₁₄` of the paragraphs "Order 10", "Order 13", "Order 14".

Method. For each matrix the Gram matrix `G = AAᵀ` is computed over `ℤ` by `decide`, and an
annihilating polynomial `P(G) = 0` is checked over `ℤ` by `decide`. A real symmetric matrix
annihilated by `P` has all its eigenvalues among the roots of `P`
(`window_of_annihilating`, via an orthonormal eigenbasis), so if all roots of `P` lie in
`[t, c²t]`, then `tI ⪯ G ⪯ c²tI`, i.e. `CondLe A c`.

* `condLe_A7  : CondLe A7 (√3)`                    (`G` has eigenvalues `4, 9, 12`; `t = 4`);
* `condLe_A9  : CondLe A9 ((1 + √41) / 4)`         (`4, 12, (21 ± √41)/2`; `t = 4`);
* `condLe_A10 : CondLe A10 (3 / 2)`                (`W₂ ⊗ (J₅ - 2I₅)`, eigenvalues `8, 18`);
* `condLe_A13 : CondLe A13 (5 / (2 * √3))`         (`G = 12I + J`; `t = 12`, `c²t = 25`);
* `condLe_A14 : CondLe A14 (√(13 / 6))`            (`G = diag(12I + 2J, 12I + 2J)`; `t = 12`).
-/

open Matrix Kronecker Polynomial

namespace SignCond

section Annihilating

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mulVec_pow_eigen {G : Matrix n n ℝ} {v : n → ℝ} {x : ℝ} (h : G *ᵥ v = x • v) (k : ℕ) :
    (G ^ k) *ᵥ v = x ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem aeval_mulVec_eigen {G : Matrix n n ℝ} {v : n → ℝ} {x : ℝ} (h : G *ᵥ v = x • v)
    (P : ℝ[X]) : (aeval G P) *ᵥ v = P.eval x • v := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_mulVec, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      smul_mulVec_assoc, mulVec_pow_eigen h, eval_monomial, smul_smul]

/-- A real symmetric matrix all of whose eigenvalues are nonnegative is positive semidefinite
(stated with eigenvectors, through the orthonormal eigenbasis of Mathlib). -/
theorem posSemidef_of_eigen {M : Matrix n n ℝ} (hM : Mᵀ = M)
    (h : ∀ (μ : ℝ) (v : n → ℝ), v ≠ 0 → M *ᵥ v = μ • v → 0 ≤ μ) : M.PosSemidef := by
  have hH : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hM
  refine hH.posSemidef_of_eigenvalues_nonneg fun i => h _ _ ?_ (hH.mulVec_eigenvectorBasis i)
  intro h0
  apply hH.eigenvectorBasis.orthonormal.ne_zero i
  ext k
  simpa using congrFun h0 k

/-- **Annihilating polynomials.** If `G` is real symmetric, `P(G) = 0`, and every real root of `P`
lies in `[a, b]`, then `aI ⪯ G ⪯ bI`. -/
theorem window_of_annihilating {G : Matrix n n ℝ} (hG : Gᵀ = G) (P : ℝ[X])
    (hP : aeval G P = 0) {a b : ℝ} (hroots : ∀ x, P.eval x = 0 → a ≤ x ∧ x ≤ b) :
    (G - a • (1 : Matrix n n ℝ)).PosSemidef ∧ (b • (1 : Matrix n n ℝ) - G).PosSemidef := by
  have root : ∀ (x : ℝ) (v : n → ℝ), v ≠ 0 → G *ᵥ v = x • v → a ≤ x ∧ x ≤ b := by
    intro x v hv hx
    apply hroots
    have := aeval_mulVec_eigen hx P
    rw [hP, zero_mulVec] at this
    exact (smul_eq_zero.1 this.symm).resolve_right hv
  constructor
  · refine posSemidef_of_eigen (by rw [transpose_sub, hG, transpose_smul, transpose_one]) ?_
    intro μ v hv h
    have : G *ᵥ v = (μ + a) • v := by
      rw [sub_mulVec, smul_mulVec_assoc, one_mulVec, sub_eq_iff_eq_add] at h
      rw [h, add_smul]
    linarith [(root _ v hv this).1]
  · refine posSemidef_of_eigen (by rw [transpose_sub, hG, transpose_smul, transpose_one]) ?_
    intro μ v hv h
    have : G *ᵥ v = (b - μ) • v := by
      rw [sub_mulVec, smul_mulVec_assoc, one_mulVec, sub_eq_iff_eq_add] at h
      rw [sub_smul, h]
      abel
    linarith [(root _ v hv this).2]

omit [Fintype n] [DecidableEq n] in
theorem toR_zero : toR (0 : Matrix n n ℤ) = 0 := by
  ext i j; simp [toR]

omit [Fintype n] [DecidableEq n] in
theorem toR_add (M N : Matrix n n ℤ) : toR (M + N) = toR M + toR N := by
  ext i j; simp [toR]

omit [DecidableEq n] in
theorem gram_int_symm (Az : Matrix n n ℤ) : (toR (Az * Azᵀ))ᵀ = toR (Az * Azᵀ) := by
  rw [← toR_transpose, transpose_mul, transpose_transpose]

/-- `CondLe` from an annihilating polynomial of the (integer) Gram matrix. -/
theorem condLe_toR_of_annihilating (Az : Matrix n n ℤ) (P : ℝ[X])
    (hP : aeval (toR (Az * Azᵀ)) P = 0) {t c : ℝ} (ht : 0 < t)
    (hroots : ∀ x, P.eval x = 0 → t ≤ x ∧ x ≤ c ^ 2 * t) : CondLe (toR Az) c := by
  refine ⟨t, ht, ?_⟩
  rw [toR_gram]
  exact window_of_annihilating (gram_int_symm Az) P hP hroots

/-- Two eigenvalues: `(G - a)(G - b) = 0` over `ℤ` with `t ≤ a, b ≤ c²t`. -/
theorem condLe_of_roots2 {Az Gz : Matrix n n ℤ} (hG : Az * Azᵀ = Gz) {a b : ℤ}
    (hpoly : (Gz - a • 1) * (Gz - b • 1) = 0) {t c : ℝ} (ht : 0 < t)
    (ha : t ≤ a ∧ (a : ℝ) ≤ c ^ 2 * t) (hb : t ≤ b ∧ (b : ℝ) ≤ c ^ 2 * t) :
    CondLe (toR Az) c := by
  refine condLe_toR_of_annihilating Az ((X - C (a : ℝ)) * (X - C (b : ℝ))) ?_ ht ?_
  · have := congrArg toR hpoly
    rw [toR_mul, toR_sub_smul_one, toR_sub_smul_one, toR_zero] at this
    simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, hG]
    exact this
  · intro x hx
    simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb

/-- Three eigenvalues: `(G - a)(G - b)(G - d) = 0` over `ℤ` with `t ≤ a, b, d ≤ c²t`. -/
theorem condLe_of_roots3 {Az Gz : Matrix n n ℤ} (hG : Az * Azᵀ = Gz) {a b d : ℤ}
    (hpoly : (Gz - a • 1) * (Gz - b • 1) * (Gz - d • 1) = 0) {t c : ℝ} (ht : 0 < t)
    (ha : t ≤ a ∧ (a : ℝ) ≤ c ^ 2 * t) (hb : t ≤ b ∧ (b : ℝ) ≤ c ^ 2 * t)
    (hd : t ≤ d ∧ (d : ℝ) ≤ c ^ 2 * t) : CondLe (toR Az) c := by
  refine condLe_toR_of_annihilating Az ((X - C (a : ℝ)) * (X - C (b : ℝ)) * (X - C (d : ℝ)))
    ?_ ht ?_
  · have := congrArg toR hpoly
    rw [toR_mul, toR_mul, toR_sub_smul_one, toR_sub_smul_one, toR_sub_smul_one,
      toR_zero] at this
    simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, hG]
    exact this
  · intro x hx
    simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hx
    rcases hx with (rfl | rfl) | rfl
    · exact ha
    · exact hb
    · exact hd

end Annihilating

/-! ### Order 7 -/

/-- `A₇` (Appendix `app:small`): rows `+++++++`, `----+++`, `---+-++`, `--+++--`, `-+-++--`,
`-++---+`, `-++--+-` (`+ = 1`, `- = -1`). -/
def A7z : Matrix (Fin 7) (Fin 7) ℤ := !![
   1,  1,  1,  1,  1,  1,  1;
  -1, -1, -1, -1,  1,  1,  1;
  -1, -1, -1,  1, -1,  1,  1;
  -1, -1,  1,  1,  1, -1, -1;
  -1,  1, -1,  1,  1, -1, -1;
  -1,  1,  1, -1, -1, -1,  1;
  -1,  1,  1, -1, -1,  1, -1]

/-- The Gram matrix of `A₇`: `8I - J + 4N` with `N` the matching `{1,2}, {3,4}, {5,6}`. -/
def G7z : Matrix (Fin 7) (Fin 7) ℤ := !![
   7, -1, -1, -1, -1, -1, -1;
  -1,  7,  3, -1, -1, -1, -1;
  -1,  3,  7, -1, -1, -1, -1;
  -1, -1, -1,  7,  3, -1, -1;
  -1, -1, -1,  3,  7, -1, -1;
  -1, -1, -1, -1, -1,  7,  3;
  -1, -1, -1, -1, -1,  3,  7]

noncomputable def A7 : Matrix (Fin 7) (Fin 7) ℝ := toR A7z

theorem A7z_sign : ∀ i j, A7z i j = 1 ∨ A7z i j = -1 := by decide

theorem A7z_gram : A7z * A7zᵀ = G7z := by decide

/-- `(G - 4)(G - 9)(G - 12) = 0`: the eigenvalues of `G` are `4, 9, 12`. -/
theorem G7z_poly : (G7z - (4 : ℤ) • 1) * (G7z - (9 : ℤ) • 1) * (G7z - (12 : ℤ) • 1) = 0 := by
  decide

theorem isSign_A7 : IsSign A7 := isSign_toR A7z_sign

/-- **Order 7, upper bound.** `κ(A₇) ≤ √3`: `4I ⪯ A₇A₇ᵀ ⪯ 12I`. -/
theorem condLe_A7 : CondLe A7 (Real.sqrt 3) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine condLe_of_roots3 A7z_gram G7z_poly (t := 4) (by norm_num) ?_ ?_ ?_ <;>
    rw [h3] <;> norm_num

/-! ### Order 9 -/

/-- `A₉` (Appendix `app:small`): rows `---------`, `--+--++-+`, `-+-+--+-+`, `---++++--`,
`+-++-----`, `+++-+-+--`, `-+++-+-+-`, `-++++---+`, `--+++-++-`. -/
def A9z : Matrix (Fin 9) (Fin 9) ℤ := !![
  -1, -1, -1, -1, -1, -1, -1, -1, -1;
  -1, -1,  1, -1, -1,  1,  1, -1,  1;
  -1,  1, -1,  1, -1, -1,  1, -1,  1;
  -1, -1, -1,  1,  1,  1,  1, -1, -1;
   1, -1,  1,  1, -1, -1, -1, -1, -1;
   1,  1,  1, -1,  1, -1,  1, -1, -1;
  -1,  1,  1,  1, -1,  1, -1,  1, -1;
  -1,  1,  1,  1,  1, -1, -1, -1,  1;
  -1, -1,  1,  1,  1, -1,  1,  1, -1]

/-- The Gram matrix of `A₉`. -/
def G9z : Matrix (Fin 9) (Fin 9) ℤ := !![
   9,  1,  1,  1,  3, -1, -1, -1, -1;
   1,  9,  1,  1, -1, -1, -1, -1, -1;
   1,  1,  9,  1, -1, -1, -1,  3, -1;
   1,  1,  1,  9, -1, -1, -1, -1,  3;
   3, -1, -1, -1,  9,  1,  1,  1,  1;
  -1, -1, -1, -1,  1,  9, -3,  1,  1;
  -1, -1, -1, -1,  1, -3,  9,  1,  1;
  -1, -1,  3, -1,  1,  1,  1,  9,  1;
  -1, -1, -1,  3,  1,  1,  1,  1,  9]

noncomputable def A9 : Matrix (Fin 9) (Fin 9) ℝ := toR A9z

theorem A9z_sign : ∀ i j, A9z i j = 1 ∨ A9z i j = -1 := by decide

theorem A9z_gram : A9z * A9zᵀ = G9z := by decide

/-- `(G - 12)(G - 4)(G² - 21G + 100) = 0`. -/
theorem G9z_poly :
    (G9z - (12 : ℤ) • 1) * (G9z - (4 : ℤ) • 1) * (G9z * G9z - (21 : ℤ) • G9z + (100 : ℤ) • 1) =
      0 := by
  decide

theorem isSign_A9 : IsSign A9 := isSign_toR A9z_sign

/-- The roots of `(x - 12)(x - 4)(x² - 21x + 100)` lie in `[4, (21 + √41)/2]`. -/
theorem roots9 (x : ℝ) (hx : (x - 12) * (x - 4) * (x * x - 21 * x + 100) = 0) :
    4 ≤ x ∧ x ≤ ((1 + Real.sqrt 41) / 4) ^ 2 * 4 := by
  set s := Real.sqrt 41 with hs_def
  have hs : s ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 41
  have hb : ((1 + s) / 4) ^ 2 * 4 = (21 + s) / 2 := by nlinarith
  rw [hb]
  have hs3 : 3 ≤ s := by nlinarith
  rcases mul_eq_zero.1 hx with hx | hx
  · rcases mul_eq_zero.1 hx with hx | hx
    · have : x = 12 := by linarith
      subst this; constructor <;> linarith
    · have : x = 4 := by linarith
      subst this; constructor <;> linarith
  · constructor
    · by_contra hlt
      push_neg at hlt
      nlinarith [mul_pos (sub_pos.2 hlt) (show (0 : ℝ) < 17 - x by linarith)]
    · by_contra hlt
      push_neg at hlt
      have h1 : 0 < x - (21 + s) / 2 := by linarith
      have h2 : 0 < x - (21 - s) / 2 := by linarith
      have : (x - (21 + s) / 2) * (x - (21 - s) / 2) = x * x - 21 * x + 100 := by nlinarith
      nlinarith [mul_pos h1 h2]

/-- **Order 9, upper bound.** `κ(A₉) ≤ (1 + √41)/4`: `4I ⪯ A₉A₉ᵀ ⪯ ½(21 + √41) I`. -/
theorem condLe_A9 : CondLe A9 ((1 + Real.sqrt 41) / 4) := by
  refine condLe_toR_of_annihilating A9z
    ((X - C 12) * (X - C 4) * (X * X - C 21 * X + C 100)) ?_ (t := 4) (by norm_num) ?_
  · have := congrArg toR G9z_poly
    rw [toR_mul, toR_mul, toR_sub_smul_one, toR_sub_smul_one, toR_add, toR_sub, toR_mul,
      toR_smul, toR_smul, toR_one, toR_zero] at this
    simp only [map_mul, map_sub, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      A9z_gram, smul_mul_assoc, one_mul]
    push_cast at this
    exact this
  · intro x hx
    simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C] at hx
    exact roots9 x hx

/-! ### Order 10 -/

/-- `J₅ - 2I₅`. -/
def C5z : Matrix (Fin 5) (Fin 5) ℤ := Matrix.of (fun _ _ => 1) - (2 : ℤ) • 1

/-- `(J₅ - 2I₅)(J₅ - 2I₅)ᵀ = 4I + J`. -/
def G5z : Matrix (Fin 5) (Fin 5) ℤ := (4 : ℤ) • 1 + Matrix.of (fun _ _ => 1)

theorem C5z_sign : ∀ i j, C5z i j = 1 ∨ C5z i j = -1 := by decide

theorem C5z_gram : C5z * C5zᵀ = G5z := by decide

theorem G5z_poly : (G5z - (4 : ℤ) • 1) * (G5z - (9 : ℤ) • 1) = 0 := by decide

/-- `κ(J₅ - 2I₅) ≤ 3/2` (Gram eigenvalues `4` and `9`). -/
theorem condLe_C5 : CondLe (toR C5z) (3 / 2) :=
  condLe_of_roots2 C5z_gram G5z_poly (t := 4) (by norm_num) (by norm_num) (by norm_num)

/-- The paper's matrix of order `10`: `W₂ ⊗ (J₅ - 2I₅)`, relabelled by `Fin 2 × Fin 5 ≃ Fin 10`. -/
noncomputable def A10 : Matrix (Fin 10) (Fin 10) ℝ :=
  reindex finProdFinEquiv finProdFinEquiv (W2 ⊗ₖ toR C5z)

theorem isSign_A10 : IsSign A10 :=
  isSign_reindex _ (isSign_kronecker (isSign_toR C5z_sign))

/-- **Order 10, upper bound.** `κ(W₂ ⊗ (J₅ - 2I₅)) = κ(J₅ - 2I₅) ≤ 3/2` (Lemma `lem:double`). -/
theorem condLe_A10 : CondLe A10 (3 / 2) :=
  condLe_reindex _ ((condLe_kronecker_iff _ _).2 condLe_C5)

/-! ### Order 13 -/

/-- `A₁₃`: the circulant whose first row has entries `-1` in the positions `0, 1, 3, 9` and `1`
elsewhere (entry `(i, j)` is the first-row entry at position `j - i ∈ ℤ/13ℤ`). -/
def A13z : Matrix (Fin 13) (Fin 13) ℤ :=
  Matrix.of fun i j => if j - i = 0 ∨ j - i = 1 ∨ j - i = 3 ∨ j - i = 9 then -1 else 1

/-- `12I + J`. -/
def G13z : Matrix (Fin 13) (Fin 13) ℤ := (12 : ℤ) • 1 + Matrix.of (fun _ _ => 1)

noncomputable def A13 : Matrix (Fin 13) (Fin 13) ℝ := toR A13z

theorem A13z_sign : ∀ i j, A13z i j = 1 ∨ A13z i j = -1 := by decide

set_option maxRecDepth 10000 in
/-- Paper: "any two distinct rows of `A_{13}` have inner product `13-2\cdot6=1`. Hence
`A_{13}A_{13}^\top=12I+J`". -/
theorem A13z_gram : A13z * A13zᵀ = G13z := by decide

theorem G13z_poly : (G13z - (12 : ℤ) • 1) * (G13z - (25 : ℤ) • 1) = 0 := by decide

theorem isSign_A13 : IsSign A13 := isSign_toR A13z_sign

/-- **Order 13, upper bound.** `κ(A₁₃) ≤ 5/√12 = 5/(2√3)`: `12I ⪯ A₁₃A₁₃ᵀ ⪯ 25I`. -/
theorem condLe_A13 : CondLe A13 (5 / (2 * Real.sqrt 3)) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (5 / (2 * Real.sqrt 3)) ^ 2 * 12 = 25 := by
    rw [div_pow, mul_pow, h3]; norm_num
  refine condLe_of_roots2 A13z_gram G13z_poly (t := 12) (by norm_num) ?_ ?_ <;>
    rw [hc] <;> norm_num

/-! ### Order 14 -/

/-- `R = J₇ - 2I₇`. -/
def R7z : Matrix (Fin 7) (Fin 7) ℤ := Matrix.of (fun _ _ => 1) - (2 : ℤ) • 1

/-- `S`: the circulant with first row `(1,1,1,-1,1,-1,-1)` (entry `(i, j)` is the first-row entry at
position `j - i ∈ ℤ/7ℤ`). -/
def S7z : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.of fun i j => (![1, 1, 1, -1, 1, -1, -1] : Fin 7 → ℤ) (j - i)

/-- `A₁₄ = [[R, S], [Sᵀ, -R]]`, indexed by `Fin 7 ⊕ Fin 7`. -/
def A14s : Matrix (Fin 7 ⊕ Fin 7) (Fin 7 ⊕ Fin 7) ℤ := fromBlocks R7z S7z S7zᵀ (-R7z)

/-- `diag(12I + 2J, 12I + 2J)`. -/
def G14s : Matrix (Fin 7 ⊕ Fin 7) (Fin 7 ⊕ Fin 7) ℤ :=
  (12 : ℤ) • 1 + (2 : ℤ) • fromBlocks (Matrix.of fun _ _ => 1) 0 0 (Matrix.of fun _ _ => 1)

theorem A14s_sign : ∀ i j, A14s i j = 1 ∨ A14s i j = -1 := by decide

set_option maxRecDepth 10000 in
/-- Paper: "`A_{14}A_{14}^\top=\begin{pmatrix}12I+2J&0\\0&12I+2J\end{pmatrix}`". -/
theorem A14s_gram : A14s * A14sᵀ = G14s := by decide

set_option maxRecDepth 10000 in
theorem G14s_poly : (G14s - (12 : ℤ) • 1) * (G14s - (26 : ℤ) • 1) = 0 := by decide

/-- The paper's `A₁₄`, relabelled by `Fin 7 ⊕ Fin 7 ≃ Fin 14`. -/
noncomputable def A14 : Matrix (Fin 14) (Fin 14) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv (toR A14s)

theorem isSign_A14 : IsSign A14 := isSign_reindex _ (isSign_toR A14s_sign)

/-- **Order 14, upper bound.** `κ(A₁₄) ≤ √(13/6)`: `12I ⪯ A₁₄A₁₄ᵀ ⪯ 26I`. -/
theorem condLe_A14 : CondLe A14 (Real.sqrt (13 / 6)) := by
  have h : Real.sqrt (13 / 6) ^ 2 = 13 / 6 := Real.sq_sqrt (by norm_num)
  refine condLe_reindex _ ?_
  refine condLe_of_roots2 A14s_gram G14s_poly (t := 12) (by norm_num) ?_ ?_ <;>
    rw [h] <;> norm_num

end SignCond
