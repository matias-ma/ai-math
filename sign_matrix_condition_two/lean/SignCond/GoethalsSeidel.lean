import SignCond.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The Goethals–Seidel identity

Paper: *Let `a, b, c, d ∈ ℝ^j` (indexed by `ℤ/jℤ`) with circulants `A, B, C, D`, where
`C(x)_{u,v} = x_{v-u}`, and let `R e_u = e_{-u}` be the reversal. The Goethals–Seidel array*
```
Z = [[ A,   BR,   CR,    DR  ],
     [-BR,  A,   -DᵀR,   CᵀR ],
     [-CR,  DᵀR,  A,    -BᵀR ],
     [-DR, -CᵀR,  BᵀR,   A   ]]
```
*satisfies `Z Zᵀ = I₄ ⊗ (A Aᵀ + B Bᵀ + C Cᵀ + D Dᵀ)`.*

Two layers.

* `gsArray A B C D R` builds the `4j × 4j` matrix `Z` (index type `Fin 4 × n`) from its
  `4 × 4` table of blocks `gsTable A B C D R`. `gs_identity` is the abstract statement: it
  holds for any square real matrices with `Rᵀ = R`, `R R = 1`, `R P R = Pᵀ` for
  `P ∈ {A, B, C, D}` and the fifteen commutation relations listed in its hypotheses.
* `circ x` (entries `x (v - u)`) and `rev` (entries `1` if `u + v = 0`) on `ZMod j` satisfy
  all those hypotheses, which gives `gs_identity_circ` for the concrete array.

Also: every block maps the all-ones vector to a multiple of it (`circ_mulVec_one`,
`circ_transpose_mulVec_one`, `rev_mulVec_one`), and the `4 × 4` quaternion identity
`quat_mul_transpose`.
-/

open Matrix Kronecker

namespace SignCond

section Abstract

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `4 × 4` table of `n × n` blocks of the Goethals–Seidel array. -/
def gsTable (A B C D R : Matrix n n ℝ) : Matrix (Fin 4) (Fin 4) (Matrix n n ℝ) :=
  !![A, B * R, C * R, D * R;
    -(B * R), A, -(Dᵀ * R), Cᵀ * R;
    -(C * R), Dᵀ * R, A, -(Bᵀ * R);
    -(D * R), -(Cᵀ * R), Bᵀ * R, A]

/-- The Goethals–Seidel array: the block table `gsTable A B C D R` read as a single real
matrix indexed by `Fin 4 × n`, i.e. entry `((p, u), (q, v))` is entry `(u, v)` of block
`(p, q)`. (`Matrix.comp` is Mathlib's flattening of a matrix of matrices.) -/
def gsArray (A B C D R : Matrix n n ℝ) : Matrix (Fin 4 × n) (Fin 4 × n) ℝ :=
  Matrix.comp (Fin 4) (Fin 4) n n ℝ (gsTable A B C D R)

omit [DecidableEq n] in
theorem gsArray_apply (A B C D R : Matrix n n ℝ) (p q : Fin 4) (u v : n) :
    gsArray A B C D R (p, u) (q, v) = gsTable A B C D R p q u v := rfl

/-- Block form of `Z * Zᵀ`: the product of the block tables, where transposing the big
matrix transposes the table and every block. -/
theorem gsTable_mul (A B C D R : Matrix n n ℝ)
    (hRT : Rᵀ = R) (hRR : R * R = 1)
    (hA : R * A * R = Aᵀ) (hB : R * B * R = Bᵀ) (hC : R * C * R = Cᵀ) (hD : R * D * R = Dᵀ)
    (hAB : A * B = B * A) (hAC : A * C = C * A) (hAD : A * D = D * A)
    (hBC : B * C = C * B) (hBD : B * D = D * B) (hCD : C * D = D * C)
    (hABt : A * Bᵀ = Bᵀ * A) (hACt : A * Cᵀ = Cᵀ * A) (hADt : A * Dᵀ = Dᵀ * A)
    (hBCt : B * Cᵀ = Cᵀ * B) (hBDt : B * Dᵀ = Dᵀ * B) (hCDt : C * Dᵀ = Dᵀ * C)
    (hBn : B * Bᵀ = Bᵀ * B) (hCn : C * Cᵀ = Cᵀ * C) (hDn : D * Dᵀ = Dᵀ * D) :
    gsTable A B C D R * ((gsTable A B C D R)ᵀ).map (·ᵀ) =
      diagonal fun _ => A * Aᵀ + B * Bᵀ + C * Cᵀ + D * Dᵀ := by
  -- Moving `R` to the right: `R Pᵀ = P R` and `R P = Pᵀ R`, and `R R = 1`.
  have rr : ∀ X : Matrix n n ℝ, X * R * R = X := fun X => by rw [mul_assoc, hRR, mul_one]
  have sw : ∀ P : Matrix n n ℝ, R * P * R = Pᵀ →
      (∀ X, X * R * Pᵀ = X * P * R) ∧ (∀ X, X * R * P = X * Pᵀ * R) := by
    intro P hP
    refine ⟨fun X => ?_, fun X => ?_⟩
    · rw [← hP]; simp only [← mul_assoc, rr]
    · rw [← hP]; simp only [← mul_assoc, rr]
  obtain ⟨sA1, sA2⟩ := sw A hA
  obtain ⟨sB1, sB2⟩ := sw B hB
  obtain ⟨sC1, sC2⟩ := sw C hC
  obtain ⟨sD1, sD2⟩ := sw D hD
  -- Transposed commutation relations, derived from the hypotheses.
  have tr : ∀ X Y : Matrix n n ℝ, X * Y = Y * X → Xᵀ * Yᵀ = Yᵀ * Xᵀ := fun X Y h => by
    rw [← transpose_mul, ← transpose_mul, h]
  have hABT := tr _ _ hAB
  have hACT := tr _ _ hAC
  have hADT := tr _ _ hAD
  have hBCT := tr _ _ hBC
  have hBDT := tr _ _ hBD
  have hCDT := tr _ _ hCD
  have hBCtT := tr _ _ hBCt
  have hBDtT := tr _ _ hBDt
  have hCDtT := tr _ _ hCDt
  simp only [transpose_transpose] at hBCtT hBDtT hCDtT
  refine Matrix.ext fun i k => ?_
  simp only [mul_apply, Fin.sum_univ_four, map_apply, transpose_apply]
  -- Read off the blocks, push transposes inside, move every `R` to the right end of each
  -- word, put each word of length two in a fixed order, and collect terms.
  fin_cases i <;> fin_cases k <;>
    simp only [gsTable, of_apply, cons_val_zero, cons_val_one, cons_val_two, cons_val_three,
      head_cons, tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      diagonal_apply_eq, diagonal_apply_ne, ne_eq, Fin.reduceEq, not_false_eq_true] <;>
    simp only [transpose_neg, transpose_mul, transpose_transpose, hRT, neg_mul, mul_neg, neg_neg,
      ← mul_assoc, rr, sA1, sA2, sB1, sB2, sC1, sC2, sD1, sD2] <;>
    simp only [← hAB, ← hAC, ← hAD, ← hBC, ← hBD, ← hCD, ← hABt, ← hACt, ← hADt, ← hBCt, ← hBDt,
      ← hCDt, ← hBn, ← hCn, ← hDn, ← hABT, ← hACT, ← hADT, ← hBCT, ← hBDT, ← hCDT,
      ← hBCtT, ← hBDtT, ← hCDtT] <;>
    abel

/-- **Goethals–Seidel identity, abstract form.** Let `A, B, C, D, R` be real `n × n` matrices
with `Rᵀ = R`, `R R = 1`, `R P R = Pᵀ` for `P ∈ {A, B, C, D}`, such that `A, B, C, D`
commute pairwise, each of `A, B, C, D` commutes with the transposes of the others, and
`B, C, D` are normal. Then the Goethals–Seidel array `Z` satisfies
`Z Zᵀ = I₄ ⊗ (A Aᵀ + B Bᵀ + C Cᵀ + D Dᵀ)`. -/
theorem gs_identity (A B C D R : Matrix n n ℝ)
    (hRT : Rᵀ = R) (hRR : R * R = 1)
    (hA : R * A * R = Aᵀ) (hB : R * B * R = Bᵀ) (hC : R * C * R = Cᵀ) (hD : R * D * R = Dᵀ)
    (hAB : A * B = B * A) (hAC : A * C = C * A) (hAD : A * D = D * A)
    (hBC : B * C = C * B) (hBD : B * D = D * B) (hCD : C * D = D * C)
    (hABt : A * Bᵀ = Bᵀ * A) (hACt : A * Cᵀ = Cᵀ * A) (hADt : A * Dᵀ = Dᵀ * A)
    (hBCt : B * Cᵀ = Cᵀ * B) (hBDt : B * Dᵀ = Dᵀ * B) (hCDt : C * Dᵀ = Dᵀ * C)
    (hBn : B * Bᵀ = Bᵀ * B) (hCn : C * Cᵀ = Cᵀ * C) (hDn : D * Dᵀ = Dᵀ * D) :
    gsArray A B C D R * (gsArray A B C D R)ᵀ =
      (1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ (A * Aᵀ + B * Bᵀ + C * Cᵀ + D * Dᵀ) := by
  have hT : (gsArray A B C D R)ᵀ =
      Matrix.comp (Fin 4) (Fin 4) n n ℝ (((gsTable A B C D R)ᵀ).map (·ᵀ)) := rfl
  have hM : gsArray A B C D R * (gsArray A B C D R)ᵀ =
      Matrix.comp (Fin 4) (Fin 4) n n ℝ (gsTable A B C D R * ((gsTable A B C D R)ᵀ).map (·ᵀ)) := by
    rw [hT, gsArray, ← compRingEquiv_apply, ← compRingEquiv_apply, ← compRingEquiv_apply,
      map_mul]
  rw [hM, gsTable_mul A B C D R hRT hRR hA hB hC hD hAB hAC hAD hBC hBD hCD hABt hACt hADt
    hBCt hBDt hCDt hBn hCn hDn]
  ext ⟨p, u⟩ ⟨q, v⟩
  rw [comp_apply, kronecker_apply, one_apply]
  by_cases h : p = q
  · subst h
    rw [diagonal_apply_eq, if_pos rfl, one_mul]
  · rw [diagonal_apply_ne _ h, if_neg h, zero_mul, zero_apply]

end Abstract

section Concrete

variable {j : ℕ} [NeZero j]

/-- The circulant matrix of `x : ℤ/jℤ → ℝ`, with entries `circ x u v = x (v - u)`.
Mathlib's `Matrix.circulant x` has entries `x (u - v)`; `circ_eq_transpose_circulant`
relates the two. -/
def circ (x : ZMod j → ℝ) : Matrix (ZMod j) (ZMod j) ℝ := Matrix.of fun u v => x (v - u)

/-- The reversal permutation matrix, `R e_v = e_{-v}`: entry `(u, v)` is `1` if
`u + v = 0` and `0` otherwise. -/
def rev : Matrix (ZMod j) (ZMod j) ℝ := Matrix.of fun u v => if u + v = 0 then 1 else 0

omit [NeZero j] in
theorem circ_apply (x : ZMod j → ℝ) (u v : ZMod j) : circ x u v = x (v - u) := rfl

omit [NeZero j] in
theorem circ_eq_transpose_circulant (x : ZMod j → ℝ) : circ x = (circulant x)ᵀ := rfl

omit [NeZero j] in
/-- The transpose of a circulant is the circulant of the reflected vector. -/
theorem circ_transpose (x : ZMod j → ℝ) : (circ x)ᵀ = circ fun t => x (-t) := by
  ext u v
  simp [circ_apply, neg_sub]

/-- Circulants commute. -/
theorem circ_mul_comm (x y : ZMod j → ℝ) : circ x * circ y = circ y * circ x := by
  rw [circ_eq_transpose_circulant, circ_eq_transpose_circulant, ← transpose_mul,
    ← transpose_mul, circulant_mul_comm]

theorem rev_mul_apply (M : Matrix (ZMod j) (ZMod j) ℝ) (u w : ZMod j) :
    (rev * M : Matrix (ZMod j) (ZMod j) ℝ) u w = M (-u) w := by
  simp [rev, mul_apply, add_eq_zero_iff_neg_eq]

theorem mul_rev_apply (M : Matrix (ZMod j) (ZMod j) ℝ) (u w : ZMod j) :
    (M * rev : Matrix (ZMod j) (ZMod j) ℝ) u w = M u (-w) := by
  simp [rev, mul_apply, add_eq_zero_iff_eq_neg]

omit [NeZero j] in
theorem rev_transpose : (rev : Matrix (ZMod j) (ZMod j) ℝ)ᵀ = rev := by
  ext u v
  simp [rev, add_comm]

theorem rev_mul_rev : (rev : Matrix (ZMod j) (ZMod j) ℝ) * rev = 1 := by
  ext u v
  rw [rev_mul_apply, one_apply]
  simp [rev, neg_add_eq_zero]

/-- `R C(x) R = C(x)ᵀ`. -/
theorem rev_circ_rev (x : ZMod j → ℝ) : rev * circ x * rev = (circ x)ᵀ := by
  ext u v
  rw [mul_rev_apply, rev_mul_apply, transpose_apply, circ_apply, circ_apply, neg_sub_neg]

/-- `C(x) R` is symmetric. -/
theorem circ_mul_rev_symm (x : ZMod j → ℝ) : (circ x * rev)ᵀ = circ x * rev := by
  rw [transpose_mul, rev_transpose, ← rev_circ_rev, ← mul_assoc, ← mul_assoc, rev_mul_rev,
    one_mul]

/-- **Goethals–Seidel identity for circulants.** For `a, b, c, d : ℤ/jℤ → ℝ` with circulants
`A = circ a`, …, and the reversal `R = rev`, the Goethals–Seidel array satisfies
`Z Zᵀ = I₄ ⊗ (A Aᵀ + B Bᵀ + C Cᵀ + D Dᵀ)`. -/
theorem gs_identity_circ (a b c d : ZMod j → ℝ) :
    gsArray (circ a) (circ b) (circ c) (circ d) rev *
        (gsArray (circ a) (circ b) (circ c) (circ d) rev)ᵀ =
      (1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ
        (circ a * (circ a)ᵀ + circ b * (circ b)ᵀ + circ c * (circ c)ᵀ + circ d * (circ d)ᵀ) := by
  apply gs_identity
  all_goals first
    | exact rev_transpose
    | exact rev_mul_rev
    | exact rev_circ_rev _
    | exact circ_mul_comm _ _
    | (simp only [circ_transpose]; exact circ_mul_comm _ _)

/-! ### The all-ones vector -/

/-- `C(x) 𝟙 = (∑ x) 𝟙`. -/
theorem circ_mulVec_one (x : ZMod j → ℝ) :
    circ x *ᵥ (1 : ZMod j → ℝ) = (∑ v, x v) • (1 : ZMod j → ℝ) := by
  ext u
  simp only [mulVec, dotProduct, circ_apply, Pi.one_apply, mul_one, Pi.smul_apply,
    smul_eq_mul]
  exact (Equiv.subRight u).sum_comp x

/-- `C(x)ᵀ 𝟙 = (∑ x) 𝟙`. -/
theorem circ_transpose_mulVec_one (x : ZMod j → ℝ) :
    (circ x)ᵀ *ᵥ (1 : ZMod j → ℝ) = (∑ v, x v) • (1 : ZMod j → ℝ) := by
  ext u
  simp only [mulVec, dotProduct, transpose_apply, circ_apply, Pi.one_apply, mul_one,
    Pi.smul_apply, smul_eq_mul]
  exact (Equiv.subLeft u).sum_comp x

/-- `R 𝟙 = 𝟙`. -/
theorem rev_mulVec_one : (rev : Matrix (ZMod j) (ZMod j) ℝ) *ᵥ (1 : ZMod j → ℝ) = 1 := by
  ext u
  simp [rev, mulVec, dotProduct, add_eq_zero_iff_neg_eq]

end Concrete

/-! ### The quaternion matrix -/

/-- The `4 × 4` "quaternion" matrix of `r : Fin 4 → ℝ`. -/
def quat (r : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![r 0, r 1, r 2, r 3;
    -r 1, r 0, -r 3, r 2;
    -r 2, r 3, r 0, -r 1;
    -r 3, -r 2, r 1, r 0]

theorem quat_mul_transpose (r : Fin 4 → ℝ) :
    quat r * (quat r)ᵀ = (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [quat, mul_apply, Fin.sum_univ_four, one_apply] <;> ring

end SignCond
