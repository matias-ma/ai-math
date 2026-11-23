import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Golay pairs: doubling, lift and square (Lemmas `lem:lift` and `lem:square`)

A sequence of length `n` is a function `P : Fin n → ℤ`; its polynomial is evaluated by
`peval P z = ∑ v, P v * z ^ v`. A pair `(P, Q)` is Golay (`IsGolay`) if
`|P(z)|² + |Q(z)|² = 2n` for all `|z| = 1`.

* The three unit-circle identities: `doubling_identity` (`|p + cq|² + |p - cq|² = 2|p|² + 2|q|²`),
  `lift_identity` (the `2 × 2` matrix of the lift is twice a unitary) and `square_identity`.
* Concatenation and reversal (`seqRev`): `peval_append`, `peval_rev` (`x^rev(w) = w^(n-1) conj x(w)`).
* Doubling: `isGolay_double`.
* The lift: `liftP`, `liftQ` with coefficients `(P_x, Q_x, P_x, -Q_x)` and `(P_x, Q_x, -P_x, Q_x)`;
  `peval_liftP`, `peval_liftQ`, `isGolay_lift`, `liftP_one`, `liftQ_one`, the coefficient
  identities `liftP_four_mul` … and `isSignSeq_liftP`, `isSignSeq_liftQ`.
* The square: `sqP`, `sqQ`; `peval_sqP`, `peval_sqQ`, `isGolay_sq`, `sqP_one`, `sqQ_one`,
  `isSignSeq_sqP`, `isSignSeq_sqQ`.
-/

open Complex ComplexConjugate

namespace SignCond

/-! ### Identities on the unit circle -/

private theorem norm_sq_eq (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * conj x := by
  rw [mul_conj']; push_cast; rfl

private theorem mul_conj_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [mul_conj', hz]; simp

/-- Doubling: `|p + c q|² + |p - c q|² = 2|p|² + 2|q|²` for `|c| = 1`. -/
theorem doubling_identity (p q c : ℂ) (hc : ‖c‖ = 1) :
    ‖p + c * q‖ ^ 2 + ‖p - c * q‖ ^ 2 = 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 := by
  have h := mul_conj_eq_one hc
  apply ofReal_injective
  push_cast
  simp only [← ofReal_pow, norm_sq_eq, map_add, map_sub, map_mul]
  linear_combination (2 * q * conj q) * h

/-- The lift: for `|z| = 1`,
`|(1+z²)p + (z-z³)q|² + |(1-z²)p + (z+z³)q|² = 4(|p|² + |q|²)`. -/
theorem lift_identity (z p q : ℂ) (hz : ‖z‖ = 1) :
    ‖(1 + z ^ 2) * p + (z - z ^ 3) * q‖ ^ 2 + ‖(1 - z ^ 2) * p + (z + z ^ 3) * q‖ ^ 2 =
      4 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  have h := mul_conj_eq_one hz
  apply ofReal_injective
  push_cast
  simp only [← ofReal_pow, norm_sq_eq, map_add, map_sub, map_mul, map_pow, map_one]
  linear_combination
    (2 * p * conj p * (z * conj z + 1) + 2 * q * conj q * ((z * conj z) ^ 2 + z * conj z + 2) -
      2 * conj z * p * conj q * (z * conj z + 1) - 2 * z * conj p * q * (z * conj z + 1)) * h

/-- The square: for `|W| = 1`, `|u b + v W ā|² + |u a - v W b̄|² = (|u|² + |v|²)(|a|² + |b|²)`. -/
theorem square_identity (u v a b W : ℂ) (hW : ‖W‖ = 1) :
    ‖u * b + v * (W * conj a)‖ ^ 2 + ‖u * a - v * (W * conj b)‖ ^ 2 =
      (‖u‖ ^ 2 + ‖v‖ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := mul_conj_eq_one hW
  apply ofReal_injective
  push_cast
  simp only [← ofReal_pow, norm_sq_eq, map_add, map_sub, map_mul, conj_conj]
  linear_combination (v * conj v * (a * conj a + b * conj b)) * h

/-- The square identity with `W = w^(l-1)`, as in the proof of Lemma `lem:square`. -/
theorem square_identity_pow (u v a b w : ℂ) (hw : ‖w‖ = 1) (l : ℕ) :
    ‖u * b + v * (w ^ (l - 1) * conj a)‖ ^ 2 + ‖u * a - v * (w ^ (l - 1) * conj b)‖ ^ 2 =
      (‖u‖ ^ 2 + ‖v‖ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
  square_identity u v a b _ (by rw [norm_pow, hw, one_pow])

/-! ### Sequences, polynomials, concatenation and reversal -/

/-- The polynomial of a sequence: `peval P z = ∑ v, P v * z ^ v`. -/
noncomputable def peval {n : ℕ} (P : Fin n → ℤ) (z : ℂ) : ℂ := ∑ v : Fin n, (P v : ℂ) * z ^ (v : ℕ)

/-- A sign sequence: every coefficient is `1` or `-1`. -/
def IsSignSeq {n : ℕ} (P : Fin n → ℤ) : Prop := ∀ v, P v = 1 ∨ P v = -1

/-- `(P, Q)` is a Golay pair of length `n`: `|P(z)|² + |Q(z)|² = 2n` for all `|z| = 1`.
(Sign coefficients are a separate hypothesis, `IsSignSeq`.) -/
def IsGolay {n : ℕ} (P Q : Fin n → ℤ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ‖peval P z‖ ^ 2 + ‖peval Q z‖ ^ 2 = 2 * n

/-- The reversal `x^rev`, `x^rev_v = x_{n-1-v}`. -/
def seqRev {n : ℕ} (x : Fin n → ℤ) : Fin n → ℤ := fun v => x (Fin.rev v)

theorem peval_append {n m : ℕ} (P : Fin n → ℤ) (Q : Fin m → ℤ) (z : ℂ) :
    peval (Fin.append P Q) z = peval P z + z ^ n * peval Q z := by
  simp only [peval, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.coe_castAdd,
    Fin.coe_natAdd, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem peval_neg {n : ℕ} (P : Fin n → ℤ) (z : ℂ) : peval (-P) z = -peval P z := by
  simp [peval, Finset.sum_neg_distrib]

/-- `x^rev(w) = w^(n-1) conj (x(w))` for `|w| = 1`. -/
theorem peval_rev {n : ℕ} (x : Fin n → ℤ) {w : ℂ} (hw : ‖w‖ = 1) :
    peval (seqRev x) w = w ^ (n - 1) * conj (peval x w) := by
  have h := mul_conj_eq_one hw
  simp only [peval, seqRev, map_sum, map_mul, map_intCast, map_pow, Finset.mul_sum]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hv : n - 1 = (n - (v + 1)) + v := by omega
  rw [hv, pow_add, mul_left_comm, mul_assoc, ← mul_pow, h, one_pow, mul_one]

theorem peval_rev_one {n : ℕ} (x : Fin n → ℤ) : peval (seqRev x) 1 = peval x 1 := by
  rw [peval_rev x (by simp), one_pow, one_mul]
  simp [peval]

theorem norm_peval_rev {n : ℕ} (x : Fin n → ℤ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖peval (seqRev x) w‖ = ‖peval x w‖ := by
  rw [peval_rev x hw, norm_mul, norm_pow, hw, one_pow, one_mul, Complex.norm_conj]

/-- Replacing `Q` by `Q^rev` keeps a Golay pair Golay (used for `d = 80`). -/
theorem isGolay_rev {n : ℕ} {P Q : Fin n → ℤ} (h : IsGolay P Q) : IsGolay P (seqRev Q) := by
  intro z hz
  rw [norm_peval_rev Q hz]
  exact h z hz

theorem isSignSeq_rev {n : ℕ} {x : Fin n → ℤ} (h : IsSignSeq x) : IsSignSeq (seqRev x) :=
  fun _ => h _

/-! ### Doubling -/

/-- Doubling: `(P|Q, P|-Q)` is a Golay pair of length `2n`. -/
theorem isGolay_double {n : ℕ} {P Q : Fin n → ℤ} (h : IsGolay P Q) :
    IsGolay (Fin.append P Q) (Fin.append P (-Q)) := by
  intro z hz
  rw [peval_append, peval_append, peval_neg, mul_neg, ← sub_eq_add_neg,
    doubling_identity _ _ _ (by rw [norm_pow, hz, one_pow])]
  have := h z hz
  push_cast
  linarith

theorem isSignSeq_double {n : ℕ} {P Q : Fin n → ℤ} (hP : IsSignSeq P) (hQ : IsSignSeq Q) :
    IsSignSeq (Fin.append P Q) ∧ IsSignSeq (Fin.append P (-Q)) := by
  constructor <;> intro v <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) v <;>
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply]
  · exact hP i
  · exact hQ i
  · exact hP i
  · rcases hQ i with h | h <;> simp [h]

/-! ### The lift (Lemma `lem:lift`) -/

private theorem divNat_finProdFinEquiv {m k : ℕ} (a : Fin m) (b : Fin k) :
    (finProdFinEquiv (a, b)).divNat = a :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a, b))

private theorem modNat_finProdFinEquiv {m k : ℕ} (a : Fin m) (b : Fin k) :
    (finProdFinEquiv (a, b)).modNat = b :=
  congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a, b))

/-- Sum over `Fin (m * k)` as a double sum, position `i = b + k a`. -/
private theorem sum_fin_mul {m k : ℕ} (f : Fin (m * k) → ℂ) :
    ∑ i, f i = ∑ a : Fin m, ∑ b : Fin k, f (finProdFinEquiv (a, b)) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]

/-- `P'`: coefficients `(P_x, Q_x, P_x, -Q_x)` in positions `4x, …, 4x+3`. -/
def liftP {n : ℕ} (P Q : Fin n → ℤ) : Fin (n * 4) → ℤ := fun i =>
  ![P i.divNat, Q i.divNat, P i.divNat, -Q i.divNat] i.modNat

/-- `Q'`: coefficients `(P_x, Q_x, -P_x, Q_x)` in positions `4x, …, 4x+3`. -/
def liftQ {n : ℕ} (P Q : Fin n → ℤ) : Fin (n * 4) → ℤ := fun i =>
  ![P i.divNat, Q i.divNat, -P i.divNat, Q i.divNat] i.modNat

theorem peval_liftP {n : ℕ} (P Q : Fin n → ℤ) (z : ℂ) :
    peval (liftP P Q) z = (1 + z ^ 2) * peval P (z ^ 4) + (z - z ^ 3) * peval Q (z ^ 4) := by
  rw [peval, sum_fin_mul]
  simp only [liftP, divNat_finProdFinEquiv, modNat_finProdFinEquiv, finProdFinEquiv_apply_val,
    Fin.sum_univ_four, peval, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast
  rw [← pow_mul]
  simp only [show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_add]
  ring

theorem peval_liftQ {n : ℕ} (P Q : Fin n → ℤ) (z : ℂ) :
    peval (liftQ P Q) z = (1 - z ^ 2) * peval P (z ^ 4) + (z + z ^ 3) * peval Q (z ^ 4) := by
  rw [peval, sum_fin_mul]
  simp only [liftQ, divNat_finProdFinEquiv, modNat_finProdFinEquiv, finProdFinEquiv_apply_val,
    Fin.sum_univ_four, peval, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast
  rw [← pow_mul]
  simp only [show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_add]
  ring

/-- Lemma `lem:lift`: the lift of a Golay pair of length `n` is a Golay pair of length `4n`. -/
theorem isGolay_lift {n : ℕ} {P Q : Fin n → ℤ} (h : IsGolay P Q) :
    IsGolay (liftP P Q) (liftQ P Q) := by
  intro z hz
  rw [peval_liftP, peval_liftQ, lift_identity z _ _ hz,
    h (z ^ 4) (by rw [norm_pow, hz, one_pow])]
  push_cast
  ring

/-- `P'(1) = 2 P(1)`. -/
theorem liftP_one {n : ℕ} (P Q : Fin n → ℤ) : peval (liftP P Q) 1 = 2 * peval P 1 := by
  rw [peval_liftP]; norm_num

/-- `Q'(1) = 2 Q(1)`. -/
theorem liftQ_one {n : ℕ} (P Q : Fin n → ℤ) : peval (liftQ P Q) 1 = 2 * peval Q 1 := by
  rw [peval_liftQ]; norm_num

theorem liftP_apply {n : ℕ} (P Q : Fin n → ℤ) (x : Fin n) (b : Fin 4) :
    liftP P Q (finProdFinEquiv (x, b)) = ![P x, Q x, P x, -Q x] b := by
  simp [liftP, divNat_finProdFinEquiv, modNat_finProdFinEquiv]

theorem liftQ_apply {n : ℕ} (P Q : Fin n → ℤ) (x : Fin n) (b : Fin 4) :
    liftQ P Q (finProdFinEquiv (x, b)) = ![P x, Q x, -P x, Q x] b := by
  simp [liftQ, divNat_finProdFinEquiv, modNat_finProdFinEquiv]

private theorem fin_four_mul_add {n : ℕ} (x : Fin n) (b : Fin 4) (h : 4 * (x : ℕ) + b < n * 4) :
    (⟨4 * x + b, h⟩ : Fin (n * 4)) = finProdFinEquiv (x, b) := by
  ext; simp [finProdFinEquiv_apply_val]; ring

/-- Equation `eq:liftcoefficients`: `P'_{4x} = Q'_{4x} = P_x` and `P'_{4x+1} = Q'_{4x+1} = Q_x`. -/
theorem lift_coefficients {n : ℕ} (P Q : Fin n → ℤ) (x : Fin n) :
    liftP P Q ⟨4 * x, by omega⟩ = P x ∧ liftQ P Q ⟨4 * x, by omega⟩ = P x ∧
      liftP P Q ⟨4 * x + 1, by omega⟩ = Q x ∧ liftQ P Q ⟨4 * x + 1, by omega⟩ = Q x := by
  have e0 := fin_four_mul_add x 0 (by simp; omega)
  have e1 := fin_four_mul_add x 1 (by simp; omega)
  simp only [Fin.val_zero, add_zero, Fin.val_one] at e0 e1
  rw [e0, e1, liftP_apply, liftQ_apply, liftP_apply, liftQ_apply]
  simp

theorem isSignSeq_liftP {n : ℕ} {P Q : Fin n → ℤ} (hP : IsSignSeq P) (hQ : IsSignSeq Q) :
    IsSignSeq (liftP P Q) := by
  intro i
  simp only [liftP]
  generalize i.modNat = b
  generalize i.divNat = x
  fin_cases b <;> simp
  · exact hP x
  · exact hQ x
  · exact hP x
  · rcases hQ x with h | h <;> simp [h]

theorem isSignSeq_liftQ {n : ℕ} {P Q : Fin n → ℤ} (hP : IsSignSeq P) (hQ : IsSignSeq Q) :
    IsSignSeq (liftQ P Q) := by
  intro i
  simp only [liftQ]
  generalize i.modNat = b
  generalize i.divNat = x
  fin_cases b <;> simp
  · exact hP x
  · exact hQ x
  · rcases hP x with h | h <;> simp [h]
  · exact hQ x

/-! ### The square (Lemma `lem:square`) -/

/-- `U = (A + B) / 2` (exact for sign sequences, see `two_mul_halfSum`). -/
def halfSum {l : ℕ} (A B : Fin l → ℤ) : Fin l → ℤ := fun x => (A x + B x) / 2

/-- `V = (A - B) / 2` (exact for sign sequences, see `two_mul_halfDiff`). -/
def halfDiff {l : ℕ} (A B : Fin l → ℤ) : Fin l → ℤ := fun x => (A x - B x) / 2

/-- `P`, with `P_{x + l y} = U_x B_y + V_x A^rev_y` (`0 ≤ x, y < l`), i.e.
`P(z) = U(z) B(z^l) + V(z) A^rev(z^l)`. -/
def sqP {l : ℕ} (A B : Fin l → ℤ) : Fin (l * l) → ℤ := fun i =>
  halfSum A B i.modNat * B i.divNat + halfDiff A B i.modNat * seqRev A i.divNat

/-- `Q`, with `Q_{x + l y} = U_x A_y - V_x B^rev_y`, i.e. `Q(z) = U(z) A(z^l) - V(z) B^rev(z^l)`. -/
def sqQ {l : ℕ} (A B : Fin l → ℤ) : Fin (l * l) → ℤ := fun i =>
  halfSum A B i.modNat * A i.divNat - halfDiff A B i.modNat * seqRev B i.divNat

private theorem peval_mul_comp {l : ℕ} (U B : Fin l → ℤ) (z : ℂ) :
    peval U z * peval B (z ^ l) =
      ∑ y : Fin l, ∑ x : Fin l, ((U x * B y : ℤ) : ℂ) * z ^ ((x : ℕ) + l * y) := by
  rw [peval, peval, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  push_cast
  rw [pow_add, pow_mul]
  ring

theorem peval_sqP {l : ℕ} (A B : Fin l → ℤ) (z : ℂ) :
    peval (sqP A B) z =
      peval (halfSum A B) z * peval B (z ^ l) + peval (halfDiff A B) z * peval (seqRev A) (z ^ l) := by
  rw [peval_mul_comp, peval_mul_comp, ← Finset.sum_add_distrib, peval, sum_fin_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [sqP, divNat_finProdFinEquiv, modNat_finProdFinEquiv, finProdFinEquiv_apply_val]
  push_cast
  ring

theorem peval_sqQ {l : ℕ} (A B : Fin l → ℤ) (z : ℂ) :
    peval (sqQ A B) z =
      peval (halfSum A B) z * peval A (z ^ l) - peval (halfDiff A B) z * peval (seqRev B) (z ^ l) := by
  rw [peval_mul_comp, peval_mul_comp, ← Finset.sum_sub_distrib, peval, sum_fin_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [sqQ, divNat_finProdFinEquiv, modNat_finProdFinEquiv, finProdFinEquiv_apply_val]
  push_cast
  ring

theorem two_mul_halfSum {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B) (x : Fin l) :
    2 * halfSum A B x = A x + B x := by
  simp only [halfSum]
  rcases hA x with h1 | h1 <;> rcases hB x with h2 | h2 <;> simp [h1, h2]

theorem two_mul_halfDiff {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B)
    (x : Fin l) : 2 * halfDiff A B x = A x - B x := by
  simp only [halfDiff]
  rcases hA x with h1 | h1 <;> rcases hB x with h2 | h2 <;> simp [h1, h2]

theorem peval_halfSum {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B) (z : ℂ) :
    2 * peval (halfSum A B) z = peval A z + peval B z := by
  simp only [peval, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ((2 * halfSum A B x : ℤ) : ℂ) = ((A x + B x : ℤ) : ℂ) := by rw [two_mul_halfSum hA hB]
  push_cast at h
  linear_combination z ^ (x : ℕ) * h

theorem peval_halfDiff {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B) (z : ℂ) :
    2 * peval (halfDiff A B) z = peval A z - peval B z := by
  simp only [peval, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ((2 * halfDiff A B x : ℤ) : ℂ) = ((A x - B x : ℤ) : ℂ) := by rw [two_mul_halfDiff hA hB]
  push_cast at h
  linear_combination z ^ (x : ℕ) * h

/-- Lemma `lem:square`, Golay property: `|P(z)|² + |Q(z)|² = 2 l²` on the unit circle. -/
theorem isGolay_sq {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B)
    (h : IsGolay A B) : IsGolay (sqP A B) (sqQ A B) := by
  intro z hz
  have hw : ‖z ^ l‖ = 1 := by rw [norm_pow, hz, one_pow]
  rw [peval_sqP, peval_sqQ, peval_rev A hw, peval_rev B hw, square_identity_pow _ _ _ _ _ hw,
    h _ hw]
  -- `|U(z)|² + |V(z)|² = (|A(z)|² + |B(z)|²) / 2 = l`
  have hU := peval_halfSum hA hB z
  have hV := peval_halfDiff hA hB z
  have hd := doubling_identity (peval A z) (peval B z) 1 (by simp)
  simp only [one_mul] at hd
  rw [← hU, ← hV, norm_mul, norm_mul] at hd
  simp only [Complex.norm_ofNat] at hd
  have hAB := h z hz
  have hUV : ‖peval (halfSum A B) z‖ ^ 2 + ‖peval (halfDiff A B) z‖ ^ 2 = l := by nlinarith
  rw [hUV]
  push_cast
  ring

private theorem conj_peval_one {n : ℕ} (A : Fin n → ℤ) : conj (peval A 1) = peval A 1 := by
  simp [peval, map_sum]

private theorem peval_one_sq {n : ℕ} (A : Fin n → ℤ) :
    ((‖peval A 1‖ ^ 2 : ℝ) : ℂ) = peval A 1 ^ 2 := by
  rw [norm_sq_eq, conj_peval_one, sq]

/-- Lemma `lem:square`, regularity: `P(1) = l`. -/
theorem sqP_one {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B)
    (h : IsGolay A B) : peval (sqP A B) 1 = l := by
  have h1 := h 1 (by simp)
  have e : peval A 1 ^ 2 + peval B 1 ^ 2 = 2 * l := by
    rw [← peval_one_sq, ← peval_one_sq]; exact_mod_cast h1
  have hU := peval_halfSum hA hB 1
  have hV := peval_halfDiff hA hB 1
  rw [peval_sqP, one_pow, peval_rev_one]
  linear_combination (1 / 2 * peval B 1) * hU + (1 / 2 * peval A 1) * hV + 1 / 2 * e

/-- Lemma `lem:square`, regularity: `Q(1) = l`. -/
theorem sqQ_one {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B)
    (h : IsGolay A B) : peval (sqQ A B) 1 = l := by
  have h1 := h 1 (by simp)
  have e : peval A 1 ^ 2 + peval B 1 ^ 2 = 2 * l := by
    rw [← peval_one_sq, ← peval_one_sq]; exact_mod_cast h1
  have hU := peval_halfSum hA hB 1
  have hV := peval_halfDiff hA hB 1
  rw [peval_sqQ, one_pow, peval_rev_one]
  linear_combination (1 / 2 * peval A 1) * hU - (1 / 2 * peval B 1) * hV + 1 / 2 * e

/-- Lemma `lem:square`: `P` is a sign sequence (exactly one of `U_x`, `V_x` is nonzero). -/
theorem isSignSeq_sqP {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B) :
    IsSignSeq (sqP A B) := by
  intro i
  simp only [sqP, halfSum, halfDiff, seqRev]
  generalize i.modNat = x
  generalize i.divNat = y
  rcases hA x with h1 | h1 <;> rcases hB x with h2 | h2 <;> rcases hB y with h3 | h3 <;>
    rcases hA (Fin.rev y) with h4 | h4 <;> simp [h1, h2, h3, h4]

theorem isSignSeq_sqQ {l : ℕ} {A B : Fin l → ℤ} (hA : IsSignSeq A) (hB : IsSignSeq B) :
    IsSignSeq (sqQ A B) := by
  intro i
  simp only [sqQ, halfSum, halfDiff, seqRev]
  generalize i.modNat = x
  generalize i.divNat = y
  rcases hA x with h1 | h1 <;> rcases hB x with h2 | h2 <;> rcases hA y with h3 | h3 <;>
    rcases hB (Fin.rev y) with h4 | h4 <;> simp [h1, h2, h3, h4]

end SignCond
