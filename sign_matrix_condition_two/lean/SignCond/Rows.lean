import SignCond.Golay

/-!
# The four rows (Lemma `lem:rows`)

* `cs2`, `norm2_add_le`, `sqrt_norm2_add_le`: Cauchy–Schwarz in `ℝ²` and the triangle inequality
  in `ℂ²`, written with the four coordinates (used here and in `SignCond/Tails.lean`).
* `rows_energy_identity`: `|-(p+cr)|² + |p-cr|² + |q+ct|² + |q-ct|² = 2(|p|²+|q|²) + 2(|r|²+|t|²)`
  for `|c| = 1`.
* `rows_prefix_bounds`: if `|p|² + |q|² = 2l²` (`l ≥ 0`) and `ε ≥ 0` (in the paper `ε ∈ {0,1}`),
  then `2(l-ε)² ≤ |p-ε|² + |q-ε|² ≤ 2(l+ε)²`.
* `rows_arith`, `rows_arith_le` (and the integer forms `rows_arith_int`, `rows_arith_int_le`):
  `4(l+ε)² + 12r = 12j - 8s² - 8ε(l-3) ≤ 12j - 8s²` with `j = l² - ε + r`, `s = l - ε`.
* The sequence statement. `peval_tail`: deleting the first coefficient, `z · P̄(z) = P(z) - P₀`.
  `rowsEnergy Pb Qb R T z` is `|a(z)|² + |b(z)|² + |c(z)|² + |d(z)|²` for
  `a = -(Pb|R)`, `b = Pb|-R`, `c = Qb|T`, `d = Qb|-T`. `lem_rows_one` (`ε = 1`) and
  `lem_rows_zero` (`ε = 0`) give the sums `(-s, s, s, s)` and `4s² ≤ E ≤ 12j - 8s²` on the circle.
-/

open Complex ComplexConjugate

namespace SignCond

/-! ### Cauchy–Schwarz and the triangle inequality in `ℂ²` -/

/-- Cauchy–Schwarz in `ℝ²`: `ac + bd ≤ √(a²+b²) √(c²+d²)`. -/
theorem cs2 (a b c d : ℝ) :
    a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (a * d - b * c)]

/-- The triangle inequality in `ℂ²`, squared:
`|p+r|² + |q+t|² ≤ (√(|p|²+|q|²) + √(|r|²+|t|²))²`. -/
theorem norm2_add_le (p q r t : ℂ) :
    ‖p + r‖ ^ 2 + ‖q + t‖ ^ 2 ≤
      (Real.sqrt (‖p‖ ^ 2 + ‖q‖ ^ 2) + Real.sqrt (‖r‖ ^ 2 + ‖t‖ ^ 2)) ^ 2 := by
  have h1 := norm_add_le p r
  have h2 := norm_add_le q t
  have hcs := cs2 ‖p‖ ‖q‖ ‖r‖ ‖t‖
  have e1 := Real.sq_sqrt (show 0 ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2 by positivity)
  have e2 := Real.sq_sqrt (show 0 ≤ ‖r‖ ^ 2 + ‖t‖ ^ 2 by positivity)
  calc ‖p + r‖ ^ 2 + ‖q + t‖ ^ 2 ≤ (‖p‖ + ‖r‖) ^ 2 + (‖q‖ + ‖t‖) ^ 2 := by gcongr
    _ ≤ _ := by nlinarith

/-- The triangle inequality in `ℂ²` (unsquared). -/
theorem sqrt_norm2_add_le (p q r t : ℂ) :
    Real.sqrt (‖p + r‖ ^ 2 + ‖q + t‖ ^ 2) ≤
      Real.sqrt (‖p‖ ^ 2 + ‖q‖ ^ 2) + Real.sqrt (‖r‖ ^ 2 + ‖t‖ ^ 2) := by
  rw [Real.sqrt_le_left (by positivity)]
  exact norm2_add_le p q r t

/-! ### Pointwise facts -/

/-- Lemma `lem:rows`, proof: for `|c| = 1`,
`|-(p+cr)|² + |p-cr|² + |q+ct|² + |q-ct|² = 2(|p|²+|q|²) + 2(|r|²+|t|²)`. -/
theorem rows_energy_identity (p q r t c : ℂ) (hc : ‖c‖ = 1) :
    ‖-(p + c * r)‖ ^ 2 + ‖p - c * r‖ ^ 2 + ‖q + c * t‖ ^ 2 + ‖q - c * t‖ ^ 2 =
      2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) + 2 * (‖r‖ ^ 2 + ‖t‖ ^ 2) := by
  rw [norm_neg]
  have h1 := doubling_identity p r c hc
  have h2 := doubling_identity q t c hc
  linarith

private theorem sq_norm_sub_ofReal (p : ℂ) (e : ℝ) :
    ‖p - e‖ ^ 2 = (p.re - e) ^ 2 + p.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- Lemma `lem:rows`, proof: if `|p|² + |q|² = 2l²` with `l ≥ 0` and `ε ≥ 0`, then
`2(l-ε)² ≤ |p-ε|² + |q-ε|² ≤ 2(l+ε)²` (the vector `(p, q)` has norm `√2 l`, `(ε, ε)` has norm
`√2 ε`). The paper uses `ε ∈ {0, 1}`. -/
theorem rows_prefix_bounds (p q : ℂ) {l ε : ℝ} (hl : 0 ≤ l) (hε : 0 ≤ ε)
    (h : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 2 * l ^ 2) :
    2 * (l - ε) ^ 2 ≤ ‖p - ε‖ ^ 2 + ‖q - ε‖ ^ 2 ∧
      ‖p - ε‖ ^ 2 + ‖q - ε‖ ^ 2 ≤ 2 * (l + ε) ^ 2 := by
  rw [sq_norm_sub_ofReal, sq_norm_sub_ofReal]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h
  -- `|Re p + Re q| ≤ √2 · √(|p|² + |q|²) = 2l`
  have hsq : (p.re + q.re) ^ 2 ≤ (2 * l) ^ 2 := by
    nlinarith [sq_nonneg (p.re - q.re), sq_nonneg p.im, sq_nonneg q.im]
  have habs := abs_le_of_sq_le_sq hsq (by linarith)
  rw [abs_le] at habs
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left habs.1 hε, mul_le_mul_of_nonneg_left habs.2 hε]

/-- Lemma `lem:rows`, the arithmetic: with `j = l² - ε + r` and `s = l - ε`, `ε ∈ {0,1}`,
`4(l+ε)² + 12r = 12j - 8s² - 8ε(l-3)`. -/
theorem rows_arith (l ε r : ℝ) (hε : ε = 0 ∨ ε = 1) :
    4 * (l + ε) ^ 2 + 12 * r = 12 * (l ^ 2 - ε + r) - 8 * (l - ε) ^ 2 - 8 * ε * (l - 3) := by
  rcases hε with rfl | rfl <;> ring

/-- Lemma `lem:rows`, the arithmetic, inequality form (needs only `l ≥ 3`). -/
theorem rows_arith_le {l ε : ℝ} (r : ℝ) (hε : ε = 0 ∨ ε = 1) (hl : 3 ≤ l) :
    4 * (l + ε) ^ 2 + 12 * r ≤ 12 * (l ^ 2 - ε + r) - 8 * (l - ε) ^ 2 := by
  rw [rows_arith l ε r hε]
  have : 0 ≤ ε := by rcases hε with rfl | rfl <;> norm_num
  nlinarith

theorem rows_arith_int (l ε r : ℤ) (hε : ε = 0 ∨ ε = 1) :
    4 * (l + ε) ^ 2 + 12 * r = 12 * (l ^ 2 - ε + r) - 8 * (l - ε) ^ 2 - 8 * ε * (l - 3) := by
  rcases hε with rfl | rfl <;> ring

theorem rows_arith_int_le {l ε : ℤ} (r : ℤ) (hε : ε = 0 ∨ ε = 1) (hl : 3 ≤ l) :
    4 * (l + ε) ^ 2 + 12 * r ≤ 12 * (l ^ 2 - ε + r) - 8 * (l - ε) ^ 2 := by
  rw [rows_arith_int l ε r hε]
  have : 0 ≤ ε := by rcases hε with rfl | rfl <;> norm_num
  nlinarith

/-! ### The sequences -/

/-- Deleting the first coefficient: `z · P̄(z) = P(z) - P₀`. -/
theorem peval_tail {n : ℕ} (P : Fin (n + 1) → ℤ) (z : ℂ) :
    z * peval (Fin.tail P) z = peval P z - P 0 := by
  rw [peval, peval, Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.tail, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem peval_tail_one {n : ℕ} (P : Fin (n + 1) → ℤ) :
    peval (Fin.tail P) 1 = peval P 1 - P 0 := by
  simpa using peval_tail P 1

theorem norm_peval_tail {n : ℕ} (P : Fin (n + 1) → ℤ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖peval (Fin.tail P) z‖ = ‖peval P z - P 0‖ := by
  rw [← peval_tail, norm_mul, hz, one_mul]

/-- `E(z) = |a(z)|² + |b(z)|² + |c(z)|² + |d(z)|²` for the rows
`a = -(Pb|R)`, `b = Pb|-R`, `c = Qb|T`, `d = Qb|-T`. -/
noncomputable def rowsEnergy {n r : ℕ} (Pb Qb : Fin n → ℤ) (R T : Fin r → ℤ) (z : ℂ) : ℝ :=
  ‖peval (-Fin.append Pb R) z‖ ^ 2 + ‖peval (Fin.append Pb (-R)) z‖ ^ 2 +
    ‖peval (Fin.append Qb T) z‖ ^ 2 + ‖peval (Fin.append Qb (-T)) z‖ ^ 2

/-- `E = 2(|Pb|² + |Qb|²) + 2(|R|² + |T|²)` on the unit circle. -/
theorem rowsEnergy_eq {n r : ℕ} (Pb Qb : Fin n → ℤ) (R T : Fin r → ℤ) {z : ℂ} (hz : ‖z‖ = 1) :
    rowsEnergy Pb Qb R T z =
      2 * (‖peval Pb z‖ ^ 2 + ‖peval Qb z‖ ^ 2) + 2 * (‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2) := by
  rw [rowsEnergy, peval_neg, peval_append, peval_append, peval_append, peval_append, peval_neg,
    peval_neg, mul_neg, mul_neg, ← sub_eq_add_neg, ← sub_eq_add_neg]
  exact rows_energy_identity _ _ _ _ _ (by rw [norm_pow, hz, one_pow])

/-- The sums of the rows: `(-s, s, s, s)` when `Pb(1) = Qb(1) = s` and `R(1) = T(1) = 0`. -/
theorem rows_sums {n r : ℕ} (Pb Qb : Fin n → ℤ) (R T : Fin r → ℤ) {s : ℂ}
    (hP : peval Pb 1 = s) (hQ : peval Qb 1 = s) (hR : peval R 1 = 0) (hT : peval T 1 = 0) :
    peval (-Fin.append Pb R) 1 = -s ∧ peval (Fin.append Pb (-R)) 1 = s ∧
      peval (Fin.append Qb T) 1 = s ∧ peval (Fin.append Qb (-T)) 1 = s := by
  simp only [peval_neg, peval_append, hP, hQ, hR, hT, one_pow]
  simp

/-- Lemma `lem:rows`, energy bounds from the prefix bounds:
if `2s² ≤ |Pb|² + |Qb|² ≤ 2(l+ε)²` and `|R|² + |T|² ≤ 6r` at `z` (with `|z| = 1`), then
`4s² ≤ E(z) ≤ 4(l+ε)² + 12r`. -/
theorem rows_bounds {n r : ℕ} (Pb Qb : Fin n → ℤ) (R T : Fin r → ℤ) {z : ℂ} (hz : ‖z‖ = 1)
    {s l ε : ℝ} (hlo : 2 * s ^ 2 ≤ ‖peval Pb z‖ ^ 2 + ‖peval Qb z‖ ^ 2)
    (hhi : ‖peval Pb z‖ ^ 2 + ‖peval Qb z‖ ^ 2 ≤ 2 * (l + ε) ^ 2)
    (hRT : ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 ≤ 6 * r) :
    4 * s ^ 2 ≤ rowsEnergy Pb Qb R T z ∧ rowsEnergy Pb Qb R T z ≤ 4 * (l + ε) ^ 2 + 12 * r := by
  rw [rowsEnergy_eq Pb Qb R T hz]
  constructor <;> nlinarith [norm_nonneg (peval R z), norm_nonneg (peval T z)]

/-- Lemma `lem:rows`, case `ε = 1`. `(P, Q)` is a Golay pair of length `n + 1 = l²` with
`P(1) = Q(1) = l` and `P₀ = Q₀ = 1`; `P̄ = Fin.tail P`, `Q̄ = Fin.tail Q`; `(R, T)` is a tail of
length `r` with `R(1) = T(1) = 0` and `|R|² + |T|² ≤ 6r` on the circle. With `j = n + r` (the
length of the rows) and `s = l - 1`: the sums are `(-s, s, s, s)` and `4s² ≤ E ≤ 12j - 8s²` on
the unit circle. (The paper assumes `l ≥ 4` even; `l ≥ 3` suffices here.) -/
theorem lem_rows_one {n r : ℕ} {l : ℝ} (hl : 3 ≤ l) (P Q : Fin (n + 1) → ℤ) (R T : Fin r → ℤ)
    (hG : IsGolay P Q) (hlen : ((n + 1 : ℕ) : ℝ) = l ^ 2) (hP0 : P 0 = 1) (hQ0 : Q 0 = 1)
    (hP1 : peval P 1 = l) (hQ1 : peval Q 1 = l) (hR1 : peval R 1 = 0) (hT1 : peval T 1 = 0)
    (hRT : ∀ z : ℂ, ‖z‖ = 1 → ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 ≤ 6 * r) :
    (peval (-Fin.append (Fin.tail P) R) 1 = -((l - 1 : ℝ) : ℂ) ∧
      peval (Fin.append (Fin.tail P) (-R)) 1 = ((l - 1 : ℝ) : ℂ) ∧
      peval (Fin.append (Fin.tail Q) T) 1 = ((l - 1 : ℝ) : ℂ) ∧
      peval (Fin.append (Fin.tail Q) (-T)) 1 = ((l - 1 : ℝ) : ℂ)) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
      4 * (l - 1) ^ 2 ≤ rowsEnergy (Fin.tail P) (Fin.tail Q) R T z ∧
        rowsEnergy (Fin.tail P) (Fin.tail Q) R T z ≤ 12 * ((n + r : ℕ) : ℝ) - 8 * (l - 1) ^ 2 := by
  refine ⟨rows_sums _ _ R T ?_ ?_ hR1 hT1, fun z hz => ?_⟩
  · rw [peval_tail_one, hP1, hP0]; push_cast; ring
  · rw [peval_tail_one, hQ1, hQ0]; push_cast; ring
  have hg := hG z hz
  rw [hlen] at hg
  have hb := rows_prefix_bounds (peval P z) (peval Q z) (by linarith : (0 : ℝ) ≤ l)
    (zero_le_one) hg
  rw [Complex.ofReal_one] at hb
  have e1 := norm_peval_tail P hz
  have e2 := norm_peval_tail Q hz
  rw [hP0, Int.cast_one] at e1
  rw [hQ0, Int.cast_one] at e2
  have hrows := rows_bounds (Fin.tail P) (Fin.tail Q) R T hz (s := l - 1) (l := l) (ε := 1)
    (by rw [e1, e2]; exact hb.1) (by rw [e1, e2]; exact hb.2) (hRT z hz)
  have har := rows_arith_le (r : ℝ) (Or.inr rfl) hl
  have hn : ((n + r : ℕ) : ℝ) = l ^ 2 - 1 + r := by
    push_cast at hlen ⊢; linarith
  rw [hn]
  exact ⟨hrows.1, by linarith [hrows.2]⟩

/-- Lemma `lem:rows`, case `ε = 0`: no deletion, `s = l`, `j = n + r` with `n = l²`. -/
theorem lem_rows_zero {n r : ℕ} {l : ℝ} (hl : 3 ≤ l) (P Q : Fin n → ℤ) (R T : Fin r → ℤ)
    (hG : IsGolay P Q) (hlen : (n : ℝ) = l ^ 2)
    (hP1 : peval P 1 = l) (hQ1 : peval Q 1 = l) (hR1 : peval R 1 = 0) (hT1 : peval T 1 = 0)
    (hRT : ∀ z : ℂ, ‖z‖ = 1 → ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 ≤ 6 * r) :
    (peval (-Fin.append P R) 1 = -(l : ℂ) ∧ peval (Fin.append P (-R)) 1 = l ∧
      peval (Fin.append Q T) 1 = l ∧ peval (Fin.append Q (-T)) 1 = l) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
      4 * l ^ 2 ≤ rowsEnergy P Q R T z ∧
        rowsEnergy P Q R T z ≤ 12 * ((n + r : ℕ) : ℝ) - 8 * l ^ 2 := by
  refine ⟨rows_sums _ _ R T hP1 hQ1 hR1 hT1, fun z hz => ?_⟩
  have hg := hG z hz
  rw [hlen] at hg
  have hrows := rows_bounds P Q R T hz (s := l) (l := l) (ε := 0)
    (by linarith) (by linarith) (hRT z hz)
  have har := rows_arith_le (r : ℝ) (Or.inl rfl) hl
  have hn : ((n + r : ℕ) : ℝ) = l ^ 2 - 0 + r := by
    push_cast; linarith
  rw [hn]
  simp only [add_zero, sub_zero] at hrows har ⊢
  exact ⟨hrows.1, by linarith [hrows.2]⟩

end SignCond
