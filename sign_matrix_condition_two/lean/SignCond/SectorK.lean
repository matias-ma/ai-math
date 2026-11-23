import SignCond.Defs

/-!
# Lemma `lem:sector` at the level of the matrix `K`

The paper multiplies the first four rows of `K` by `-Oᵀ`, splits off `-γ I_{4-β}`, and reduces the
remaining matrix `M` to the blocks `B_y`. We follow the same splitting with explicit coordinates:
for `x = (x_top, y)` put `p = -Oᵀ x_top`, `a = V_βᵀ p / 2 = U_βᵀ x_top / 2` and (for `β = 3`)
`π = 𝟙ᵀ p / 2`. Then (`K1_form`, `K3_form`)

* `β = 1`: `‖Kᵀx‖² = (-α a + c y)² + (c a + y)² + γ² (‖x_top‖² - a²)`,
* `β = 3`: `‖Kᵀx‖² = ‖-α a + c y‖² + ‖c a + G₃ᵀ y‖² + γ² π²`, `‖x_top‖² = ‖a‖² + π²`,

with `c = 2√j = √(2t)`, `t = 2j`. The first two terms are the quadratic form of `M`; for `β = 3`
it splits further along `v = (1,-1,1)` (the kernel of `G₃ - I`, eigenvalue `1` of `G₃`, `ν = 1`) and
its orthogonal plane (eigenvalues `1 ± i√3`, `ν = 4`). Each piece is bounded by the determinants
`L_ν`, `U_ν` of `Sector.lean` (`sector_nonneg`), exactly as for the blocks `B_y`.
-/

open Matrix

namespace SignCond

/-! ### Quadratic-form lemmas -/

/-- `A a² + 2 B a y + C y² ≥ 0` when `C > 0` and `B² ≤ A C`. -/
theorem quad_nonneg {A B C : ℝ} (a y : ℝ) (hC : 0 < C) (hdet : B ^ 2 ≤ A * C) :
    0 ≤ A * a ^ 2 + 2 * B * a * y + C * y ^ 2 := by
  have h : C * (A * a ^ 2 + 2 * B * a * y + C * y ^ 2) =
      (C * y + B * a) ^ 2 + (A * C - B ^ 2) * a ^ 2 := by ring
  have h2 : 0 ≤ C * (A * a ^ 2 + 2 * B * a * y + C * y ^ 2) := by
    rw [h]; have := mul_nonneg (sub_nonneg.2 hdet) (sq_nonneg a); positivity
  rw [mul_comm] at h2
  exact nonneg_of_mul_nonneg_left h2 hC

/-- `A X + 2 c m + C Y ≥ 0` when `X, Y ≥ 0`, `C > 0`, `m² ≤ D X Y` and `c² D ≤ A C`. -/
theorem quad_cs {A C X Y m c D : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hC : 0 < C) (hD : 0 ≤ D)
    (hm : m ^ 2 ≤ D * X * Y) (hdet : c ^ 2 * D ≤ A * C) : 0 ≤ A * X + 2 * c * m + C * Y := by
  have hA : 0 ≤ A := by
    have h1 : 0 ≤ A * C := le_trans (mul_nonneg (sq_nonneg c) hD) hdet
    exact nonneg_of_mul_nonneg_left h1 hC
  have hs : 0 ≤ A * X + C * Y := by positivity
  have hXY : 0 ≤ X * Y := mul_nonneg hX hY
  have h3 : 4 * c ^ 2 * m ^ 2 ≤ 4 * c ^ 2 * (D * X * Y) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have h4 : c ^ 2 * D * (X * Y) ≤ A * C * (X * Y) := mul_le_mul_of_nonneg_right hdet hXY
  have h1 : (2 * c * m) ^ 2 ≤ (A * X + C * Y) ^ 2 := by
    have e1 : (2 * c * m) ^ 2 = 4 * c ^ 2 * m ^ 2 := by ring
    have e2 : (A * X + C * Y) ^ 2 = (A * X - C * Y) ^ 2 + 4 * (A * C * (X * Y)) := by ring
    have e3 : 4 * c ^ 2 * (D * X * Y) = 4 * (c ^ 2 * D * (X * Y)) := by ring
    rw [e1, e2]
    have := sq_nonneg (A * X - C * Y)
    linarith
  have := abs_le_of_sq_le_sq h1 hs
  have := neg_abs_le (2 * c * m)
  linarith

/-- Cauchy–Schwarz in `ℝ³`. -/
theorem cs3 (b0 b1 b2 w0 w1 w2 : ℝ) :
    (b0 * w0 + b1 * w1 + b2 * w2) ^ 2 ≤ (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) := by
  nlinarith [sq_nonneg (b0 * w1 - b1 * w0), sq_nonneg (b0 * w2 - b2 * w0),
    sq_nonneg (b1 * w2 - b2 * w1)]

/-- Cauchy–Schwarz in `ℝ⁴` against `(-1, 1, 1, 1)/2`: `a² ≤ ‖x‖²` for `a = (-x₀+x₁+x₂+x₃)/2`. -/
theorem cs4_half (x0 x1 x2 x3 : ℝ) :
    ((-x0 + x1 + x2 + x3) / 2) ^ 2 ≤ x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 := by
  nlinarith [sq_nonneg (x0 + x1), sq_nonneg (x0 + x2), sq_nonneg (x0 + x3), sq_nonneg (x1 - x2),
    sq_nonneg (x1 - x3), sq_nonneg (x2 - x3)]

/-! ### The `ν = 1` and `ν = 4` pieces -/

/-- The scalar hypotheses of Lemma `lem:sector` in the form used below: with `t = c²/2`,
`L_ν ≥ 0`, `U_ν ≥ 0` for `ν ∈ {1, 4}`, and `c² > 4` (so `2t - ν > 0`). -/
structure SectorHyp (α c : ℝ) : Prop where
  L1 : 0 ≤ sectorL 1 (c ^ 2 / 2) α
  L4 : 0 ≤ sectorL 4 (c ^ 2 / 2) α
  U1 : 0 ≤ sectorU 1 (c ^ 2 / 2) α
  U4 : 0 ≤ sectorU 4 (c ^ 2 / 2) α
  c4 : 4 < c ^ 2

theorem detL1 (α c : ℝ) :
    (α ^ 2 + c ^ 2 / 2) * (c ^ 2 / 2 + 1) - (c * (1 - α)) ^ 2 = sectorL 1 (c ^ 2 / 2) α := by
  unfold sectorL; ring

theorem detU1 (α c : ℝ) :
    (c ^ 2 - α ^ 2) * (c ^ 2 - 1) - (-(c * (1 - α))) ^ 2 = sectorU 1 (c ^ 2 / 2) α := by
  unfold sectorU; ring

theorem detL4 (α c : ℝ) :
    (α ^ 2 + c ^ 2 / 2) * (c ^ 2 / 2 + 4) - c ^ 2 * ((1 - α) ^ 2 + 3) = sectorL 4 (c ^ 2 / 2) α := by
  unfold sectorL; ring

theorem detU4 (α c : ℝ) :
    (c ^ 2 - α ^ 2) * (c ^ 2 - 4) - (-c) ^ 2 * ((1 - α) ^ 2 + 3) = sectorU 4 (c ^ 2 / 2) α := by
  unfold sectorU; ring

/-- The real `2 × 2` block `B₀` (`ν = 1`): with `t = c²/2`,
`t (a² + y²) ≤ (-α a + c y)² + (c a + y)² ≤ 4t (a² + y²)`. -/
theorem block1_window {α c : ℝ} (h : SectorHyp α c) (a y : ℝ) :
    c ^ 2 / 2 * (a ^ 2 + y ^ 2) ≤ (-α * a + c * y) ^ 2 + (c * a + y) ^ 2 ∧
      (-α * a + c * y) ^ 2 + (c * a + y) ^ 2 ≤ 2 * c ^ 2 * (a ^ 2 + y ^ 2) := by
  have hc := h.c4
  have q1 := quad_nonneg (A := α ^ 2 + c ^ 2 / 2) (B := c * (1 - α)) (C := c ^ 2 / 2 + 1) a y
    (by positivity) (by linarith [detL1 α c, h.L1])
  have q2 := quad_nonneg (A := c ^ 2 - α ^ 2) (B := -(c * (1 - α))) (C := c ^ 2 - 1) a y
    (by linarith) (by linarith [detU1 α c, h.U1])
  have e1 : (-α * a + c * y) ^ 2 + (c * a + y) ^ 2 - c ^ 2 / 2 * (a ^ 2 + y ^ 2) =
      (α ^ 2 + c ^ 2 / 2) * a ^ 2 + 2 * (c * (1 - α)) * a * y + (c ^ 2 / 2 + 1) * y ^ 2 := by ring
  have e2 : 2 * c ^ 2 * (a ^ 2 + y ^ 2) - ((-α * a + c * y) ^ 2 + (c * a + y) ^ 2) =
      (c ^ 2 - α ^ 2) * a ^ 2 + 2 * (-(c * (1 - α))) * a * y + (c ^ 2 - 1) * y ^ 2 := by ring
  constructor <;> linarith

/-- `Φ = ‖-α a + c y‖² + ‖c a + G₃ᵀ y‖²`, the quadratic form of `M` for `β = 3`. -/
noncomputable def phi3 (α c a0 a1 a2 y0 y1 y2 : ℝ) : ℝ :=
  (-α * a0 + c * y0) ^ 2 + (-α * a1 + c * y1) ^ 2 + (-α * a2 + c * y2) ^ 2 +
    (c * a0 + (y0 - y1 - y2)) ^ 2 + (c * a1 + (y0 + y1 - y2)) ^ 2 + (c * a2 + (y0 + y1 + y2)) ^ 2

/-- `‖a₁‖²` for the component `a₁` of `a` orthogonal to `v = (1,-1,1)`. -/
noncomputable def perpSq (a0 a1 a2 : ℝ) : ℝ :=
  (a0 - (a0 - a1 + a2) / 3) ^ 2 + (a1 + (a0 - a1 + a2) / 3) ^ 2 + (a2 - (a0 - a1 + a2) / 3) ^ 2

/-- The cross term `m = (1-α) a₁·y₁ - a·S y` (`S = G₃ - I`). -/
noncomputable def cross3 (α a0 a1 a2 y0 y1 y2 : ℝ) : ℝ :=
  (1 - α) * ((a0 - (a0 - a1 + a2) / 3) * (y0 - (y0 - y1 + y2) / 3) +
      (a1 + (a0 - a1 + a2) / 3) * (y1 + (y0 - y1 + y2) / 3) +
      (a2 - (a0 - a1 + a2) / 3) * (y2 - (y0 - y1 + y2) / 3)) -
    (a0 * (y1 + y2) + a1 * (-y0 + y2) + a2 * (-y0 - y1))

theorem cross3_sq (α a0 a1 a2 y0 y1 y2 : ℝ) :
    cross3 α a0 a1 a2 y0 y1 y2 ^ 2 ≤ ((1 - α) ^ 2 + 3) * perpSq a0 a1 a2 * perpSq y0 y1 y2 := by
  have h := cs3 (a0 - (a0 - a1 + a2) / 3) (a1 + (a0 - a1 + a2) / 3) (a2 - (a0 - a1 + a2) / 3)
    ((1 - α) * (y0 - (y0 - y1 + y2) / 3) - (y1 + y2))
    ((1 - α) * (y1 + (y0 - y1 + y2) / 3) - (-y0 + y2))
    ((1 - α) * (y2 - (y0 - y1 + y2) / 3) - (-y0 - y1))
  have e1 : cross3 α a0 a1 a2 y0 y1 y2 =
      (a0 - (a0 - a1 + a2) / 3) * ((1 - α) * (y0 - (y0 - y1 + y2) / 3) - (y1 + y2)) +
      (a1 + (a0 - a1 + a2) / 3) * ((1 - α) * (y1 + (y0 - y1 + y2) / 3) - (-y0 + y2)) +
      (a2 - (a0 - a1 + a2) / 3) * ((1 - α) * (y2 - (y0 - y1 + y2) / 3) - (-y0 - y1)) := by
    unfold cross3; ring
  have e2 : ((1 - α) * (y0 - (y0 - y1 + y2) / 3) - (y1 + y2)) ^ 2 +
      ((1 - α) * (y1 + (y0 - y1 + y2) / 3) - (-y0 + y2)) ^ 2 +
      ((1 - α) * (y2 - (y0 - y1 + y2) / 3) - (-y0 - y1)) ^ 2 =
      ((1 - α) ^ 2 + 3) * perpSq y0 y1 y2 := by
    unfold perpSq; ring
  rw [e1]
  refine h.trans (le_of_eq ?_)
  rw [e2]
  unfold perpSq
  ring

theorem phi3_lower_id (α c a0 a1 a2 y0 y1 y2 : ℝ) :
    phi3 α c a0 a1 a2 y0 y1 y2 - c ^ 2 / 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2) =
      ((α ^ 2 + c ^ 2 / 2) * (a0 - a1 + a2) ^ 2 + 2 * (c * (1 - α)) * (a0 - a1 + a2) * (y0 - y1 + y2)
        + (c ^ 2 / 2 + 1) * (y0 - y1 + y2) ^ 2) / 3 +
      ((α ^ 2 + c ^ 2 / 2) * perpSq a0 a1 a2 + 2 * c * cross3 α a0 a1 a2 y0 y1 y2 +
        (c ^ 2 / 2 + 4) * perpSq y0 y1 y2) := by
  unfold phi3 perpSq cross3; ring

theorem phi3_upper_id (α c a0 a1 a2 y0 y1 y2 : ℝ) :
    2 * c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2) - phi3 α c a0 a1 a2 y0 y1 y2 =
      ((c ^ 2 - α ^ 2) * (a0 - a1 + a2) ^ 2 + 2 * (-(c * (1 - α))) * (a0 - a1 + a2) * (y0 - y1 + y2)
        + (c ^ 2 - 1) * (y0 - y1 + y2) ^ 2) / 3 +
      ((c ^ 2 - α ^ 2) * perpSq a0 a1 a2 + 2 * (-c) * cross3 α a0 a1 a2 y0 y1 y2 +
        (c ^ 2 - 4) * perpSq y0 y1 y2) := by
  unfold phi3 perpSq cross3; ring

/-- The `3 × 3` part of `M` for `β = 3`: with `t = c²/2`, `t N ≤ Φ ≤ 4t N`,
`N = ‖a‖² + ‖y‖²`. -/
theorem block3_window {α c : ℝ} (h : SectorHyp α c) (a0 a1 a2 y0 y1 y2 : ℝ) :
    c ^ 2 / 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2) ≤ phi3 α c a0 a1 a2 y0 y1 y2 ∧
      phi3 α c a0 a1 a2 y0 y1 y2 ≤ 2 * c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2) := by
  have hc := h.c4
  have hA1 : 0 ≤ perpSq a0 a1 a2 := by unfold perpSq; positivity
  have hY1 : 0 ≤ perpSq y0 y1 y2 := by unfold perpSq; positivity
  have hm := cross3_sq α a0 a1 a2 y0 y1 y2
  have hD : (0 : ℝ) ≤ (1 - α) ^ 2 + 3 := by positivity
  have q1 := quad_nonneg (A := α ^ 2 + c ^ 2 / 2) (B := c * (1 - α)) (C := c ^ 2 / 2 + 1)
    (a0 - a1 + a2) (y0 - y1 + y2) (by positivity) (by linarith [detL1 α c, h.L1])
  have q4 := quad_cs (A := α ^ 2 + c ^ 2 / 2) (C := c ^ 2 / 2 + 4) (c := c) hA1 hY1
    (by positivity) hD hm (by linarith [detL4 α c, h.L4])
  have r1 := quad_nonneg (A := c ^ 2 - α ^ 2) (B := -(c * (1 - α))) (C := c ^ 2 - 1)
    (a0 - a1 + a2) (y0 - y1 + y2) (by linarith) (by linarith [detU1 α c, h.U1])
  have r4 := quad_cs (A := c ^ 2 - α ^ 2) (C := c ^ 2 - 4) (c := -c) hA1 hY1
    (by linarith) hD hm (by linarith [detU4 α c, h.U4])
  have l := phi3_lower_id α c a0 a1 a2 y0 y1 y2
  have u := phi3_upper_id α c a0 a1 a2 y0 y1 y2
  constructor <;> linarith

end SignCond
