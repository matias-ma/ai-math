import SignCond.CriterionTau

/-!
# Lemmas `lem:sector` and `lem:scales` at a general scale `τ`

Paper (rewritten version), Lemma `lem:sector`: with `t = 2j`, `α = 2(s-k)`, `γ = 2(s+k)` and
`p_ν(x) = x² - (α² + 4t + ν) x + 4t² + 4tα + να²` (`pnu`), if `t/2 + 1 < τ² ≤ 2t`,
`τ ≤ γ < 2τ`, `p_ν(τ²) ≥ 0` and `p_ν(4τ²) > 0` for `ν ∈ {1, 4}`, then
`τ² I ⪯ K Kᵀ ≺ 4τ² I` for both borders.

The proof follows `SectorK.lean` / `SectorMatrix.lean` (the case `τ² = 2j`): `K1_form` and
`K3_form` write `‖Kᵀx‖²` as the quadratic form of `M` plus `γ²` times the square of the coordinate
on which `K` acts as `-γ`. The quadratic form of `M` splits into the `ν = 1` and `ν = 4` pieces,
whose determinants against `x (a² + y²)` are `dnu α c ν x = p_ν(x)` (with `c² = 4j = 2t`,
`dnu_eq_pnu`). Strict positivity of a `2 × 2` form with positive determinant is `quad_pos`; the
Cauchy–Schwarz version for the `ν = 4` plane is `quad_cs_pos`.

Lemma `lem:scales`: part 1 is the strict form of `sector_nonneg` (`Sector.lean`); part 2 uses the
two exact expansions `scales_expand_lo`, `scales_expand_hi` in powers of `ρ` and bounds them
coefficient by coefficient (`scales_lo_bound`, `scales_hi_bound`).
-/

open Matrix
open scoped Real

namespace SignCond

/-- Paper (Lemma `lem:sector`): `p_ν(x) = x² - (α² + 4t + ν) x + 4t² + 4tα + να²` with `t = 2j`. -/
noncomputable def pnu (j : ℕ) (α ν x : ℝ) : ℝ :=
  x ^ 2 - (α ^ 2 + 4 * (2 * (j : ℝ)) + ν) * x + 4 * (2 * (j : ℝ)) ^ 2 + 4 * (2 * (j : ℝ)) * α +
    ν * α ^ 2

/-! ### Determinants -/

/-- `det (B_y B_y^* - x I) = (α² + c² - x)(c² + ν - x) - c² ((1-α)² + ν - 1)`, with `c² = 2t`. -/
noncomputable def dnu (α c ν x : ℝ) : ℝ :=
  (α ^ 2 + c ^ 2 - x) * (c ^ 2 + ν - x) - c ^ 2 * ((1 - α) ^ 2 + (ν - 1))

theorem dnu_eq_pnu {j : ℕ} {c : ℝ} (hc : c ^ 2 = 4 * j) (α ν x : ℝ) :
    dnu α c ν x = pnu j α ν x := by
  unfold dnu pnu; rw [hc]; ring

theorem dnu_one (α c x : ℝ) :
    dnu α c 1 x = (α ^ 2 + c ^ 2 - x) * (c ^ 2 + 1 - x) - (c * (1 - α)) ^ 2 := by
  unfold dnu; ring

theorem dnu_one' (α c x : ℝ) :
    dnu α c 1 x = (x - α ^ 2 - c ^ 2) * (x - c ^ 2 - 1) - (-(c * (1 - α))) ^ 2 := by
  unfold dnu; ring

theorem dnu_four (α c x : ℝ) :
    dnu α c 4 x = (α ^ 2 + c ^ 2 - x) * (c ^ 2 + 4 - x) - c ^ 2 * ((1 - α) ^ 2 + 3) := by
  unfold dnu; ring

theorem dnu_four' (α c x : ℝ) :
    dnu α c 4 x = (x - α ^ 2 - c ^ 2) * (x - c ^ 2 - 4) - (-c) ^ 2 * ((1 - α) ^ 2 + 3) := by
  unfold dnu; ring

/-! ### Strict quadratic-form lemmas -/

/-- `A a² + 2 B a y + C y² > 0` for `(a, y) ≠ 0` when `C > 0` and `B² < A C`. -/
theorem quad_pos {A B C : ℝ} (a y : ℝ) (hC : 0 < C) (hdet : B ^ 2 < A * C)
    (hn : 0 < a ^ 2 + y ^ 2) : 0 < A * a ^ 2 + 2 * B * a * y + C * y ^ 2 := by
  have h : C * (A * a ^ 2 + 2 * B * a * y + C * y ^ 2) =
      (C * y + B * a) ^ 2 + (A * C - B ^ 2) * a ^ 2 := by ring
  rcases (sq_nonneg a).lt_or_eq with ha | ha
  · have h1 := mul_pos (sub_pos.2 hdet) ha
    have h2 : C * 0 < C * (A * a ^ 2 + 2 * B * a * y + C * y ^ 2) := by
      rw [h, mul_zero]; nlinarith [sq_nonneg (C * y + B * a)]
    exact lt_of_mul_lt_mul_left h2 hC.le
  · have ha0 : a = 0 := by simpa using ha.symm
    have hy : 0 < y ^ 2 := by rw [ha0] at hn; simpa using hn
    have e : A * a ^ 2 + 2 * B * a * y + C * y ^ 2 = C * y ^ 2 := by rw [ha0]; ring
    rw [e]; exact mul_pos hC hy

/-- `A X + 2 c m + C Y > 0` when `X, Y ≥ 0`, `X + Y > 0`, `C > 0`, `m² ≤ D X Y` and `c² D < A C`. -/
theorem quad_cs_pos {A C X Y m c D : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXY : 0 < X + Y) (hC : 0 < C)
    (hD : 0 ≤ D) (hm : m ^ 2 ≤ D * X * Y) (hdet : c ^ 2 * D < A * C) :
    0 < A * X + 2 * c * m + C * Y := by
  have hAC : 0 < A * C := lt_of_le_of_lt (mul_nonneg (sq_nonneg c) hD) hdet
  have hA : 0 < A := by
    by_contra h
    push_neg at h
    nlinarith
  have hP : 0 < A * X + C * Y := by
    rcases hX.lt_or_eq with h | h
    · have := mul_pos hA h; have := mul_nonneg hC.le hY; linarith
    · rw [← h] at hXY ⊢; have := mul_pos hC (by linarith : 0 < Y); linarith
  have h3 : 4 * c ^ 2 * m ^ 2 ≤ 4 * c ^ 2 * (D * X * Y) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have e1 : (2 * c * m) ^ 2 = 4 * c ^ 2 * m ^ 2 := by ring
  have e2 : (A * X + C * Y) ^ 2 = (A * X - C * Y) ^ 2 + 4 * (A * C * (X * Y)) := by ring
  have e3 : 4 * c ^ 2 * (D * X * Y) = 4 * (c ^ 2 * D * (X * Y)) := by ring
  have hsq : (2 * c * m) ^ 2 < (A * X + C * Y) ^ 2 := by
    rcases (mul_nonneg hX hY).lt_or_eq with hxy | hxy
    · have h4 : c ^ 2 * D * (X * Y) < A * C * (X * Y) := mul_lt_mul_of_pos_right hdet hxy
      have := sq_nonneg (A * X - C * Y)
      rw [e1, e2]
      linarith
    · have h5 : 4 * c ^ 2 * (D * X * Y) = 0 := by rw [e3, ← hxy]; ring
      have h6 := pow_pos hP 2
      rw [e1]
      linarith
  have := abs_lt_of_sq_lt_sq hsq hP.le
  have := neg_abs_le (2 * c * m)
  linarith

/-! ### The blocks at scale `τ` -/

/-- The scalar hypotheses in the form used below (`lo = τ²`, `hi = 4τ²`, `c² = 4j = 2t`):
`p_ν(lo) ≥ 0`, `p_ν(hi) > 0` for `ν ∈ {1, 4}`, `lo < c² + 1` and `c² + 4 < hi`. -/
structure SectorHypTau (α c lo hi : ℝ) : Prop where
  L1 : 0 ≤ dnu α c 1 lo
  L4 : 0 ≤ dnu α c 4 lo
  U1 : 0 < dnu α c 1 hi
  U4 : 0 < dnu α c 4 hi
  lo1 : lo < c ^ 2 + 1
  hi4 : c ^ 2 + 4 < hi

/-- The real `2 × 2` block `B₀` (`ν = 1`):
`lo (a² + y²) ≤ (-α a + c y)² + (c a + y)² ≤ hi (a² + y²)`, strictly on the right if `(a,y) ≠ 0`. -/
theorem block1_windowTau {α c lo hi : ℝ} (h : SectorHypTau α c lo hi) (a y : ℝ) :
    lo * (a ^ 2 + y ^ 2) ≤ (-α * a + c * y) ^ 2 + (c * a + y) ^ 2 ∧
      (-α * a + c * y) ^ 2 + (c * a + y) ^ 2 ≤ hi * (a ^ 2 + y ^ 2) ∧
      (0 < a ^ 2 + y ^ 2 → (-α * a + c * y) ^ 2 + (c * a + y) ^ 2 < hi * (a ^ 2 + y ^ 2)) := by
  have q1 := quad_nonneg (A := α ^ 2 + c ^ 2 - lo) (B := c * (1 - α)) (C := c ^ 2 + 1 - lo) a y
    (by linarith [h.lo1]) (by linarith [dnu_one α c lo, h.L1])
  have q2 := quad_nonneg (A := hi - α ^ 2 - c ^ 2) (B := -(c * (1 - α))) (C := hi - c ^ 2 - 1) a y
    (by linarith [h.hi4]) (by linarith [dnu_one' α c hi, h.U1])
  have e1 : (-α * a + c * y) ^ 2 + (c * a + y) ^ 2 - lo * (a ^ 2 + y ^ 2) =
      (α ^ 2 + c ^ 2 - lo) * a ^ 2 + 2 * (c * (1 - α)) * a * y + (c ^ 2 + 1 - lo) * y ^ 2 := by
    ring
  have e2 : hi * (a ^ 2 + y ^ 2) - ((-α * a + c * y) ^ 2 + (c * a + y) ^ 2) =
      (hi - α ^ 2 - c ^ 2) * a ^ 2 + 2 * (-(c * (1 - α))) * a * y + (hi - c ^ 2 - 1) * y ^ 2 := by
    ring
  refine ⟨by linarith, by linarith, fun hn => ?_⟩
  have q3 := quad_pos (A := hi - α ^ 2 - c ^ 2) (B := -(c * (1 - α))) (C := hi - c ^ 2 - 1) a y
    (by linarith [h.hi4]) (by linarith [dnu_one' α c hi, h.U1]) hn
  linarith

theorem phi3_lower_tau (α c x a0 a1 a2 y0 y1 y2 : ℝ) :
    phi3 α c a0 a1 a2 y0 y1 y2 - x * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2) =
      ((α ^ 2 + c ^ 2 - x) * (a0 - a1 + a2) ^ 2 +
          2 * (c * (1 - α)) * (a0 - a1 + a2) * (y0 - y1 + y2) +
          (c ^ 2 + 1 - x) * (y0 - y1 + y2) ^ 2) / 3 +
        ((α ^ 2 + c ^ 2 - x) * perpSq a0 a1 a2 + 2 * c * cross3 α a0 a1 a2 y0 y1 y2 +
          (c ^ 2 + 4 - x) * perpSq y0 y1 y2) := by
  unfold phi3 perpSq cross3; ring

theorem phi3_upper_tau (α c x a0 a1 a2 y0 y1 y2 : ℝ) :
    x * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2) - phi3 α c a0 a1 a2 y0 y1 y2 =
      ((x - α ^ 2 - c ^ 2) * (a0 - a1 + a2) ^ 2 +
          2 * (-(c * (1 - α))) * (a0 - a1 + a2) * (y0 - y1 + y2) +
          (x - c ^ 2 - 1) * (y0 - y1 + y2) ^ 2) / 3 +
        ((x - α ^ 2 - c ^ 2) * perpSq a0 a1 a2 + 2 * (-c) * cross3 α a0 a1 a2 y0 y1 y2 +
          (x - c ^ 2 - 4) * perpSq y0 y1 y2) := by
  unfold phi3 perpSq cross3; ring

theorem nsq_split (a0 a1 a2 y0 y1 y2 : ℝ) :
    a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2 =
      ((a0 - a1 + a2) ^ 2 + (y0 - y1 + y2) ^ 2) / 3 + (perpSq a0 a1 a2 + perpSq y0 y1 y2) := by
  unfold perpSq; ring

/-- The `3 × 3` part of `M` for `β = 3`: `lo N ≤ Φ ≤ hi N`, strictly on the right if `N > 0`,
where `N = ‖a‖² + ‖y‖²`. -/
theorem block3_windowTau {α c lo hi : ℝ} (h : SectorHypTau α c lo hi) (a0 a1 a2 y0 y1 y2 : ℝ) :
    lo * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2) ≤ phi3 α c a0 a1 a2 y0 y1 y2 ∧
      phi3 α c a0 a1 a2 y0 y1 y2 ≤ hi * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2) ∧
      (0 < a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2 →
        phi3 α c a0 a1 a2 y0 y1 y2 < hi * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2)) := by
  have hA1 : 0 ≤ perpSq a0 a1 a2 := by unfold perpSq; positivity
  have hY1 : 0 ≤ perpSq y0 y1 y2 := by unfold perpSq; positivity
  have hm := cross3_sq α a0 a1 a2 y0 y1 y2
  have hD : (0 : ℝ) ≤ (1 - α) ^ 2 + 3 := by positivity
  have q1 := quad_nonneg (A := α ^ 2 + c ^ 2 - lo) (B := c * (1 - α)) (C := c ^ 2 + 1 - lo)
    (a0 - a1 + a2) (y0 - y1 + y2) (by linarith [h.lo1]) (by linarith [dnu_one α c lo, h.L1])
  have q4 := quad_cs (A := α ^ 2 + c ^ 2 - lo) (C := c ^ 2 + 4 - lo) (c := c) hA1 hY1
    (by linarith [h.lo1]) hD hm (by linarith [dnu_four α c lo, h.L4])
  have r1 := quad_nonneg (A := hi - α ^ 2 - c ^ 2) (B := -(c * (1 - α))) (C := hi - c ^ 2 - 1)
    (a0 - a1 + a2) (y0 - y1 + y2) (by linarith [h.hi4]) (by linarith [dnu_one' α c hi, h.U1])
  have r4 := quad_cs (A := hi - α ^ 2 - c ^ 2) (C := hi - c ^ 2 - 4) (c := -c) hA1 hY1
    (by linarith [h.hi4]) hD hm (by linarith [dnu_four' α c hi, h.U4])
  have l := phi3_lower_tau α c lo a0 a1 a2 y0 y1 y2
  have u := phi3_upper_tau α c hi a0 a1 a2 y0 y1 y2
  refine ⟨by linarith, by linarith, fun hpos => ?_⟩
  rcases (add_nonneg (sq_nonneg (a0 - a1 + a2)) (sq_nonneg (y0 - y1 + y2))).lt_or_eq with hv | hv
  · have r1' := quad_pos (A := hi - α ^ 2 - c ^ 2) (B := -(c * (1 - α))) (C := hi - c ^ 2 - 1)
      (a0 - a1 + a2) (y0 - y1 + y2) (by linarith [h.hi4]) (by linarith [dnu_one' α c hi, h.U1]) hv
    linarith
  · have hs := nsq_split a0 a1 a2 y0 y1 y2
    have hp : 0 < perpSq a0 a1 a2 + perpSq y0 y1 y2 := by
      rw [← hv] at hs; linarith
    have r4' := quad_cs_pos (A := hi - α ^ 2 - c ^ 2) (C := hi - c ^ 2 - 4) (c := -c) hA1 hY1 hp
      (by linarith [h.hi4]) hD hm (by linarith [dnu_four' α c hi, h.U4])
    linarith

/-! ### The lemma -/

/-- **Lemma `lem:sector`** (body). -/
theorem sector_windowAt {j s k : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (hτlo : 2 * (j : ℝ) / 2 + 1 < τ ^ 2) (hτhi : τ ^ 2 ≤ 2 * (2 * (j : ℝ)))
    (hγ1 : τ ≤ 2 * ((s : ℝ) + k)) (hγ2 : 2 * ((s : ℝ) + k) < 2 * τ)
    (hp : ∀ ν : ℝ, (ν = 1 ∨ ν = 4) →
      0 ≤ pnu j (2 * ((s : ℝ) - k)) ν (τ ^ 2) ∧ 0 < pnu j (2 * ((s : ℝ) - k)) ν (4 * τ ^ 2)) :
    WindowAt (Kmat 1 ![-(s : ℝ), s, s, s] k j) τ ∧ WindowAt (Kmat 3 ![-(s : ℝ), s, s, s] k j) τ := by
  set α : ℝ := 2 * ((s : ℝ) - k) with hαdef
  set γ : ℝ := 2 * ((s : ℝ) + k) with hγdef
  set c : ℝ := 2 * Real.sqrt j with hcdef
  have hc2 : c ^ 2 = 4 * j := by
    rw [hcdef, mul_pow, Real.sq_sqrt (Nat.cast_nonneg j)]; ring
  have H : SectorHypTau α c (τ ^ 2) (4 * τ ^ 2) :=
    ⟨by rw [dnu_eq_pnu hc2]; exact (hp 1 (Or.inl rfl)).1,
      by rw [dnu_eq_pnu hc2]; exact (hp 4 (Or.inr rfl)).1,
      by rw [dnu_eq_pnu hc2]; exact (hp 1 (Or.inl rfl)).2,
      by rw [dnu_eq_pnu hc2]; exact (hp 4 (Or.inr rfl)).2,
      by rw [hc2]; linarith, by rw [hc2]; linarith⟩
  have hγlo : τ ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ hτ.le hγ1 2
  have hγhi : γ ^ 2 < 4 * τ ^ 2 := by nlinarith
  constructor
  · rw [windowAt_iff_form]
    intro x
    have hxx : x ≠ 0 → 0 < x ⬝ᵥ x := fun hx => dot_self_pos hx
    have hD := cs4_half (x (.inl 0)) (x (.inl 1)) (x (.inl 2)) (x (.inl 3))
    obtain ⟨b1, b2, b3⟩ := block1_windowTau H
      ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) (x (.inr 0))
    have hD0 : 0 ≤ x (.inl 0) ^ 2 + x (.inl 1) ^ 2 + x (.inl 2) ^ 2 + x (.inl 3) ^ 2 -
        ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 := by linarith
    have g1 := mul_le_mul_of_nonneg_right hγlo hD0
    have g2 := mul_le_mul_of_nonneg_right hγhi.le hD0
    have e : x ⬝ᵥ x = (((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 +
        x (.inr 0) ^ 2) + (x (.inl 0) ^ 2 + x (.inl 1) ^ 2 + x (.inl 2) ^ 2 + x (.inl 3) ^ 2 -
        ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2) := by
      simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_one]; ring
    rw [e] at hxx
    rw [K1_form, e, ← hαdef, ← hγdef, ← hcdef]
    refine ⟨by linarith, fun hx => ?_⟩
    have hpos := hxx hx
    rcases (add_nonneg (sq_nonneg ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2))
      (sq_nonneg (x (.inr 0)))).lt_or_eq with hn | hn
    · have := b3 hn
      linarith
    · have hDpos : 0 < x (.inl 0) ^ 2 + x (.inl 1) ^ 2 + x (.inl 2) ^ 2 + x (.inl 3) ^ 2 -
          ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 := by linarith
      have g3 := mul_lt_mul_of_pos_right hγhi hDpos
      linarith
  · rw [windowAt_iff_form]
    intro x
    have hxx : x ≠ 0 → 0 < x ⬝ᵥ x := fun hx => dot_self_pos hx
    obtain ⟨b1, b2, b3⟩ := block3_windowTau H
      ((x (.inl 0) + x (.inl 1) + x (.inl 2) - x (.inl 3)) / 2)
      ((x (.inl 0) + x (.inl 1) - x (.inl 2) + x (.inl 3)) / 2)
      ((x (.inl 0) - x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) (x (.inr 0)) (x (.inr 1))
      (x (.inr 2))
    have hπ := sq_nonneg ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2)
    have g1 := mul_le_mul_of_nonneg_right hγlo hπ
    have g2 := mul_le_mul_of_nonneg_right hγhi.le hπ
    have e : x ⬝ᵥ x =
        (((x (.inl 0) + x (.inl 1) + x (.inl 2) - x (.inl 3)) / 2) ^ 2 +
          ((x (.inl 0) + x (.inl 1) - x (.inl 2) + x (.inl 3)) / 2) ^ 2 +
          ((x (.inl 0) - x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 +
          x (.inr 0) ^ 2 + x (.inr 1) ^ 2 + x (.inr 2) ^ 2) +
        ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 := by
      simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three]; ring
    rw [e] at hxx
    rw [K3_form, e, ← hαdef, ← hγdef, ← hcdef]
    refine ⟨by linarith, fun hx => ?_⟩
    have hpos := hxx hx
    have hN0 : 0 ≤ ((x (.inl 0) + x (.inl 1) + x (.inl 2) - x (.inl 3)) / 2) ^ 2 +
          ((x (.inl 0) + x (.inl 1) - x (.inl 2) + x (.inl 3)) / 2) ^ 2 +
          ((x (.inl 0) - x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 +
          x (.inr 0) ^ 2 + x (.inr 1) ^ 2 + x (.inr 2) ^ 2 := by positivity
    rcases hN0.lt_or_eq with hn | hn
    · have := b3 hn
      linarith
    · have hπpos : 0 < ((-x (.inl 0) + x (.inl 1) + x (.inl 2) + x (.inl 3)) / 2) ^ 2 := by
        linarith
      have g3 := mul_lt_mul_of_pos_right hγhi hπpos
      linarith

/-- **Lemma `lem:sector`.** "Let `j\ge1` and `s\ge k\ge0` be integers, and suppose that
`s=(-s,s,s,s)`. Put `t=2j`, `\alpha=2(s-k)`, and `\gamma=2(s+k)`, and for `\nu\in\{1,4\}` let
`p_\nu(x)=x^2-(\alpha^2+4t+\nu)x+4t^2+4t\alpha+\nu\alpha^2`. Let `\tau>0` with
`\tfrac12t+1<\tau^2\le2t`. Suppose that `\tau\le\gamma<2\tau`, and that `p_\nu(\tau^2)\ge0` and
`p_\nu(4\tau^2)>0` for `\nu\in\{1,4\}`. Then `\tau^2I\preceq KK^\top\prec4\tau^2I` for both
`\beta=1` and `\beta=3`."

(`j ≥ 1` and `k ≤ s` are kept to mirror the paper; the proof does not use them.) -/
theorem lem_sector_tau {j s k : ℕ} (_hj : 1 ≤ j) (_hks : k ≤ s) (τ : ℝ) (hτ : 0 < τ)
    (hτlo : 2 * (j : ℝ) / 2 + 1 < τ ^ 2) (hτhi : τ ^ 2 ≤ 2 * (2 * (j : ℝ)))
    (hγ1 : τ ≤ 2 * ((s : ℝ) + k)) (hγ2 : 2 * ((s : ℝ) + k) < 2 * τ)
    (hp : ∀ ν : ℝ, (ν = 1 ∨ ν = 4) →
      0 ≤ pnu j (2 * ((s : ℝ) - k)) ν (τ ^ 2) ∧ 0 < pnu j (2 * ((s : ℝ) - k)) ν (4 * τ ^ 2)) :
    WindowAt (Kmat 1 ![-(s : ℝ), s, s, s] k j) τ ∧ WindowAt (Kmat 3 ![-(s : ℝ), s, s, s] k j) τ :=
  sector_windowAt τ hτ hτlo hτhi hγ1 hγ2 hp

/-! ### Lemma `lem:scales` -/

theorem pnu_two_j (j : ℕ) (α ν : ℝ) : pnu j α ν (2 * j) = sectorL ν (2 * j) α := by
  unfold pnu sectorL; ring

theorem pnu_eight_j (j : ℕ) (α ν : ℝ) : pnu j α ν (4 * (2 * j)) = sectorU ν (2 * j) α := by
  unfold pnu sectorU; ring

/-- Strict concavity bound: `U_4(α) > 0` on `[0, b]` when `U_4(0) > 0`, `U_4(b) > 0`, `t ≥ 1`. -/
theorem sectorU_four_pos_of_endpoints {t α b : ℝ} (ht : 1 ≤ t) (hα : 0 ≤ α) (hαb : α ≤ b)
    (h0 : 0 < sectorU 4 t 0) (hb : 0 < sectorU 4 t b) : 0 < sectorU 4 t α := by
  rcases hα.lt_or_eq with hα' | hα'
  · have hb0 : 0 < b := lt_of_lt_of_le hα' hαb
    have key := sectorU_four_interp t α b
    have h1 : 0 ≤ (b - α) * sectorU 4 t 0 := mul_nonneg (by linarith) h0.le
    have h2 : 0 < α * sectorU 4 t b := mul_pos hα' hb
    have h3 : 0 ≤ 4 * (t - 1) * b * α * (b - α) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * (t - 1)) hb0.le)
        hα) (by linarith : (0 : ℝ) ≤ b - α)
      linarith
    have h4 : b * 0 < b * sectorU 4 t α := by rw [mul_zero]; linarith
    exact lt_of_mul_lt_mul_left h4 hb0.le
  · rw [← hα']; exact h0

/-- **Lemma `lem:scales`, part 1.** If `j ≥ 5` and `0 ≤ α ≤ ρ`, then `p_ν(ρ²) ≥ 0` and
`p_ν(4ρ²) > 0` (`ρ = √(2j)`, `ν ∈ {1, 4}`). -/
theorem lem_scales_one {j : ℕ} {α : ℝ} (hj : 5 ≤ j) (hα0 : 0 ≤ α) (hαρ : α ≤ Real.sqrt (2 * j))
    {ν : ℝ} (hν : ν = 1 ∨ ν = 4) :
    0 ≤ pnu j α ν (Real.sqrt (2 * j) ^ 2) ∧ 0 < pnu j α ν (4 * Real.sqrt (2 * j) ^ 2) := by
  set ρ := Real.sqrt (2 * (j : ℝ)) with hρdef
  have hj5 : (5 : ℝ) ≤ j := by exact_mod_cast hj
  have hρ2 : ρ ^ 2 = 2 * j := Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ3 : 3 < ρ := by nlinarith
  rw [hρ2, pnu_two_j, pnu_eight_j]
  have hU4 : 0 < sectorU 4 (2 * j) α := by
    refine sectorU_four_pos_of_endpoints (by linarith) hα0 hαρ ?_ ?_
    · rw [sectorU_four_zero]
      have : 0 < 2 * (j : ℝ) - 4 := by linarith
      have : 0 < 4 * (2 * (j : ℝ)) := by linarith
      positivity
    · rw [← hρ2, sectorU_four_rho]
      have : 0 < ρ - 3 := by linarith
      have : 0 < 4 * ρ ^ 2 := by nlinarith
      positivity
  have hU1 : 0 < sectorU 1 (2 * j) α := by
    rw [sectorU_one]
    have : α ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hα0 hαρ 2
    nlinarith
  have hU : 0 < sectorU ν (2 * j) α := by rcases hν with rfl | rfl <;> assumption
  refine ⟨?_, hU⟩
  rw [sectorL_eq]
  have hν0 : 0 ≤ ν := by rcases hν with rfl | rfl <;> norm_num
  have : 0 ≤ 3 * (2 * (j : ℝ)) * α := by positivity
  have : 0 ≤ 3 / 4 * ν * α ^ 2 := by positivity
  linarith

/-- Paper, proof of Lemma `lem:scales`: with `α = ρ + u`, `τ = ρ + u/4`, `t = ρ²`,
`p_ν(τ²) = (8-7u)/2 ρ³ + u(64-31u)/16 ρ² + 3u(8ν-3u²)/16 ρ + 15u²(16ν-u²)/256`. -/
theorem scales_expand_lo (ρ u ν : ℝ) :
    ((ρ + u / 4) ^ 2) ^ 2 - ((ρ + u) ^ 2 + 4 * ρ ^ 2 + ν) * (ρ + u / 4) ^ 2 + 4 * (ρ ^ 2) ^ 2 +
        4 * ρ ^ 2 * (ρ + u) + ν * (ρ + u) ^ 2 =
      (8 - 7 * u) / 2 * ρ ^ 3 + u * (64 - 31 * u) / 16 * ρ ^ 2 +
        3 * u * (8 * ν - 3 * u ^ 2) / 16 * ρ + 15 * u ^ 2 * (16 * ν - u ^ 2) / 256 := by
  ring

/-- `p_ν(4τ²) = 2(2-u) ρ³ - (13u² - 16u + 12ν)/4 ρ² - (3/2) u³ ρ + 3u²(4ν - u²)/16`. -/
theorem scales_expand_hi (ρ u ν : ℝ) :
    (4 * (ρ + u / 4) ^ 2) ^ 2 - ((ρ + u) ^ 2 + 4 * ρ ^ 2 + ν) * (4 * (ρ + u / 4) ^ 2) +
        4 * (ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (ρ + u) + ν * (ρ + u) ^ 2 =
      2 * (2 - u) * ρ ^ 3 - (13 * u ^ 2 - 16 * u + 12 * ν) / 4 * ρ ^ 2 - 3 / 2 * u ^ 3 * ρ +
        3 * u ^ 2 * (4 * ν - u ^ 2) / 16 := by
  ring

theorem cube_bounds {u : ℝ} (hu : |u| < 1) : u ^ 2 < 1 ∧ -1 < u ^ 3 ∧ u ^ 3 < 1 := by
  have h3 : |u ^ 3| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg u) hu (by norm_num)
  have h2 : |u ^ 2| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg u) hu (by norm_num)
  obtain ⟨h3a, h3b⟩ := abs_lt.1 h3
  exact ⟨(abs_lt.1 h2).2, h3a, h3b⟩

/-- The coefficient bounds for `p_ν(τ²)`: it exceeds `ρ(ρ² - 12ρ - 12)/2`. -/
theorem scales_lo_bound {ρ u ν : ℝ} (hρ : 0 < ρ) (hu : |u| < 1) (hν : ν = 1 ∨ ν = 4) :
    ρ * (ρ ^ 2 - 12 * ρ - 12) / 2 < (8 - 7 * u) / 2 * ρ ^ 3 + u * (64 - 31 * u) / 16 * ρ ^ 2 +
        3 * u * (8 * ν - 3 * u ^ 2) / 16 * ρ + 15 * u ^ 2 * (16 * ν - u ^ 2) / 256 := by
  obtain ⟨hu1, hu2⟩ := abs_lt.1 hu
  obtain ⟨hsq, hc1, hc2⟩ := cube_bounds hu
  have c3 : 1 / 2 < (8 - 7 * u) / 2 := by linarith
  have c2 : -6 ≤ u * (64 - 31 * u) / 16 := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < u + 1) (by linarith : (0 : ℝ) < 1 - u)]
  have c1 : -6 ≤ 3 * u * (8 * ν - 3 * u ^ 2) / 16 := by
    rcases hν with rfl | rfl
    · nlinarith
    · have hq : 0 < 87 + 9 * u - 9 * u ^ 2 := by linarith
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + u) hq]
  have c0 : 0 ≤ 15 * u ^ 2 * (16 * ν - u ^ 2) / 256 := by
    have : 0 < 16 * ν - u ^ 2 := by rcases hν with rfl | rfl <;> linarith
    have := mul_nonneg (sq_nonneg u) this.le
    linarith
  have h3 : 1 / 2 * ρ ^ 3 < (8 - 7 * u) / 2 * ρ ^ 3 := mul_lt_mul_of_pos_right c3 (by positivity)
  have h2 : -6 * ρ ^ 2 ≤ u * (64 - 31 * u) / 16 * ρ ^ 2 :=
    mul_le_mul_of_nonneg_right c2 (sq_nonneg ρ)
  have h1 : -6 * ρ ≤ 3 * u * (8 * ν - 3 * u ^ 2) / 16 * ρ := mul_le_mul_of_nonneg_right c1 hρ.le
  have e : ρ * (ρ ^ 2 - 12 * ρ - 12) / 2 = 1 / 2 * ρ ^ 3 + -6 * ρ ^ 2 + -6 * ρ := by ring
  rw [e]
  linarith

/-- The coefficient bounds for `p_ν(4τ²)`: it exceeds `2ρ(ρ² - 10ρ - 1)`. -/
theorem scales_hi_bound {ρ u ν : ℝ} (hρ : 0 < ρ) (hu : |u| < 1) (hν : ν = 1 ∨ ν = 4) :
    2 * ρ * (ρ ^ 2 - 10 * ρ - 1) < 2 * (2 - u) * ρ ^ 3 -
        (13 * u ^ 2 - 16 * u + 12 * ν) / 4 * ρ ^ 2 - 3 / 2 * u ^ 3 * ρ +
        3 * u ^ 2 * (4 * ν - u ^ 2) / 16 := by
  obtain ⟨hu1, hu2⟩ := abs_lt.1 hu
  obtain ⟨hsq, hc1, hc2⟩ := cube_bounds hu
  have hν4 : ν ≤ 4 := by rcases hν with rfl | rfl <;> norm_num
  have d3 : 2 < 2 * (2 - u) := by linarith
  have d2 : -20 ≤ -(13 * u ^ 2 - 16 * u + 12 * ν) / 4 := by linarith
  have d1 : -2 ≤ -(3 / 2 * u ^ 3) := by linarith
  have d0 : 0 ≤ 3 * u ^ 2 * (4 * ν - u ^ 2) / 16 := by
    have : 0 < 4 * ν - u ^ 2 := by rcases hν with rfl | rfl <;> linarith
    have := mul_nonneg (sq_nonneg u) this.le
    linarith
  have h3 : 2 * ρ ^ 3 < 2 * (2 - u) * ρ ^ 3 := mul_lt_mul_of_pos_right d3 (by positivity)
  have h2 : -20 * ρ ^ 2 ≤ -(13 * u ^ 2 - 16 * u + 12 * ν) / 4 * ρ ^ 2 :=
    mul_le_mul_of_nonneg_right d2 (sq_nonneg ρ)
  have h1 : -2 * ρ ≤ -(3 / 2 * u ^ 3) * ρ := mul_le_mul_of_nonneg_right d1 hρ.le
  have e : 2 * ρ * (ρ ^ 2 - 10 * ρ - 1) = 2 * ρ ^ 3 + -20 * ρ ^ 2 + -2 * ρ := by ring
  rw [e]
  linarith

/-- **Lemma `lem:scales`, part 2.** If `ρ ≥ 14` and `|α - ρ| < 1`, then `τ = (3ρ + α)/4` satisfies
`p_ν(τ²) > 0` and `p_ν(4τ²) > 0` (`ρ = √(2j)`, `ν ∈ {1, 4}`). -/
theorem lem_scales_two {j : ℕ} {α : ℝ} (hρ : 14 ≤ Real.sqrt (2 * j))
    (hα : |α - Real.sqrt (2 * j)| < 1) {ν : ℝ} (hν : ν = 1 ∨ ν = 4) :
    0 < pnu j α ν (((3 * Real.sqrt (2 * j) + α) / 4) ^ 2) ∧
      0 < pnu j α ν (4 * ((3 * Real.sqrt (2 * j) + α) / 4) ^ 2) := by
  set ρ := Real.sqrt (2 * (j : ℝ)) with hρdef
  have hρ2 : 2 * (j : ℝ) = ρ ^ 2 := (Real.sq_sqrt (by positivity)).symm
  obtain ⟨u, rfl⟩ : ∃ u, α = ρ + u := ⟨α - ρ, by ring⟩
  have hu : |u| < 1 := by simpa using hα
  have hτ : (3 * ρ + (ρ + u)) / 4 = ρ + u / 4 := by ring
  have hρ0 : 0 < ρ := by linarith
  rw [hτ]
  unfold pnu
  rw [hρ2]
  constructor
  · have E := scales_expand_lo ρ u ν
    have B := scales_lo_bound hρ0 hu hν
    have hq : 0 < ρ ^ 2 - 12 * ρ - 12 := by nlinarith
    have : 0 < ρ * (ρ ^ 2 - 12 * ρ - 12) / 2 := by positivity
    linarith
  · have E := scales_expand_hi ρ u ν
    have B := scales_hi_bound hρ0 hu hν
    have hq : 0 < ρ ^ 2 - 10 * ρ - 1 := by nlinarith
    have : 0 < 2 * ρ * (ρ ^ 2 - 10 * ρ - 1) := by positivity
    linarith

/-- **Lemma `lem:scales`.** "Let `t=2j` and `\rho=\sqrt{t}`, let `\alpha` be a real number, and let
`p_\nu` be as in Lemma `lem:sector`, for `\nu\in\{1,4\}`.
1. If `j\ge5` and `0\le\alpha\le\rho`, then `p_\nu(\rho^2)\ge0` and `p_\nu(4\rho^2)>0`.
2. If `\rho\ge14` and `|\alpha-\rho|<1`, then `\tau=\tfrac14(3\rho+\alpha)` satisfies
   `p_\nu(\tau^2)>0` and `p_\nu(4\tau^2)>0`." -/
theorem lem_scales (j : ℕ) (α : ℝ) :
    (5 ≤ j → 0 ≤ α → α ≤ Real.sqrt (2 * j) → ∀ ν : ℝ, (ν = 1 ∨ ν = 4) →
      0 ≤ pnu j α ν (Real.sqrt (2 * j) ^ 2) ∧ 0 < pnu j α ν (4 * Real.sqrt (2 * j) ^ 2)) ∧
    (14 ≤ Real.sqrt (2 * j) → |α - Real.sqrt (2 * j)| < 1 → ∀ ν : ℝ, (ν = 1 ∨ ν = 4) →
      0 < pnu j α ν (((3 * Real.sqrt (2 * j) + α) / 4) ^ 2) ∧
        0 < pnu j α ν (4 * ((3 * Real.sqrt (2 * j) + α) / 4) ^ 2)) :=
  ⟨fun hj hα0 hαρ _ hν => lem_scales_one hj hα0 hαρ hν,
    fun hρ hα _ hν => lem_scales_two hρ hα hν⟩

end SignCond
