import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The scalar arithmetic in the proof of Proposition `prop:large`

* `sqrt_two_bounds`: `7/5 < √2 < 10/7`.
* `s_bounds` (the paragraph "The sums", `eq:sbounds`): `(4/5)√j - 1 < s ≤ √j`.
* `gamma_bounds` (the paragraph "The constant sector"): `ρ < γ < 2ρ` for `γ = 4s - 2m`.
* `no_endpoint`, `no_endpoint_real`: `25j = 2(5i+4)²` has no solution, so `ρ/2 ≠ i + 4/5`.
* `d_facts`: `(d⁺)² < 2(d - q - 1/5)²` for `(d, d⁺, q) ∈ {(64,80,7), (80,100,9), (100,104,9),
  (104,128,9)}`; `half_rho_lt` (`ρ/2 < l⁺/√2` from `j < (l⁺)²`); `k_lower` (the chain
  `s - m > 2^a q - 1`) and `k_lower_int` (hence `k ≥ 2^a q` for an integer `k`).
* `window_identity`: `(3ρ - 2s)² - (12j - 8s²) = 3(ρ - 2s)²` when `ρ² = 2j`; `window_bounds`:
  `ρ + δ < √E < 2ρ - δ`.
-/

namespace SignCond

/-- `7/5 < √2 < 10/7`. -/
theorem sqrt_two_bounds : 7 / 5 < Real.sqrt 2 ∧ Real.sqrt 2 < 10 / 7 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `eq:sbounds`: with `s = l - ε`, `l ≥ 0`, `l² ≤ j + ε < (l⁺)²`, `l ≥ (4/5) l⁺`, `ε ∈ {0,1}`:
`(4/5)√j - 1 < s ≤ √j`. (For `ε = 1` we assume `l ≥ 1`.) -/
theorem s_bounds {l lp j ε s : ℝ} (hε : ε = 0 ∨ ε = 1) (hs : s = l - ε) (hl : 1 ≤ l)
    (hj : 0 ≤ j) (hlj : l ^ 2 ≤ j + ε) (hlp : j + ε < lp ^ 2) (hlp0 : 0 ≤ lp)
    (hratio : 4 * lp ≤ 5 * l) :
    4 / 5 * Real.sqrt j - 1 < s ∧ s ≤ Real.sqrt j := by
  have hε0 : 0 ≤ ε := by rcases hε with rfl | rfl <;> norm_num
  have hε1 : ε ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
  have hsj := Real.sq_sqrt hj
  have hsj0 := Real.sqrt_nonneg j
  constructor
  · have : Real.sqrt j < lp := by
      rw [Real.sqrt_lt' (by nlinarith)]; linarith
    linarith
  · rw [hs]
    rcases hε with rfl | rfl
    · rw [sub_zero]; exact Real.le_sqrt_of_sq_le (by linarith)
    · exact Real.le_sqrt_of_sq_le (by nlinarith)

/-- The constant sector: if `ρ ≥ 90`, `√j = ρ/√2`, `(4/5)√j - 1 < s ≤ √j` and
`ρ/2 - 4/5 < m < ρ/2 + 1/5`, then `γ = 4s - 2m` satisfies `ρ < γ < 2ρ`. -/
theorem gamma_bounds {ρ s m sj : ℝ} (hρ : 90 ≤ ρ) (hsj : sj = ρ / Real.sqrt 2)
    (hs1 : 4 / 5 * sj - 1 < s) (hs2 : s ≤ sj) (hm1 : ρ / 2 - 4 / 5 < m) (hm2 : m < ρ / 2 + 1 / 5) :
    ρ < 4 * s - 2 * m ∧ 4 * s - 2 * m < 2 * ρ := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  have hpos : 0 < Real.sqrt 2 := by linarith
  have e : sj * Real.sqrt 2 = ρ := by rw [hsj]; field_simp
  have hsj0 : 0 < sj := by rw [hsj]; positivity
  have lo : 7 / 10 * ρ < sj := by nlinarith
  have hi : sj < 5 / 7 * ρ := by nlinarith
  constructor <;> linarith

/-- `25j = 2(5i+4)²` has no solution in naturals (it fails modulo `5`). -/
theorem no_endpoint (j i : ℕ) : 25 * j ≠ 2 * (5 * i + 4) ^ 2 := by
  intro h
  ring_nf at h
  omega

/-- Hence the endpoints of `(ρ/2 - 4/5, ρ/2 + 1/5)` are not integers: `√(2j)/2 ≠ i + 4/5`. -/
theorem no_endpoint_real (j i : ℕ) : Real.sqrt (2 * j) / 2 ≠ i + 4 / 5 := by
  intro h
  have hs : Real.sqrt (2 * j) = 2 * i + 8 / 5 := by linarith
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * j by positivity)
  rw [hs] at hsq
  have : ((25 * j : ℕ) : ℝ) = ((2 * (5 * i + 4) ^ 2 : ℕ) : ℝ) := by
    push_cast; linarith
  exact no_endpoint j i (by exact_mod_cast this)

/-- The four numeric facts `(d⁺)² < 2(d - q - 1/5)²`. -/
theorem d_facts :
    (80 : ℝ) ^ 2 < 2 * (64 - 7 - 1 / 5) ^ 2 ∧ (100 : ℝ) ^ 2 < 2 * (80 - 9 - 1 / 5) ^ 2 ∧
      (104 : ℝ) ^ 2 < 2 * (100 - 9 - 1 / 5) ^ 2 ∧ (128 : ℝ) ^ 2 < 2 * (104 - 9 - 1 / 5) ^ 2 := by
  norm_num

/-- `ρ/2 = √(j/2) < l⁺/√2` when `ρ = √(2j)`, `0 ≤ j < (l⁺)²`, `l⁺ ≥ 0`. -/
theorem half_rho_lt {j lp : ℝ} (hj : 0 ≤ j) (hlp : 0 ≤ lp) (h : j < lp ^ 2) :
    Real.sqrt (2 * j) / 2 < lp / Real.sqrt 2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hpos : 0 < Real.sqrt 2 := by norm_num
  rw [lt_div_iff₀ hpos, Real.sqrt_mul (by norm_num), mul_comm (Real.sqrt 2),
    show Real.sqrt j * Real.sqrt 2 / 2 * Real.sqrt 2 = Real.sqrt j * Real.sqrt 2 ^ 2 / 2 by ring, h2]
  have : Real.sqrt j < lp := by rw [Real.sqrt_lt' (by nlinarith)]; exact h
  linarith

/-- The size of the masks: if `s ≥ l - 1`, `l = X d` (`X = 2^a ≥ 1`), `m < ρ/2 + 1/5`,
`ρ/2 < X d⁺/√2` and `(d⁺)² < 2(d - q - 1/5)²` with `d - q - 1/5 > 0`, `d⁺ ≥ 0`, then
`s - m > X q - 1`. -/
theorem k_lower {s m ρ l d dp q X : ℝ} (hX : 1 ≤ X) (hl : l = X * d) (hs : l - 1 ≤ s)
    (hm : m < ρ / 2 + 1 / 5) (hρ : ρ / 2 < X * dp / Real.sqrt 2)
    (hd : dp ^ 2 < 2 * (d - q - 1 / 5) ^ 2) (hc : 0 < d - q - 1 / 5) (hdp : 0 ≤ dp) :
    X * q - 1 < s - m := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hpos : 0 < Real.sqrt 2 := by norm_num
  -- `d⁺ < √2 (d - q - 1/5)`, i.e. `d⁺/√2 < d - q - 1/5`
  have hlt : dp < Real.sqrt 2 * (d - q - 1 / 5) := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul hcon hcon (by positivity) hdp
    nlinarith
  have hdiv : X * dp / Real.sqrt 2 < X * (d - q - 1 / 5) := by
    rw [div_lt_iff₀ hpos]; nlinarith
  linarith

/-- With an integer `k = s - m`: `k ≥ 2^a q`. -/
theorem k_lower_int {k : ℤ} {a q : ℕ} (h : ((2 ^ a * q : ℕ) : ℝ) - 1 < k) : ((2 ^ a * q : ℕ) : ℤ) ≤ k := by
  have : (((2 ^ a * q : ℕ) : ℤ) : ℝ) - 1 < (k : ℝ) := by exact_mod_cast h
  have : ((2 ^ a * q : ℕ) : ℤ) - 1 < k := by exact_mod_cast this
  omega

/-- The window: `(3ρ - 2s)² - (12j - 8s²) = 3(ρ - 2s)²` when `ρ² = 2j`. -/
theorem window_identity {ρ s j : ℝ} (h : ρ ^ 2 = 2 * j) :
    (3 * ρ - 2 * s) ^ 2 - (12 * j - 8 * s ^ 2) = 3 * (ρ - 2 * s) ^ 2 := by
  linear_combination 6 * h

/-- The window: if `2s ≤ √E`, `(√E)² ≤ 12j - 8s²`, `δ < 2s - ρ`, `s ≤ √j` and
`ρ = √(2j) > 0`, then `ρ + δ < √E < 2ρ - δ` (`δ ≥ 0` is not needed). -/
theorem window_bounds {ρ s j δ e : ℝ} (hρ : ρ = Real.sqrt (2 * j)) (hρ0 : 0 < ρ)
    (hs : s ≤ Real.sqrt j) (h2s : 2 * s ≤ e) (he : e ^ 2 ≤ 12 * j - 8 * s ^ 2)
    (hδ : δ < 2 * s - ρ) : ρ + δ < e ∧ e < 2 * ρ - δ := by
  have hj : 0 < 2 * j := by rw [hρ] at hρ0; exact Real.sqrt_pos.mp hρ0
  have hρsq : ρ ^ 2 = 2 * j := by rw [hρ]; exact Real.sq_sqrt hj.le
  have hsj : Real.sqrt j ≤ ρ := by rw [hρ]; exact Real.sqrt_le_sqrt (by linarith)
  have hid := window_identity (s := s) hρsq
  have hpos : 0 ≤ 3 * ρ - 2 * s := by linarith
  have hsq : e ^ 2 ≤ (3 * ρ - 2 * s) ^ 2 := by nlinarith [sq_nonneg (ρ - 2 * s)]
  have habs := abs_le_of_sq_le_sq hsq hpos
  have := le_abs_self e
  constructor <;> linarith

end SignCond
