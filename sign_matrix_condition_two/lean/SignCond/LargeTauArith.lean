import SignCond.LargeArith

/-!
# The scalar arithmetic in the proof of Proposition `prop:large` (rewritten paper, `j ≥ 9999`)

All statements are inequalities between real numbers. Notation of the proof: `q = √j`,
`ρ = √(2j)` (so `ρ² = 2q²`), `s = l - ε`, `α` the even integer with `|α - ρ| < 1`,
`k = s - α/2` (i.e. `α = 2(s - k)`), `τ = (3ρ + α)/4`.

* `rho_q_bounds`: `7/5 q < ρ < 10/7 q` (from `ρ² = 2q²`, `7/5 < √2 < 10/7`).
* `exists_even_near`: "Since `ρ² = 2j` is even, `ρ` is not an odd integer, so there is a unique even
  integer `α` with `|α - ρ| < 1`" (existence, `α = 2m`).
* `k_pos_arith`: `α/2 < s`, i.e. `k > 0` ("`k > (3/35)√j - 3/2 > 0`"); `alpha_pos_arith`: `α > 0`.
* `sector_arith`: the paragraph "The constant sector": `t/2 + 1 < τ² ≤ 2t` and `τ ≤ γ < 2τ` for
  `γ = 2(s + k)`, and `ρ ≥ 14`.
* `upper_arith`: eq. `upper`, `√(12j - 8s² + 800) < 3ρ - 2s - 3/4`, via `D = 2s - ρ` and the
  identity `upper_identity`.
* `masks_arith`: the paragraph "The masks" when `α < ρ`: `k > 12` and `j < 196k²`.
* `energy_lt_arith`: `E_ℓ < 8j`; `bias_arith`: `√E_ℓ / 2 ≤ ((j - s)/2)/33`;
  `card_arith`: `k ≤ (j - s)/2`.
* `window_arith`: the paragraph "The window" (eq. `window`), both cases.
-/

namespace SignCond

/-- `7/5 q < ρ < 10/7 q` when `ρ² = 2q²`, `ρ ≥ 0`, `q > 0`. -/
theorem rho_q_bounds {ρ q : ℝ} (hρ : 0 ≤ ρ) (hq : 0 < q) (h : ρ ^ 2 = 2 * q ^ 2) :
    7 / 5 * q < ρ ∧ ρ < 10 / 7 * q := by
  constructor
  · by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul hc hc hρ (by positivity)]
  · by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul hc hc (by positivity) hρ]

/-- `(2m - 1)² = 2j` has no solution: an odd square is odd. -/
theorem odd_sq_ne_two_mul (j n : ℕ) : (2 * n + 1) ^ 2 ≠ 2 * j := by
  intro h
  ring_nf at h
  omega

/-- Paper: "Since `ρ² = 2j` is even, `ρ` is not an odd integer, so there is a unique even integer
`α` with `|α - ρ| < 1`." (Existence; `α = 2m`.) -/
theorem exists_even_near (j : ℕ) : ∃ m : ℕ, |2 * (m : ℝ) - Real.sqrt (2 * j)| < 1 := by
  set ρ := Real.sqrt (2 * (j : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = 2 * j := Real.sq_sqrt (by positivity)
  set m := ⌊(ρ + 1) / 2⌋₊ with hmdef
  have h1 : (m : ℝ) ≤ (ρ + 1) / 2 := Nat.floor_le (by positivity)
  have h2 : (ρ + 1) / 2 < m + 1 := Nat.lt_floor_add_one _
  have h3 : 2 * (m : ℝ) ≠ ρ + 1 := by
    intro heq
    have hm1 : 1 ≤ m := by
      by_contra hc
      have : m = 0 := by omega
      rw [this] at heq; simp at heq; linarith
    have hρ' : ρ = 2 * ((m - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hm1]; push_cast; linarith
    rw [hρ'] at hρ2
    apply odd_sq_ne_two_mul j (m - 1)
    exact_mod_cast hρ2
  refine ⟨m, abs_lt.2 ⟨by linarith, ?_⟩⟩
  have : 2 * (m : ℝ) < ρ + 1 := lt_of_le_of_ne (by linarith) h3
  linarith

/-- `k > 0`: `α/2 < s` (paper: "`k > (3/35)√j - 3/2 > 0`"). -/
theorem k_pos_arith {q ρ s α : ℝ} (hρq : ρ < 10 / 7 * q) (hq : 99 < q) (hs1 : 4 / 5 * q - 1 < s)
    (hα : |α - ρ| < 1) : α / 2 < s := by
  have := (abs_lt.1 hα).2
  linarith

/-- `α > 0`. -/
theorem alpha_pos_arith {q ρ α : ℝ} (hρq : 7 / 5 * q < ρ) (hq : 99 < q) (hα : |α - ρ| < 1) :
    0 < α := by
  have := (abs_lt.1 hα).1
  linarith

/-- Paper, "The constant sector": `t/2 + 1 < τ² ≤ 2t` (`t = 2j`), `τ ≤ γ < 2τ` for
`γ = 2(s + k) = 4s - α`, and `ρ ≥ 14`, `τ > 0`. -/
theorem sector_arith {j q ρ s k α τ : ℝ} (hq0 : 0 ≤ q) (hqj : q ^ 2 = j) (hρ0 : 0 ≤ ρ)
    (hρj : ρ ^ 2 = 2 * j) (hq99 : 99 < q) (hs1 : 4 / 5 * q - 1 < s) (hs2 : s ≤ q)
    (hα : |α - ρ| < 1) (hk : α = 2 * (s - k)) (hτ : τ = (3 * ρ + α) / 4) :
    2 * j / 2 + 1 < τ ^ 2 ∧ τ ^ 2 ≤ 2 * (2 * j) ∧ τ ≤ 2 * (s + k) ∧ 2 * (s + k) < 2 * τ ∧
      0 < τ ∧ 14 ≤ ρ := by
  obtain ⟨hρ1, hρ2⟩ := rho_q_bounds (q := q) hρ0 (by linarith) (by rw [hρj, ← hqj])
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  have hτ1 : ρ - 1 / 4 < τ := by rw [hτ]; linarith
  have hτ2 : τ < ρ + 1 / 4 := by rw [hτ]; linarith
  have hτ0 : 0 < τ := by linarith
  refine ⟨?_, ?_, ?_, ?_, hτ0, by linarith⟩
  · have hp : 0 < (τ - (ρ - 1 / 4)) * (τ + (ρ - 1 / 4)) := mul_pos (by linarith) (by linarith)
    nlinarith
  · have hp : 0 < ((ρ + 1 / 4) - τ) * ((ρ + 1 / 4) + τ) := mul_pos (by linarith) (by linarith)
    nlinarith
  · rw [hτ]; linarith
  · rw [hτ]; linarith

/-- The identity behind eq. `upper`: with `D = 2s - ρ` and `ρ² = 2j`,
`(3ρ - 2s - 3/4)² - (12j - 8s² + 800) = 3D² + (3/2)D - 3ρ + 9/16 - 800`. -/
theorem upper_identity {ρ s j : ℝ} (h : ρ ^ 2 = 2 * j) :
    (3 * ρ - 2 * s - 3 / 4) ^ 2 - (12 * j - 8 * s ^ 2 + 800) =
      3 * (2 * s - ρ) ^ 2 + 3 / 2 * (2 * s - ρ) - 3 * ρ + 9 / 16 - 800 := by
  linear_combination 6 * h

/-- `ρ < (99/56) l`, from `ρ² = 2j < 2(l⁺)²` and `4l⁺ ≤ 5l`. -/
theorem rho_lt_l {j l lp ρ : ℝ} (hl : 0 ≤ l) (hρ0 : 0 ≤ ρ) (hρj : ρ ^ 2 = 2 * j)
    (hjlp : j < lp ^ 2) (hlp0 : 0 ≤ lp) (hratio : 4 * lp ≤ 5 * l) : ρ < 99 / 56 * l := by
  have h16 : 16 * lp ^ 2 ≤ 25 * l ^ 2 := by nlinarith [mul_le_mul hratio hratio (by positivity) (by positivity)]
  by_contra hc
  push_neg at hc
  nlinarith [mul_le_mul hc hc (by positivity) hρ0]

/-- **eq. `upper`**: `√(12j - 8s² + 800) < 3ρ - 2s - 3/4`. Paper: "Put `D = 2s - ρ`. ... We have
`ρ < √2 l⁺ ≤ (5/4)√2 l < (99/56) l`, and therefore `D ≥ 2l - 2 - ρ > (13/56) l - 2 > 0`. Hence
`3D² + (3/2)D - 3ρ > 3((13/56)l - 2)² + (3/2)((13/56)l - 2) - (297/56) l`. The right-hand side is
increasing in `l` for `l ≥ 100`, and for `l = 100` it exceeds `851`." -/
theorem upper_arith {j l lp s ρ q : ℝ} (hl : 100 ≤ l) (hs : l - 1 ≤ s) (hsq : s ≤ q)
    (hρ0 : 0 ≤ ρ) (hρj : ρ ^ 2 = 2 * j) (hjlp : j < lp ^ 2) (hlp0 : 0 ≤ lp)
    (hratio : 4 * lp ≤ 5 * l) (hρq : 7 / 5 * q < ρ) :
    Real.sqrt (12 * j - 8 * s ^ 2 + 800) < 3 * ρ - 2 * s - 3 / 4 := by
  have hρl := rho_lt_l (by linarith) hρ0 hρj hjlp hlp0 hratio
  set x := 13 / 56 * l - 2 with hx
  have hx21 : 21 < x := by rw [hx]; linarith
  have hD : x < 2 * s - ρ := by rw [hx]; linarith
  have hD2 : x ^ 2 < (2 * s - ρ) ^ 2 := by
    have := mul_lt_mul'' hD hD (by linarith) (by linarith)
    nlinarith
  have hl' : l = 56 / 13 * (x + 2) := by rw [hx]; ring
  have hpos : 0 < 3 * ρ - 2 * s - 3 / 4 := by linarith
  have hkey : 0 < 3 * (2 * s - ρ) ^ 2 + 3 / 2 * (2 * s - ρ) - 3 * ρ + 9 / 16 - 800 := by
    have hρx : ρ < 99 / 56 * (56 / 13 * (x + 2)) := by rw [← hl']; exact hρl
    nlinarith [mul_pos (by linarith : (0 : ℝ) < x - 21) (by linarith : (0 : ℝ) < x - 21)]
  rw [Real.sqrt_lt' hpos]
  have := upper_identity (s := s) hρj
  linarith

/-- Paper, "The masks", case `α < ρ`: "`k > l - 1 - l⁺/√2`. We have `2(l - 13)² > (l⁺)²` ...
Hence `k > 12` ... we have `k > (3/35)√j - 1 ≥ (1/14)√j`, because `√j ≥ 70`. Thus `j ≤ 196k²`." -/
theorem masks_arith {j l lp s ρ q α k : ℝ} (hl : 100 ≤ l) (hs : l - 1 ≤ s) (hs1 : 4 / 5 * q - 1 < s)
    (_hq99 : 99 < q) (hq0 : 0 ≤ q) (hqj : q ^ 2 = j) (hρ0 : 0 ≤ ρ) (hρj : ρ ^ 2 = 2 * j)
    (hjlp : j < lp ^ 2) (h13 : lp ^ 2 < 2 * (l - 13) ^ 2) (hαρ : α < ρ) (hk : α = 2 * (s - k))
    (hρq : ρ < 10 / 7 * q) : 12 < k ∧ j < 196 * k ^ 2 := by
  have hρl : ρ < 2 * (l - 13) := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul hc hc (by linarith) hρ0]
  have hk' : k = s - α / 2 := by linarith
  refine ⟨by linarith, ?_⟩
  have h14 : q < 14 * k := by linarith
  have := mul_lt_mul'' h14 h14 hq0 hq0
  nlinarith

/-- Paper: "`E_ℓ < 8j`, because `8(l-1)² - (25/4) l² - 800 > 0` for `l ≥ 100`" (with
`E_ℓ ≤ 12j - 8s² + 800`, `s ≥ l - 1`, `j < (l⁺)² ≤ (25/16) l²`). -/
theorem energy_lt_arith {j l lp s E : ℝ} (hl : 100 ≤ l) (hs : l - 1 ≤ s) (hjlp : j < lp ^ 2)
    (hlp0 : 0 ≤ lp) (hratio : 4 * lp ≤ 5 * l) (hE : E ≤ 12 * j - 8 * s ^ 2 + 800) : E < 8 * j := by
  have h16 : 16 * lp ^ 2 ≤ 25 * l ^ 2 := by
    nlinarith [mul_le_mul hratio hratio (by positivity) (by linarith)]
  have hs2 : (l - 1) ^ 2 ≤ s ^ 2 := by
    have := mul_le_mul hs hs (by linarith) (by linarith)
    nlinarith
  nlinarith

/-- Paper: "`|𝒫̂(ℓ)|/N < 2√(2j)/(j - √j) = 2√2/(√j - 1) < 1/33`", in the form used:
`√E/2 ≤ ((j - s)/2)/33` when `E < 8j`, `s ≤ √j = q`, `q > 99`. -/
theorem bias_arith {j q s E : ℝ} (hq99 : 99 < q) (hqj : q ^ 2 = j) (hsq : s ≤ q) (hE : E < 8 * j) :
    Real.sqrt E / 2 ≤ (j - s) / 2 / 33 := by
  have hy : 0 ≤ (q ^ 2 - q) / 33 := by nlinarith
  have hE' : E ≤ ((q ^ 2 - q) / 33) ^ 2 := by
    have h1 : (98 : ℝ) ^ 2 < (q - 1) ^ 2 := by nlinarith
    have : ((q ^ 2 - q) / 33) ^ 2 = q ^ 2 * (q - 1) ^ 2 / 1089 := by ring
    rw [this]
    have hq2 : 0 < q ^ 2 := by positivity
    nlinarith
  have := Real.sqrt_le_sqrt hE'
  rw [Real.sqrt_sq hy] at this
  have : (q ^ 2 - q) / 33 ≤ (j - s) / 33 := by rw [hqj]; linarith
  linarith

/-- Paper: "`½(j - s) ≥ s ≥ k`". -/
theorem card_arith {j q s k α : ℝ} (hq : 3 ≤ q) (hqj : q ^ 2 = j) (hsq : s ≤ q) (hα : 0 < α)
    (hk : α = 2 * (s - k)) : k ≤ (j - s) / 2 := by
  have : 3 * q ≤ q ^ 2 := by nlinarith
  linarith

/-- Paper, "The window" (eq. `window`): with `e = √E_ℓ`, `2s ≤ e < 3ρ - 2s - 3/4`,
`α = 2(s - k)`, `τ = (3ρ + α)/4`, `|α - ρ| < 1`, and either `α ≥ ρ` and `δ ≤ 2k`, or `α < ρ` and
`δ ≤ 2k - 3/4`: then `τ + δ ≤ e < 2τ - δ`. -/
theorem window_arith {e s k α ρ τ δ : ℝ} (h2s : 2 * s ≤ e) (hup : e < 3 * ρ - 2 * s - 3 / 4)
    (hk : α = 2 * (s - k)) (hτ : τ = (3 * ρ + α) / 4) (hα : |α - ρ| < 1)
    (hδ : (ρ ≤ α ∧ δ ≤ 2 * k) ∨ (α < ρ ∧ δ ≤ 2 * k - 3 / 4)) :
    τ + δ ≤ e ∧ e < 2 * τ - δ := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  rcases hδ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor
    · rw [hτ]; linarith
    · rw [hτ]; linarith
  · constructor
    · rw [hτ]; linarith
    · rw [hτ]; linarith

end SignCond
