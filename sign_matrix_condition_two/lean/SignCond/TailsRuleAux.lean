import SignCond.BasePairs

/-!
# Helpers for `TailsRule.lean` (the recursive tails of Lemma `lem:tails`, new paper)

* `inG_lt_32`: the elements of `𝒢` below `32` are `2, 4, 8, 10, 16, 20, 26`.
* `maxG_gap`: "We use the following facts about `m = w - g`. If `g < 32` then `m ≤ 4`, and if
  `g < 64` then `m ≤ 10`. If `g ≥ 32` then `m ≤ g/4`, and if `g ≥ 64` then `m ≤ g/4 - 2`."
  (together with `m = 0` for `g = 2` and `m ≤ 2` for `g = 4`, read off the same list).
* `golayG g`: "for every `g ∈ 𝒢` we fix a Golay pair of length `g`, obtained by doubling from
  `((1),(1))`, `(A₁₀, B₁₀)`, `(A₂₆, B₂₆)`, or from the pair of length `100` that Lemma `lem:square`
  produces from `(A₁₀, B₁₀)`"; `isGolayPair_golayG`, and `golayG_two_peval` (the pair of length `2`
  is `((1,1),(1,-1))`).
* `TPair`, `tailStep`: one step of the rule (eq. `tailrule`), `Φ = P^∓ | U^± | (-1,1)^η`,
  `Ψ = Q^∓ | V^± | (1,-1)^η`, with its length, signs, sums, polynomial identity and the bound
  `8g + 8η + 16η√g + 4B` (eq. `tailrec`) in `tailStep_energy`.
* The scalar inequalities used in the two bounds of the proof of Lemma `lem:tails`.
-/

open Complex

namespace SignCond

/-! ### The set `𝒢` below `64` and the gaps -/

/-- `𝒢 ∩ [0, 32) = {2, 4, 8, 10, 16, 20, 26}`. -/
theorem inG_lt_32 {n : ℕ} (hn : InG n) (h : n < 32) :
    n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 10 ∨ n = 16 ∨ n = 20 ∨ n = 26 := by
  obtain ⟨h1, b, hb | hb | hb | hb⟩ := hn <;> subst hb
  · have hb5 : b < 5 := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
      norm_num at this; omega
    interval_cases b <;> simp_all
  · have hb2 : b < 2 := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
      norm_num at this; omega
    interval_cases b <;> simp_all
  · have hb1 : b < 1 := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
      norm_num at this; omega
    interval_cases b <;> simp_all
  · have := Nat.one_le_two_pow (n := b); omega

/-- The facts about `m = w - g` (paper, proof of Lemma `lem:tails`): `w` is even and `g` is the
largest element of `𝒢` with `g ≤ w`; then `w` is smaller than the next element `g⁺` of `𝒢`, so
`m ≤ g⁺ - g - 2`, and the list of elements of `𝒢` up to `64` and `g⁺ ≤ 5g/4` (for `g ≥ 64`) give
the bounds. -/
theorem maxG_gap {w g : ℕ} (hw : Even w) (hg : IsMaxG w g) :
    (g < 32 → w - g ≤ 4) ∧ (g = 2 → w - g = 0) ∧ (g = 4 → w - g ≤ 2) ∧
      (g < 64 → w - g ≤ 10) ∧ (32 ≤ g → 4 * (w - g) ≤ g) ∧ (64 ≤ g → 4 * (w - g) + 8 ≤ g) := by
  obtain ⟨hgG, hgw, hmax⟩ := hg
  have hwe := Nat.even_iff.mp hw
  have above : ∀ n, InG n → g < n → w + 2 ≤ n := by
    intro n hn hgn
    have hlt : w < n := by
      by_contra hc
      have := hmax n hn (by omega)
      omega
    have := Nat.even_iff.mp (inG_even hn)
    omega
  have key : (g = 2 ∧ w + 2 ≤ 4) ∨ (g = 4 ∧ w + 2 ≤ 8) ∨ (g = 8 ∧ w + 2 ≤ 10) ∨
      (g = 10 ∧ w + 2 ≤ 16) ∨ (g = 16 ∧ w + 2 ≤ 20) ∨ (g = 20 ∧ w + 2 ≤ 26) ∨
      (g = 26 ∧ w + 2 ≤ 32) ∨ (g = 32 ∧ w + 2 ≤ 40) ∨ (g = 40 ∧ w + 2 ≤ 52) ∨
      (g = 52 ∧ w + 2 ≤ 64) ∨ (64 ≤ g ∧ 4 * (w + 2) ≤ 5 * g) := by
    rcases lt_or_ge g 32 with h32 | h32
    · rcases inG_lt_32 hgG h32 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨rfl, above 4 ⟨by norm_num, 2, by norm_num⟩ (by norm_num)⟩
      · exact Or.inr (Or.inl ⟨rfl, above 8 ⟨by norm_num, 3, by norm_num⟩ (by norm_num)⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, above 10 ⟨by norm_num, 0, by norm_num⟩ (by norm_num)⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, above 16 ⟨by norm_num, 4, by norm_num⟩ (by norm_num)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, above 20 ⟨by norm_num, 1, by norm_num⟩ (by norm_num)⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, above 26 ⟨by norm_num, 0, by norm_num⟩ (by norm_num)⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, above 32 ⟨by norm_num, 5, by norm_num⟩ (by norm_num)⟩))))))
    rcases lt_or_ge g 64 with h64 | h64
    · rcases inG_window32 hgG h32 h64 with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, above 40 ⟨by norm_num, 2, by norm_num⟩ (by norm_num)⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, above 52 ⟨by norm_num, 1, by norm_num⟩ (by norm_num)⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, above 64 ⟨by norm_num, 6, by norm_num⟩ (by norm_num)⟩)))))))))
    · obtain ⟨m', hm'G, hgm', h4, -⟩ := next_inG hgG h64
      have := above m' hm'G hgm'
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h64, by omega⟩)))))))))
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> omega

/-! ### The fixed Golay pairs of the lengths in `𝒢` -/

/-- Reindex a pair of sequences along `m = n`. -/
def castPair {n m : ℕ} (h : m = n) (p : (Fin n → ℤ) × (Fin n → ℤ)) : (Fin m → ℤ) × (Fin m → ℤ) :=
  (p.1 ∘ Fin.cast h, p.2 ∘ Fin.cast h)

theorem isGolayPair_castPair {n m : ℕ} (h : m = n) {p : (Fin n → ℤ) × (Fin n → ℤ)}
    (hp : IsGolayPair p.1 p.2) : IsGolayPair (castPair h p).1 (castPair h p).2 :=
  isGolayPair_comp_cast h hp

/-- Paper: "For every `g ∈ 𝒢` we fix a Golay pair of length `g`, obtained by doubling from
`((1),(1))`, `(A₁₀, B₁₀)`, `(A₂₆, B₂₆)`, or from the pair of length `100` that Lemma `lem:square`
produces from `(A₁₀, B₁₀)`." Written as a recursion: lengths `1, 10, 26, 100` are the four
starting pairs, and an even length `g ≥ 2` outside this list is the doubling of the pair of length
`g/2` (for `g ∈ 𝒢` this is `golayDoubleIter`; for other `g` the value is never used). -/
def golayG (g : ℕ) : (Fin g → ℤ) × (Fin g → ℤ) :=
  if h1 : g = 1 then castPair h1 golayOne
  else if h10 : g = 10 then castPair h10 (golayA10, golayB10)
  else if h26 : g = 26 then castPair h26 (golayA26, golayB26)
  else if h100 : g = 100 then castPair (h100.trans (by norm_num)) (golaySquare golayA10 golayB10)
  else if h2 : 2 ≤ g ∧ g % 2 = 0 then castPair (by omega) (golayDouble (golayG (g / 2)))
  else (fun _ => 1, fun _ => 1)
termination_by g
decreasing_by omega

/-- Halving an element of `𝒢` outside `{10, 26, 100}` stays in `𝒢 ∪ {1}`. -/
theorem half_inG {g : ℕ} (hg : InG g) (h10 : g ≠ 10) (h26 : g ≠ 26) (h100 : g ≠ 100) :
    (InG (g / 2) ∨ g / 2 = 1) ∧ 2 ≤ g ∧ g % 2 = 0 := by
  have hge := Nat.even_iff.mp (inG_even hg)
  have hg2 := inG_two_le hg
  refine ⟨?_, hg2, hge⟩
  obtain ⟨h1, a, ha | ha | ha | ha⟩ := hg
  · rcases a with _ | a
    · simp at ha; omega
    · rw [pow_succ] at ha
      have hX := Nat.one_le_two_pow (n := a)
      have hh : g / 2 = 2 ^ a := by omega
      rw [hh]
      rcases a with _ | a
      · right; rfl
      · left; exact inG_pow (by omega)
  · rcases a with _ | a
    · simp at ha; omega
    · rw [pow_succ] at ha
      have hh : g / 2 = 2 ^ a * 10 := by omega
      rw [hh]; left; exact ⟨by omega, a, Or.inr (Or.inl rfl)⟩
  · rcases a with _ | a
    · simp at ha; omega
    · rw [pow_succ] at ha
      have hh : g / 2 = 2 ^ a * 26 := by omega
      rw [hh]; left; exact ⟨by omega, a, Or.inr (Or.inr (Or.inl rfl))⟩
  · rcases a with _ | a
    · simp at ha; omega
    · rw [pow_succ] at ha
      have hh : g / 2 = 2 ^ a * 100 := by omega
      rw [hh]; left; exact ⟨by omega, a, Or.inr (Or.inr (Or.inr rfl))⟩

/-- The fixed pairs are Golay pairs. -/
theorem isGolayPair_golayG : ∀ g : ℕ, (InG g ∨ g = 1) → IsGolayPair (golayG g).1 (golayG g).2 := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro hg
  rw [golayG]
  split_ifs with h1 h10 h26 h100 h2
  · exact isGolayPair_castPair h1 isGolayPair_one
  · exact isGolayPair_castPair h10 isGolayPair_10
  · exact isGolayPair_castPair h26 isGolayPair_26
  · exact isGolayPair_castPair _ (golaySquare_regular isGolayPair_10).1
  · have hG : InG g := hg.resolve_right h1
    exact isGolayPair_castPair _
      (isGolayPair_double (ih (g / 2) (by omega) (half_inG hG h10 h26 h100).1))
  · exfalso
    have hG : InG g := hg.resolve_right h1
    exact h2 (half_inG hG h10 h26 h100).2

theorem golayG_one : golayG 1 = golayOne := by
  rw [golayG, dif_pos rfl]; rfl

theorem golayG_two : golayG 2 = castPair (by norm_num) (golayDouble (golayG 1)) := by
  conv_lhs => rw [golayG]
  rw [dif_neg (by norm_num), dif_neg (by norm_num), dif_neg (by norm_num), dif_neg (by norm_num),
    dif_pos (by norm_num)]

/-- The pair of length `2` is `((1, 1), (1, -1))`. -/
theorem golayG_two_peval (w : ℂ) :
    peval (golayG 2).1 w = 1 + w ∧ peval (golayG 2).2 w = 1 - w := by
  rw [golayG_two, golayG_one]
  simp only [castPair, golayDouble, peval_comp_cast, peval_append, peval_neg]
  refine ⟨?_, ?_⟩ <;> simp [golayOne, peval] <;> ring

/-! ### One step of the rule (eq. `tailrule`) -/

/-- A pair of sequences of a common length `n`. -/
abbrev TPair := Σ n : ℕ, (Fin n → ℤ) × (Fin n → ℤ)

/-- One step of eq. `tailrule`: from a pair `(P, Q)` of length `g` and a pair `t = (U, V)`, the pair
`(P^∓ | U^± | (-1,1)^η, Q^∓ | V^± | (1,-1)^η)` (the last block present only when `η = 1`). -/
def tailStep {g : ℕ} (η : ℕ) (P Q : Fin g → ℤ) (t : TPair) : TPair :=
  if η = 1 then
    ⟨g * 2 + t.1 * 2 + 2, (Fin.append (Fin.append (mpSeq P) (ppSeq t.2.1)) (-onePair),
      Fin.append (Fin.append (mpSeq Q) (ppSeq t.2.2)) onePair)⟩
  else ⟨g * 2 + t.1 * 2, (Fin.append (mpSeq P) (ppSeq t.2.1), Fin.append (mpSeq Q) (ppSeq t.2.2))⟩

theorem tailStep_fst {g η : ℕ} (P Q : Fin g → ℤ) (t : TPair) (hη : η = 0 ∨ η = 1) :
    (tailStep η P Q t).1 = g * 2 + t.1 * 2 + 2 * η := by
  rcases hη with rfl | rfl <;> simp [tailStep]

theorem tailStep_sign {g η : ℕ} {P Q : Fin g → ℤ} {t : TPair} (hP : IsSignSeq P)
    (hQ : IsSignSeq Q) (h1 : IsSignSeq t.2.1) (h2 : IsSignSeq t.2.2) :
    IsSignSeq (tailStep η P Q t).2.1 ∧ IsSignSeq (tailStep η P Q t).2.2 := by
  by_cases h : η = 1
  · rw [tailStep, if_pos h]
    exact ⟨isSignSeq_append (isSignSeq_append (isSignSeq_mpSeq hP) (isSignSeq_ppSeq h1))
      (isSignSeq_neg isSignSeq_onePair),
      isSignSeq_append (isSignSeq_append (isSignSeq_mpSeq hQ) (isSignSeq_ppSeq h2))
        isSignSeq_onePair⟩
  · rw [tailStep, if_neg h]
    exact ⟨isSignSeq_append (isSignSeq_mpSeq hP) (isSignSeq_ppSeq h1),
      isSignSeq_append (isSignSeq_mpSeq hQ) (isSignSeq_ppSeq h2)⟩

/-- "Each block in eq. `tailrule` has zero sum." -/
theorem tailStep_sum {g η : ℕ} (P Q : Fin g → ℤ) {t : TPair} (h1 : peval t.2.1 1 = 0)
    (h2 : peval t.2.2 1 = 0) :
    peval (tailStep η P Q t).2.1 1 = 0 ∧ peval (tailStep η P Q t).2.2 1 = 0 := by
  by_cases h : η = 1
  · rw [tailStep, if_pos h]
    dsimp only
    simp [peval_append, peval_mpSeq, peval_ppSeq, peval_neg, peval_onePair, h1, h2]
  · rw [tailStep, if_neg h]
    dsimp only
    simp [peval_append, peval_mpSeq, peval_ppSeq, peval_neg, peval_onePair, h1, h2]

theorem peval_tailStep_one {g : ℕ} (P Q : Fin g → ℤ) (t : TPair) (z : ℂ) :
    peval (tailStep 1 P Q t).2.1 z = (1 - z) * (peval P (z ^ 2) + -z ^ (g * 2 + t.1 * 2)) +
      (1 + z) * (z ^ (g * 2) * peval t.2.1 (z ^ 2)) := by
  rw [tailStep, if_pos rfl]
  dsimp only
  rw [peval_append, peval_append, peval_mpSeq, peval_ppSeq, peval_neg, peval_onePair]
  ring

theorem peval_tailStep_one' {g : ℕ} (P Q : Fin g → ℤ) (t : TPair) (z : ℂ) :
    peval (tailStep 1 P Q t).2.2 z = (1 - z) * (peval Q (z ^ 2) + z ^ (g * 2 + t.1 * 2)) +
      (1 + z) * (z ^ (g * 2) * peval t.2.2 (z ^ 2)) := by
  rw [tailStep, if_pos rfl]
  dsimp only
  rw [peval_append, peval_append, peval_mpSeq, peval_ppSeq, peval_onePair]
  ring

theorem peval_tailStep_zero {g η : ℕ} (P Q : Fin g → ℤ) (t : TPair) (hη : η ≠ 1) (z : ℂ) :
    peval (tailStep η P Q t).2.1 z = (1 - z) * peval P (z ^ 2) +
      (1 + z) * (z ^ (g * 2) * peval t.2.1 (z ^ 2)) := by
  rw [tailStep, if_neg hη]
  dsimp only
  rw [peval_append, peval_mpSeq, peval_ppSeq]
  ring

theorem peval_tailStep_zero' {g η : ℕ} (P Q : Fin g → ℤ) (t : TPair) (hη : η ≠ 1) (z : ℂ) :
    peval (tailStep η P Q t).2.2 z = (1 - z) * peval Q (z ^ 2) +
      (1 + z) * (z ^ (g * 2) * peval t.2.2 (z ^ 2)) := by
  rw [tailStep, if_neg hη]
  dsimp only
  rw [peval_append, peval_mpSeq, peval_ppSeq]
  ring

/-- Eq. `tailrec` for one step: `(Φ(z), Ψ(z)) = (1-z)x + (1+z)y` with
`x = (P(z²), Q(z²)) + η z^{2(g+m)}(-1, 1)`, `y = z^{2g}(U(z²), V(z²))`, `‖x‖ ≤ √(2g) + η√2`,
`‖y‖² ≤ B`, and Cauchy–Schwarz with `|1-z|² + |1+z|² = 4` give
`|Φ(z)|² + |Ψ(z)|² ≤ 4(‖x‖² + ‖y‖²) ≤ 8g + 8η + 16η√g + 4B`. -/
theorem tailStep_energy {g η : ℕ} {P Q : Fin g → ℤ} {t : TPair} {B : ℝ} (hη : η = 0 ∨ η = 1)
    (hG : IsGolay P Q)
    (ht : ∀ z : ℂ, ‖z‖ = 1 → ‖peval t.2.1 z‖ ^ 2 + ‖peval t.2.2 z‖ ^ 2 ≤ B) {z : ℂ}
    (hz : ‖z‖ = 1) :
    ‖peval (tailStep η P Q t).2.1 z‖ ^ 2 + ‖peval (tailStep η P Q t).2.2 z‖ ^ 2 ≤
      8 * (g : ℝ) + 8 * (η : ℝ) + 16 * (η : ℝ) * Real.sqrt g + 4 * B := by
  have hz2 : ‖z ^ 2‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hy : ‖z ^ (g * 2) * peval t.2.1 (z ^ 2)‖ ^ 2 + ‖z ^ (g * 2) * peval t.2.2 (z ^ 2)‖ ^ 2
      ≤ B := by
    rw [norm_mul, norm_mul, norm_pow, hz, one_pow, one_mul, one_mul]
    exact ht _ hz2
  rcases hη with rfl | rfl
  · rw [peval_tailStep_zero _ _ _ (by norm_num), peval_tailStep_zero' _ _ _ (by norm_num)]
    have hx : ‖peval P (z ^ 2)‖ ^ 2 + ‖peval Q (z ^ 2)‖ ^ 2 ≤ (Real.sqrt (2 * g)) ^ 2 := by
      rw [hG _ hz2, Real.sq_sqrt (by positivity)]
    have := interleave_bound hz hx hy
    rw [Real.sq_sqrt (by positivity)] at this
    push_cast
    linarith
  · rw [peval_tailStep_one, peval_tailStep_one']
    have hc : ‖z ^ (g * 2 + t.1 * 2)‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hx : ‖peval P (z ^ 2) + -z ^ (g * 2 + t.1 * 2)‖ ^ 2 +
        ‖peval Q (z ^ 2) + z ^ (g * 2 + t.1 * 2)‖ ^ 2 ≤
          (Real.sqrt (2 * g) + Real.sqrt 2) ^ 2 := by
      have := norm2_add_le (peval P (z ^ 2)) (peval Q (z ^ 2)) (-z ^ (g * 2 + t.1 * 2))
        (z ^ (g * 2 + t.1 * 2))
      rw [hG _ hz2, norm_neg, hc, show (1 : ℝ) ^ 2 + 1 ^ 2 = 2 by norm_num] at this
      exact this
    have := interleave_bound hz hx hy
    rw [interleave_value (by positivity)] at this
    push_cast
    linarith

/-! ### Scalar inequalities -/

/-- `16√g ≤ 2g + 32`, i.e. `2(√g - 4)² ≥ 0`. -/
theorem sqrt_le_two_mul_add {g : ℝ} (hg : 0 ≤ g) : 16 * Real.sqrt g ≤ 2 * g + 32 := by
  have h := Real.sq_sqrt hg
  nlinarith [sq_nonneg (Real.sqrt g - 4)]

/-- `16√g - 4g ≤ 16`, i.e. `4(√g - 2)² ≥ 0`. -/
theorem sqrt_sub_le_sixteen {g : ℝ} (hg : 0 ≤ g) : 16 * Real.sqrt g - 4 * g ≤ 16 := by
  have h := Real.sq_sqrt hg
  nlinarith [sq_nonneg (Real.sqrt g - 2)]

theorem one_le_sqrt_of_one_le {g : ℝ} (hg : 1 ≤ g) : 1 ≤ Real.sqrt g := by
  have := Real.sqrt_le_sqrt hg
  rwa [Real.sqrt_one] at this

theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- First bound, case `g < 32` (there `m ≤ 4` and `M_m ≤ 4m`): `15r/2 - M_r ≥ 7g - m + 7η - 16η√g`,
which is positive; for `η = 1` either `g = 4, m ≤ 2` or `g ≥ 8`. -/
theorem first_scalar_small {g m η : ℝ} (hη : η = 0 ∨ η = 1) (_hm0 : 0 ≤ m) (hm : m ≤ 4)
    (hg : 2 ≤ g) (h1 : η = 1 → (g = 4 ∧ m ≤ 2) ∨ 8 ≤ g) :
    8 * g + 8 * η + 16 * η * Real.sqrt g + 4 * (4 * m) ≤ 15 * (2 * g + 2 * m + 2 * η) / 2 := by
  rcases hη with rfl | rfl
  · linarith
  · rcases h1 rfl with ⟨rfl, hm2⟩ | h8
    · rw [sqrt_four]; linarith
    · have := sqrt_le_two_mul_add (show 0 ≤ g by linarith)
      linarith

/-- First bound, case `g ≥ 32` (there `m ≤ g/4` and `M_m ≤ 15m/2`):
`15r/2 - M_r ≥ 13g/4 + 7 - 16√g > 0`. -/
theorem first_scalar_large {g m η : ℝ} (hη : η = 0 ∨ η = 1) (_hm0 : 0 ≤ m) (hg : 32 ≤ g)
    (hgm : 4 * m ≤ g) :
    8 * g + 8 * η + 16 * η * Real.sqrt g + 4 * (15 * m / 2) ≤ 15 * (2 * g + 2 * m + 2 * η) / 2 := by
  rcases hη with rfl | rfl
  · linarith
  · have := sqrt_le_two_mul_add (show 0 ≤ g by linarith)
    linarith

/-- Second bound, case `g < 64` (there `m ≤ 10` and `D_m ≤ 3m/2`):
`D_r ≤ -4g + 16√g + 18m ≤ 16 + 180`. -/
theorem second_scalar_small_g {g m η : ℝ} (hη : η = 0 ∨ η = 1) (hg : 0 ≤ g) (_hm0 : 0 ≤ m)
    (hm : m ≤ 10) :
    8 * g + 8 * η + 16 * η * Real.sqrt g + 4 * (15 * m / 2) ≤ 6 * (2 * g + 2 * m + 2 * η) + 400 := by
  have := sqrt_sub_le_sixteen hg
  have := Real.sqrt_nonneg g
  rcases hη with rfl | rfl <;> linarith

/-- Second bound, case `g ≥ 64`, `m ≤ 2` (there `D_m ≤ 0`). -/
theorem second_scalar_small_m {g m η : ℝ} (hη : η = 0 ∨ η = 1) (hg : 0 ≤ g) (_hm0 : 0 ≤ m)
    (hm : m ≤ 2) :
    8 * g + 8 * η + 16 * η * Real.sqrt g + 4 * (4 * m) ≤ 6 * (2 * g + 2 * m + 2 * η) + 400 := by
  have := sqrt_sub_le_sixteen hg
  have := Real.sqrt_nonneg g
  rcases hη with rfl | rfl <;> linarith

/-- The first expression in eq. `tailD2`: if `g ≥ 4m + 8` then, since `16√g - 4g` is decreasing for
`g ≥ 4`, `-4g + 12m + 16√g - 4 ≤ -16m - 32 + 32√(m+2) - 4 + 12m`. -/
theorem tailD2_scalar {g m : ℝ} (hm0 : 0 ≤ m) (hg : 4 * m + 8 ≤ g) :
    -4 * g + 12 * m + 16 * Real.sqrt g - 4 ≤ -4 * m - 36 + 32 * Real.sqrt (m + 2) := by
  have hs2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt (by linarith)
  have ht2 : Real.sqrt (m + 2) ^ 2 = m + 2 := Real.sq_sqrt (by linarith)
  have hs0 := Real.sqrt_nonneg g
  have ht0 := Real.sqrt_nonneg (m + 2)
  have ht1 : 1 ≤ Real.sqrt (m + 2) := one_le_sqrt_of_one_le (by linarith)
  have hts : 2 * Real.sqrt (m + 2) ≤ Real.sqrt g := by
    have h := Real.sqrt_le_sqrt (show (2 * Real.sqrt (m + 2)) ^ 2 ≤ g by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  nlinarith [mul_nonneg (sub_nonneg.mpr hts)
    (show 0 ≤ Real.sqrt g + 2 * Real.sqrt (m + 2) - 4 by linarith)]

/-- `36 - 4(√(m+2) - 4)² ≤ 36`. -/
theorem tailD2_scalar' {m : ℝ} (hm0 : 0 ≤ m) : -4 * m - 36 + 32 * Real.sqrt (m + 2) ≤ 36 := by
  have ht2 : Real.sqrt (m + 2) ^ 2 = m + 2 := Real.sq_sqrt (by linarith)
  nlinarith [sq_nonneg (Real.sqrt (m + 2) - 4)]

/-- Second bound, case `g ≥ 64`, `m ≥ 4`, `g' < 32` (there `m' ≤ 4` and `D_{m'} ≤ -2m'`):
`D_m ≤ -4g' + 16√g' - 4 + 4m'` and `D_r ≤ 36 + 4D_m`. -/
theorem second_scalar_rec_small {g m η g' m' η' : ℝ} (hη : η = 0 ∨ η = 1)
    (hη' : η' = 0 ∨ η' = 1) (hm0 : 0 ≤ m) (hg : 4 * m + 8 ≤ g) (hg'0 : 0 ≤ g') (_hm'0 : 0 ≤ m')
    (hm' : m' ≤ 4) (hmeq : m = 2 * g' + 2 * m' + 2 * η') :
    8 * g + 8 * η + 16 * η * Real.sqrt g +
        4 * (8 * g' + 8 * η' + 16 * η' * Real.sqrt g' + 4 * (4 * m')) ≤
      6 * (2 * g + 2 * m + 2 * η) + 400 := by
  have h1 := tailD2_scalar hm0 hg
  have h2 := tailD2_scalar' hm0
  have h3 := sqrt_sub_le_sixteen hg'0
  have hs1 := one_le_sqrt_of_one_le (show 1 ≤ g by linarith)
  have hs' := Real.sqrt_nonneg g'
  rcases hη with rfl | rfl <;> rcases hη' with rfl | rfl <;> linarith

/-- Second bound, case `g ≥ 64`, `m ≥ 4`, `g' ≥ 32` (there `m' ≤ g'/4` and `D_{m'} ≤ 3m'/2`):
`D_r ≤ -24g' + 64m' - 60 + 64√g' + 32√(m+2) ≤ -8g' - 60 + 64√g' + 32√(5g'/2 + 4)`, and
`√(5g'/2 + 4) ≤ (13/8)√g'`, so `D_r ≤ -8g' + 116√g' - 60 ≤ 116²/32 - 60 < 400` (here with `-36`
in place of `-60`, which also suffices). -/
theorem second_scalar_rec_large {g m η g' m' η' : ℝ} (hη : η = 0 ∨ η = 1)
    (hη' : η' = 0 ∨ η' = 1) (hm0 : 0 ≤ m) (hg : 4 * m + 8 ≤ g) (hg' : 32 ≤ g') (_hm'0 : 0 ≤ m')
    (hm' : 4 * m' ≤ g') (hmeq : m = 2 * g' + 2 * m' + 2 * η') :
    8 * g + 8 * η + 16 * η * Real.sqrt g +
        4 * (8 * g' + 8 * η' + 16 * η' * Real.sqrt g' + 4 * (15 * m' / 2)) ≤
      6 * (2 * g + 2 * m + 2 * η) + 400 := by
  have h1 := tailD2_scalar hm0 hg
  have hs1 := one_le_sqrt_of_one_le (show 1 ≤ g by linarith)
  have hs' := Real.sqrt_nonneg g'
  have hs'2 : Real.sqrt g' ^ 2 = g' := Real.sq_sqrt (by linarith)
  have hη1 : η' ≤ 1 := by rcases hη' with h | h <;> linarith
  have hη0 : 0 ≤ η' := by rcases hη' with h | h <;> linarith
  have ht : Real.sqrt (m + 2) ≤ 13 / 8 * Real.sqrt g' := by
    have hle : m + 2 ≤ (13 / 8 * Real.sqrt g') ^ 2 := by
      rw [mul_pow, hs'2]; linarith
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by positivity)] at h
  have hfin : -8 * g' + 116 * Real.sqrt g' ≤ 436 := by
    nlinarith [sq_nonneg (Real.sqrt g' - 29 / 4)]
  rcases hη with rfl | rfl <;> rcases hη' with rfl | rfl <;> linarith

end SignCond
