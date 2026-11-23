import SignCond.Rows
import Mathlib.Data.Nat.Log

/-!
# Tails (Lemma `lem:tails`)

* The set `𝒢 = {2^a g : a ≥ 0, g ∈ {1, 10, 26, 100}} \ {1}` (`InG`): `inG_even` (all elements are
  even), `inG_window` (`𝒢 ∩ [64·2^a, 128·2^a) = {64, 80, 100, 104}·2^a`), `inG_window32`
  (`𝒢 ∩ [32, 64) = {32, 40, 52}`), `inG_iff_of_le_160` (the elements of `𝒢` in `[32, 160]`),
  `next_inG` (for `m ∈ 𝒢`, `m ≥ 64`, the next element `m⁺` satisfies `4m⁺ ≤ 5m`),
  `IsMaxG h m` (`m` is the largest element of `𝒢` with `m ≤ h`), `exists_isMaxG`, and
  `interleave_params` (the case analysis of the fifth case of the rule).
* The scalar inequalities: `append_scalar`, `append_scalar'`, `deletion_scalar`,
  `interleave_small_scalar`, `interleave_large_scalar`.
* The abstract induction: `tails_induction` (a predicate `A r B`, "there is a balanced pair of
  length `r` with energy at most `B`", closed under the five operations, holds with `B = 6r` for
  every even `r`) and `tails_induction_E` (the formulation with an energy function `E`).
* The pointwise analytic facts behind the operations: `norm_one_sub_pow_sq_le`, `append_bound`,
  `deletion_bound`, `deletion_value`, `interleave_bound`, `interleave_value`.
* The seeds (Table `tab:seeds`): `seedA2`, `seedB2`, …, `seedA26`, `seedB26`, the identities
  `seed_2`, …, `seed_26`, and the seed pairs `seedPair_2`, …, `seedPair_26` (balanced sign pairs
  with energy at most `4r`).
* The concrete operations: `mpSeq` (`x^∓`), `ppSeq` (`x^±`), `onePair` (`(1,-1)`), the predicates
  `TailPair r B` and `GolayLen n`, and `tailPair_zero`, `tailPair_seed`, `tailPair_double`,
  `tailPair_append`, `tailPair_delete`, `tailPair_interleave`.
* Golay pairs of every length in `𝒢`: `isGolay_10`, `isGolay_26` (the pairs `A₁₀, B₁₀, A₂₆, B₂₆`),
  `golayLen_100` (Lemma `lem:square` applied to `(A₁₀, B₁₀)`), `golayLen_of_inG`.
* `lem_tails`: Lemma `lem:tails` itself.
-/

open Complex ComplexConjugate

namespace SignCond

/-! ### The set `𝒢` -/

/-- `n ∈ 𝒢 = {2^a g : a ≥ 0, g ∈ {1, 10, 26, 100}} \ {1}`. -/
def InG (n : ℕ) : Prop :=
  n ≠ 1 ∧ ∃ a : ℕ, n = 2 ^ a ∨ n = 2 ^ a * 10 ∨ n = 2 ^ a * 26 ∨ n = 2 ^ a * 100

/-- `2^b ≤ 2^k 2^a` or `2^(k+1) 2^a ≤ 2^b`. -/
private theorem pow_split (a b k : ℕ) : 2 ^ b ≤ 2 ^ k * 2 ^ a ∨ 2 ^ (k + 1) * 2 ^ a ≤ 2 ^ b := by
  rcases le_or_lt b (k + a) with h | h
  · left; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) h
  · right; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- All elements of `𝒢` are even. -/
theorem inG_even {n : ℕ} (h : InG n) : Even n := by
  obtain ⟨h1, a, ha | ha | ha | ha⟩ := h <;> subst ha
  · rcases a with _ | a
    · exact absurd rfl h1
    · exact ⟨2 ^ a, by rw [pow_succ]; ring⟩
  · exact ⟨2 ^ a * 5, by ring⟩
  · exact ⟨2 ^ a * 13, by ring⟩
  · exact ⟨2 ^ a * 50, by ring⟩

theorem inG_pow {a : ℕ} (ha : 1 ≤ a) : InG (2 ^ a) :=
  ⟨fun h => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) ha
    omega, a, Or.inl rfl⟩

theorem inG_64 (a : ℕ) : InG (64 * 2 ^ a) := by
  have : 64 * 2 ^ a = 2 ^ (a + 6) := by rw [pow_add]; ring
  rw [this]; exact inG_pow (by omega)

theorem inG_128 (a : ℕ) : InG (128 * 2 ^ a) := by
  have : 128 * 2 ^ a = 2 ^ (a + 7) := by rw [pow_add]; ring
  rw [this]; exact inG_pow (by omega)

theorem inG_80 (a : ℕ) : InG (80 * 2 ^ a) :=
  ⟨by have := Nat.one_le_two_pow (n := a); omega, a + 3, Or.inr (Or.inl (by rw [pow_add]; ring))⟩

theorem inG_100 (a : ℕ) : InG (100 * 2 ^ a) :=
  ⟨by have := Nat.one_le_two_pow (n := a); omega, a, Or.inr (Or.inr (Or.inr (by ring)))⟩

theorem inG_104 (a : ℕ) : InG (104 * 2 ^ a) :=
  ⟨by have := Nat.one_le_two_pow (n := a); omega, a + 2,
    Or.inr (Or.inr (Or.inl (by rw [pow_add]; ring)))⟩

theorem inG_two : InG 2 := inG_pow (a := 1) le_rfl

/-- `𝒢 ∩ [64·2^a, 128·2^a) = {64, 80, 100, 104}·2^a`. -/
theorem inG_window {a n : ℕ} (hn : InG n) (h1 : 64 * 2 ^ a ≤ n) (h2 : n < 128 * 2 ^ a) :
    n = 64 * 2 ^ a ∨ n = 80 * 2 ^ a ∨ n = 100 * 2 ^ a ∨ n = 104 * 2 ^ a := by
  obtain ⟨-, b, hb⟩ := hn
  have hX := Nat.one_le_two_pow (n := a)
  rcases hb with rfl | rfl | rfl | rfl
  · have s1 := pow_split a b 5
    have s2 := pow_split a b 6
    norm_num at s1 s2
    omega
  · have s1 := pow_split a b 2
    have s2 := pow_split a b 3
    norm_num at s1 s2
    omega
  · have s1 := pow_split a b 1
    have s2 := pow_split a b 2
    norm_num at s1 s2
    omega
  · have s1 := pow_split a b 0
    have s2 := pow_split b a 0
    norm_num at s1 s2
    omega

/-- `𝒢 ∩ [32, 64) = {32, 40, 52}`. -/
theorem inG_window32 {n : ℕ} (hn : InG n) (h1 : 32 ≤ n) (h2 : n < 64) :
    n = 32 ∨ n = 40 ∨ n = 52 := by
  obtain ⟨-, b, hb⟩ := hn
  have hY := Nat.one_le_two_pow (n := b)
  rcases hb with rfl | rfl | rfl | rfl
  · have s1 := pow_split 0 b 4
    have s2 := pow_split 0 b 5
    norm_num at s1 s2
    omega
  · have s1 := pow_split 0 b 1
    have s2 := pow_split 0 b 2
    norm_num at s1 s2
    omega
  · have s1 := pow_split 0 b 0
    have s2 := pow_split 0 b 1
    norm_num at s1 s2
    omega
  · omega

/-- Every `h ≥ 64` lies in a window `[64·2^a, 128·2^a)`. -/
theorem exists_window {h : ℕ} (hh : 64 ≤ h) : ∃ a, 64 * 2 ^ a ≤ h ∧ h < 128 * 2 ^ a := by
  refine ⟨Nat.log 2 (h / 64), ?_, ?_⟩
  · have := Nat.pow_log_le_self 2 (show h / 64 ≠ 0 by omega)
    omega
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (h / 64)
    rw [pow_succ] at this
    omega

private theorem two_pow_cases (a : ℕ) : 2 ^ a = 1 ∨ 2 ^ a = 2 ∨ 4 ≤ 2 ^ a := by
  rcases a with _ | _ | a
  · simp
  · simp
  · right; right
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 2 ≤ a + 2 by omega)
    simpa using this

/-- The elements of `𝒢` in `[32, 160]` are exactly `32, 40, 52, 64, 80, 100, 104, 128, 160`. -/
theorem inG_iff_of_le_160 {n : ℕ} (h1 : 32 ≤ n) (h2 : n ≤ 160) :
    InG n ↔ n ∈ ({32, 40, 52, 64, 80, 100, 104, 128, 160} : Finset ℕ) := by
  constructor
  · intro hn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases lt_or_ge n 64 with h | h
    · rcases inG_window32 hn h1 h with rfl | rfl | rfl <;> simp
    rcases lt_or_ge n 128 with h' | h'
    · have := inG_window (a := 0) hn (by simpa using h) (by simpa using h')
      omega
    · have := inG_window (a := 1) hn (by simpa using h') (by norm_num; omega)
      omega
  · intro hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact inG_pow (a := 5) (by norm_num)
    · exact ⟨by norm_num, 2, by norm_num⟩
    · exact ⟨by norm_num, 1, by norm_num⟩
    · simpa using inG_64 0
    · simpa using inG_80 0
    · simpa using inG_100 0
    · simpa using inG_104 0
    · simpa using inG_128 0
    · simpa using inG_80 1

/-- For `m ∈ 𝒢` with `m ≥ 64`, the next element `m⁺` of `𝒢` satisfies `4m⁺ ≤ 5m`
("consecutive elements of `𝒢` that are at least `64` have ratio at most `5/4`"). -/
theorem next_inG {m : ℕ} (hm : InG m) (h64 : 64 ≤ m) :
    ∃ m' : ℕ, InG m' ∧ m < m' ∧ 4 * m' ≤ 5 * m ∧ ∀ n, InG n → m < n → m' ≤ n := by
  obtain ⟨a, ha1, ha2⟩ := exists_window h64
  have hX := Nat.one_le_two_pow (n := a)
  -- any element of `𝒢` strictly between `m` and `m'` lies in the window
  have key : ∀ m' : ℕ, m' ≤ 128 * 2 ^ a → ∀ n, InG n → m < n → n < m' →
      n = 64 * 2 ^ a ∨ n = 80 * 2 ^ a ∨ n = 100 * 2 ^ a ∨ n = 104 * 2 ^ a :=
    fun m' hm' n hn h1 h2 => inG_window hn (by omega) (by omega)
  rcases inG_window hm ha1 ha2 with rfl | rfl | rfl | rfl
  · refine ⟨80 * 2 ^ a, inG_80 a, by omega, by omega, fun n hn h => ?_⟩
    by_contra hc; have := key (80 * 2 ^ a) (by omega) n hn h (by omega); omega
  · refine ⟨100 * 2 ^ a, inG_100 a, by omega, by omega, fun n hn h => ?_⟩
    by_contra hc; have := key (100 * 2 ^ a) (by omega) n hn h (by omega); omega
  · refine ⟨104 * 2 ^ a, inG_104 a, by omega, by omega, fun n hn h => ?_⟩
    by_contra hc; have := key (104 * 2 ^ a) (by omega) n hn h (by omega); omega
  · refine ⟨128 * 2 ^ a, inG_128 a, by omega, by omega, fun n hn h => ?_⟩
    by_contra hc; have := key (128 * 2 ^ a) (by omega) n hn h (by omega); omega

/-- `m` is the largest element of `𝒢` with `m ≤ h`. -/
def IsMaxG (h m : ℕ) : Prop := InG m ∧ m ≤ h ∧ ∀ n, InG n → n ≤ h → n ≤ m

theorem exists_isMaxG {h : ℕ} (hh : 2 ≤ h) : ∃ m, IsMaxG h m := by
  classical
  exact ⟨Nat.findGreatest InG h, Nat.findGreatest_spec (P := InG) hh inG_two,
    Nat.findGreatest_le h, fun n hn hnh => Nat.le_findGreatest hnh hn⟩

/-- The fifth case of the rule. Let `h ≥ 30` be even with `h + 2 ∉ 𝒢`, and let `m` be the largest
element of `𝒢` with `m ≤ h`; put `t = h - m`. Then `m ≥ 32`, `t` is even, and either
`m ≤ 128`, `t ≤ 28` and `4t ≤ m`, or `m ≥ 160` and `4t + 16 ≤ m` (i.e. `t ≤ m/4 - 4`).
Moreover `4t + 16 ≤ m` whenever `h ≥ 64`. -/
theorem interleave_params {h m : ℕ} (hh : 30 ≤ h) (he : Even h) (hg : ¬ InG (h + 2))
    (hm : IsMaxG h m) :
    32 ≤ m ∧ Even (h - m) ∧ (64 ≤ h → 4 * (h - m) + 16 ≤ m) ∧
      ((m ≤ 128 ∧ h - m ≤ 28 ∧ 4 * (h - m) ≤ m) ∨ (160 ≤ m ∧ 4 * (h - m) + 16 ≤ m)) := by
  obtain ⟨hmG, hmh, hmax⟩ := hm
  have hme := inG_even hmG
  rw [Nat.even_iff] at he hme
  have hte : Even (h - m) := by rw [Nat.even_iff]; omega
  have h32 : 32 ≤ h := by
    by_contra hc
    have : h = 30 := by omega
    subst this
    exact hg (inG_pow (a := 5) (by norm_num))
  have m32 : 32 ≤ m := hmax 32 (inG_pow (a := 5) (by norm_num)) h32
  -- `n ∈ 𝒢`, `m < n` forces `h + 4 ≤ n`
  have above : ∀ n, InG n → m < n → h + 4 ≤ n := by
    intro n hn hmn
    have hne : n ≠ h + 2 := fun e => hg (e ▸ hn)
    have hle : h < n := by by_contra hc; have := hmax n hn (by omega); omega
    have := Nat.even_iff.mp (inG_even hn)
    omega
  refine ⟨m32, hte, ?_⟩
  rcases lt_or_ge h 64 with hlt | hge
  · refine ⟨fun h' => absurd h' (by omega), Or.inl ?_⟩
    rcases inG_window32 hmG m32 (by omega) with rfl | rfl | rfl
    · have := above 40 ⟨by norm_num, 2, by norm_num⟩ (by norm_num); omega
    · have := above 52 ⟨by norm_num, 1, by norm_num⟩ (by norm_num); omega
    · have := above 64 (by simpa using inG_64 0) (by norm_num); omega
  · obtain ⟨a, ha1, ha2⟩ := exists_window hge
    have hlo : 64 * 2 ^ a ≤ m := hmax _ (inG_64 a) ha1
    have hX := two_pow_cases a
    have hbound : 4 * (h - m) + 16 ≤ m := by
      rcases inG_window hmG hlo (by omega) with rfl | rfl | rfl | rfl
      · have := above _ (inG_80 a) (by omega); omega
      · have := above _ (inG_100 a) (by omega); omega
      · have := above _ (inG_104 a) (by omega); omega
      · have := above _ (inG_128 a) (by omega); omega
    refine ⟨fun _ => hbound, ?_⟩
    have hw := inG_window hmG hlo (by omega)
    generalize 2 ^ a = X at hw hX
    omega

/-! ### Scalar inequalities -/

/-- Third case: `4r + 4√(8r-16) ≤ 6r` for `r ≥ 30` (equivalent to `r² - 32r + 64 ≥ 0`). -/
theorem append_scalar {r : ℝ} (hr : 30 ≤ r) : 4 * r + 4 * Real.sqrt (8 * r - 16) ≤ 6 * r := by
  have : Real.sqrt (8 * r - 16) ≤ r / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  linarith

/-- Third case, in the form used: `(√(4(r-2)) + √8)² ≤ 6r` for `r ≥ 30`. -/
theorem append_scalar' {r : ℝ} (hr : 30 ≤ r) :
    (Real.sqrt (4 * (r - 2)) + Real.sqrt 8) ^ 2 ≤ 6 * r := by
  have h1 := Real.sq_sqrt (show 0 ≤ 4 * (r - 2) by linarith)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
  have h3 : Real.sqrt (4 * (r - 2)) * Real.sqrt 8 = 2 * Real.sqrt (8 * r - 16) := by
    rw [← Real.sqrt_mul (by linarith)]
    rw [show 4 * (r - 2) * 8 = 2 ^ 2 * (8 * r - 16) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have := append_scalar hr
  nlinarith

/-- Fourth case: `8g + 8 + 16√g ≤ 12g - 12` for `g ≥ 25`
(`g - 4√g - 5 = (√g - 5)(√g + 1) ≥ 0`). -/
theorem deletion_scalar {g : ℝ} (hg : 25 ≤ g) : 8 * g + 8 + 16 * Real.sqrt g ≤ 12 * g - 12 := by
  have hs : 5 ≤ Real.sqrt g := by
    rw [show (5 : ℝ) = Real.sqrt (5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have e := Real.sq_sqrt (show 0 ≤ g by linarith)
  nlinarith

/-- Fifth case, `32 ≤ m ≤ 128`: if `32 ≤ m` and `t ≤ m/4` then
`8m + 8 + 16√m + 16t ≤ 6(2m + 2t + 2)` (here `B = 4t`). -/
theorem interleave_small_scalar {m t : ℝ} (hm : 32 ≤ m) (ht : 4 * t ≤ m) :
    8 * m + 8 + 16 * Real.sqrt m + 16 * t ≤ 6 * (2 * m + 2 * t + 2) := by
  have e := Real.sq_sqrt (show 0 ≤ m by linarith)
  have hs0 := Real.sqrt_nonneg m
  have hs : 16 / 3 ≤ Real.sqrt m := by nlinarith
  nlinarith

/-- Fifth case, `m ≥ 160` (`m ≥ 144` suffices): if `t ≤ m/4 - 4` then
`8m + 8 + 16√m + 24t ≤ 6(2m + 2t + 2)` (here `B = 6t`). -/
theorem interleave_large_scalar {m t : ℝ} (hm : 144 ≤ m) (ht : 4 * t + 16 ≤ m) :
    8 * m + 8 + 16 * Real.sqrt m + 24 * t ≤ 6 * (2 * m + 2 * t + 2) := by
  have hs : 12 ≤ Real.sqrt m := by
    rw [show (12 : ℝ) = Real.sqrt (12 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have e := Real.sq_sqrt (show 0 ≤ m by linarith)
  nlinarith

/-! ### The abstract induction -/

/-- The seed lengths. -/
def seedLengths : Finset ℕ := {2, 6, 10, 14, 18, 22, 26}

section Induction

variable (A : ℕ → ℝ → Prop)

/-- Every even `r ≤ 28` has `A r (4r)` (seeds and doubling). -/
theorem tails_small
    (hmono : ∀ r B B', A r B → B ≤ B' → A r B') (h0 : A 0 0)
    (hseed : ∀ r ∈ seedLengths, A r (4 * r))
    (hdouble : ∀ u B, Even u → A u B → A (2 * u) (2 * B)) :
    ∀ r, Even r → r ≤ 28 → A r (4 * r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr hr28
    rw [Nat.even_iff] at hr
    rcases (by omega : r = 0 ∨ (r % 4 = 0 ∧ 0 < r) ∨ r % 4 = 2) with h | h | h
    · subst h; simpa using h0
    · obtain ⟨u, rfl⟩ : ∃ u, r = 2 * u := ⟨r / 2, by omega⟩
      have hu := hdouble u _ (Nat.even_iff.mpr (by omega))
        (ih u (by omega) (Nat.even_iff.mpr (by omega)) (by omega))
      exact hmono _ _ _ hu (le_of_eq (by push_cast; ring))
    · apply hseed
      simp only [seedLengths, Finset.mem_insert, Finset.mem_singleton]
      omega

/-- Lemma `lem:tails`, the induction, abstractly. `A r B` stands for "there is a balanced pair of
sign sequences of length `r` with energy at most `B`". If `A` is monotone in `B`, holds for the
empty pair and the seeds, and is closed under doubling, appending, deletion and interleaving
(with the bounds of the paper), then `A r (6r)` for every even `r`. -/
theorem tails_induction
    (hmono : ∀ r B B', A r B → B ≤ B' → A r B') (h0 : A 0 0)
    (hseed : ∀ r ∈ seedLengths, A r (4 * r))
    (hdouble : ∀ u B, Even u → A u B → A (2 * u) (2 * B))
    (happend : ∀ u B, Even u → A u B → A (u + 2) ((Real.sqrt B + Real.sqrt 8) ^ 2))
    (hdelete : ∀ g, InG g → A (2 * g - 2) (8 * g + 8 + 16 * Real.sqrt g))
    (hinter : ∀ m t B, InG m → Even t → A t B →
      A (2 * m + 2 * t + 2) (8 * m + 8 + 16 * Real.sqrt m + 4 * B)) :
    ∀ r, Even r → A r (6 * r) := by
  have small := tails_small A hmono h0 hseed hdouble
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    have hr' := Nat.even_iff.mp hr
    rcases (by omega : r = 0 ∨ (r % 4 = 0 ∧ 0 < r) ∨ r % 4 = 2) with h | h | h
    · -- empty pair
      subst h; simpa using h0
    · -- (2) doubling
      obtain ⟨u, rfl⟩ : ∃ u, r = 2 * u := ⟨r / 2, by omega⟩
      have hu := hdouble u _ (Nat.even_iff.mpr (by omega))
        (ih u (by omega) (Nat.even_iff.mpr (by omega)))
      exact hmono _ _ _ hu (le_of_eq (by push_cast; ring))
    rcases (by omega : r ≤ 26 ∨ (30 ≤ r ∧ r ≤ 58) ∨ 62 ≤ r) with h1 | h1 | h1
    · -- (1) seeds
      have := small r hr (by omega)
      exact hmono _ _ _ this (by have : (0 : ℝ) ≤ r := r.cast_nonneg; linarith)
    · -- (3) appending to the pair of length `r - 2 = 2u`, `u` even, `u ≤ 28`
      obtain ⟨u, hu⟩ : ∃ u, r - 2 = 2 * u := ⟨(r - 2) / 2, by omega⟩
      have hA : A (r - 2) (4 * ((r - 2 : ℕ) : ℝ)) := by
        have := hdouble u _ (Nat.even_iff.mpr (by omega))
          (small u (Nat.even_iff.mpr (by omega)) (by omega))
        rw [hu]
        exact hmono _ _ _ this (le_of_eq (by push_cast; ring))
      have := happend (r - 2) _ (Nat.even_iff.mpr (by omega)) hA
      rw [show r - 2 + 2 = r by omega] at this
      refine hmono _ _ _ this ?_
      have hc : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [hc]
      exact append_scalar' (by exact_mod_cast (show 30 ≤ r by omega))
    by_cases hg : InG ((r + 2) / 2)
    · -- (4) deletion, `g = (r + 2)/2 ∈ 𝒢`
      have := hdelete _ hg
      rw [show 2 * ((r + 2) / 2) - 2 = r by omega] at this
      refine hmono _ _ _ this ?_
      have hgr : (((r + 2) / 2 : ℕ) : ℝ) = ((r : ℝ) + 2) / 2 := by
        have e : ((r + 2) / 2) * 2 = r + 2 := by omega
        have e' : (((r + 2) / 2 : ℕ) : ℝ) * 2 = (r : ℝ) + 2 := by exact_mod_cast e
        linarith
      have := deletion_scalar (g := (((r + 2) / 2 : ℕ) : ℝ))
        (by rw [hgr]; have : (62 : ℝ) ≤ r := by exact_mod_cast h1
            linarith)
      rw [hgr] at this ⊢
      linarith
    · -- (5) interleaving, `h = (r - 2)/2`, `m` the largest element of `𝒢` with `m ≤ h`
      set h := (r - 2) / 2 with hh
      have hh30 : 30 ≤ h := by omega
      have hhe : Even h := Nat.even_iff.mpr (by omega)
      have hg' : ¬ InG (h + 2) := by rwa [show h + 2 = (r + 2) / 2 by omega]
      obtain ⟨m, hm⟩ := exists_isMaxG (h := h) (by omega)
      obtain ⟨m32, hte, -, hcase⟩ := interleave_params hh30 hhe hg' hm
      have hmh := hm.2.1
      set t := h - m with ht
      have hr2 : 2 * m + 2 * t + 2 = r := by omega
      have hmR : (32 : ℝ) ≤ m := by exact_mod_cast m32
      have hrR : (r : ℝ) = 2 * m + 2 * t + 2 := by exact_mod_cast hr2.symm
      rcases hcase with ⟨-, ht28, ht4⟩ | ⟨m160, ht4⟩
      · -- `32 ≤ m ≤ 128`: `B = 4t`
        have := hinter m t _ hm.1 hte (small t hte ht28)
        rw [hr2] at this
        refine hmono _ _ _ this ?_
        rw [hrR]
        have := interleave_small_scalar hmR (t := t) (by exact_mod_cast ht4)
        linarith
      · -- `m ≥ 160`: `B = 6t` by the induction hypothesis
        have := hinter m t _ hm.1 hte (ih t (by omega) hte)
        rw [hr2] at this
        refine hmono _ _ _ this ?_
        rw [hrR]
        have := interleave_large_scalar (m := m) (t := t) (by exact_mod_cast (by omega : 144 ≤ m))
          (by exact_mod_cast ht4)
        linarith

end Induction

/-- Lemma `lem:tails`, the induction, with an energy function `E : ℕ → ℝ` (for instance
`E r` = the least energy bound of a balanced pair of length `r`). Hypotheses as in the task:
`E 0 = 0`, seeds `E r ≤ 4r`, doubling `E(2u) ≤ 2E(u)`, appending `E(u+2) ≤ (√E(u) + √8)²`,
deletion `E(2g-2) ≤ 8g + 8 + 16√g` (`g ∈ 𝒢`), interleaving
`E(2m+2t+2) ≤ 8m + 8 + 16√m + 4E(t)` (`m ∈ 𝒢`, `t` even). Then `E r ≤ 6r` for all even `r`.
(Nonnegativity of `E` is not needed.) -/
theorem tails_induction_E (E : ℕ → ℝ) (h0 : E 0 = 0)
    (hseed : ∀ r ∈ seedLengths, E r ≤ 4 * r)
    (hdouble : ∀ u, Even u → E (2 * u) ≤ 2 * E u)
    (happend : ∀ u, Even u → E (u + 2) ≤ (Real.sqrt (E u) + Real.sqrt 8) ^ 2)
    (hdelete : ∀ g, InG g → E (2 * g - 2) ≤ 8 * g + 8 + 16 * Real.sqrt g)
    (hinter : ∀ m t, InG m → Even t → E (2 * m + 2 * t + 2) ≤ 8 * m + 8 + 16 * Real.sqrt m + 4 * E t) :
    ∀ r, Even r → E r ≤ 6 * r := by
  refine tails_induction (fun r B => E r ≤ B) (fun r B B' h hB => h.trans hB) h0.le hseed
    (fun u B hu h => (hdouble u hu).trans (by linarith)) (fun u B hu h => (happend u hu).trans ?_)
    hdelete (fun m t B hm ht h => (hinter m t hm ht).trans (by linarith))
  gcongr

/-! ### Pointwise analytic facts behind the operations -/

/-- `|1 - z^u|² ≤ 4` for `|z| = 1`. -/
theorem norm_one_sub_pow_sq_le {z : ℂ} (hz : ‖z‖ = 1) (u : ℕ) : ‖1 - z ^ u‖ ^ 2 ≤ 4 := by
  have h : ‖1 - z ^ u‖ ≤ 2 := by
    calc ‖1 - z ^ u‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ u‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  have := norm_nonneg (1 - z ^ u)
  nlinarith

/-- `|1 - z|² + |1 + z|² = 4` for `|z| = 1`. -/
theorem norm_one_sub_sq_add_norm_one_add_sq {z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - z‖ ^ 2 + ‖1 + z‖ ^ 2 = 4 := by
  have := doubling_identity 1 z 1 (by simp)
  simp only [one_mul, norm_one, hz] at this
  linarith

/-- Appending: if `|R|² + |T|² ≤ B` then `|R + c(1-z)|² + |T + c(1-z)|² ≤ (√B + √8)²`
for `|c| = 1`, `|z| = 1` (with `c = z^u` this is appending `(1, -1)` to both sequences). -/
theorem append_bound {R T c z : ℂ} {B : ℝ} (hc : ‖c‖ = 1) (hz : ‖z‖ = 1)
    (h : ‖R‖ ^ 2 + ‖T‖ ^ 2 ≤ B) :
    ‖R + c * (1 - z)‖ ^ 2 + ‖T + c * (1 - z)‖ ^ 2 ≤ (Real.sqrt B + Real.sqrt 8) ^ 2 := by
  refine (norm2_add_le R T _ _).trans ?_
  have h8 : ‖c * (1 - z)‖ ^ 2 + ‖c * (1 - z)‖ ^ 2 ≤ 8 := by
    rw [norm_mul, hc, one_mul]
    have := norm_one_sub_pow_sq_le hz 1
    rw [pow_one] at this
    linarith
  gcongr

/-- `4(√(2g) + √2)² = 8g + 8 + 16√g` for `g ≥ 0`. -/
theorem deletion_value {g : ℝ} (hg : 0 ≤ g) :
    4 * (Real.sqrt (2 * g) + Real.sqrt 2) ^ 2 = 8 * g + 8 + 16 * Real.sqrt g := by
  have h1 := Real.sq_sqrt (show 0 ≤ 2 * g by linarith)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 : Real.sqrt (2 * g) * Real.sqrt 2 = 2 * Real.sqrt g := by
    rw [← Real.sqrt_mul (by linarith), show 2 * g * 2 = 2 ^ 2 * g by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  nlinarith

/-- Deletion: if `|P|² + |Q|² = 2g` and `|a| = |b| = |w| = 1` then
`|1 - w|² (|P - a|² + |Q - b|²) ≤ 4(√(2g) + √2)² = 8g + 8 + 16√g`. -/
theorem deletion_bound {P Q a b w : ℂ} {g : ℝ} (hg : 0 ≤ g) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hw : ‖w‖ = 1) (h : ‖P‖ ^ 2 + ‖Q‖ ^ 2 = 2 * g) :
    ‖1 - w‖ ^ 2 * (‖P - a‖ ^ 2 + ‖Q - b‖ ^ 2) ≤ 8 * g + 8 + 16 * Real.sqrt g := by
  rw [← deletion_value hg]
  have hv : ‖P - a‖ ^ 2 + ‖Q - b‖ ^ 2 ≤ (Real.sqrt (2 * g) + Real.sqrt 2) ^ 2 := by
    have := norm2_add_le P Q (-a) (-b)
    rw [norm_neg, norm_neg, ha, hb, h, ← sub_eq_add_neg, ← sub_eq_add_neg,
      show (1 : ℝ) ^ 2 + 1 ^ 2 = 2 by norm_num] at this
    exact this
  have h4 := norm_one_sub_pow_sq_le hw 1
  rw [pow_one] at h4
  have := sq_nonneg (Real.sqrt (2 * g) + Real.sqrt 2)
  have := add_nonneg (sq_nonneg ‖P - a‖) (sq_nonneg ‖Q - b‖)
  nlinarith

/-- Interleaving: if `|x₁|² + |x₂|² ≤ X²`, `|y₁|² + |y₂|² ≤ B` and `|z| = 1`, then
`|(1-z)x₁ + (1+z)y₁|² + |(1-z)x₂ + (1+z)y₂|² ≤ 4(X² + B)`
(Cauchy–Schwarz with `|1-z|² + |1+z|² = 4`). -/
theorem interleave_bound {x₁ x₂ y₁ y₂ z : ℂ} {X B : ℝ} (hz : ‖z‖ = 1)
    (hx : ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 ≤ X ^ 2) (hy : ‖y₁‖ ^ 2 + ‖y₂‖ ^ 2 ≤ B) :
    ‖(1 - z) * x₁ + (1 + z) * y₁‖ ^ 2 + ‖(1 - z) * x₂ + (1 + z) * y₂‖ ^ 2 ≤ 4 * (X ^ 2 + B) := by
  refine (norm2_add_le _ _ _ _).trans ?_
  simp only [norm_mul, mul_pow]
  rw [← mul_add, ← mul_add, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have h4 := norm_one_sub_sq_add_norm_one_add_sq hz
  set α := ‖1 - z‖
  set β := ‖1 + z‖
  set Sx := ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2
  set Sy := ‖y₁‖ ^ 2 + ‖y₂‖ ^ 2
  have hSx : 0 ≤ Sx := by positivity
  have hSy : 0 ≤ Sy := by positivity
  have ex := Real.sq_sqrt hSx
  have ey := Real.sq_sqrt hSy
  -- `(α√Sx + β√Sy)² ≤ (α² + β²)(Sx + Sy)`
  have cs : (α * Real.sqrt Sx + β * Real.sqrt Sy) ^ 2 ≤ (α ^ 2 + β ^ 2) * (Sx + Sy) := by
    nlinarith [sq_nonneg (α * Real.sqrt Sy - β * Real.sqrt Sx)]
  rw [h4] at cs
  linarith

/-- Interleaving with `X = √(2m) + √2`: the bound is `8m + 8 + 16√m + 4B`. -/
theorem interleave_value {m B : ℝ} (hm : 0 ≤ m) :
    4 * ((Real.sqrt (2 * m) + Real.sqrt 2) ^ 2 + B) = 8 * m + 8 + 16 * Real.sqrt m + 4 * B := by
  have := deletion_value hm
  linarith

/-! ### The seeds (Table `tab:seeds`)

Each identity is a polynomial identity in `z` and `w = conj z` modulo `z w = 1`; it is checked by
`linear_combination Q * (z w = 1)`, where the quotient `Q` was computed outside Lean and the
identity `LHS - RHS = Q (z w - 1)` is verified by `ring`. -/

theorem conj_peval {n : ℕ} (A : Fin n → ℤ) (z : ℂ) : conj (peval A z) = peval A (conj z) := by
  simp [peval, map_sum]

theorem mul_conj_eq_one_of_norm {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj', hz]; simp

theorem ofReal_sq_norm (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * conj x := by
  rw [Complex.mul_conj']; push_cast; rfl

/-- Seed of length `2`: `A = -+`, `B` empty. -/
def seedA2 : Fin 2 → ℤ := ![-1, 1]

/-- Seed of length `2`, the sequence `B`. -/
def seedB2 : Fin 0 → ℤ := ![]

/-- Seed of length `6`: `A = --++`, `B = -+`. -/
def seedA6 : Fin 4 → ℤ := ![-1, -1, 1, 1]

/-- Seed of length `6`, the sequence `B`. -/
def seedB6 : Fin 2 → ℤ := ![-1, 1]

/-- Seed of length `10`: `A = -+--++`, `B = -+-+`. -/
def seedA10 : Fin 6 → ℤ := ![-1, 1, -1, -1, 1, 1]

/-- Seed of length `10`, the sequence `B`. -/
def seedB10 : Fin 4 → ℤ := ![-1, 1, -1, 1]

/-- Seed of length `14`: `A = -+-+--++`, `B = -+--++`. -/
def seedA14 : Fin 8 → ℤ := ![-1, 1, -1, 1, -1, -1, 1, 1]

/-- Seed of length `14`, the sequence `B`. -/
def seedB14 : Fin 6 → ℤ := ![-1, 1, -1, -1, 1, 1]

/-- Seed of length `18`: `A = -++----+++`, `B = --+-+-++`. -/
def seedA18 : Fin 10 → ℤ := ![-1, 1, 1, -1, -1, -1, -1, 1, 1, 1]

/-- Seed of length `18`, the sequence `B`. -/
def seedB18 : Fin 8 → ℤ := ![-1, -1, 1, -1, 1, -1, 1, 1]

/-- Seed of length `22`: `A = -++--+---+++`, `B = --+-+--+++`. -/
def seedA22 : Fin 12 → ℤ := ![-1, 1, 1, -1, -1, 1, -1, -1, -1, 1, 1, 1]

/-- Seed of length `22`, the sequence `B`. -/
def seedB22 : Fin 10 → ℤ := ![-1, -1, 1, -1, 1, -1, -1, 1, 1, 1]

/-- Seed of length `26`: `A = -++-+-+----+++`, `B = ---+--++-+++`. -/
def seedA26 : Fin 14 → ℤ := ![-1, 1, 1, -1, 1, -1, 1, -1, -1, -1, -1, 1, 1, 1]

/-- Seed of length `26`, the sequence `B`. -/
def seedB26 : Fin 12 → ℤ := ![-1, -1, -1, 1, -1, -1, 1, 1, -1, 1, 1, 1]

/-- Table `tab:seeds`, row `r = 2`: `|A(z)|² + |B(z)|² = ‖1 - z‖ ^ 2` for `|z| = 1`. -/
theorem seed_2 {z : ℂ} (hz : ‖z‖ = 1) :
    ‖peval seedA2 z‖ ^ 2 + ‖peval seedB2 z‖ ^ 2 =
      ‖1 - z‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval, map_sub, map_one, map_pow]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, seedA2, seedB2]
  linear_combination (0) * hw

/-- Table `tab:seeds`, row `r = 6`: `|A(z)|² + |B(z)|² = 2 * ‖1 - z ^ 2‖ ^ 2 + ‖1 - z ^ 3‖ ^ 2` for `|z| = 1`. -/
theorem seed_6 {z : ℂ} (hz : ‖z‖ = 1) :
    ‖peval seedA6 z‖ ^ 2 + ‖peval seedB6 z‖ ^ 2 =
      2 * ‖1 - z ^ 2‖ ^ 2 + ‖1 - z ^ 3‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval, map_sub, map_one, map_pow]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, seedA6, seedB6]
  linear_combination (1 - w ^ 2 - z * w + z * w ^ 2 - z ^ 2 + z ^ 2 * w) * hw

/-- Table `tab:seeds`, row `r = 10`: `|A(z)|² + |B(z)|² = 4 * ‖1 - z‖ ^ 2 + ‖1 - z ^ 5‖ ^ 2` for `|z| = 1`. -/
theorem seed_10 {z : ℂ} (hz : ‖z‖ = 1) :
    ‖peval seedA10 z‖ ^ 2 + ‖peval seedB10 z‖ ^ 2 =
      4 * ‖1 - z‖ ^ 2 + ‖1 - z ^ 5‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval, map_sub, map_one, map_pow]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, seedA10, seedB10]
  linear_combination (3 - 2 * w - 2 * w ^ 2 + w ^ 4 - 2 * z + 5 * z * w - 2 * z * w ^ 3 - z * w ^ 4 - 2 * z ^ 2 + 3 * z ^ 2 * w ^ 2 - z ^ 2 * w ^ 4 - 2 * z ^ 3 * w + z ^ 3 * w ^ 3 + z ^ 3 * w ^ 4 + z ^ 4 - z ^ 4 * w - z ^ 4 * w ^ 2 + z ^ 4 * w ^ 3) * hw

/-- Table `tab:seeds`, row `r = 14`: `|A(z)|² + |B(z)|² = 4 * ‖1 - z‖ ^ 2 + 2 * ‖1 - z ^ 2‖ ^ 2 + ‖1 - z ^ 7‖ ^ 2` for `|z| = 1`. -/
theorem seed_14 {z : ℂ} (hz : ‖z‖ = 1) :
    ‖peval seedA14 z‖ ^ 2 + ‖peval seedB14 z‖ ^ 2 =
      4 * ‖1 - z‖ ^ 2 + 2 * ‖1 - z ^ 2‖ ^ 2 + ‖1 - z ^ 7‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval, map_sub, map_one, map_pow]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, seedA14, seedB14]
  linear_combination (5 - 2 * w - 4 * w ^ 2 + w ^ 6 - 2 * z + 7 * z * w - 4 * z * w ^ 3 - z * w ^ 6 - 4 * z ^ 2 + 7 * z ^ 2 * w ^ 2 - 4 * z ^ 2 * w ^ 4 + z ^ 2 * w ^ 6 - 4 * z ^ 3 * w + 5 * z ^ 3 * w ^ 3 + 2 * z ^ 3 * w ^ 4 - 2 * z ^ 3 * w ^ 5 - z ^ 3 * w ^ 6 - 4 * z ^ 4 * w ^ 2 + 2 * z ^ 4 * w ^ 3 + 3 * z ^ 4 * w ^ 4 - z ^ 4 * w ^ 6 - 2 * z ^ 5 * w ^ 3 + z ^ 5 * w ^ 5 + z ^ 5 * w ^ 6 + z ^ 6 - z ^ 6 * w + z ^ 6 * w ^ 2 - z ^ 6 * w ^ 3 - z ^ 6 * w ^ 4 + z ^ 6 * w ^ 5) * hw

/-- Table `tab:seeds`, row `r = 18`: `|A(z)|² + |B(z)|² = 4 * ‖1 - z ^ 3‖ ^ 2 + 4 * ‖1 - z ^ 4‖ ^ 2 + ‖1 - z ^ 9‖ ^ 2` for `|z| = 1`. -/
theorem seed_18 {z : ℂ} (hz : ‖z‖ = 1) :
    ‖peval seedA18 z‖ ^ 2 + ‖peval seedB18 z‖ ^ 2 =
      4 * ‖1 - z ^ 3‖ ^ 2 + 4 * ‖1 - z ^ 4‖ ^ 2 + ‖1 - z ^ 9‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval, map_sub, map_one, map_pow]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, seedA18, seedB18]
  linear_combination (7 + 2 * w ^ 2 - 6 * w ^ 3 - 4 * w ^ 4 - 2 * w ^ 5 + 2 * w ^ 7 + w ^ 8 + 5 * z * w + 2 * z * w ^ 3 - 4 * z * w ^ 4 - 4 * z * w ^ 5 + z * w ^ 8 + 2 * z ^ 2 + 3 * z ^ 2 * w ^ 2 + 2 * z ^ 2 * w ^ 3 + 2 * z ^ 2 * w ^ 4 - 2 * z ^ 2 * w ^ 5 - 4 * z ^ 2 * w ^ 6 - 2 * z ^ 2 * w ^ 7 - z ^ 2 * w ^ 8 - 6 * z ^ 3 + 2 * z ^ 3 * w + 2 * z ^ 3 * w ^ 2 + 5 * z ^ 3 * w ^ 3 + 2 * z ^ 3 * w ^ 4 - 2 * z ^ 3 * w ^ 6 - 2 * z ^ 3 * w ^ 7 - z ^ 3 * w ^ 8 - 4 * z ^ 4 - 4 * z ^ 4 * w + 2 * z ^ 4 * w ^ 2 + 2 * z ^ 4 * w ^ 3 + 7 * z ^ 4 * w ^ 4 + 2 * z ^ 4 * w ^ 5 - 2 * z ^ 4 * w ^ 6 - 2 * z ^ 4 * w ^ 7 - z ^ 4 * w ^ 8 - 2 * z ^ 5 - 4 * z ^ 5 * w - 2 * z ^ 5 * w ^ 2 + 2 * z ^ 5 * w ^ 4 + 5 * z ^ 5 * w ^ 5 + 2 * z ^ 5 * w ^ 6 - z ^ 5 * w ^ 8 - 4 * z ^ 6 * w ^ 2 - 2 * z ^ 6 * w ^ 3 - 2 * z ^ 6 * w ^ 4 + 2 * z ^ 6 * w ^ 5 + 3 * z ^ 6 * w ^ 6 + 2 * z ^ 6 * w ^ 7 + z ^ 6 * w ^ 8 + 2 * z ^ 7 - 2 * z ^ 7 * w ^ 2 - 2 * z ^ 7 * w ^ 3 - 2 * z ^ 7 * w ^ 4 + 2 * z ^ 7 * w ^ 6 + z ^ 7 * w ^ 7 + z ^ 7 * w ^ 8 + z ^ 8 + z ^ 8 * w - z ^ 8 * w ^ 2 - z ^ 8 * w ^ 3 - z ^ 8 * w ^ 4 - z ^ 8 * w ^ 5 + z ^ 8 * w ^ 6 + z ^ 8 * w ^ 7) * hw

/-- Table `tab:seeds`, row `r = 22`: `|A(z)|² + |B(z)|² = 4 * ‖1 - z ^ 2‖ ^ 2 + 2 * ‖1 - z ^ 3‖ ^ 2 + 2 * ‖1 - z ^ 6‖ ^ 2 + 2 * ‖1 - z ^ 7‖ ^ 2 + ‖1 - z ^ 11‖ ^ 2` for `|z| = 1`. -/
theorem seed_22 {z : ℂ} (hz : ‖z‖ = 1) :
    ‖peval seedA22 z‖ ^ 2 + ‖peval seedB22 z‖ ^ 2 =
      4 * ‖1 - z ^ 2‖ ^ 2 + 2 * ‖1 - z ^ 3‖ ^ 2 + 2 * ‖1 - z ^ 6‖ ^ 2 + 2 * ‖1 - z ^ 7‖ ^ 2 + ‖1 - z ^ 11‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval, map_sub, map_one, map_pow]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, seedA22, seedB22]
  linear_combination (9 - 2 * w ^ 2 - 4 * w ^ 3 - 4 * w ^ 6 - 2 * w ^ 7 + 2 * w ^ 9 + w ^ 10 + 7 * z * w - 2 * z * w ^ 3 - 2 * z * w ^ 4 - 2 * z * w ^ 5 - 2 * z * w ^ 7 + z * w ^ 10 - 2 * z ^ 2 + 9 * z ^ 2 * w ^ 2 + 2 * z ^ 2 * w ^ 3 - 2 * z ^ 2 * w ^ 4 - 2 * z ^ 2 * w ^ 5 - 2 * z ^ 2 * w ^ 8 - 2 * z ^ 2 * w ^ 9 - z ^ 2 * w ^ 10 - 4 * z ^ 3 - 2 * z ^ 3 * w + 2 * z ^ 3 * w ^ 2 + 9 * z ^ 3 * w ^ 3 + 2 * z ^ 3 * w ^ 4 - 2 * z ^ 3 * w ^ 5 - 4 * z ^ 3 * w ^ 6 - z ^ 3 * w ^ 10 - 2 * z ^ 4 * w - 2 * z ^ 4 * w ^ 2 + 2 * z ^ 4 * w ^ 3 + 7 * z ^ 4 * w ^ 4 + 4 * z ^ 4 * w ^ 5 - 2 * z ^ 4 * w ^ 6 - 6 * z ^ 4 * w ^ 7 - 2 * z ^ 4 * w ^ 8 + z ^ 4 * w ^ 10 - 2 * z ^ 5 * w - 2 * z ^ 5 * w ^ 2 - 2 * z ^ 5 * w ^ 3 + 4 * z ^ 5 * w ^ 4 + 5 * z ^ 5 * w ^ 5 + 4 * z ^ 5 * w ^ 6 - 4 * z ^ 5 * w ^ 8 - 2 * z ^ 5 * w ^ 9 - z ^ 5 * w ^ 10 - 4 * z ^ 6 - 4 * z ^ 6 * w ^ 3 - 2 * z ^ 6 * w ^ 4 + 4 * z ^ 6 * w ^ 5 + 5 * z ^ 6 * w ^ 6 + 4 * z ^ 6 * w ^ 7 - 2 * z ^ 6 * w ^ 9 - z ^ 6 * w ^ 10 - 2 * z ^ 7 - 2 * z ^ 7 * w - 6 * z ^ 7 * w ^ 4 + 4 * z ^ 7 * w ^ 6 + 5 * z ^ 7 * w ^ 7 + 2 * z ^ 7 * w ^ 8 - z ^ 7 * w ^ 10 - 2 * z ^ 8 * w ^ 2 - 2 * z ^ 8 * w ^ 4 - 4 * z ^ 8 * w ^ 5 + 2 * z ^ 8 * w ^ 7 + 3 * z ^ 8 * w ^ 8 + 2 * z ^ 8 * w ^ 9 + z ^ 8 * w ^ 10 + 2 * z ^ 9 - 2 * z ^ 9 * w ^ 2 - 2 * z ^ 9 * w ^ 5 - 2 * z ^ 9 * w ^ 6 + 2 * z ^ 9 * w ^ 8 + z ^ 9 * w ^ 9 + z ^ 9 * w ^ 10 + z ^ 10 + z ^ 10 * w - z ^ 10 * w ^ 2 - z ^ 10 * w ^ 3 + z ^ 10 * w ^ 4 - z ^ 10 * w ^ 5 - z ^ 10 * w ^ 6 - z ^ 10 * w ^ 7 + z ^ 10 * w ^ 8 + z ^ 10 * w ^ 9) * hw

/-- Table `tab:seeds`, row `r = 26`: `|A(z)|² + |B(z)|² = 2 * ‖1 - z ^ 5‖ ^ 2 + 6 * ‖1 - z ^ 6‖ ^ 2 + 2 * ‖1 - z ^ 8‖ ^ 2 + 2 * ‖1 - z ^ 9‖ ^ 2 + ‖1 - z ^ 13‖ ^ 2` for `|z| = 1`. -/
theorem seed_26 {z : ℂ} (hz : ‖z‖ = 1) :
    ‖peval seedA26 z‖ ^ 2 + ‖peval seedB26 z‖ ^ 2 =
      2 * ‖1 - z ^ 5‖ ^ 2 + 6 * ‖1 - z ^ 6‖ ^ 2 + 2 * ‖1 - z ^ 8‖ ^ 2 + 2 * ‖1 - z ^ 9‖ ^ 2 + ‖1 - z ^ 13‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval, map_sub, map_one, map_pow]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, seedA26, seedB26]
  linear_combination (11 - 4 * w ^ 5 - 4 * w ^ 6 - 4 * w ^ 8 - 2 * w ^ 9 + 2 * w ^ 11 + w ^ 12 + 9 * z * w - 2 * z * w ^ 2 + 2 * z * w ^ 3 - 2 * z * w ^ 4 - 4 * z * w ^ 6 - 2 * z * w ^ 7 - 2 * z * w ^ 9 + z * w ^ 12 - 2 * z ^ 2 * w + 7 * z ^ 2 * w ^ 2 - 2 * z ^ 2 * w ^ 5 - 2 * z ^ 2 * w ^ 7 - 2 * z ^ 2 * w ^ 8 + 2 * z ^ 2 * w ^ 9 - z ^ 2 * w ^ 12 + 2 * z ^ 3 * w + 5 * z ^ 3 * w ^ 3 + 2 * z ^ 3 * w ^ 4 - 2 * z ^ 3 * w ^ 6 - 2 * z ^ 3 * w ^ 7 - 2 * z ^ 3 * w ^ 8 - 4 * z ^ 3 * w ^ 9 + z ^ 3 * w ^ 12 - 2 * z ^ 4 * w + 2 * z ^ 4 * w ^ 3 + 3 * z ^ 4 * w ^ 4 + 2 * z ^ 4 * w ^ 5 - 2 * z ^ 4 * w ^ 8 - 2 * z ^ 4 * w ^ 10 - z ^ 4 * w ^ 12 - 4 * z ^ 5 - 2 * z ^ 5 * w ^ 2 + 2 * z ^ 5 * w ^ 4 + 3 * z ^ 5 * w ^ 5 + 4 * z ^ 5 * w ^ 6 - 2 * z ^ 5 * w ^ 8 - 2 * z ^ 5 * w ^ 9 + z ^ 5 * w ^ 12 - 4 * z ^ 6 - 4 * z ^ 6 * w - 2 * z ^ 6 * w ^ 3 + 4 * z ^ 6 * w ^ 5 + 7 * z ^ 6 * w ^ 6 + 4 * z ^ 6 * w ^ 7 + 2 * z ^ 6 * w ^ 8 - 2 * z ^ 6 * w ^ 9 - 2 * z ^ 6 * w ^ 10 - 2 * z ^ 6 * w ^ 11 - z ^ 6 * w ^ 12 - 2 * z ^ 7 * w - 2 * z ^ 7 * w ^ 2 - 2 * z ^ 7 * w ^ 3 + 4 * z ^ 7 * w ^ 6 + 5 * z ^ 7 * w ^ 7 + 4 * z ^ 7 * w ^ 8 - 4 * z ^ 7 * w ^ 10 - 2 * z ^ 7 * w ^ 11 - z ^ 7 * w ^ 12 - 4 * z ^ 8 - 2 * z ^ 8 * w ^ 2 - 2 * z ^ 8 * w ^ 3 - 2 * z ^ 8 * w ^ 4 - 2 * z ^ 8 * w ^ 5 + 2 * z ^ 8 * w ^ 6 + 4 * z ^ 8 * w ^ 7 + 5 * z ^ 8 * w ^ 8 + 4 * z ^ 8 * w ^ 9 - 2 * z ^ 8 * w ^ 11 - z ^ 8 * w ^ 12 - 2 * z ^ 9 - 2 * z ^ 9 * w + 2 * z ^ 9 * w ^ 2 - 4 * z ^ 9 * w ^ 3 - 2 * z ^ 9 * w ^ 5 - 2 * z ^ 9 * w ^ 6 + 4 * z ^ 9 * w ^ 8 + 5 * z ^ 9 * w ^ 9 + 2 * z ^ 9 * w ^ 10 - z ^ 9 * w ^ 12 - 2 * z ^ 10 * w ^ 4 - 2 * z ^ 10 * w ^ 6 - 4 * z ^ 10 * w ^ 7 + 2 * z ^ 10 * w ^ 9 + 3 * z ^ 10 * w ^ 10 + 2 * z ^ 10 * w ^ 11 + z ^ 10 * w ^ 12 + 2 * z ^ 11 - 2 * z ^ 11 * w ^ 6 - 2 * z ^ 11 * w ^ 7 - 2 * z ^ 11 * w ^ 8 + 2 * z ^ 11 * w ^ 10 + z ^ 11 * w ^ 11 + z ^ 11 * w ^ 12 + z ^ 12 + z ^ 12 * w - z ^ 12 * w ^ 2 + z ^ 12 * w ^ 3 - z ^ 12 * w ^ 4 + z ^ 12 * w ^ 5 - z ^ 12 * w ^ 6 - z ^ 12 * w ^ 7 - z ^ 12 * w ^ 8 - z ^ 12 * w ^ 9 + z ^ 12 * w ^ 10 + z ^ 12 * w ^ 11) * hw

/-- From a seed: if `A`, `B` are sign sequences with `A(1) = B(1) = 0` and
`|A|² + |B|² ≤ 2r` on the circle (`r = |A| + |B|`), then `(A|B, A|-B)` is a balanced pair of sign
sequences with energy at most `4r`. -/
theorem seed_pair {n m : ℕ} {A : Fin n → ℤ} {B : Fin m → ℤ} {r : ℝ} (hA : IsSignSeq A)
    (hB : IsSignSeq B) (hA1 : peval A 1 = 0) (hB1 : peval B 1 = 0)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ‖peval A z‖ ^ 2 + ‖peval B z‖ ^ 2 ≤ 2 * r) :
    IsSignSeq (Fin.append A B) ∧ IsSignSeq (Fin.append A (-B)) ∧
      peval (Fin.append A B) 1 = 0 ∧ peval (Fin.append A (-B)) 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval (Fin.append A B) z‖ ^ 2 + ‖peval (Fin.append A (-B)) z‖ ^ 2 ≤ 4 * r := by
  have s1 : IsSignSeq (Fin.append A B) := fun v =>
    Fin.addCases (fun i => by simpa using hA i) (fun i => by simpa using hB i) v
  have s2 : IsSignSeq (Fin.append A (-B)) := fun v =>
    Fin.addCases (fun i => by simpa using hA i)
      (fun i => by rcases hB i with h | h <;> simp [h]) v
  refine ⟨s1, s2, by simp [peval_append, hA1, hB1], by simp [peval_append, peval_neg, hA1, hB1],
    fun z hz => ?_⟩
  rw [peval_append, peval_append, peval_neg, mul_neg, ← sub_eq_add_neg,
    doubling_identity _ _ _ (by rw [norm_pow, hz, one_pow])]
  linarith [h z hz]

/-- Seed pair `(A|B, A|-B)` of length `2`: sign sequences, balanced, energy at most `4·2`. -/
theorem seedPair_2 :
    IsSignSeq (Fin.append seedA2 seedB2) ∧ IsSignSeq (Fin.append seedA2 (-seedB2)) ∧
      peval (Fin.append seedA2 seedB2) 1 = 0 ∧ peval (Fin.append seedA2 (-seedB2)) 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval (Fin.append seedA2 seedB2) z‖ ^ 2 +
        ‖peval (Fin.append seedA2 (-seedB2)) z‖ ^ 2 ≤ 4 * 2 := by
  refine seed_pair (by unfold IsSignSeq; decide) (by unfold IsSignSeq; decide)
    (by norm_num [peval, Fin.sum_univ_succ, seedA2])
    (by norm_num [peval, Fin.sum_univ_succ, seedB2]) (fun z hz => ?_)
  rw [seed_2 hz]
  have := norm_one_sub_pow_sq_le hz 1
  rw [pow_one] at this
  linarith

/-- Seed pair `(A|B, A|-B)` of length `6`: sign sequences, balanced, energy at most `4·6`. -/
theorem seedPair_6 :
    IsSignSeq (Fin.append seedA6 seedB6) ∧ IsSignSeq (Fin.append seedA6 (-seedB6)) ∧
      peval (Fin.append seedA6 seedB6) 1 = 0 ∧ peval (Fin.append seedA6 (-seedB6)) 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval (Fin.append seedA6 seedB6) z‖ ^ 2 +
        ‖peval (Fin.append seedA6 (-seedB6)) z‖ ^ 2 ≤ 4 * 6 := by
  refine seed_pair (by unfold IsSignSeq; decide) (by unfold IsSignSeq; decide)
    (by norm_num [peval, Fin.sum_univ_succ, seedA6])
    (by norm_num [peval, Fin.sum_univ_succ, seedB6]) (fun z hz => ?_)
  rw [seed_6 hz]
  have := norm_one_sub_pow_sq_le hz 1
  rw [pow_one] at this
  linarith [norm_one_sub_pow_sq_le hz 2, norm_one_sub_pow_sq_le hz 3]

/-- Seed pair `(A|B, A|-B)` of length `10`: sign sequences, balanced, energy at most `4·10`. -/
theorem seedPair_10 :
    IsSignSeq (Fin.append seedA10 seedB10) ∧ IsSignSeq (Fin.append seedA10 (-seedB10)) ∧
      peval (Fin.append seedA10 seedB10) 1 = 0 ∧ peval (Fin.append seedA10 (-seedB10)) 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval (Fin.append seedA10 seedB10) z‖ ^ 2 +
        ‖peval (Fin.append seedA10 (-seedB10)) z‖ ^ 2 ≤ 4 * 10 := by
  refine seed_pair (by unfold IsSignSeq; decide) (by unfold IsSignSeq; decide)
    (by norm_num [peval, Fin.sum_univ_succ, seedA10])
    (by norm_num [peval, Fin.sum_univ_succ, seedB10]) (fun z hz => ?_)
  rw [seed_10 hz]
  have := norm_one_sub_pow_sq_le hz 1
  rw [pow_one] at this
  linarith [norm_one_sub_pow_sq_le hz 5]

/-- Seed pair `(A|B, A|-B)` of length `14`: sign sequences, balanced, energy at most `4·14`. -/
theorem seedPair_14 :
    IsSignSeq (Fin.append seedA14 seedB14) ∧ IsSignSeq (Fin.append seedA14 (-seedB14)) ∧
      peval (Fin.append seedA14 seedB14) 1 = 0 ∧ peval (Fin.append seedA14 (-seedB14)) 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval (Fin.append seedA14 seedB14) z‖ ^ 2 +
        ‖peval (Fin.append seedA14 (-seedB14)) z‖ ^ 2 ≤ 4 * 14 := by
  refine seed_pair (by unfold IsSignSeq; decide) (by unfold IsSignSeq; decide)
    (by norm_num [peval, Fin.sum_univ_succ, seedA14])
    (by norm_num [peval, Fin.sum_univ_succ, seedB14]) (fun z hz => ?_)
  rw [seed_14 hz]
  have := norm_one_sub_pow_sq_le hz 1
  rw [pow_one] at this
  linarith [norm_one_sub_pow_sq_le hz 2, norm_one_sub_pow_sq_le hz 7]

/-- Seed pair `(A|B, A|-B)` of length `18`: sign sequences, balanced, energy at most `4·18`. -/
theorem seedPair_18 :
    IsSignSeq (Fin.append seedA18 seedB18) ∧ IsSignSeq (Fin.append seedA18 (-seedB18)) ∧
      peval (Fin.append seedA18 seedB18) 1 = 0 ∧ peval (Fin.append seedA18 (-seedB18)) 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval (Fin.append seedA18 seedB18) z‖ ^ 2 +
        ‖peval (Fin.append seedA18 (-seedB18)) z‖ ^ 2 ≤ 4 * 18 := by
  refine seed_pair (by unfold IsSignSeq; decide) (by unfold IsSignSeq; decide)
    (by norm_num [peval, Fin.sum_univ_succ, seedA18])
    (by norm_num [peval, Fin.sum_univ_succ, seedB18]) (fun z hz => ?_)
  rw [seed_18 hz]
  have := norm_one_sub_pow_sq_le hz 1
  rw [pow_one] at this
  linarith [norm_one_sub_pow_sq_le hz 3, norm_one_sub_pow_sq_le hz 4, norm_one_sub_pow_sq_le hz 9]

/-- Seed pair `(A|B, A|-B)` of length `22`: sign sequences, balanced, energy at most `4·22`. -/
theorem seedPair_22 :
    IsSignSeq (Fin.append seedA22 seedB22) ∧ IsSignSeq (Fin.append seedA22 (-seedB22)) ∧
      peval (Fin.append seedA22 seedB22) 1 = 0 ∧ peval (Fin.append seedA22 (-seedB22)) 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval (Fin.append seedA22 seedB22) z‖ ^ 2 +
        ‖peval (Fin.append seedA22 (-seedB22)) z‖ ^ 2 ≤ 4 * 22 := by
  refine seed_pair (by unfold IsSignSeq; decide) (by unfold IsSignSeq; decide)
    (by norm_num [peval, Fin.sum_univ_succ, seedA22])
    (by norm_num [peval, Fin.sum_univ_succ, seedB22]) (fun z hz => ?_)
  rw [seed_22 hz]
  have := norm_one_sub_pow_sq_le hz 1
  rw [pow_one] at this
  linarith [norm_one_sub_pow_sq_le hz 2, norm_one_sub_pow_sq_le hz 3, norm_one_sub_pow_sq_le hz 6, norm_one_sub_pow_sq_le hz 7, norm_one_sub_pow_sq_le hz 11]

/-- Seed pair `(A|B, A|-B)` of length `26`: sign sequences, balanced, energy at most `4·26`. -/
theorem seedPair_26 :
    IsSignSeq (Fin.append seedA26 seedB26) ∧ IsSignSeq (Fin.append seedA26 (-seedB26)) ∧
      peval (Fin.append seedA26 seedB26) 1 = 0 ∧ peval (Fin.append seedA26 (-seedB26)) 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval (Fin.append seedA26 seedB26) z‖ ^ 2 +
        ‖peval (Fin.append seedA26 (-seedB26)) z‖ ^ 2 ≤ 4 * 26 := by
  refine seed_pair (by unfold IsSignSeq; decide) (by unfold IsSignSeq; decide)
    (by norm_num [peval, Fin.sum_univ_succ, seedA26])
    (by norm_num [peval, Fin.sum_univ_succ, seedB26]) (fun z hz => ?_)
  rw [seed_26 hz]
  have := norm_one_sub_pow_sq_le hz 1
  rw [pow_one] at this
  linarith [norm_one_sub_pow_sq_le hz 5, norm_one_sub_pow_sq_le hz 6, norm_one_sub_pow_sq_le hz 8, norm_one_sub_pow_sq_le hz 9, norm_one_sub_pow_sq_le hz 13]


/-! ### Concrete operations on sequences -/

private theorem divNat_fpf {m k : ℕ} (a : Fin m) (b : Fin k) :
    (finProdFinEquiv (a, b)).divNat = a :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a, b))

private theorem modNat_fpf {m k : ℕ} (a : Fin m) (b : Fin k) :
    (finProdFinEquiv (a, b)).modNat = b :=
  congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a, b))

private theorem sum_fin_mul' {m k : ℕ} (f : Fin (m * k) → ℂ) :
    ∑ i, f i = ∑ a : Fin m, ∑ b : Fin k, f (finProdFinEquiv (a, b)) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]

/-- `x^∓ = (x₀, -x₀, x₁, -x₁, …)`. -/
def mpSeq {n : ℕ} (x : Fin n → ℤ) : Fin (n * 2) → ℤ := fun i =>
  ![x i.divNat, -x i.divNat] i.modNat

/-- `x^± = (x₀, x₀, x₁, x₁, …)`. -/
def ppSeq {n : ℕ} (x : Fin n → ℤ) : Fin (n * 2) → ℤ := fun i => x i.divNat

/-- `x^∓(z) = (1 - z) x(z²)`. -/
theorem peval_mpSeq {n : ℕ} (x : Fin n → ℤ) (z : ℂ) :
    peval (mpSeq x) z = (1 - z) * peval x (z ^ 2) := by
  rw [peval, sum_fin_mul']
  simp only [mpSeq, divNat_fpf, modNat_fpf, finProdFinEquiv_apply_val, Fin.sum_univ_two, peval,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero,
    Fin.val_one]
  push_cast
  rw [← pow_mul, pow_add]
  ring

/-- `x^±(z) = (1 + z) x(z²)`. -/
theorem peval_ppSeq {n : ℕ} (x : Fin n → ℤ) (z : ℂ) :
    peval (ppSeq x) z = (1 + z) * peval x (z ^ 2) := by
  rw [peval, sum_fin_mul']
  simp only [ppSeq, divNat_fpf, finProdFinEquiv_apply_val, Fin.sum_univ_two, peval,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.val_zero, Fin.val_one]
  rw [← pow_mul, pow_add]
  ring

theorem isSignSeq_mpSeq {n : ℕ} {x : Fin n → ℤ} (h : IsSignSeq x) : IsSignSeq (mpSeq x) := by
  intro i
  simp only [mpSeq]
  generalize i.modNat = b
  generalize i.divNat = a
  clear i
  fin_cases b <;> simp
  · exact h a
  · rcases h a with e | e <;> simp [e]

theorem isSignSeq_ppSeq {n : ℕ} {x : Fin n → ℤ} (h : IsSignSeq x) : IsSignSeq (ppSeq x) :=
  fun _ => h _

theorem isSignSeq_append {n m : ℕ} {A : Fin n → ℤ} {B : Fin m → ℤ} (hA : IsSignSeq A)
    (hB : IsSignSeq B) : IsSignSeq (Fin.append A B) := fun v =>
  Fin.addCases (fun i => by simpa using hA i) (fun i => by simpa using hB i) v

theorem isSignSeq_neg {n : ℕ} {A : Fin n → ℤ} (hA : IsSignSeq A) : IsSignSeq (-A) := fun v => by
  rcases hA v with h | h <;> simp [h]

/-- The pair `(1, -1)`. -/
def onePair : Fin 2 → ℤ := ![1, -1]

theorem peval_onePair (z : ℂ) : peval onePair z = 1 - z := by
  simp [peval, onePair, Fin.sum_univ_two]; ring

theorem isSignSeq_onePair : IsSignSeq onePair := by unfold IsSignSeq onePair; decide

/-- `TailPair r B`: there is a balanced pair `(R, T)` of sign sequences of length `r`
(`R(1) = T(1) = 0`) with energy at most `B` (`|R(z)|² + |T(z)|² ≤ B` for `|z| = 1`). -/
def TailPair (r : ℕ) (B : ℝ) : Prop :=
  ∃ R T : Fin r → ℤ, IsSignSeq R ∧ IsSignSeq T ∧ peval R 1 = 0 ∧ peval T 1 = 0 ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 ≤ B

/-- `GolayLen n`: there is a Golay pair of sign sequences of length `n`. -/
def GolayLen (n : ℕ) : Prop :=
  ∃ P Q : Fin n → ℤ, IsSignSeq P ∧ IsSignSeq Q ∧ IsGolay P Q

theorem tailPair_mono {r : ℕ} {B B' : ℝ} (h : TailPair r B) (hB : B ≤ B') : TailPair r B' := by
  obtain ⟨R, T, h1, h2, h3, h4, h5⟩ := h
  exact ⟨R, T, h1, h2, h3, h4, fun z hz => (h5 z hz).trans hB⟩

/-- The empty pair. -/
theorem tailPair_zero : TailPair 0 0 :=
  ⟨Fin.elim0, Fin.elim0, fun v => v.elim0, fun v => v.elim0, by simp [peval], by simp [peval],
    fun z _ => by simp [peval]⟩

/-- Doubling: `(R|T, R|-T)`. -/
theorem tailPair_double {u : ℕ} {B : ℝ} (h : TailPair u B) : TailPair (2 * u) (2 * B) := by
  obtain ⟨R, T, hR, hT, hR1, hT1, hE⟩ := h
  rw [two_mul]
  refine ⟨Fin.append R T, Fin.append R (-T), isSignSeq_append hR hT,
    isSignSeq_append hR (isSignSeq_neg hT), by simp [peval_append, hR1, hT1],
    by simp [peval_append, peval_neg, hR1, hT1], fun z hz => ?_⟩
  rw [peval_append, peval_append, peval_neg, mul_neg, ← sub_eq_add_neg,
    doubling_identity _ _ _ (by rw [norm_pow, hz, one_pow])]
  linarith [hE z hz]

/-- Appending `(1, -1)` to both sequences. -/
theorem tailPair_append {u : ℕ} {B : ℝ} (h : TailPair u B) :
    TailPair (u + 2) ((Real.sqrt B + Real.sqrt 8) ^ 2) := by
  obtain ⟨R, T, hR, hT, hR1, hT1, hE⟩ := h
  refine ⟨Fin.append R onePair, Fin.append T onePair, isSignSeq_append hR isSignSeq_onePair,
    isSignSeq_append hT isSignSeq_onePair, by simp [peval_append, hR1, peval_onePair],
    by simp [peval_append, hT1, peval_onePair], fun z hz => ?_⟩
  rw [peval_append, peval_append, peval_onePair]
  exact append_bound (by rw [norm_pow, hz, one_pow]) hz (hE z hz)

/-- Deletion: from a Golay pair `(P, Q)` of length `g`, `(P̄^∓, Q̄^∓)` has length `2g - 2`. -/
theorem tailPair_delete {g : ℕ} (hg : GolayLen g) (hg1 : 1 ≤ g) :
    TailPair (2 * g - 2) (8 * g + 8 + 16 * Real.sqrt g) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  obtain ⟨P, Q, hP, hQ, hG⟩ := hg
  rw [show 2 * (g' + 1) - 2 = g' * 2 by omega]
  have hs : ∀ (x : Fin (g' + 1) → ℤ), IsSignSeq x → IsSignSeq (Fin.tail x) := fun x hx v => hx _
  refine ⟨mpSeq (Fin.tail P), mpSeq (Fin.tail Q), isSignSeq_mpSeq (hs P hP),
    isSignSeq_mpSeq (hs Q hQ), by simp [peval_mpSeq], by simp [peval_mpSeq], fun z hz => ?_⟩
  have hz2 : ‖z ^ 2‖ = 1 := by rw [norm_pow, hz, one_pow]
  rw [peval_mpSeq, peval_mpSeq, norm_mul, norm_mul, mul_pow, mul_pow, ← mul_add,
    norm_peval_tail P hz2, norm_peval_tail Q hz2]
  have hGz := hG _ hz2
  have hn1 : ∀ x : ℤ, (x = 1 ∨ x = -1) → ‖(x : ℂ)‖ = 1 := by
    rintro x (rfl | rfl) <;> simp
  exact deletion_bound (by positivity) (hn1 _ (hP 0)) (hn1 _ (hQ 0)) hz
    hGz

/-- Interleaving: `R = P^∓ | U^± | (1,-1)`, `T = Q^∓ | V^± | (1,-1)` from a Golay pair `(P, Q)` of
length `m` and a balanced pair `(U, V)` of length `t`. -/
theorem tailPair_interleave {m t : ℕ} {B : ℝ} (hm : GolayLen m) (h : TailPair t B) :
    TailPair (2 * m + 2 * t + 2) (8 * m + 8 + 16 * Real.sqrt m + 4 * B) := by
  obtain ⟨P, Q, hP, hQ, hG⟩ := hm
  obtain ⟨U, V, hU, hV, hU1, hV1, hE⟩ := h
  rw [show 2 * m + 2 * t + 2 = m * 2 + t * 2 + 2 by ring]
  refine ⟨Fin.append (Fin.append (mpSeq P) (ppSeq U)) onePair,
    Fin.append (Fin.append (mpSeq Q) (ppSeq V)) onePair,
    isSignSeq_append (isSignSeq_append (isSignSeq_mpSeq hP) (isSignSeq_ppSeq hU)) isSignSeq_onePair,
    isSignSeq_append (isSignSeq_append (isSignSeq_mpSeq hQ) (isSignSeq_ppSeq hV)) isSignSeq_onePair,
    by simp [peval_append, peval_mpSeq, peval_ppSeq, peval_onePair, hU1],
    by simp [peval_append, peval_mpSeq, peval_ppSeq, peval_onePair, hV1], fun z hz => ?_⟩
  have hz2 : ‖z ^ 2‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hc : ‖z ^ (m * 2 + t * 2)‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hc' : ‖z ^ (m * 2)‖ = 1 := by rw [norm_pow, hz, one_pow]
  simp only [peval_append, peval_mpSeq, peval_ppSeq, peval_onePair]
  have key : ∀ (p u : ℂ), (1 - z) * p + z ^ (m * 2) * ((1 + z) * u) + z ^ (m * 2 + t * 2) * (1 - z)
      = (1 - z) * (p + z ^ (m * 2 + t * 2)) + (1 + z) * (z ^ (m * 2) * u) := fun p u => by ring
  rw [key, key, ← interleave_value (by positivity : (0 : ℝ) ≤ m)]
  refine interleave_bound hz ?_ ?_
  · have := norm2_add_le (peval P (z ^ 2)) (peval Q (z ^ 2)) (z ^ (m * 2 + t * 2))
      (z ^ (m * 2 + t * 2))
    rw [hG _ hz2, hc, show (1 : ℝ) ^ 2 + 1 ^ 2 = 2 by norm_num] at this
    exact this
  · rw [norm_mul, norm_mul, hc', one_mul, one_mul]
    exact hE _ hz2

/-- `A_{10} = +++++-+--+`. -/
def golayA10 : Fin 10 → ℤ := ![1, 1, 1, 1, 1, -1, 1, -1, -1, 1]

/-- `B_{10} = ++--+++-+-`. -/
def golayB10 : Fin 10 → ℤ := ![1, 1, -1, -1, 1, 1, 1, -1, 1, -1]

/-- `(A_{10}, B_{10})` is a Golay pair. -/
theorem isGolay_10 : IsGolay golayA10 golayB10 := by
  intro z hz
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, golayA10, golayB10]
  linear_combination (18 - 2 * w - 2 * w ^ 4 - 2 * w ^ 6 + 2 * w ^ 7 - 2 * z + 16 * z * w - 2 * z * w ^ 2 - 2 * z * w ^ 4 - 2 * z * w ^ 5 - 2 * z * w ^ 6 + 2 * z * w ^ 8 - 2 * z ^ 2 * w + 14 * z ^ 2 * w ^ 2 - 4 * z ^ 2 * w ^ 3 - 2 * z ^ 2 * w ^ 6 - 2 * z ^ 2 * w ^ 7 + 2 * z ^ 2 * w ^ 8 - 4 * z ^ 3 * w ^ 2 + 12 * z ^ 3 * w ^ 3 - 4 * z ^ 3 * w ^ 4 + 2 * z ^ 3 * w ^ 5 - 2 * z ^ 3 * w ^ 7 - 2 * z ^ 4 - 2 * z ^ 4 * w - 4 * z ^ 4 * w ^ 3 + 10 * z ^ 4 * w ^ 4 - 4 * z ^ 4 * w ^ 5 + 2 * z ^ 4 * w ^ 7 - 2 * z ^ 4 * w ^ 8 - 2 * z ^ 5 * w + 2 * z ^ 5 * w ^ 3 - 4 * z ^ 5 * w ^ 4 + 8 * z ^ 5 * w ^ 5 - 4 * z ^ 5 * w ^ 6 - 2 * z ^ 6 - 2 * z ^ 6 * w - 2 * z ^ 6 * w ^ 2 - 4 * z ^ 6 * w ^ 5 + 6 * z ^ 6 * w ^ 6 - 2 * z ^ 6 * w ^ 7 + 2 * z ^ 7 - 2 * z ^ 7 * w ^ 2 - 2 * z ^ 7 * w ^ 3 + 2 * z ^ 7 * w ^ 4 - 2 * z ^ 7 * w ^ 6 + 4 * z ^ 7 * w ^ 7 - 2 * z ^ 7 * w ^ 8 + 2 * z ^ 8 * w + 2 * z ^ 8 * w ^ 2 - 2 * z ^ 8 * w ^ 4 - 2 * z ^ 8 * w ^ 7 + 2 * z ^ 8 * w ^ 8) * hw

/-- `A_{26} = ++++-++--+-+-+--+-+++--+++`. -/
def golayA26 : Fin 26 → ℤ := ![1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, 1, 1, 1]

/-- `B_{26} = ++++-++--+-+++++-+---++---`. -/
def golayB26 : Fin 26 → ℤ := ![1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1]

/-- `(A_{26}, B_{26})` is a Golay pair. -/
theorem isGolay_26 : IsGolay golayA26 golayB26 := by
  intro z hz
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_sq_norm, conj_peval]
  have hw := mul_conj_eq_one_of_norm hz
  generalize (starRingEnd ℂ) z = w at hw ⊢
  simp [peval, Fin.sum_univ_succ, golayA26, golayB26]
  linear_combination (50 - 2 * w - 2 * w ^ 2 - 2 * w ^ 3 + 2 * w ^ 4 - 2 * w ^ 5 - 2 * w ^ 6 + 2 * w ^ 7 + 2 * w ^ 8 - 2 * w ^ 9 + 2 * w ^ 10 - 2 * w ^ 11 - 2 * w ^ 13 - 2 * z + 48 * z * w - 4 * z * w ^ 2 - 4 * z * w ^ 3 - 4 * z * w ^ 6 + 4 * z * w ^ 8 - 2 * z * w ^ 12 - 2 * z * w ^ 13 - 2 * z * w ^ 14 - 2 * z ^ 2 - 4 * z ^ 2 * w + 46 * z ^ 2 * w ^ 2 - 6 * z ^ 2 * w ^ 3 - 2 * z ^ 2 * w ^ 4 - 2 * z ^ 2 * w ^ 5 - 2 * z ^ 2 * w ^ 6 - 2 * z ^ 2 * w ^ 7 + 2 * z ^ 2 * w ^ 8 + 2 * z ^ 2 * w ^ 9 + 2 * z ^ 2 * w ^ 10 - 2 * z ^ 2 * w ^ 11 - 4 * z ^ 2 * w ^ 13 - 2 * z ^ 2 * w ^ 14 - 2 * z ^ 2 * w ^ 15 - 2 * z ^ 3 - 4 * z ^ 3 * w - 6 * z ^ 3 * w ^ 2 + 44 * z ^ 3 * w ^ 3 - 4 * z ^ 3 * w ^ 4 - 4 * z ^ 3 * w ^ 5 - 4 * z ^ 3 * w ^ 6 + 4 * z ^ 3 * w ^ 10 - 2 * z ^ 3 * w ^ 12 - 2 * z ^ 3 * w ^ 13 - 4 * z ^ 3 * w ^ 14 - 2 * z ^ 3 * w ^ 15 - 2 * z ^ 3 * w ^ 16 + 2 * z ^ 4 - 2 * z ^ 4 * w ^ 2 - 4 * z ^ 4 * w ^ 3 + 42 * z ^ 4 * w ^ 4 - 2 * z ^ 4 * w ^ 5 - 2 * z ^ 4 * w ^ 6 - 6 * z ^ 4 * w ^ 7 - 2 * z ^ 4 * w ^ 8 + 2 * z ^ 4 * w ^ 9 - 2 * z ^ 4 * w ^ 10 + 6 * z ^ 4 * w ^ 11 - 2 * z ^ 4 * w ^ 14 - 4 * z ^ 4 * w ^ 15 - 2 * z ^ 4 * w ^ 16 - 2 * z ^ 4 * w ^ 17 - 2 * z ^ 5 - 2 * z ^ 5 * w ^ 2 - 4 * z ^ 5 * w ^ 3 - 2 * z ^ 5 * w ^ 4 + 40 * z ^ 5 * w ^ 5 - 4 * z ^ 5 * w ^ 6 - 4 * z ^ 5 * w ^ 8 - 4 * z ^ 5 * w ^ 9 + 4 * z ^ 5 * w ^ 10 - 4 * z ^ 5 * w ^ 11 + 6 * z ^ 5 * w ^ 12 - 2 * z ^ 5 * w ^ 13 - 2 * z ^ 5 * w ^ 15 - 4 * z ^ 5 * w ^ 16 - 2 * z ^ 5 * w ^ 17 - 2 * z ^ 5 * w ^ 18 - 2 * z ^ 6 - 4 * z ^ 6 * w - 2 * z ^ 6 * w ^ 2 - 4 * z ^ 6 * w ^ 3 - 2 * z ^ 6 * w ^ 4 - 4 * z ^ 6 * w ^ 5 + 38 * z ^ 6 * w ^ 6 - 2 * z ^ 6 * w ^ 7 + 2 * z ^ 6 * w ^ 8 - 6 * z ^ 6 * w ^ 9 - 2 * z ^ 6 * w ^ 10 + 2 * z ^ 6 * w ^ 11 - 4 * z ^ 6 * w ^ 12 + 4 * z ^ 6 * w ^ 13 - 2 * z ^ 6 * w ^ 14 - 2 * z ^ 6 * w ^ 16 - 4 * z ^ 6 * w ^ 17 - 2 * z ^ 6 * w ^ 18 - 2 * z ^ 6 * w ^ 19 + 2 * z ^ 7 - 2 * z ^ 7 * w ^ 2 - 6 * z ^ 7 * w ^ 4 - 2 * z ^ 7 * w ^ 6 + 36 * z ^ 7 * w ^ 7 - 4 * z ^ 7 * w ^ 8 + 4 * z ^ 7 * w ^ 9 - 8 * z ^ 7 * w ^ 10 + 2 * z ^ 7 * w ^ 12 - 2 * z ^ 7 * w ^ 13 + 4 * z ^ 7 * w ^ 14 - 2 * z ^ 7 * w ^ 15 - 2 * z ^ 7 * w ^ 17 - 4 * z ^ 7 * w ^ 18 - 2 * z ^ 7 * w ^ 19 - 2 * z ^ 7 * w ^ 20 + 2 * z ^ 8 + 4 * z ^ 8 * w + 2 * z ^ 8 * w ^ 2 - 2 * z ^ 8 * w ^ 4 - 4 * z ^ 8 * w ^ 5 + 2 * z ^ 8 * w ^ 6 - 4 * z ^ 8 * w ^ 7 + 34 * z ^ 8 * w ^ 8 - 2 * z ^ 8 * w ^ 9 + 2 * z ^ 8 * w ^ 10 - 6 * z ^ 8 * w ^ 11 + 4 * z ^ 8 * w ^ 13 - 2 * z ^ 8 * w ^ 14 + 4 * z ^ 8 * w ^ 15 - 2 * z ^ 8 * w ^ 16 - 2 * z ^ 8 * w ^ 18 - 4 * z ^ 8 * w ^ 19 - 2 * z ^ 8 * w ^ 20 - 2 * z ^ 8 * w ^ 21 - 2 * z ^ 9 + 2 * z ^ 9 * w ^ 2 + 2 * z ^ 9 * w ^ 4 - 4 * z ^ 9 * w ^ 5 - 6 * z ^ 9 * w ^ 6 + 4 * z ^ 9 * w ^ 7 - 2 * z ^ 9 * w ^ 8 + 32 * z ^ 9 * w ^ 9 - 6 * z ^ 9 * w ^ 12 - 2 * z ^ 9 * w ^ 13 + 4 * z ^ 9 * w ^ 14 - 2 * z ^ 9 * w ^ 15 + 4 * z ^ 9 * w ^ 16 - 2 * z ^ 9 * w ^ 17 - 2 * z ^ 9 * w ^ 19 - 4 * z ^ 9 * w ^ 20 - 2 * z ^ 9 * w ^ 21 - 2 * z ^ 9 * w ^ 22 + 2 * z ^ 10 + 2 * z ^ 10 * w ^ 2 + 4 * z ^ 10 * w ^ 3 - 2 * z ^ 10 * w ^ 4 + 4 * z ^ 10 * w ^ 5 - 2 * z ^ 10 * w ^ 6 - 8 * z ^ 10 * w ^ 7 + 2 * z ^ 10 * w ^ 8 + 30 * z ^ 10 * w ^ 10 + 2 * z ^ 10 * w ^ 11 - 4 * z ^ 10 * w ^ 13 - 2 * z ^ 10 * w ^ 14 + 4 * z ^ 10 * w ^ 15 - 2 * z ^ 10 * w ^ 16 + 4 * z ^ 10 * w ^ 17 - 2 * z ^ 10 * w ^ 18 - 2 * z ^ 10 * w ^ 20 - 4 * z ^ 10 * w ^ 21 - 2 * z ^ 10 * w ^ 22 - 2 * z ^ 10 * w ^ 23 - 2 * z ^ 11 - 2 * z ^ 11 * w ^ 2 + 6 * z ^ 11 * w ^ 4 - 4 * z ^ 11 * w ^ 5 + 2 * z ^ 11 * w ^ 6 - 6 * z ^ 11 * w ^ 8 + 2 * z ^ 11 * w ^ 10 + 28 * z ^ 11 * w ^ 11 + 2 * z ^ 11 * w ^ 12 - 2 * z ^ 11 * w ^ 13 - 4 * z ^ 11 * w ^ 14 - 2 * z ^ 11 * w ^ 15 + 4 * z ^ 11 * w ^ 16 - 2 * z ^ 11 * w ^ 17 + 4 * z ^ 11 * w ^ 18 - 2 * z ^ 11 * w ^ 19 - 2 * z ^ 11 * w ^ 21 - 4 * z ^ 11 * w ^ 22 - 2 * z ^ 11 * w ^ 23 - 2 * z ^ 11 * w ^ 24 - 2 * z ^ 12 * w - 2 * z ^ 12 * w ^ 3 + 6 * z ^ 12 * w ^ 5 - 4 * z ^ 12 * w ^ 6 + 2 * z ^ 12 * w ^ 7 - 6 * z ^ 12 * w ^ 9 + 2 * z ^ 12 * w ^ 11 + 26 * z ^ 12 * w ^ 12 + 2 * z ^ 12 * w ^ 13 - 4 * z ^ 12 * w ^ 14 - 6 * z ^ 12 * w ^ 15 + 2 * z ^ 12 * w ^ 17 + 6 * z ^ 12 * w ^ 19 - 2 * z ^ 12 * w ^ 21 - 4 * z ^ 12 * w ^ 22 - 2 * z ^ 12 * w ^ 23 - 2 * z ^ 13 - 2 * z ^ 13 * w - 4 * z ^ 13 * w ^ 2 - 2 * z ^ 13 * w ^ 3 - 2 * z ^ 13 * w ^ 5 + 4 * z ^ 13 * w ^ 6 - 2 * z ^ 13 * w ^ 7 + 4 * z ^ 13 * w ^ 8 - 2 * z ^ 13 * w ^ 9 - 4 * z ^ 13 * w ^ 10 - 2 * z ^ 13 * w ^ 11 + 2 * z ^ 13 * w ^ 12 + 24 * z ^ 13 * w ^ 13 + 2 * z ^ 13 * w ^ 14 - 4 * z ^ 13 * w ^ 15 - 6 * z ^ 13 * w ^ 16 + 2 * z ^ 13 * w ^ 18 + 6 * z ^ 13 * w ^ 20 - 2 * z ^ 13 * w ^ 22 - 4 * z ^ 13 * w ^ 23 - 2 * z ^ 13 * w ^ 24 - 2 * z ^ 14 * w - 2 * z ^ 14 * w ^ 2 - 4 * z ^ 14 * w ^ 3 - 2 * z ^ 14 * w ^ 4 - 2 * z ^ 14 * w ^ 6 + 4 * z ^ 14 * w ^ 7 - 2 * z ^ 14 * w ^ 8 + 4 * z ^ 14 * w ^ 9 - 2 * z ^ 14 * w ^ 10 - 4 * z ^ 14 * w ^ 11 - 4 * z ^ 14 * w ^ 12 + 2 * z ^ 14 * w ^ 13 + 22 * z ^ 14 * w ^ 14 - 2 * z ^ 14 * w ^ 16 - 8 * z ^ 14 * w ^ 17 + 2 * z ^ 14 * w ^ 18 + 4 * z ^ 14 * w ^ 19 + 2 * z ^ 14 * w ^ 20 + 4 * z ^ 14 * w ^ 21 - 2 * z ^ 14 * w ^ 22 - 2 * z ^ 14 * w ^ 24 - 2 * z ^ 15 * w ^ 2 - 2 * z ^ 15 * w ^ 3 - 4 * z ^ 15 * w ^ 4 - 2 * z ^ 15 * w ^ 5 - 2 * z ^ 15 * w ^ 7 + 4 * z ^ 15 * w ^ 8 - 2 * z ^ 15 * w ^ 9 + 4 * z ^ 15 * w ^ 10 - 2 * z ^ 15 * w ^ 11 - 6 * z ^ 15 * w ^ 12 - 4 * z ^ 15 * w ^ 13 + 20 * z ^ 15 * w ^ 15 + 2 * z ^ 15 * w ^ 16 - 4 * z ^ 15 * w ^ 17 - 6 * z ^ 15 * w ^ 18 + 4 * z ^ 15 * w ^ 19 + 6 * z ^ 15 * w ^ 20 + 2 * z ^ 15 * w ^ 22 + 2 * z ^ 15 * w ^ 24 - 2 * z ^ 16 * w ^ 3 - 2 * z ^ 16 * w ^ 4 - 4 * z ^ 16 * w ^ 5 - 2 * z ^ 16 * w ^ 6 - 2 * z ^ 16 * w ^ 8 + 4 * z ^ 16 * w ^ 9 - 2 * z ^ 16 * w ^ 10 + 4 * z ^ 16 * w ^ 11 - 6 * z ^ 16 * w ^ 13 - 2 * z ^ 16 * w ^ 14 + 2 * z ^ 16 * w ^ 15 + 18 * z ^ 16 * w ^ 16 + 4 * z ^ 16 * w ^ 17 - 6 * z ^ 16 * w ^ 18 - 8 * z ^ 16 * w ^ 19 + 2 * z ^ 16 * w ^ 20 + 8 * z ^ 16 * w ^ 21 + 2 * z ^ 16 * w ^ 22 - 2 * z ^ 16 * w ^ 24 - 2 * z ^ 17 * w ^ 4 - 2 * z ^ 17 * w ^ 5 - 4 * z ^ 17 * w ^ 6 - 2 * z ^ 17 * w ^ 7 - 2 * z ^ 17 * w ^ 9 + 4 * z ^ 17 * w ^ 10 - 2 * z ^ 17 * w ^ 11 + 2 * z ^ 17 * w ^ 12 - 8 * z ^ 17 * w ^ 14 - 4 * z ^ 17 * w ^ 15 + 4 * z ^ 17 * w ^ 16 + 16 * z ^ 17 * w ^ 17 + 6 * z ^ 17 * w ^ 18 - 4 * z ^ 17 * w ^ 19 - 6 * z ^ 17 * w ^ 20 + 6 * z ^ 17 * w ^ 22 + 4 * z ^ 17 * w ^ 23 + 2 * z ^ 17 * w ^ 24 - 2 * z ^ 18 * w ^ 5 - 2 * z ^ 18 * w ^ 6 - 4 * z ^ 18 * w ^ 7 - 2 * z ^ 18 * w ^ 8 - 2 * z ^ 18 * w ^ 10 + 4 * z ^ 18 * w ^ 11 + 2 * z ^ 18 * w ^ 13 + 2 * z ^ 18 * w ^ 14 - 6 * z ^ 18 * w ^ 15 - 6 * z ^ 18 * w ^ 16 + 6 * z ^ 18 * w ^ 17 + 14 * z ^ 18 * w ^ 18 + 4 * z ^ 18 * w ^ 19 - 6 * z ^ 18 * w ^ 20 - 4 * z ^ 18 * w ^ 21 + 2 * z ^ 18 * w ^ 22 + 4 * z ^ 18 * w ^ 23 + 2 * z ^ 18 * w ^ 24 - 2 * z ^ 19 * w ^ 6 - 2 * z ^ 19 * w ^ 7 - 4 * z ^ 19 * w ^ 8 - 2 * z ^ 19 * w ^ 9 - 2 * z ^ 19 * w ^ 11 + 6 * z ^ 19 * w ^ 12 + 4 * z ^ 19 * w ^ 14 + 4 * z ^ 19 * w ^ 15 - 8 * z ^ 19 * w ^ 16 - 4 * z ^ 19 * w ^ 17 + 4 * z ^ 19 * w ^ 18 + 12 * z ^ 19 * w ^ 19 + 2 * z ^ 19 * w ^ 20 - 4 * z ^ 19 * w ^ 21 - 2 * z ^ 19 * w ^ 22 + 2 * z ^ 19 * w ^ 24 - 2 * z ^ 20 * w ^ 7 - 2 * z ^ 20 * w ^ 8 - 4 * z ^ 20 * w ^ 9 - 2 * z ^ 20 * w ^ 10 + 6 * z ^ 20 * w ^ 13 + 2 * z ^ 20 * w ^ 14 + 6 * z ^ 20 * w ^ 15 + 2 * z ^ 20 * w ^ 16 - 6 * z ^ 20 * w ^ 17 - 6 * z ^ 20 * w ^ 18 + 2 * z ^ 20 * w ^ 19 + 10 * z ^ 20 * w ^ 20 + 4 * z ^ 20 * w ^ 21 - 2 * z ^ 20 * w ^ 22 - 4 * z ^ 20 * w ^ 23 - 2 * z ^ 20 * w ^ 24 - 2 * z ^ 21 * w ^ 8 - 2 * z ^ 21 * w ^ 9 - 4 * z ^ 21 * w ^ 10 - 2 * z ^ 21 * w ^ 11 - 2 * z ^ 21 * w ^ 12 + 4 * z ^ 21 * w ^ 14 + 8 * z ^ 21 * w ^ 16 - 4 * z ^ 21 * w ^ 18 - 4 * z ^ 21 * w ^ 19 + 4 * z ^ 21 * w ^ 20 + 8 * z ^ 21 * w ^ 21 + 2 * z ^ 21 * w ^ 22 - 2 * z ^ 21 * w ^ 24 - 2 * z ^ 22 * w ^ 9 - 2 * z ^ 22 * w ^ 10 - 4 * z ^ 22 * w ^ 11 - 4 * z ^ 22 * w ^ 12 - 2 * z ^ 22 * w ^ 13 - 2 * z ^ 22 * w ^ 14 + 2 * z ^ 22 * w ^ 15 + 2 * z ^ 22 * w ^ 16 + 6 * z ^ 22 * w ^ 17 + 2 * z ^ 22 * w ^ 18 - 2 * z ^ 22 * w ^ 19 - 2 * z ^ 22 * w ^ 20 + 2 * z ^ 22 * w ^ 21 + 6 * z ^ 22 * w ^ 22 + 4 * z ^ 22 * w ^ 23 + 2 * z ^ 22 * w ^ 24 - 2 * z ^ 23 * w ^ 10 - 2 * z ^ 23 * w ^ 11 - 2 * z ^ 23 * w ^ 12 - 4 * z ^ 23 * w ^ 13 + 4 * z ^ 23 * w ^ 17 + 4 * z ^ 23 * w ^ 18 - 4 * z ^ 23 * w ^ 20 + 4 * z ^ 23 * w ^ 22 + 4 * z ^ 23 * w ^ 23 + 2 * z ^ 23 * w ^ 24 - 2 * z ^ 24 * w ^ 11 - 2 * z ^ 24 * w ^ 13 - 2 * z ^ 24 * w ^ 14 + 2 * z ^ 24 * w ^ 15 - 2 * z ^ 24 * w ^ 16 + 2 * z ^ 24 * w ^ 17 + 2 * z ^ 24 * w ^ 18 + 2 * z ^ 24 * w ^ 19 - 2 * z ^ 24 * w ^ 20 - 2 * z ^ 24 * w ^ 21 + 2 * z ^ 24 * w ^ 22 + 2 * z ^ 24 * w ^ 23 + 2 * z ^ 24 * w ^ 24) * hw

theorem inG_two_le {n : ℕ} (h : InG n) : 2 ≤ n := by
  obtain ⟨h1, a, rfl | rfl | rfl | rfl⟩ := h
  · have := Nat.one_le_two_pow (n := a); omega
  all_goals have := Nat.one_le_two_pow (n := a); omega

theorem golayLen_one : GolayLen 1 :=
  ⟨![1], ![1], by unfold IsSignSeq; decide, by unfold IsSignSeq; decide, fun z _ => by
    simp [peval]; norm_num⟩

theorem golayLen_double {n : ℕ} (h : GolayLen n) : GolayLen (2 * n) := by
  obtain ⟨P, Q, hP, hQ, hG⟩ := h
  rw [two_mul]
  obtain ⟨s1, s2⟩ := isSignSeq_double hP hQ
  exact ⟨_, _, s1, s2, isGolay_double hG⟩

theorem golayLen_pow_mul {g : ℕ} (h : GolayLen g) (a : ℕ) : GolayLen (2 ^ a * g) := by
  induction a with
  | zero => simpa using h
  | succ a ih => rw [pow_succ, mul_comm (2 ^ a) 2, mul_assoc]; exact golayLen_double ih

theorem golayLen_10 : GolayLen 10 :=
  ⟨_, _, by unfold IsSignSeq golayA10; decide, by unfold IsSignSeq golayB10; decide, isGolay_10⟩

theorem golayLen_26 : GolayLen 26 :=
  ⟨_, _, by unfold IsSignSeq golayA26; decide, by unfold IsSignSeq golayB26; decide, isGolay_26⟩

/-- The pair of length `100` that Lemma `lem:square` produces from `(A₁₀, B₁₀)`. -/
theorem golayLen_100 : GolayLen 100 := by
  have hA : IsSignSeq golayA10 := by unfold IsSignSeq golayA10; decide
  have hB : IsSignSeq golayB10 := by unfold IsSignSeq golayB10; decide
  exact ⟨sqP golayA10 golayB10, sqQ golayA10 golayB10, isSignSeq_sqP hA hB, isSignSeq_sqQ hA hB,
    isGolay_sq hA hB isGolay_10⟩

/-- "There is a Golay pair of every length in `𝒢`." -/
theorem golayLen_of_inG {n : ℕ} (h : InG n) : GolayLen n := by
  obtain ⟨-, a, rfl | rfl | rfl | rfl⟩ := h
  · simpa using golayLen_pow_mul golayLen_one a
  · exact golayLen_pow_mul golayLen_10 a
  · exact golayLen_pow_mul golayLen_26 a
  · exact golayLen_pow_mul golayLen_100 a

theorem tailPair_seed {r : ℕ} (hr : r ∈ seedLengths) : TailPair r (4 * r) := by
  simp only [seedLengths, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2, h3, h4, h5⟩ := seedPair_2; exact ⟨_, _, h1, h2, h3, h4, by exact_mod_cast h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := seedPair_6; exact ⟨_, _, h1, h2, h3, h4, by exact_mod_cast h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := seedPair_10; exact ⟨_, _, h1, h2, h3, h4, by exact_mod_cast h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := seedPair_14; exact ⟨_, _, h1, h2, h3, h4, by exact_mod_cast h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := seedPair_18; exact ⟨_, _, h1, h2, h3, h4, by exact_mod_cast h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := seedPair_22; exact ⟨_, _, h1, h2, h3, h4, by exact_mod_cast h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := seedPair_26; exact ⟨_, _, h1, h2, h3, h4, by exact_mod_cast h5⟩

/-- **Lemma `lem:tails`.** For every even `r ≥ 0` there are sign sequences `R`, `T` of length `r`
with `R(1) = T(1) = 0` and `|R(z)|² + |T(z)|² ≤ 6r` for all `|z| = 1`. -/
theorem lem_tails (r : ℕ) (hr : Even r) :
    ∃ R T : Fin r → ℤ, IsSignSeq R ∧ IsSignSeq T ∧ peval R 1 = 0 ∧ peval T 1 = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 ≤ 6 * r :=
  tails_induction TailPair (fun _ _ _ h hB => tailPair_mono h hB) tailPair_zero
    (fun _ hr => tailPair_seed hr) (fun _ _ _ h => tailPair_double h)
    (fun _ _ _ h => tailPair_append h)
    (fun g hg => tailPair_delete (golayLen_of_inG hg)
      (by have := inG_two_le hg; omega))
    (fun m t B hm _ h => tailPair_interleave (golayLen_of_inG hm) h) r hr

end SignCond
