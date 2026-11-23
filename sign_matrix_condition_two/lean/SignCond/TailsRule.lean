import SignCond.TailsRuleAux

/-!
# Tails by one recursion (paper: paragraph "Tails", eqs. `tail`, `tailrule`, `tailrec`, `tailD`,
`tailD2`, and Lemma `lem:tails`)

Paper: "We define sign sequences `Φ_r` and `Ψ_r` of every even length `r ≥ 0` by one recursion.
Let `Φ_0` and `Ψ_0` be empty, and let `Φ_2 = Ψ_2 = (1,-1)`. For `r ≥ 4`, let `η ∈ {0,1}` with
`η ≡ r/2 (mod 2)`, so that `w = r/2 - η` is even, let `g` be the largest element of `𝒢` with
`g ≤ w`, let `m = w - g`, and let `(P,Q)` be the Golay pair of length `g`. We put
`Φ_r = P^∓ | Φ_m^± | (-1,1)^η`, `Ψ_r = Q^∓ | Ψ_m^± | (1,-1)^η` (eq. `tailrule`), where the last
block is omitted when `η = 0`."

* Parameters: `tEta r = η`, `tW r = w`, `tG r = g`, `tM r = m`.
* `tailRaw r` is the pair `(Φ_r, Ψ_r)` together with its length; `tailPhi r`, `tailPsi r` are its
  components (of length `(tailRaw r).1`, which is `r` for even `r`: `tailRaw_fst`), and
  `tailPhi' r`, `tailPsi' r : Fin r → ℤ` the same sequences typed at length `r`.
* `TailCond400` is eq. `tail` (with the bound `6r + 400`).
* `tailE r z = |Φ_r(z)|² + |Ψ_r(z)|²`; "`M_r ≤ B`" is written `∀ z, ‖z‖ = 1 → tailE r z ≤ B`.
* `tail_rec` is eq. `tailrec`, `tail_recD` is eq. `tailD`; `tailE_six` is `M_6 ≤ 40`;
  `tails_first_bound` is `M_r ≤ 15r/2`; `tails_second_bound` is `M_r - 6r ≤ 400`;
  `lem_tails_rule` is Lemma `lem:tails`.
-/

open Complex

namespace SignCond

/-! ### The parameters of the recursion -/

/-- `η ∈ {0, 1}` with `η ≡ r/2 (mod 2)`. -/
def tEta (r : ℕ) : ℕ := r / 2 % 2

/-- `w = r/2 - η`. -/
def tW (r : ℕ) : ℕ := r / 2 - tEta r

open Classical in
/-- `g`, the largest element of `𝒢` with `g ≤ w`. -/
noncomputable def tG (r : ℕ) : ℕ := Nat.findGreatest InG (tW r)

/-- `m = w - g`. -/
noncomputable def tM (r : ℕ) : ℕ := tW r - tG r

/-- "`m < r`". -/
theorem tM_lt {r : ℕ} (hr : 4 ≤ r) : tM r < r := by
  unfold tM tW tEta; omega

theorem tG_spec {r : ℕ} (h : 2 ≤ tW r) : IsMaxG (tW r) (tG r) := by
  classical
  unfold tG
  exact ⟨Nat.findGreatest_spec (P := InG) h inG_two, Nat.findGreatest_le _,
    fun n hn hnw => Nat.le_findGreatest hnw hn⟩

/-- For `r ≥ 4`: `g` is the largest element of `𝒢` below `w`, `w` is even, `η ∈ {0,1}`,
`r/2 = g + m + η` ("the lengths add up to `2g + 2m + 2η = r`"), and `m` is even. -/
theorem tail_params {r : ℕ} (hr : 4 ≤ r) :
    IsMaxG (tW r) (tG r) ∧ Even (tW r) ∧ (tEta r = 0 ∨ tEta r = 1) ∧
      r / 2 = tG r + tM r + tEta r ∧ Even (tM r) := by
  have h2 : 2 ≤ tW r := by unfold tW tEta; omega
  have hmax := tG_spec h2
  have hle : tG r ≤ tW r := hmax.2.1
  have hge := Nat.even_iff.mp (inG_even hmax.1)
  have hwe : tW r % 2 = 0 := by unfold tW tEta; omega
  have hη : tEta r = 0 ∨ tEta r = 1 := by
    show r / 2 % 2 = 0 ∨ r / 2 % 2 = 1
    omega
  refine ⟨hmax, Nat.even_iff.mpr hwe, hη, ?_, ?_⟩
  · unfold tM; unfold tW at hle ⊢; omega
  · rw [Nat.even_iff]; unfold tM; omega

/-- The facts about `m = w - g` (see `maxG_gap`). -/
theorem tail_gap {r : ℕ} (hr : 4 ≤ r) :
    (tG r < 32 → tM r ≤ 4) ∧ (tG r = 2 → tM r = 0) ∧ (tG r = 4 → tM r ≤ 2) ∧
      (tG r < 64 → tM r ≤ 10) ∧ (32 ≤ tG r → 4 * tM r ≤ tG r) ∧
      (64 ≤ tG r → 4 * tM r + 8 ≤ tG r) := by
  obtain ⟨hmax, hw, -⟩ := tail_params hr
  exact maxG_gap hw hmax

/-! ### The sequences `Φ_r`, `Ψ_r` (eq. `tailrule`) -/

/-- The pair `(Φ_r, Ψ_r)` with its length: empty for `r < 2`, `((1,-1), (1,-1))` for `r = 2`
(also for `r = 3`, never used), and eq. `tailrule` for `r ≥ 4`. -/
noncomputable def tailRaw (r : ℕ) : TPair :=
  if r < 2 then ⟨0, (Fin.elim0, Fin.elim0)⟩
  else if _h : r < 4 then ⟨2, (onePair, onePair)⟩
  else tailStep (tEta r) (golayG (tG r)).1 (golayG (tG r)).2 (tailRaw (tM r))
termination_by r
decreasing_by exact tM_lt (by omega)

/-- `Φ_r` (of length `(tailRaw r).1 = r` for even `r`). -/
noncomputable def tailPhi (r : ℕ) : Fin (tailRaw r).1 → ℤ := (tailRaw r).2.1

/-- `Ψ_r` (of length `(tailRaw r).1 = r` for even `r`). -/
noncomputable def tailPsi (r : ℕ) : Fin (tailRaw r).1 → ℤ := (tailRaw r).2.2

/-- `Φ_r` typed at length `r` (coefficients of `tailPhi r`; equal to it for even `r`). -/
noncomputable def tailPhi' (r : ℕ) : Fin r → ℤ := fun i => coeff (tailPhi r) i

/-- `Ψ_r` typed at length `r` (coefficients of `tailPsi r`; equal to it for even `r`). -/
noncomputable def tailPsi' (r : ℕ) : Fin r → ℤ := fun i => coeff (tailPsi r) i

/-- Paper, eq. `tail`: `Φ(1) = Ψ(1) = 0` and `|Φ(z)|² + |Ψ(z)|² ≤ 6r + 400` for all `|z| = 1`. -/
def TailCond400 {r : ℕ} (R T : Fin r → ℤ) : Prop :=
  peval R 1 = 0 ∧ peval T 1 = 0 ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 ≤ 6 * (r : ℝ) + 400

/-- `|Φ_r(z)|² + |Ψ_r(z)|²`; the paper's `M_r` is its maximum over `|z| = 1`. -/
noncomputable def tailE (r : ℕ) (z : ℂ) : ℝ :=
  ‖peval (tailPhi r) z‖ ^ 2 + ‖peval (tailPsi r) z‖ ^ 2

theorem tailRaw_of_lt_two {r : ℕ} (h : r < 2) : tailRaw r = ⟨0, (Fin.elim0, Fin.elim0)⟩ := by
  rw [tailRaw, if_pos h]

theorem tailRaw_of_lt_four {r : ℕ} (h1 : 2 ≤ r) (h2 : r < 4) :
    tailRaw r = ⟨2, (onePair, onePair)⟩ := by
  rw [tailRaw, if_neg (by omega), dif_pos h2]

theorem tailRaw_of_four_le {r : ℕ} (h : 4 ≤ r) :
    tailRaw r = tailStep (tEta r) (golayG (tG r)).1 (golayG (tG r)).2 (tailRaw (tM r)) := by
  conv_lhs => rw [tailRaw]
  rw [if_neg (by omega), dif_neg (by omega)]

/-- "The lengths add up to `2g + 2m + 2η = r`": `Φ_r`, `Ψ_r` have length `r` for even `r`. -/
theorem tailRaw_fst (r : ℕ) (hr : Even r) : (tailRaw r).1 = r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  have hre := Nat.even_iff.mp hr
  rcases lt_or_ge r 4 with h4 | h4
  · rcases lt_or_ge r 2 with h2 | h2
    · rw [tailRaw_of_lt_two h2]; dsimp only; omega
    · rw [tailRaw_of_lt_four h2 h4]; dsimp only; omega
  · obtain ⟨-, -, hη, hsum, hme⟩ := tail_params h4
    rw [tailRaw_of_four_le h4, tailStep_fst _ _ _ hη, ih _ (tM_lt h4) hme]
    omega

/-- `Φ_r`, `Ψ_r` are sign sequences with `Φ_r(1) = Ψ_r(1) = 0` ("each block in eq. `tailrule` has
zero sum, so `Φ_r(1) = Ψ_r(1) = 0` by induction"). -/
theorem tailRaw_sign_sum (r : ℕ) :
    IsSignSeq (tailRaw r).2.1 ∧ IsSignSeq (tailRaw r).2.2 ∧ peval (tailRaw r).2.1 1 = 0 ∧
      peval (tailRaw r).2.2 1 = 0 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  rcases lt_or_ge r 4 with h4 | h4
  · rcases lt_or_ge r 2 with h2 | h2
    · rw [tailRaw_of_lt_two h2]
      exact ⟨fun v => v.elim0, fun v => v.elim0, by simp [peval], by simp [peval]⟩
    · rw [tailRaw_of_lt_four h2 h4]
      exact ⟨isSignSeq_onePair, isSignSeq_onePair, by simp [peval_onePair],
        by simp [peval_onePair]⟩
  · obtain ⟨hmax, -, -, -, -⟩ := tail_params h4
    obtain ⟨s1, s2, e1, e2⟩ := ih _ (tM_lt h4)
    obtain ⟨hP, hQ, -⟩ := isGolayPair_golayG _ (Or.inl hmax.1)
    rw [tailRaw_of_four_le h4]
    obtain ⟨t1, t2⟩ := tailStep_sign (η := tEta r) hP hQ s1 s2
    obtain ⟨u1, u2⟩ := tailStep_sum (η := tEta r) (golayG (tG r)).1 (golayG (tG r)).2 e1 e2
    exact ⟨t1, t2, u1, u2⟩

/-! ### The recursive bound (eq. `tailrec`) and the small cases -/

/-- Eq. `tailrec`: for `r ≥ 4`, `M_r ≤ 8g + 8η + 16η√g + 4M_m` (with any bound `B` for `M_m`). -/
theorem tail_rec {r : ℕ} (hr : 4 ≤ r) {B : ℝ} (hB : ∀ z : ℂ, ‖z‖ = 1 → tailE (tM r) z ≤ B)
    {z : ℂ} (hz : ‖z‖ = 1) :
    tailE r z ≤ 8 * (tG r : ℝ) + 8 * (tEta r : ℝ) + 16 * (tEta r : ℝ) * Real.sqrt (tG r) +
      4 * B := by
  obtain ⟨hmax, -, hη, -⟩ := tail_params hr
  unfold tailE tailPhi tailPsi
  rw [tailRaw_of_four_le hr]
  exact tailStep_energy (t := tailRaw (tM r)) hη (isGolayPair_golayG _ (Or.inl hmax.1)).2.2
    (fun z hz => hB z hz) hz

/-- Eq. `tailD`: with `D_r = M_r - 6r`, for even `r ≥ 4`,
`D_r ≤ -4g + 12m + η(16√g - 4) + 4D_m`. -/
theorem tail_recD {r : ℕ} (hr : 4 ≤ r) (hre : Even r) {D : ℝ}
    (hD : ∀ z : ℂ, ‖z‖ = 1 → tailE (tM r) z - 6 * (tM r : ℝ) ≤ D) {z : ℂ} (hz : ‖z‖ = 1) :
    tailE r z - 6 * (r : ℝ) ≤
      -4 * (tG r : ℝ) + 12 * (tM r : ℝ) + (tEta r : ℝ) * (16 * Real.sqrt (tG r) - 4) + 4 * D := by
  obtain ⟨-, -, -, hsum, -⟩ := tail_params hr
  have hcast : (r : ℝ) = 2 * (tG r : ℝ) + 2 * (tM r : ℝ) + 2 * (tEta r : ℝ) := by
    have := Nat.even_iff.mp hre
    have : r = 2 * tG r + 2 * tM r + 2 * tEta r := by omega
    exact_mod_cast this
  have := tail_rec hr (B := 6 * (tM r : ℝ) + D) (fun z hz => by linarith [hD z hz]) hz
  rw [hcast]
  linarith

theorem tailE_zero (z : ℂ) : tailE 0 z = 0 := by
  unfold tailE tailPhi tailPsi
  rw [tailRaw_of_lt_two (by norm_num)]
  simp [peval]

/-- `M_2 ≤ 8`, since `Φ_2(z) = Ψ_2(z) = 1 - z`. -/
theorem tailE_two {r : ℕ} (h1 : 2 ≤ r) (h2 : r < 4) {z : ℂ} (hz : ‖z‖ = 1) : tailE r z ≤ 8 := by
  unfold tailE tailPhi tailPsi
  rw [tailRaw_of_lt_four h1 h2]
  dsimp only
  rw [peval_onePair]
  have := norm_one_sub_pow_sq_le hz 1
  rw [pow_one] at this
  linarith

theorem tW_four : tW 4 = 2 := by decide

theorem tW_six : tW 6 = 2 := by decide

theorem tEta_four : tEta 4 = 0 := by decide

theorem tEta_six : tEta 6 = 1 := by decide

theorem tG_four : tG 4 = 2 := by
  obtain ⟨hmax, -⟩ := tail_params (r := 4) le_rfl
  have h1 := inG_two_le hmax.1
  have h2 := hmax.2.1
  rw [tW_four] at h2
  omega

theorem tG_six : tG 6 = 2 := by
  obtain ⟨hmax, -⟩ := tail_params (r := 6) (by norm_num)
  have h1 := inG_two_le hmax.1
  have h2 := hmax.2.1
  rw [tW_six] at h2
  omega

theorem tM_four : tM 4 = 0 := by unfold tM; rw [tW_four, tG_four]

theorem tM_six : tM 6 = 0 := by unfold tM; rw [tW_six, tG_six]

/-- "`M_4 ≤ 16` by eq. `tailrec`." -/
theorem tailE_four {z : ℂ} (hz : ‖z‖ = 1) : tailE 4 z ≤ 16 := by
  have := tail_rec (r := 4) le_rfl (B := 0) (fun z _ => by rw [tM_four, tailE_zero]) hz
  rw [tG_four, tEta_four] at this
  norm_num at this
  linarith

/-- `M_6 ≤ 40`: "There `g = 2`, `m = 0`, and `η = 1`, so `Φ_6(z) = (1-z)(1+z²-z⁴)` and
`Ψ_6(z) = (1-z)(1-z²+z⁴)`, and for `z = e^{iθ}`,
`|Φ_6(z)|² + |Ψ_6(z)|² = |1-z|²(6 - 4cos 2θ) ≤ 40`." (Here: `|1+u|² + |1-u|² = 2 + 2|u|²` with
`u = z²(1-z²)`, `|1-z²|² ≤ 4` and `|1-z|² ≤ 4`.) -/
theorem tailE_six {z : ℂ} (hz : ‖z‖ = 1) : tailE 6 z ≤ 40 := by
  have h0fst : (tailRaw 0).1 = 0 := by rw [tailRaw_of_lt_two (by norm_num)]
  have h0p : ∀ w, peval (tailRaw 0).2.1 w = 0 := by
    intro w; rw [tailRaw_of_lt_two (by norm_num)]; simp [peval]
  have h0q : ∀ w, peval (tailRaw 0).2.2 w = 0 := by
    intro w; rw [tailRaw_of_lt_two (by norm_num)]; simp [peval]
  have key : ∀ A C : ℂ, A = (1 - z) * (1 + z ^ 2 * (1 - z ^ 2)) →
      C = (1 - z) * (1 - z ^ 2 * (1 - z ^ 2)) → ‖A‖ ^ 2 + ‖C‖ ^ 2 ≤ 40 := by
    rintro A C rfl rfl
    have hz2 : ‖z ^ 2‖ = 1 := by rw [norm_pow, hz, one_pow]
    rw [norm_mul, norm_mul, mul_pow, mul_pow, ← mul_add, doubling_identity 1 (1 - z ^ 2) _ hz2,
      norm_one]
    have a := norm_one_sub_pow_sq_le hz 1
    have b := norm_one_sub_pow_sq_le hz 2
    rw [pow_one] at a
    have := mul_le_mul a (show 2 * (1 : ℝ) ^ 2 + 2 * ‖1 - z ^ 2‖ ^ 2 ≤ 10 by linarith)
      (by positivity) (by norm_num)
    linarith
  unfold tailE tailPhi tailPsi
  rw [tailRaw_of_four_le (by norm_num), tEta_six, peval_tailStep_one, peval_tailStep_one']
  apply key
  · rw [tG_six, tM_six, h0p, h0fst, (golayG_two_peval _).1]; ring
  · rw [tG_six, tM_six, h0q, h0fst, (golayG_two_peval _).2]; ring

/-- "`M_m ≤ 4m` for `m ≤ 4`." -/
theorem tailE_small {m : ℕ} (hm : Even m) (h4 : m ≤ 4) :
    ∀ z : ℂ, ‖z‖ = 1 → tailE m z ≤ 4 * (m : ℝ) := by
  intro z hz
  have := Nat.even_iff.mp hm
  obtain rfl | rfl | rfl : m = 0 ∨ m = 2 ∨ m = 4 := by omega
  · rw [tailE_zero]; norm_num
  · have := tailE_two (le_refl 2) (by norm_num) hz; push_cast; linarith
  · have := tailE_four hz; push_cast; linarith

/-! ### The two bounds -/

/-- **First bound.** `M_r ≤ 15r/2` for every even `r`. -/
theorem tails_first_bound (r : ℕ) (hr : Even r) :
    ∀ z : ℂ, ‖z‖ = 1 → tailE r z ≤ 15 * (r : ℝ) / 2 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro z hz
  have hre := Nat.even_iff.mp hr
  rcases lt_or_ge r 4 with h4 | h4
  · obtain rfl | rfl : r = 0 ∨ r = 2 := by omega
    · rw [tailE_zero]; norm_num
    · have := tailE_two (le_refl 2) (by norm_num) hz; push_cast; linarith
  by_cases h6 : r = 6
  · subst h6; have := tailE_six hz; push_cast; linarith
  obtain ⟨hmax, -, hη, hsum, hme⟩ := tail_params h4
  obtain ⟨g1, g2, g4, -, g32, -⟩ := tail_gap h4
  have hg2 := inG_two_le hmax.1
  have hge := Nat.even_iff.mp (inG_even hmax.1)
  have hcast : (r : ℝ) = 2 * (tG r : ℝ) + 2 * (tM r : ℝ) + 2 * (tEta r : ℝ) := by
    have : r = 2 * tG r + 2 * tM r + 2 * tEta r := by omega
    exact_mod_cast this
  have hηR : (tEta r : ℝ) = 0 ∨ (tEta r : ℝ) = 1 := by rcases hη with h | h <;> simp [h]
  rcases lt_or_ge (tG r) 32 with hg32 | hg32
  · have hm4 := g1 hg32
    refine (tail_rec h4 (tailE_small hme hm4) hz).trans ?_
    rw [hcast]
    refine first_scalar_small hηR (by positivity) (by exact_mod_cast hm4)
      (by exact_mod_cast hg2) fun hη1 => ?_
    have hη1' : tEta r = 1 := by exact_mod_cast hη1
    have hg4 : 4 ≤ tG r := by
      by_contra hc
      have hg2' : tG r = 2 := by omega
      have := g2 hg2'
      omega
    rcases lt_or_ge (tG r) 8 with hg8 | hg8
    · left
      have h4' : tG r = 4 := by
        rcases inG_lt_32 hmax.1 hg32 with h | h | h | h | h | h | h <;> omega
      exact ⟨by exact_mod_cast h4', by exact_mod_cast g4 h4'⟩
    · right; exact_mod_cast hg8
  · have hm := g32 hg32
    refine (tail_rec h4 (ih (tM r) (tM_lt h4) hme) hz).trans ?_
    rw [hcast]
    exact first_scalar_large hηR (by positivity) (by exact_mod_cast hg32) (by exact_mod_cast hm)

/-- **Second bound.** `M_r - 6r ≤ 400` for every even `r` (eq. `tailD` applied twice). -/
theorem tails_second_bound (r : ℕ) (hr : Even r) :
    ∀ z : ℂ, ‖z‖ = 1 → tailE r z - 6 * (r : ℝ) ≤ 400 := by
  intro z hz
  suffices h : tailE r z ≤ 6 * (r : ℝ) + 400 by linarith
  have hre := Nat.even_iff.mp hr
  rcases lt_or_ge r 4 with h4 | h4
  · obtain rfl | rfl : r = 0 ∨ r = 2 := by omega
    · rw [tailE_zero]; norm_num
    · have := tailE_two (le_refl 2) (by norm_num) hz; push_cast; linarith
  obtain ⟨hmax, -, hη, hsum, hme⟩ := tail_params h4
  obtain ⟨-, -, -, g64, -, g64'⟩ := tail_gap h4
  have hcast : (r : ℝ) = 2 * (tG r : ℝ) + 2 * (tM r : ℝ) + 2 * (tEta r : ℝ) := by
    have : r = 2 * tG r + 2 * tM r + 2 * tEta r := by omega
    exact_mod_cast this
  have hηR : (tEta r : ℝ) = 0 ∨ (tEta r : ℝ) = 1 := by rcases hη with h | h <;> simp [h]
  rcases lt_or_ge (tG r) 64 with hg | hg
  · refine (tail_rec h4 (tails_first_bound (tM r) hme) hz).trans ?_
    rw [hcast]
    exact second_scalar_small_g hηR (by positivity) (by positivity) (by exact_mod_cast g64 hg)
  have hgm := g64' hg
  have hgmR : 4 * (tM r : ℝ) + 8 ≤ tG r := by exact_mod_cast hgm
  have hme' := Nat.even_iff.mp hme
  rcases lt_or_ge (tM r) 4 with hm4 | hm4
  · refine (tail_rec h4 (tailE_small hme (by omega)) hz).trans ?_
    rw [hcast]
    exact second_scalar_small_m hηR (by positivity) (by positivity)
      (by exact_mod_cast (show tM r ≤ 2 by omega))
  -- `m ≥ 4`: the numbers `g'`, `m'`, `η'` that the recursion assigns to `m`
  obtain ⟨hmax', -, hη', hsum', hme2⟩ := tail_params hm4
  obtain ⟨g1', -, -, -, g32', -⟩ := tail_gap hm4
  have hcast' : (tM r : ℝ) = 2 * (tG (tM r) : ℝ) + 2 * (tM (tM r) : ℝ) + 2 * (tEta (tM r) : ℝ) := by
    have : tM r = 2 * tG (tM r) + 2 * tM (tM r) + 2 * tEta (tM r) := by omega
    exact_mod_cast this
  have hηR' : (tEta (tM r) : ℝ) = 0 ∨ (tEta (tM r) : ℝ) = 1 := by
    rcases hη' with h | h <;> simp [h]
  rcases lt_or_ge (tG (tM r)) 32 with hg' | hg'
  · have hBm := fun z (hz : ‖z‖ = 1) => tail_rec hm4 (tailE_small hme2 (g1' hg')) hz
    refine (tail_rec h4 hBm hz).trans ?_
    rw [hcast]
    exact second_scalar_rec_small hηR hηR' (by positivity) hgmR (by positivity) (by positivity)
      (by exact_mod_cast g1' hg') hcast'
  · have hBm := fun z (hz : ‖z‖ = 1) => tail_rec hm4 (tails_first_bound (tM (tM r)) hme2) hz
    refine (tail_rec h4 hBm hz).trans ?_
    rw [hcast]
    exact second_scalar_rec_large hηR hηR' (by positivity) hgmR (by exact_mod_cast hg')
      (by positivity) (by exact_mod_cast g32' hg') hcast'

/-! ### Lemma `lem:tails` -/

theorem coeff_fun_eq {n r : ℕ} (h : r = n) (P : Fin n → ℤ) :
    (fun i : Fin r => coeff P i) = P ∘ Fin.cast h := by
  subst h; funext i; simp [coeff]

/-- **Lemma `lem:tails`.** "For every even `r ≥ 0`, the sequences `Φ_r` and `Ψ_r` satisfy
eq. `tail`", i.e. they are sign sequences of length `r` with `Φ_r(1) = Ψ_r(1) = 0` and
`|Φ_r(z)|² + |Ψ_r(z)|² ≤ 6r + 400` for all `|z| = 1`. -/
theorem lem_tails_rule (r : ℕ) (hr : Even r) :
    IsSignSeq (tailPhi' r) ∧ IsSignSeq (tailPsi' r) ∧ TailCond400 (tailPhi' r) (tailPsi' r) := by
  have hlen := tailRaw_fst r hr
  have e1 : tailPhi' r = tailPhi r ∘ Fin.cast hlen.symm := coeff_fun_eq _ _
  have e2 : tailPsi' r = tailPsi r ∘ Fin.cast hlen.symm := coeff_fun_eq _ _
  obtain ⟨s1, s2, h1, h2⟩ := tailRaw_sign_sum r
  rw [e1, e2]
  refine ⟨isSignSeq_comp_cast _ s1, isSignSeq_comp_cast _ s2, ?_, ?_, fun z hz => ?_⟩
  · rw [peval_comp_cast]; exact h1
  · rw [peval_comp_cast]; exact h2
  · rw [peval_comp_cast, peval_comp_cast]
    have := tails_second_bound r hr z hz
    unfold tailE at this
    linarith

end SignCond
