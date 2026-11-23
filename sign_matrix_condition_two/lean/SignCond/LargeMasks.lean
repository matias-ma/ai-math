import SignCond.Hypotheses
import SignCond.BasePairs
import SignCond.Seeds
import SignCond.Fourier

/-!
# Proposition `prop:large`: the masks and the choice of `l`

* `maskLiftIter_bound`: Lemma `lem:masklift` applied `h` times.
* `mask_bound`: "bounding each of the remaining `k - 2^h q` terms by one,
  `|p_S(e^{iθ})| ≤ k - 2^h η ≤ k - 4/5` for `2π/(4^h J) ≤ |θ| ≤ π`".
* `omega_pow_arc`: for `1 ≤ ℓ < j`, `ω^ℓ = e^{iθ}` with `2π/j ≤ |θ| ≤ π`.
* `Shat_image`: `|Ŝ-ε(ℓ)| = |p_S(ω^ℓ)|`.
* `choose_l`: the largest `l = 2^h λ ∈ 𝓛` with `l² ≤ N` and the next element `l⁺ = 2^h λ⁺`.
-/

open Complex
open scoped Real

namespace SignCond

/-- Lemma `lem:masklift` applied `h` times. -/
theorem maskLiftIter_bound (S0 : Finset ℕ) {J η : ℝ} (hJ : 32 ≤ J) (hη : η ≤ S0.card / 4)
    (h0 : ∀ θ : ℝ, 2 * π / J ≤ |θ| → |θ| ≤ π → ‖pS S0 (exp (θ * I))‖ ≤ S0.card - η) (h : ℕ) :
    ∀ θ : ℝ, 2 * π / (4 ^ h * J) ≤ |θ| → |θ| ≤ π →
      ‖pS (maskLiftIter S0 h) (exp (θ * I))‖ ≤ (maskLiftIter S0 h).card - 2 ^ h * η := by
  induction h with
  | zero => simpa [maskLiftIter] using h0
  | succ h ih =>
    intro θ hθ1 hθ2
    have hJ' : 32 ≤ 4 ^ h * J := le_trans hJ (le_mul_of_one_le_left (by linarith) (one_le_pow₀
      (by norm_num)))
    have hcard : ((maskLiftIter S0 h).card : ℝ) = 2 ^ h * S0.card := by
      rw [card_maskLiftIter]; push_cast; ring
    have hη' : 2 ^ h * η ≤ (maskLiftIter S0 h).card / 4 := by
      rw [hcard]; have : (0 : ℝ) < 2 ^ h := by positivity
      nlinarith
    have := masklift (maskLiftIter S0 h) hJ' hη' ih θ
      (by rw [show 4 * (4 ^ h * J) = 4 ^ (h + 1) * J by ring]; exact hθ1) hθ2
    rw [maskLiftIter, card_maskLift]
    push_cast
    rw [pow_succ]
    linarith

theorem card_seedSet (q : ℕ) (hq : q = 7 ∨ q = 9) (σ : ℤ) : (seedSet q σ).card = q := by
  rcases hq with rfl | rfl <;> by_cases hσ : σ = -1 <;> simp [seedSet, hσ]

theorem zero_not_mem_seedSet (q : ℕ) (σ : ℤ) : 0 ∉ seedSet q σ := by
  unfold seedSet; split_ifs <;> simp

/-- `J = 6400` for `λ = 64` and `J = 16384` otherwise. -/
noncomputable def seedArc (lam : ℕ) : ℝ := if lam = 64 then 6400 else 16384

/-- Lemma `lem:seeds`, part 1, in the form used: `|p_{S_q^σ}(e^{iθ})| ≤ q - η` for
`2π/J ≤ |θ| ≤ π`, with `η = 4/5` (`q = 7`) or `η = 1` (`q = 9`). -/
theorem seed_base (hArc : LemSeedsArc) (σ : ℤ) (hσ : σ = -1 ∨ σ = 1) (lam : ℕ) :
    ∃ η : ℝ, 4 / 5 ≤ η ∧ η ≤ (seedSet (seedSize lam) σ).card / 4 ∧
      ∀ θ : ℝ, 2 * π / seedArc lam ≤ |θ| → |θ| ≤ π →
        ‖pS (seedSet (seedSize lam) σ) (exp (θ * I))‖ ≤ (seedSet (seedSize lam) σ).card - η := by
  obtain ⟨h7, h9⟩ := hArc σ hσ
  by_cases hl : lam = 64
  · have hq : seedSize lam = 7 := by simp [seedSize, hl]
    refine ⟨4 / 5, le_rfl, ?_, ?_⟩
    · rw [hq, card_seedSet 7 (Or.inl rfl)]; norm_num
    · intro θ h1 h2
      rw [hq, card_seedSet 7 (Or.inl rfl)]
      have := h7 θ (by simpa [seedArc, hl] using h1) h2
      norm_num at this ⊢; linarith
  · have hq : seedSize lam = 9 := by simp [seedSize, hl]
    refine ⟨1, by norm_num, ?_, ?_⟩
    · rw [hq, card_seedSet 9 (Or.inr rfl)]; norm_num
    · intro θ h1 h2
      rw [hq, card_seedSet 9 (Or.inr rfl)]
      have := h9 θ (by simpa [seedArc, hl] using h1) h2
      norm_num at this ⊢; linarith

theorem seedArc_ge (lam : ℕ) : 32 ≤ seedArc lam := by
  unfold seedArc; split_ifs <;> norm_num

/-- Paper: "Applying Lemma `lem:masklift` `h` times, and bounding each of the remaining `k - 2^h q`
terms by one, `|p_S(e^{iθ})| ≤ k - 2^h η ≤ k - 4/5` for `2π/(4^h J) ≤ |θ| ≤ π`." -/
theorem mask_bound (hArc : LemSeedsArc) (σ : ℤ) (hσ : σ = -1 ∨ σ = 1) (lam h : ℕ)
    (S : Finset ℕ) (hsub : maskLiftIter (seedSet (seedSize lam) σ) h ⊆ S) :
    ∀ θ : ℝ, 2 * π / (4 ^ h * seedArc lam) ≤ |θ| → |θ| ≤ π →
      ‖pS S (exp (θ * I))‖ ≤ S.card - 4 / 5 := by
  intro θ h1 h2
  obtain ⟨η, hη1, hη2, hbase⟩ := seed_base hArc σ hσ lam
  have hA := maskLiftIter_bound _ (seedArc_ge lam) hη2 hbase h θ h1 h2
  set A := maskLiftIter (seedSet (seedSize lam) σ) h
  have hsplit : pS S (exp (θ * I)) = pS (S \ A) (exp (θ * I)) + pS A (exp (θ * I)) := by
    simp only [pS]; rw [Finset.sum_sdiff hsub]
  have hrest := norm_pS_le (S \ A) (norm_exp_ofReal_mul_I θ)
  rw [Finset.card_sdiff hsub] at hrest
  have hcardle : (A.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hsub
  have hpow : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have hη0 : (0 : ℝ) ≤ η := by linarith
  rw [hsplit]
  calc ‖pS (S \ A) (exp (θ * I)) + pS A (exp (θ * I))‖
      ≤ ‖pS (S \ A) (exp (θ * I))‖ + ‖pS A (exp (θ * I))‖ := norm_add_le _ _
    _ ≤ ((S.card - A.card : ℕ) : ℝ) + (A.card - 2 ^ h * η) := add_le_add hrest hA
    _ ≤ S.card - 4 / 5 := by
      rw [Nat.cast_sub (Finset.card_le_card hsub)]
      nlinarith

/-- For `1 ≤ ℓ < j`, `ω^ℓ = e^{iθ}` with `2π/j ≤ |θ| ≤ π`. -/
theorem omega_pow_arc {j ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ < j) :
    ∃ θ : ℝ, omega j ^ ℓ = exp (θ * I) ∧ 2 * π / j ≤ |θ| ∧ |θ| ≤ π := by
  have hj : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hω : omega j ^ ℓ = exp (((2 * π * ℓ / j : ℝ) : ℂ) * I) := by
    rw [omega, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
  have hℓj : (ℓ : ℝ) < j := by exact_mod_cast h2
  by_cases hhalf : 2 * ℓ ≤ j
  · have hh : (2 : ℝ) * ℓ ≤ j := by exact_mod_cast hhalf
    refine ⟨2 * π * ℓ / j, hω, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ hj.le
      nlinarith [Real.pi_pos]
    · rw [abs_of_nonneg (by positivity), div_le_iff₀ hj]
      nlinarith [Real.pi_pos]
  · have hh : (j : ℝ) < 2 * ℓ := by exact_mod_cast (by omega : j < 2 * ℓ)
    refine ⟨2 * π * ℓ / j - 2 * π, ?_, ?_, ?_⟩
    · rw [hω]
      push_cast
      rw [sub_mul, Complex.exp_sub, show (2 * (π : ℂ)) * I = 2 * π * I by ring,
        Complex.exp_two_pi_mul_I, div_one]
    · have e : 2 * π * ℓ / j - 2 * π = -(2 * π * (j - ℓ) / j) := by field_simp; ring
      rw [e, abs_neg, abs_of_nonneg (by
        apply div_nonneg _ hj.le; nlinarith [Real.pi_pos])]
      apply div_le_div_of_nonneg_right _ hj.le
      have : (1 : ℝ) ≤ j - ℓ := by
        have : ℓ + 1 ≤ j := h2
        have : ((ℓ + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast this
        push_cast at this; linarith
      nlinarith [Real.pi_pos]
    · have e : 2 * π * ℓ / j - 2 * π = -(2 * π * (j - ℓ) / j) := by field_simp; ring
      rw [e, abs_neg, abs_of_nonneg (by
        apply div_nonneg _ hj.le; nlinarith [Real.pi_pos]), div_le_iff₀ hj]
      nlinarith [Real.pi_pos]

/-- The mask `S - ε ⊆ ℤ/jℤ` of a set `S` of positions `ε ≤ x < j + ε`. -/
def shiftMask (j ε : ℕ) (S : Finset ℕ) : Finset (ZMod j) :=
  S.image fun x => ((x - ε : ℕ) : ZMod j)

theorem shiftMask_injOn {j ε : ℕ} {S : Finset ℕ} (hS : ∀ x ∈ S, ε ≤ x ∧ x - ε < j) :
    Set.InjOn (fun x => ((x - ε : ℕ) : ZMod j)) S := by
  intro x hx y hy hxy
  have h1 := congrArg ZMod.val hxy
  simp only at h1
  rw [ZMod.val_cast_of_lt (hS x hx).2, ZMod.val_cast_of_lt (hS y hy).2] at h1
  have := (hS x hx).1; have := (hS y hy).1
  omega

theorem card_shiftMask {j ε : ℕ} {S : Finset ℕ} (hS : ∀ x ∈ S, ε ≤ x ∧ x - ε < j) :
    (shiftMask j ε S).card = S.card :=
  Finset.card_image_of_injOn (shiftMask_injOn hS)

/-- Paper, eq. `maskbound`: `|(S-ε)^(ℓ)| = |p_S(ω^ℓ)|`. -/
theorem norm_Shat_shiftMask {j ε : ℕ} [NeZero j] {S : Finset ℕ}
    (hS : ∀ x ∈ S, ε ≤ x ∧ x - ε < j) (ℓ : ℕ) :
    ‖Shat (shiftMask j ε S) ℓ‖ = ‖pS S (omega j ^ ℓ)‖ := by
  have hz : ‖omega j ^ ℓ‖ = 1 := by rw [← pow_one (omega j ^ ℓ), ← pow_mul]; exact norm_omega_pow _
  have e1 : Shat (shiftMask j ε S) ℓ = ∑ x ∈ S, (omega j ^ ℓ) ^ (x - ε) := by
    rw [Shat, shiftMask, Finset.sum_image (shiftMask_injOn hS)]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [ZMod.val_cast_of_lt (hS x hx).2, pow_mul]
  have e2 : pS S (omega j ^ ℓ) = (omega j ^ ℓ) ^ ε * ∑ x ∈ S, (omega j ^ ℓ) ^ (x - ε) := by
    rw [pS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← pow_add, Nat.add_sub_cancel' (hS x hx).1]
  rw [e1, e2, norm_mul, norm_pow, hz, one_pow, one_mul]

/-- The choice of `l`: for `N ≥ 64²` there are `h` and consecutive elements `λ, λ⁺` of the list
`64, 80, 100, 104, 128` with `(2^h λ)² ≤ N < (2^h λ⁺)²`. -/
theorem choose_l {N : ℕ} (hN : 4096 ≤ N) :
    ∃ h lam lamp : ℕ, (lam, lamp) ∈ ({(64, 80), (80, 100), (100, 104), (104, 128)} : Finset (ℕ × ℕ)) ∧
      (2 ^ h * lam) ^ 2 ≤ N ∧ N < (2 ^ h * lamp) ^ 2 := by
  have h64 : 64 ≤ Nat.sqrt N := Nat.le_sqrt'.2 (by norm_num; omega)
  obtain ⟨a, ha1, ha2⟩ := exists_window h64
  have up : ∀ m, Nat.sqrt N < 2 ^ a * m → N < (2 ^ a * m) ^ 2 := fun m h => Nat.sqrt_lt'.1 h
  have lo : ∀ m, 2 ^ a * m ≤ Nat.sqrt N → (2 ^ a * m) ^ 2 ≤ N := fun m h => Nat.le_sqrt'.1 h
  refine ⟨a, ?_⟩
  by_cases c1 : Nat.sqrt N < 2 ^ a * 80
  · exact ⟨64, 80, by simp, lo 64 (by linarith), up 80 c1⟩
  by_cases c2 : Nat.sqrt N < 2 ^ a * 100
  · exact ⟨80, 100, by simp, lo 80 (by omega), up 100 c2⟩
  by_cases c3 : Nat.sqrt N < 2 ^ a * 104
  · exact ⟨100, 104, by simp, lo 100 (by omega), up 104 c3⟩
  · exact ⟨104, 128, by simp, lo 104 (by omega), up 128 (by linarith)⟩

end SignCond
