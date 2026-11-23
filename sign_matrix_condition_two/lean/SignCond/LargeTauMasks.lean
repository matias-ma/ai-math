import SignCond.Select
import SignCond.LargeTauArith

/-!
# Proposition `prop:large` (rewritten paper): the masks

Paper, proof of Proposition `prop:large`, paragraph "The masks": "The masks have to satisfy
eq. `pools`, that is, `S₀, S₁, S₂, S₃` are subsets of `{x : a_x = -σ}`, `{x : c_x = σ}`,
`{x : d_x = σ}`, `{x : b_x = σ}`. Each of these four sets has `½(j+s)` or `½(j-s)` elements ...
If `α ≥ ρ`, we let `S₀, …, S₃` be arbitrary subsets of size `k` of these sets. Suppose that
`α < ρ`. ... Let `𝒫` be one of the four sets, say `𝒫 = {x : c_x = σ}`. Its indicator vector is
`½(𝟙 + σc)`, so `|𝒫̂(ℓ)| = ½|ĉ(ℓ)| ≤ ½√E_ℓ` for `ℓ ≠ 0`. ... By Lemma `lem:select`, each of the
four sets contains a subset `S_i` of size `k` with `|Ŝ_i(ℓ)| ≤ k - 3/8` for all `ℓ ≠ 0`."

* `Shat_eq_sum_chi`: `Ŝ(ℓ) = Σ_{x∈S} χ(ℓx)` (the translation to the sums of `lem_select`).
* `signPool v t = {x : v_x = t}`; `two_mul_card_signPool`: `2|{x : v_x = t}| = j + t·Σv`.
* `sum_chi_signPool`: for `m ≠ 0`, `Σ_{x∈𝒫} χ(mx) = (t/2) v̂(m)` (indicator `½(𝟙 + t v)`).
* `masks_step`: the four masks in both cases, with eq. `pools`, size `k`, and `δ_ℓ ≤ 2k`
  (case `α ≥ ρ`) or `δ_ℓ ≤ 2k - 3/4` for `1 ≤ ℓ < j` (case `α < ρ`, via `lem_select`).
-/

open Complex Finset
open scoped Real

namespace SignCond

variable {j : ℕ} [NeZero j]

/-- `Ŝ(ℓ) = Σ_{x∈S} ω^{ℓx} = Σ_{x∈S} χ(ℓx)`. -/
theorem Shat_eq_sum_chi (S : Finset (ZMod j)) (ℓ : ℕ) :
    Shat S ℓ = ∑ x ∈ S, chi ((ℓ : ZMod j) * x) := by
  unfold Shat
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [omega_pow_eq_chi]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id]

omit [NeZero j] in
/-- For `1 ≤ ℓ < j`, `ℓ ≠ 0` in `ℤ/jℤ`. -/
theorem natCast_ne_zero_of_lt {ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ < j) : (ℓ : ZMod j) ≠ 0 := by
  intro h
  have := ZMod.val_cast_of_lt h2
  rw [h, ZMod.val_zero] at this
  omega

/-- The trivial bound `|Ŝ(ℓ)| ≤ |S|`. -/
theorem norm_Shat_le_card (S : Finset (ZMod j)) (ℓ : ℕ) : ‖Shat S ℓ‖ ≤ S.card := by
  rw [Shat_eq_sum_chi]
  refine (norm_sum_le _ _).trans ?_
  simp [norm_chi]

omit [NeZero j] in
/-- `δ_ℓ ≤ 2B` when `|Ŝ_i(ℓ)| ≤ B` for every `i`. -/
theorem deltaL_le {S : Fin 4 → Finset (ZMod j)} {ℓ : ℕ} {B : ℝ}
    (h : ∀ i, ‖Shat (S i) ℓ‖ ≤ B) : deltaL S ℓ ≤ 2 * B := by
  unfold deltaL
  have := max_le (max_le (h 0) (h 1)) (max_le (h 2) (h 3))
  linarith

/-- The set `{x : v_x = t}`. -/
noncomputable def signPool (v : ZMod j → ℝ) (t : ℝ) : Finset (ZMod j) :=
  Finset.univ.filter fun x => v x = t

theorem mem_signPool {v : ZMod j → ℝ} {t : ℝ} {x : ZMod j} : x ∈ signPool v t ↔ v x = t := by
  simp [signPool]

/-- `2|{x : v_x = t}| = j + t Σ_x v_x` for a sign vector `v` and `t = ±1`. -/
theorem two_mul_card_signPool (v : ZMod j → ℝ) (hv : IsSignVec v) (t : ℝ) (ht : t = 1 ∨ t = -1) :
    2 * ((signPool v t).card : ℝ) = j + t * vsum v := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => v x = t) v
  have h1 : ∑ x ∈ Finset.univ.filter (fun x => v x = t), v x = (signPool v t).card * t := by
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.1 hx).2), Finset.sum_const,
      nsmul_eq_mul]
    rfl
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ v x = t), v x =
      (Finset.univ.filter (fun x => ¬ v x = t)).card * (-t) := by
    rw [Finset.sum_congr rfl (g := fun _ => -t) (fun x hx => ?_), Finset.sum_const, nsmul_eq_mul]
    have hx' := (Finset.mem_filter.1 hx).2
    rcases hv x with h | h <;> rcases ht with rfl | rfl <;> simp_all
  have hc := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ) (fun x => v x = t)
  rw [Finset.card_univ, ZMod.card] at hc
  have hcR : ((signPool v t).card : ℝ) + (Finset.univ.filter (fun x => ¬ v x = t)).card = j := by
    exact_mod_cast hc
  have ht2 : t * t = 1 := by rcases ht with rfl | rfl <;> norm_num
  unfold vsum
  rw [← hsplit, h1, h2]
  have : (Finset.univ.filter (fun x => ¬ v x = t)).card = (j : ℝ) - (signPool v t).card := by
    linarith
  rw [this]
  linear_combination ((j : ℝ) - 2 * ((signPool v t).card : ℝ)) * ht2

/-- Paper: "`½(j-s)` ≤ the size of each of the four sets": if `-s ≤ t Σv` then
`(j - s)/2 ≤ |{x : v_x = t}|`. -/
theorem card_signPool_ge (v : ZMod j → ℝ) (hv : IsSignVec v) (t : ℝ) (ht : t = 1 ∨ t = -1)
    {s : ℝ} (h : -s ≤ t * vsum v) : ((j : ℝ) - s) / 2 ≤ (signPool v t).card := by
  have := two_mul_card_signPool v hv t ht
  linarith

/-- Paper: "Its indicator vector is `½(𝟙 + σc)`, so `𝒫̂(ℓ) = ½σĉ(ℓ)` for `ℓ ≠ 0`." -/
theorem sum_chi_signPool (v : ZMod j → ℝ) (hv : IsSignVec v) (t : ℝ) (ht : t = 1 ∨ t = -1)
    (m : ZMod j) (hm : m ≠ 0) :
    ∑ x ∈ signPool v t, chi (m * x) = ((t / 2 : ℝ) : ℂ) * dft (cx v) m := by
  unfold signPool
  rw [Finset.sum_filter]
  have hpt : ∀ x : ZMod j, (if v x = t then chi (m * x) else 0) =
      (1 / 2 : ℂ) * chi (m * x) + ((t / 2 : ℝ) : ℂ) * ((v x : ℂ) * chi (m * x)) := by
    intro x
    rcases hv x with h | h <;> rcases ht with rfl | rfl <;> simp [h] <;> norm_num <;> ring
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_chi_mul, if_neg hm, mul_zero, zero_add]
  rfl

/-- `|𝒫̂(m)| = ½|v̂(m)|` for `m ≠ 0`, with `v̂(m) = hat v m.val`. -/
theorem norm_sum_chi_signPool (v : ZMod j → ℝ) (hv : IsSignVec v) (t : ℝ) (ht : t = 1 ∨ t = -1)
    (m : ZMod j) (hm : m ≠ 0) :
    ‖∑ x ∈ signPool v t, chi (m * x)‖ = ‖hat v m.val‖ / 2 := by
  rw [sum_chi_signPool v hv t ht m hm, norm_mul, hat_eq_dft, ZMod.natCast_zmod_val,
    Complex.norm_real, Real.norm_eq_abs]
  rcases ht with rfl | rfl <;> norm_num <;> rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] <;> ring

/-- `|x̂(ℓ)| ≤ √E_ℓ` for each of the four sequences. -/
theorem norm_hat_le_sqrt_energy (a b c d : ZMod j → ℝ) (ℓ : ℕ) :
    ‖hat a ℓ‖ ≤ Real.sqrt (energy a b c d ℓ) ∧ ‖hat b ℓ‖ ≤ Real.sqrt (energy a b c d ℓ) ∧
      ‖hat c ℓ‖ ≤ Real.sqrt (energy a b c d ℓ) ∧ ‖hat d ℓ‖ ≤ Real.sqrt (energy a b c d ℓ) := by
  have key : ∀ x : ℂ, ‖x‖ ^ 2 ≤ energy a b c d ℓ → ‖x‖ ≤ Real.sqrt (energy a b c d ℓ) := by
    intro x hx
    rw [← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt hx
  have h0 := sq_nonneg ‖hat a ℓ‖
  have h1 := sq_nonneg ‖hat b ℓ‖
  have h2 := sq_nonneg ‖hat c ℓ‖
  have h3 := sq_nonneg ‖hat d ℓ‖
  refine ⟨key _ ?_, key _ ?_, key _ ?_, key _ ?_⟩ <;> unfold energy <;> linarith

/-- Lemma `lem:select` applied to `𝒫 = {x : v_x = t}`: a subset of size `k` with
`|Ŝ(ℓ)| ≤ k - 3/8` for `1 ≤ ℓ < j`. -/
theorem exists_mask_select (v : ZMod j → ℝ) (hv : IsSignVec v) (t : ℝ) (ht : t = 1 ∨ t = -1)
    (k : ℕ) (hk13 : 13 ≤ k) (hkP : k ≤ (signPool v t).card) (hj : j ≤ 196 * k ^ 2)
    (hbias : ∀ ℓ : ℕ, ‖hat v ℓ‖ / 2 ≤ ((signPool v t).card : ℝ) / 33) :
    ∃ S ⊆ signPool v t, S.card = k ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j → ‖Shat S ℓ‖ ≤ (k : ℝ) - 3 / 8 := by
  obtain ⟨S, hSP, hSk, hS⟩ := lem_select (signPool v t) k hk13 hkP hj (fun m hm => by
    rw [norm_sum_chi_signPool v hv t ht m hm]; exact hbias m.val)
  refine ⟨S, hSP, hSk, fun ℓ h1 h2 => ?_⟩
  rw [Shat_eq_sum_chi]
  exact hS _ (natCast_ne_zero_of_lt h1 h2)

/-- Four subsets of the four sets satisfy eq. `pools`. -/
theorem pools_of_subsets {σ : ℝ} {a b c d : ZMod j → ℝ} {S0 S1 S2 S3 : Finset (ZMod j)}
    (h0 : S0 ⊆ signPool a (-σ)) (h1 : S1 ⊆ signPool c σ) (h2 : S2 ⊆ signPool d σ)
    (h3 : S3 ⊆ signPool b σ) : Pools σ a b c d ![S0, S1, S2, S3] :=
  ⟨fun _ hx => mem_signPool.1 (h0 hx), fun _ hx => mem_signPool.1 (h1 hx),
    fun _ hx => mem_signPool.1 (h2 hx), fun _ hx => mem_signPool.1 (h3 hx)⟩

omit [NeZero j] in
theorem card_vec4 {S0 S1 S2 S3 : Finset (ZMod j)} {k : ℕ} (h0 : S0.card = k) (h1 : S1.card = k)
    (h2 : S2.card = k) (h3 : S3.card = k) : ∀ i, (![S0, S1, S2, S3] i).card = k := by
  intro i; fin_cases i <;> assumption

omit [NeZero j] in
theorem shat_vec4 {S0 S1 S2 S3 : Finset (ZMod j)} {ℓ : ℕ} {B : ℝ} (h0 : ‖Shat S0 ℓ‖ ≤ B)
    (h1 : ‖Shat S1 ℓ‖ ≤ B) (h2 : ‖Shat S2 ℓ‖ ≤ B) (h3 : ‖Shat S3 ℓ‖ ≤ B) :
    ∀ i, ‖Shat (![S0, S1, S2, S3] i) ℓ‖ ≤ B := by
  intro i; fin_cases i <;> assumption

/-- **The masks** (paper, proof of Proposition `prop:large`). For sign vectors `a, b, c, d` with
sums `(-s, s, s, s)` (`s ≥ 0`), `σ = ±1` and `k ≤ ½(j - s)`:
1. (case `α ≥ ρ`) there are masks of size `k` satisfying eq. `pools`, with `δ_ℓ ≤ 2k`;
2. (case `α < ρ`) if `k ≥ 13`, `j ≤ 196k²` and `½√E_ℓ ≤ ½(j-s)/33` for all `ℓ`, there are masks of
   size `k` satisfying eq. `pools` with `δ_ℓ ≤ 2(k - 3/8)` for `1 ≤ ℓ < j`. -/
theorem masks_step (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (a b c d : ZMod j → ℝ) (ha : IsSignVec a)
    (hb : IsSignVec b) (hc : IsSignVec c) (hd : IsSignVec d) (s : ℝ) (hs0 : 0 ≤ s)
    (hsa : vsum a = -s) (hsb : vsum b = s) (hsc : vsum c = s) (hsd : vsum d = s) (k : ℕ)
    (hk : (k : ℝ) ≤ ((j : ℝ) - s) / 2) :
    (∃ S : Fin 4 → Finset (ZMod j), (∀ i, (S i).card = k) ∧ Pools σ a b c d S ∧
        ∀ ℓ : ℕ, deltaL S ℓ ≤ 2 * k) ∧
      (13 ≤ k → j ≤ 196 * k ^ 2 →
        (∀ ℓ : ℕ, Real.sqrt (energy a b c d ℓ) / 2 ≤ ((j : ℝ) - s) / 2 / 33) →
        ∃ S : Fin 4 → Finset (ZMod j), (∀ i, (S i).card = k) ∧ Pools σ a b c d S ∧
          ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j → deltaL S ℓ ≤ 2 * k - 3 / 4) := by
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσs : -s ≤ σ * s := by rcases hσ with rfl | rfl <;> linarith
  -- the sizes of the four sets
  have cA := card_signPool_ge a ha (-σ) hnσ (s := s) (by rw [hsa]; linarith)
  have cC := card_signPool_ge c hc σ hσ (s := s) (by rw [hsc]; linarith)
  have cD := card_signPool_ge d hd σ hσ (s := s) (by rw [hsd]; linarith)
  have cB := card_signPool_ge b hb σ hσ (s := s) (by rw [hsb]; linarith)
  have kA : k ≤ (signPool a (-σ)).card := by exact_mod_cast hk.trans cA
  have kC : k ≤ (signPool c σ).card := by exact_mod_cast hk.trans cC
  have kD : k ≤ (signPool d σ).card := by exact_mod_cast hk.trans cD
  have kB : k ≤ (signPool b σ).card := by exact_mod_cast hk.trans cB
  constructor
  · obtain ⟨S0, h0, e0⟩ := Finset.exists_subset_card_eq kA
    obtain ⟨S1, h1, e1⟩ := Finset.exists_subset_card_eq kC
    obtain ⟨S2, h2, e2⟩ := Finset.exists_subset_card_eq kD
    obtain ⟨S3, h3, e3⟩ := Finset.exists_subset_card_eq kB
    refine ⟨![S0, S1, S2, S3], card_vec4 e0 e1 e2 e3, pools_of_subsets h0 h1 h2 h3,
      fun ℓ => deltaL_le (shat_vec4 ?_ ?_ ?_ ?_)⟩
    · have := norm_Shat_le_card S0 ℓ; rwa [e0] at this
    · have := norm_Shat_le_card S1 ℓ; rwa [e1] at this
    · have := norm_Shat_le_card S2 ℓ; rwa [e2] at this
    · have := norm_Shat_le_card S3 ℓ; rwa [e3] at this
  · intro hk13 hj hE
    have hen := norm_hat_le_sqrt_energy a b c d
    have bias : ∀ (v : ZMod j → ℝ) (t : ℝ), ((j : ℝ) - s) / 2 ≤ (signPool v t).card →
        (∀ ℓ : ℕ, ‖hat v ℓ‖ ≤ Real.sqrt (energy a b c d ℓ)) →
        ∀ ℓ : ℕ, ‖hat v ℓ‖ / 2 ≤ ((signPool v t).card : ℝ) / 33 := by
      intro v t hcard hv ℓ
      have := hE ℓ
      have := hv ℓ
      have : ((j : ℝ) - s) / 2 / 33 ≤ ((signPool v t).card : ℝ) / 33 := by linarith
      linarith
    obtain ⟨S0, h0, e0, b0⟩ := exists_mask_select a ha (-σ) hnσ k hk13 kA hj
      (bias a _ cA fun ℓ => (hen ℓ).1)
    obtain ⟨S1, h1, e1, b1⟩ := exists_mask_select c hc σ hσ k hk13 kC hj
      (bias c _ cC fun ℓ => (hen ℓ).2.2.1)
    obtain ⟨S2, h2, e2, b2⟩ := exists_mask_select d hd σ hσ k hk13 kD hj
      (bias d _ cD fun ℓ => (hen ℓ).2.2.2)
    obtain ⟨S3, h3, e3, b3⟩ := exists_mask_select b hb σ hσ k hk13 kB hj
      (bias b _ cB fun ℓ => (hen ℓ).2.1)
    refine ⟨![S0, S1, S2, S3], card_vec4 e0 e1 e2 e3, pools_of_subsets h0 h1 h2 h3,
      fun ℓ hℓ1 hℓ2 => ?_⟩
    have := deltaL_le (S := ![S0, S1, S2, S3]) (ℓ := ℓ)
      (shat_vec4 (b0 ℓ hℓ1 hℓ2) (b1 ℓ hℓ1 hℓ2) (b2 ℓ hℓ1 hℓ2) (b3 ℓ hℓ1 hℓ2))
    linarith

end SignCond
