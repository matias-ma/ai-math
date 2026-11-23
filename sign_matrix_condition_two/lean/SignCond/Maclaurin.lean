import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# Maclaurin's inequality (used in the proof of Lemma `lem:select`)

For nonnegative weights `w` on a nonempty finite set `P` with `N = |P|` elements,

  `e_k(w; P) = Σ_{S ⊆ P, |S| = k} Π_{x∈S} w(x) ≤ C(N, k) · ((1/N) Σ_{x∈P} w(x))^k`.

Proof: induction on `P`. Writing `P = {a} ∪ R` with `|R| = n ≥ 1`, `t = w(a)` and `ν` the mean of `w`
over `R`, the recursion `e_{m+1}(P) = e_{m+1}(R) + t e_m(R)`, the induction hypothesis and the
tangent-line inequality `μ^{m+1} ≥ ν^{m+1} + (m+1) ν^m (μ - ν)` (for `μ, ν ≥ 0`, `μ` the mean over `P`)
give the claim, using `C(n+1,m+1) = C(n,m) + C(n,m+1)` and `(n+1) C(n,m) = (m+1) C(n+1,m+1)`.
-/

open Finset

namespace SignCond

variable {α : Type*} [DecidableEq α]

/-- The elementary symmetric sum `e_k(w; P) = Σ_{S ⊆ P, |S| = k} Π_{x∈S} w(x)`. -/
noncomputable def esum (w : α → ℝ) (P : Finset α) (k : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard k, ∏ x ∈ S, w x

omit [DecidableEq α] in
theorem esum_zero (w : α → ℝ) (P : Finset α) : esum w P 0 = 1 := by
  simp [esum, powersetCard_zero]

omit [DecidableEq α] in
theorem esum_empty_succ (w : α → ℝ) (m : ℕ) : esum w ∅ (m + 1) = 0 := by
  unfold esum
  rw [powersetCard_eq_empty.2 (by simp)]
  simp

theorem esum_insert_succ (w : α → ℝ) {a : α} {s : Finset α} (ha : a ∉ s) (m : ℕ) :
    esum w (insert a s) (m + 1) = esum w s (m + 1) + w a * esum w s m := by
  unfold esum
  rw [powersetCard_succ_insert ha, sum_union, sum_image]
  · congr 1
    rw [mul_sum]
    refine sum_congr rfl fun t ht => ?_
    have hat : a ∉ t := fun H => ha ((mem_powersetCard.1 ht).1 H)
    rw [prod_insert hat]
  · intro t ht u hu htu
    have hat : a ∉ t := fun H => ha ((mem_powersetCard.1 ht).1 H)
    have hau : a ∉ u := fun H => ha ((mem_powersetCard.1 hu).1 H)
    rw [← erase_insert hat, ← erase_insert hau]
    exact congrArg (fun v => Finset.erase v a) htu
  · rw [disjoint_left]
    intro t ht1 ht2
    rw [mem_image] at ht2
    obtain ⟨u, _, rfl⟩ := ht2
    exact ha ((mem_powersetCard.1 ht1).1 (mem_insert_self a u))

/-- Tangent-line inequality for `x ↦ x^{m+1}` on `[0, ∞)`. -/
theorem pow_tangent (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    a ^ (m + 1) + (m + 1) * a ^ m * (b - a) ≤ b ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : b * (a ^ (m + 1) + (m + 1) * a ^ m * (b - a)) ≤ b * b ^ (m + 1) :=
      mul_le_mul_of_nonneg_left ih hb
    have h2 : 0 ≤ ((m : ℝ) + 1) * a ^ m * (b - a) ^ 2 := by positivity
    have key : b ^ (m + 1 + 1) - (a ^ (m + 1 + 1) + ((((m + 1 : ℕ) : ℝ)) + 1) * a ^ (m + 1) * (b - a))
        = (b * b ^ (m + 1) - b * (a ^ (m + 1) + (m + 1) * a ^ m * (b - a)))
          + ((m : ℝ) + 1) * a ^ m * (b - a) ^ 2 := by
      push_cast; ring
    linarith

theorem maclaurin_aux (w : α → ℝ) : ∀ (P : Finset α), P.Nonempty →
    (∀ x ∈ P, 0 ≤ w x) → ∀ k : ℕ,
      esum w P k ≤ (P.card.choose k : ℝ) * ((∑ x ∈ P, w x) / P.card) ^ k := by
  intro P hP
  induction hP using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro _ k
    rcases k with _ | m
    · simp [esum_zero]
    · rw [show ({a} : Finset α) = insert a ∅ from rfl, esum_insert_succ w (notMem_empty a),
        esum_empty_succ]
      rcases m with _ | m
      · simp [esum_zero]
      · simp only [esum_empty_succ, mul_zero, add_zero]
        rw [show ({a} : Finset α) = insert a ∅ from rfl] at *
        simp only [card_insert_of_notMem (notMem_empty a), card_empty, zero_add]
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
  | cons a s ha hs ih =>
    intro hw k
    have hws : ∀ x ∈ s, 0 ≤ w x := fun x hx => hw x (mem_cons.2 (Or.inr hx))
    have ht : 0 ≤ w a := hw a (mem_cons_self a s)
    have ih' := ih hws
    rw [card_cons, sum_cons, cons_eq_insert]
    set n := s.card with hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hs.card_pos
    set σ := ∑ x ∈ s, w x with hσ
    have hσ0 : 0 ≤ σ := sum_nonneg hws
    set t := w a with htdef
    set ν := σ / n with hν
    have hν0 : 0 ≤ ν := div_nonneg hσ0 hnpos.le
    have hμ0 : 0 ≤ (t + σ) / ((n + 1 : ℕ) : ℝ) := by positivity
    rcases k with _ | m
    · simp [esum_zero]
    · rw [esum_insert_succ w ha]
      have i1 := ih' (m + 1)
      have i2 := ih' m
      set μ := (t + σ) / ((n + 1 : ℕ) : ℝ) with hμ
      set C : ℝ := (n.choose m : ℝ) with hC
      set D : ℝ := (n.choose (m + 1) : ℝ) with hD
      have hC0 : 0 ≤ C := by positivity
      have hD0 : 0 ≤ D := by positivity
      have hsum : ((n + 1).choose (m + 1) : ℝ) = C + D := by
        rw [Nat.choose_succ_succ']; push_cast; rfl
      have hchoose : ((n : ℝ) + 1) * C = (C + D) * ((m : ℝ) + 1) := by
        have := Nat.succ_mul_choose_eq n m
        rw [Nat.choose_succ_succ'] at this
        have h' : (((n + 1) * n.choose m : ℕ) : ℝ) = (((n.choose m + n.choose (m + 1)) * (m + 1) : ℕ) : ℝ) := by
          exact_mod_cast this
        push_cast at h'
        rw [hC, hD]; linarith
      have hμn : ((n : ℝ) + 1) * μ = t + n * ν := by
        rw [hμ, hν]; push_cast; field_simp
      rw [hsum]
      calc esum w s (m + 1) + t * esum w s m
          ≤ D * ν ^ (m + 1) + t * (C * ν ^ m) :=
            add_le_add i1 (mul_le_mul_of_nonneg_left i2 ht)
        _ = (C + D) * (ν ^ (m + 1) + (m + 1) * ν ^ m * (μ - ν)) := by
            linear_combination (ν ^ m * (μ - ν)) * hchoose - (C * ν ^ m) * hμn
        _ ≤ (C + D) * μ ^ (m + 1) :=
            mul_le_mul_of_nonneg_left (pow_tangent ν μ hν0 hμ0 m) (add_nonneg hC0 hD0)

/-- **Maclaurin's inequality**, in the form used: if `w ≥ 0` on `P ≠ ∅` and `Σ_P w ≤ M |P|`, then
`e_k(w; P) ≤ C(|P|, k) M^k`. -/
theorem maclaurin_le (w : α → ℝ) (P : Finset α) (hP : P.Nonempty) (hw : ∀ x ∈ P, 0 ≤ w x)
    (M : ℝ) (hM : ∑ x ∈ P, w x ≤ M * P.card) (k : ℕ) :
    esum w P k ≤ (P.card.choose k : ℝ) * M ^ k := by
  refine (maclaurin_aux w P hP hw k).trans ?_
  have hN : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have h0 : 0 ≤ (∑ x ∈ P, w x) / P.card := div_nonneg (sum_nonneg hw) hN.le
  have h1 : (∑ x ∈ P, w x) / P.card ≤ M := by rw [div_le_iff₀ hN]; exact hM
  gcongr

end SignCond
