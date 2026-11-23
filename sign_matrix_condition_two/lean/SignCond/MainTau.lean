import SignCond.LargeTau
import SignCond.DoublingTau
import SignCond.HypothesesTau

/-!
# The proof of Theorem `thm:main` (rewritten paper), with the strict inequality

Paper, "Proof of Theorem `thm:main`" (end of Section `sec:computation`):

* `finite_windowAt`: for `16 ≤ j ≤ 9998`, Proposition `prop:finite` (part 1) with masks of size
  `k = 1` and `τ = ρ = √(2j)`, Lemma `lem:scales` (part 1), Lemma `lem:sector` and Lemma
  `lem:criterion` give a sign matrix of order `4j + β` with `ρ²I ⪯ XXᵀ ≺ 4ρ²I`;
* `odd_case_tau`: every odd order `n ≠ 3` (`n ≤ 63` from `prop:finite` part 2, `j ≥ 9999` from
  `prop_large_tau`, the rest from `finite_windowAt`);
* `even_case_tau`: `n = 2^i m`, `i ≥ 1`, by Lemma `lem:double` (strict form) from `m ≥ 5` odd,
  from `W₂` (`m = 1`), from `A₆` (`n = 6`) and from `H₁₂` (`n = 3·2^i`, `i ≥ 2`);
* `main_theorem_tau`: every `n ≥ 1` has a sign matrix with `κ ≤ 2`, and `κ < 2` when `n ≠ 3`
  (`n = 3` from Lemma `lem:three`, `exists_three`).
-/

open Matrix Complex Kronecker
open scoped Real

namespace SignCond

/-- A sign vector whose sum has absolute value less than `j` takes both values. -/
theorem exists_value_tau {j : ℕ} [NeZero j] {x : ZMod j → ℝ} (hx : IsSignVec x) {v : ℝ}
    (hv : vsum x = v) (hlt : |v| < j) (τ : ℝ) (hτ : τ = 1 ∨ τ = -1) : ∃ u, x u = τ := by
  by_contra hne
  push_neg at hne
  have hall : ∀ u, x u = -τ := by
    intro u
    rcases hx u with h | h <;> rcases hτ with rfl | rfl
    · exact absurd h (hne u)
    · rw [h]; norm_num
    · rw [h]
    · exact absurd h (hne u)
  have hsum : vsum x = -τ * j := by
    simp [vsum, hall, ZMod.card, mul_comm]
  rw [hsum] at hv
  rw [← hv] at hlt
  rcases hτ with rfl | rfl <;> simp at hlt

theorem norm_Shat_singleton_tau {j : ℕ} [NeZero j] (u : ZMod j) (ℓ : ℕ) : ‖Shat {u} ℓ‖ = 1 := by
  rw [Shat, Finset.sum_singleton]; exact norm_omega_pow _

/-- `CondLt2` is the existence of a scale `τ > 0` with `τ²I ⪯ AAᵀ ≺ 4τ²I`. -/
theorem condLt2_iff_windowAt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    CondLt2 A ↔ ∃ τ : ℝ, 0 < τ ∧ WindowAt A τ := by
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨Real.sqrt t, Real.sqrt_pos.2 ht, ?_⟩
    rw [WindowAt, Real.sq_sqrt ht.le]
    exact ⟨h1, h2⟩
  · rintro ⟨τ, hτ, h⟩
    exact condLt2_of_windowAt hτ h

set_option maxHeartbeats 2000000 in
/-- The orders `4j + β` with `16 ≤ j ≤ 9998`, from Proposition `prop:finite`, part 1 (paper, proof
of Theorem `thm:main`, second paragraph): masks of size `k = 1`, `τ = ρ`. -/
theorem finite_windowAt (hF : PropFiniteTau) {j : ℕ} (hj16 : 16 ≤ j) (hj : j ≤ 9998) {β : ℕ}
    (hβ : β = 1 ∨ β = 3) :
    ∃ A : Matrix (Fin (4 * j + β)) (Fin (4 * j + β)) ℝ, IsSign A ∧
      WindowAt A (Real.sqrt (2 * j)) := by
  haveI : NeZero j := ⟨by omega⟩
  obtain ⟨a, b, c, d, s, ha, hb, hc, hd, sa, sb, sc, sd, hs1, hlo, hhi, hE⟩ := hF.1 j hj16 hj
  have hjR : (16 : ℝ) ≤ j := by exact_mod_cast hj16
  have hs1R : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  set ρ := Real.sqrt (2 * (j : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = 2 * j := Real.sq_sqrt (by positivity)
  have hρ4 : 4 < ρ := by nlinarith only [hρ2, hρ0, hjR]
  have hρpos : 0 < ρ := by linarith
  -- `s < j`, so every sequence takes both values
  have hsj : (s : ℝ) < j := by
    by_contra hcon
    push_neg at hcon
    nlinarith only [hlo, hcon, hjR]
  have hσ : sigmaOf β = 1 ∨ sigmaOf β = -1 := by
    rcases hβ with rfl | rfl <;> simp [sigmaOf] <;> norm_num
  have hσneg : -sigmaOf β = 1 ∨ -sigmaOf β = -1 := by
    rcases hσ with h | h <;> rw [h] <;> norm_num
  have habs : ∀ v : ℝ, (v = s ∨ v = -s) → |v| < j := by
    rintro v (rfl | rfl)
    · rw [abs_of_nonneg (by positivity)]; exact hsj
    · rw [abs_neg, abs_of_nonneg (by positivity)]; exact hsj
  obtain ⟨u0, hu0⟩ := exists_value_tau ha sa (habs _ (Or.inr rfl)) _ hσneg
  obtain ⟨u1, hu1⟩ := exists_value_tau hc sc (habs _ (Or.inl rfl)) _ hσ
  obtain ⟨u2, hu2⟩ := exists_value_tau hd sd (habs _ (Or.inl rfl)) _ hσ
  obtain ⟨u3, hu3⟩ := exists_value_tau hb sb (habs _ (Or.inl rfl)) _ hσ
  -- masks of size `k = 1`
  set S : Fin 4 → Finset (ZMod j) := ![{u0}, {u1}, {u2}, {u3}] with hSdef
  have hScard : ∀ i, (S i).card = 1 := by
    intro i; fin_cases i <;> simp [hSdef]
  have hpools : Pools (sigmaOf β) a b c d S := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x hx <;> simp [hSdef] at hx <;> subst hx
    · exact hu0
    · exact hu1
    · exact hu2
    · exact hu3
  -- `δ_ℓ = 2`, and eq. `finitewindow` is eq. `window` with `τ = ρ`
  have hdl : ∀ ℓ, deltaL S ℓ = 2 := by
    intro ℓ; simp [deltaL, hSdef, norm_Shat_singleton_tau]
  have hwin : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      ρ + deltaL S ℓ ≤ Real.sqrt (energy a b c d ℓ) ∧
        Real.sqrt (energy a b c d ℓ) < 2 * ρ - deltaL S ℓ := by
    intro ℓ h1 h2
    obtain ⟨e1, e2⟩ := hE ℓ h1 h2
    rw [hdl]
    have hE0 : 0 ≤ energy a b c d ℓ := le_trans (by positivity) e1
    constructor
    · rw [← Real.sqrt_sq (by positivity : 0 ≤ ρ + 2)]; exact Real.sqrt_le_sqrt e1
    · have := Real.sqrt_lt_sqrt hE0 e2
      rw [Real.sqrt_sq (by linarith only [hρ4])] at this
      linarith only [this]
  -- Lemma `lem:scales`, part 1, and Lemma `lem:sector` with `k = 1`, `τ = ρ`
  have hα : 2 * ((s : ℝ) - 1) ≤ ρ := by
    have := Real.sqrt_le_sqrt hlo
    rw [Real.sqrt_sq (by linarith only [hs1R])] at this
    linarith only [this]
  have hγ1 : ρ ≤ 2 * ((s : ℝ) + 1) := by
    have := Real.sqrt_le_sqrt hhi
    rw [Real.sqrt_sq (by linarith only [hs1R])] at this
    linarith only [this]
  have hp : ∀ ν : ℝ, (ν = 1 ∨ ν = 4) →
      0 ≤ pnu j (2 * ((s : ℝ) - ((1 : ℕ) : ℝ))) ν (ρ ^ 2) ∧
        0 < pnu j (2 * ((s : ℝ) - ((1 : ℕ) : ℝ))) ν (4 * ρ ^ 2) := by
    intro ν hν
    have h0 : (0 : ℝ) ≤ 2 * ((s : ℝ) - ((1 : ℕ) : ℝ)) := by push_cast; linarith only [hs1R]
    have h1 : 2 * ((s : ℝ) - ((1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * j) := by push_cast; exact hα
    exact lem_scales_one (by omega) h0 h1 hν
  have hsec := lem_sector_tau (j := j) (s := s) (k := 1) (by omega) hs1 ρ hρpos
    (by rw [hρ2]; linarith only [hjR]) (by rw [hρ2]; linarith only [hjR])
    (by push_cast; exact hγ1) (by push_cast; linarith only [hα, hρ4]) hp
  have hK : WindowAt (Kmat β ![vsum a, vsum b, vsum c, vsum d] ((1 : ℕ) : ℝ) j) ρ := by
    rw [sa, sb, sc, sd]
    rcases hβ with rfl | rfl
    · exact hsec.1
    · exact hsec.2
  -- Lemma `lem:criterion`
  have hX := lem_criterion_tau β hβ a b c d ha hb hc hd S 1 hScard hpools ρ hρpos hK hwin
  exact exists_fin_windowAt (Xmat_isSign hβ ha hb hc hd hpools) hX.1

theorem condLt2_cast {m n : ℕ} (h : m = n)
    (hm : ∃ A : Matrix (Fin m) (Fin m) ℝ, IsSign A ∧ CondLt2 A) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsSign A ∧ CondLt2 A := by
  subst h; exact hm

/-- Every odd order `n ≠ 3` (paper, proof of Theorem `thm:main`, first two paragraphs). -/
theorem odd_case_tau (hF : PropFiniteTau) {n : ℕ} (hn : Odd n) (h3 : n ≠ 3) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsSign A ∧ CondLt2 A := by
  by_cases h63 : n ≤ 63
  · obtain ⟨A, t, hA, ht, h1, h2⟩ := hF.2 n hn h63 h3
    exact ⟨A, hA, (t : ℝ), by exact_mod_cast ht, h1, h2⟩
  · set j := n / 4
    set β := n % 4
    have hβ : β = 1 ∨ β = 3 := by
      obtain ⟨r, rfl⟩ := hn; omega
    have hnj : 4 * j + β = n := Nat.div_add_mod n 4
    have hj16 : 16 ≤ j := by omega
    refine condLt2_cast hnj ?_
    by_cases hlarge : 9999 ≤ j
    · obtain ⟨A, hA, τ, hτ, hW⟩ := prop_large_tau j hlarge β hβ
      exact ⟨A, hA, condLt2_of_windowAt hτ hW⟩
    · obtain ⟨A, hA, hW⟩ := finite_windowAt hF hj16 (by omega) hβ
      have hj0 : (0 : ℝ) < 2 * j := by
        have : (16 : ℝ) ≤ j := by exact_mod_cast hj16
        linarith
      exact ⟨A, hA, condLt2_of_windowAt (Real.sqrt_pos.2 hj0) hW⟩

/-- Even orders `n = 2^i m`, `i ≥ 1`, `m` odd (paper, proof of Theorem `thm:main`, third
paragraph). -/
theorem even_case_tau (hF : PropFiniteTau) {i m : ℕ} (hi : 1 ≤ i) (hm : Odd m) :
    ∃ A : Matrix (Fin (2 ^ i * m)) (Fin (2 ^ i * m)) ℝ, IsSign A ∧ CondLt2 A := by
  by_cases h3 : m = 3
  · subst h3
    by_cases hi1 : i = 1
    · -- `n = 6`: the matrix `A₆`
      subst hi1
      exact ⟨A6, isSign_A6, condLt2_A6⟩
    · -- `n = 3 · 2^i`, `i ≥ 2`: Lemma `lem:double` applied `i - 2` times to `H₁₂`
      have h := exists_doubling_lt ⟨H12, isSign_H12, condLt2_H12⟩ (i - 2)
      refine condLt2_cast ?_ h
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      rw [Nat.add_sub_cancel, pow_add]; ring
  · by_cases h1 : m = 1
    · -- `n = 2^i`: Lemma `lem:double` applied `i - 1` times to `W₂`
      subst h1
      have h := exists_doubling_lt ⟨W2, isSign_W2, condLt2_W2⟩ (i - 1)
      refine condLt2_cast ?_ h
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_add]; ring
    · -- `m ≥ 5`: Lemma `lem:double` applied `i` times
      exact exists_doubling_lt (odd_case_tau hF hm h3) i

/-- **Theorem `thm:main`** (first statement). For every `n ≥ 1` there is an `n × n` sign matrix
`A` with `κ(A) ≤ 2`, and with `κ(A) < 2` if `n ≠ 3`. -/
theorem main_theorem_tau (hF : PropFiniteTau) :
    ∀ n : ℕ, 1 ≤ n → ∃ A : Matrix (Fin n) (Fin n) ℝ, IsSign A ∧ CondLe A 2 ∧
      (n ≠ 3 → CondLt2 A) := by
  intro n hn
  by_cases h3 : n = 3
  · subst h3
    obtain ⟨A, hA, -, hc⟩ := exists_three
    exact ⟨A, hA, hc, fun h => absurd rfl h⟩
  · have hlt : ∃ A : Matrix (Fin n) (Fin n) ℝ, IsSign A ∧ CondLt2 A := by
      obtain ⟨i, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        refine condLt2_cast (by ring) (odd_case_tau hF hm ?_)
        intro h; apply h3; rw [h]; ring
      · exact even_case_tau hF hi hm
    obtain ⟨A, hA, hc⟩ := hlt
    exact ⟨A, hA, condLt2_condLe hc, fun _ => hc⟩

/-- A matrix with a window `tI ⪯ AAᵀ`, `t > 0`, is invertible. -/
theorem condLe_det_ne_zero_tau {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ} (h : CondLe A c) :
    A.det ≠ 0 := by
  obtain ⟨t, ht, hw⟩ := (condLe_iff A c).1 h
  intro hdet
  have hdetT : Aᵀ.det = 0 := by rw [det_transpose]; exact hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdetT
  have h1 := (hw v).1
  rw [hv, zero_dotProduct] at h1
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have hvv0 : v ⬝ᵥ v = 0 := by nlinarith
  exact hv0 (dotProduct_self_eq_zero.1 hvv0)

end SignCond
