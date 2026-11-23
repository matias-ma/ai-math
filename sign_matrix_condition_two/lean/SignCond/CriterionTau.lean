import SignCond.Criterion

/-!
# Lemma `lem:criterion` at a general scale `τ`, with a strict upper bound

The rewritten paper compares the singular values of `X` with an interval `[τ, 2τ)` for a free
parameter `τ > 0` (instead of the fixed scale `ρ = √(2j)`), and the upper bound is strict:

* `WindowAt M τ`: `τ² I ⪯ M Mᵀ ≺ 4 τ² I` (the second difference is positive definite);
* `CondLt2 A`: `t I ⪯ A Aᵀ ≺ 4 t I` for some `t > 0` (the paper's `κ(A) < 2`), with
  `condLt2_condLe : CondLt2 A → CondLe A 2`;
* `windowAt_iff_form`: `WindowAt M τ` iff `τ² ‖x‖² ≤ ‖Mᵀx‖²` for all `x` and
  `‖Mᵀx‖² < 4τ² ‖x‖²` for all `x ≠ 0`;
* `freq_window_tau`: eq. `sectorbound` at one frequency with the strict upper bound;
* `criterion_windowAt`: the lemma. The proof is that of `criterion_window` (`Criterion.lean`):
  Parseval splits `‖Xᵀy‖²` and `‖y‖²` into the nonzero frequencies and the constant sector,
  where `X` acts as `K`. For the strict upper bound, `y ≠ 0` forces either a nonzero frequency
  component (strict by `freq_window_tau`) or a nonzero constant-sector vector `z` (strict by the
  hypothesis on `K`).
-/

open Complex ComplexConjugate Matrix Finset
open scoped Real

namespace SignCond

section Windows

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Paper: `τ² I ⪯ M Mᵀ ≺ 4 τ² I`. -/
def WindowAt (M : Matrix n n ℝ) (τ : ℝ) : Prop :=
  (M * Mᵀ - (τ ^ 2) • (1 : Matrix n n ℝ)).PosSemidef ∧
    ((4 * τ ^ 2) • (1 : Matrix n n ℝ) - M * Mᵀ).PosDef

/-- `κ(A) < 2` in window form: `t I ⪯ A Aᵀ ≺ 4 t I` for some `t > 0`. -/
def CondLt2 (A : Matrix n n ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ (A * Aᵀ - t • (1 : Matrix n n ℝ)).PosSemidef ∧
    ((4 * t) • (1 : Matrix n n ℝ) - A * Aᵀ).PosDef

theorem condLt2_condLe {A : Matrix n n ℝ} (h : CondLt2 A) : CondLe A 2 := by
  obtain ⟨t, ht, h1, h2⟩ := h
  exact ⟨t, ht, h1, by rw [show (2 : ℝ) ^ 2 * t = 4 * t by ring]; exact h2.posSemidef⟩

theorem condLt2_of_windowAt {M : Matrix n n ℝ} {τ : ℝ} (hτ : 0 < τ) (h : WindowAt M τ) :
    CondLt2 M :=
  ⟨τ ^ 2, by positivity, h.1, h.2⟩

omit [DecidableEq n] in
/-- For a real symmetric matrix, positive definiteness is positivity of the quadratic form on
nonzero vectors. -/
theorem posDef_iff_of_transpose_eq {M : Matrix n n ℝ} (hM : Mᵀ = M) :
    M.PosDef ↔ ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x) := by
  have hH : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hM
  simp only [PosDef, hH, true_and, star_trivial]

/-- `WindowAt` in quadratic-form terms. -/
theorem windowAt_iff_form (M : Matrix n n ℝ) (τ : ℝ) :
    WindowAt M τ ↔ ∀ x : n → ℝ, τ ^ 2 * (x ⬝ᵥ x) ≤ (Mᵀ *ᵥ x) ⬝ᵥ (Mᵀ *ᵥ x) ∧
      (x ≠ 0 → (Mᵀ *ᵥ x) ⬝ᵥ (Mᵀ *ᵥ x) < 4 * τ ^ 2 * (x ⬝ᵥ x)) := by
  have h1 : (M * Mᵀ - (τ ^ 2) • (1 : Matrix n n ℝ))ᵀ = M * Mᵀ - (τ ^ 2) • (1 : Matrix n n ℝ) := by
    rw [transpose_sub, transpose_gram, transpose_smul, transpose_one]
  have h2 : ((4 * τ ^ 2) • (1 : Matrix n n ℝ) - M * Mᵀ)ᵀ =
      (4 * τ ^ 2) • (1 : Matrix n n ℝ) - M * Mᵀ := by
    rw [transpose_sub, transpose_gram, transpose_smul, transpose_one]
  unfold WindowAt
  rw [posSemidef_iff_of_transpose_eq h1, posDef_iff_of_transpose_eq h2]
  simp only [sub_mulVec, smul_mulVec_assoc, one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, dotProduct_gram_mulVec, sub_nonneg, sub_pos]
  exact ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

omit [DecidableEq n] in
theorem dot_self_pos {x : n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
    (Ne.symm (mt dotProduct_self_eq_zero.1 hx))

end Windows

/-! ### One frequency, strict upper bound -/

/-- Eq. `sectorbound` at one frequency: if `‖g‖² = E ‖φ‖²`, `‖h‖² ≤ δ² ‖φ‖²` and
`τ + δ ≤ √E < 2τ - δ` (with `τ, δ ≥ 0`), then `τ² ‖φ‖² ≤ ‖g + h‖² ≤ 4τ² ‖φ‖²`, and the upper bound
is strict when `φ ≠ 0`. -/
theorem freq_window_tau {g h φ : Fin 4 → ℂ} {E dl τ : ℝ} (hE0 : 0 ≤ E) (hdl : 0 ≤ dl)
    (hτ : 0 ≤ τ) (hg : ∑ i, ‖g i‖ ^ 2 = E * ∑ i, ‖φ i‖ ^ 2)
    (hh : ∑ i, ‖h i‖ ^ 2 ≤ dl ^ 2 * ∑ i, ‖φ i‖ ^ 2)
    (hw1 : τ + dl ≤ Real.sqrt E) (hw2 : Real.sqrt E < 2 * τ - dl) :
    τ ^ 2 * ∑ i, ‖φ i‖ ^ 2 ≤ ∑ i, ‖(g + h) i‖ ^ 2 ∧
      ∑ i, ‖(g + h) i‖ ^ 2 ≤ 4 * τ ^ 2 * ∑ i, ‖φ i‖ ^ 2 ∧
      (0 < ∑ i, ‖φ i‖ ^ 2 → ∑ i, ‖(g + h) i‖ ^ 2 < 4 * τ ^ 2 * ∑ i, ‖φ i‖ ^ 2) := by
  obtain ⟨l1, l2⟩ := freq_window hE0 hdl hτ hg hh hw1 hw2.le
  refine ⟨l1, l2, fun hpos => ?_⟩
  have eg := norm_e4_sq g
  have eh := norm_e4_sq h
  have eφ := norm_e4_sq φ
  have egh := norm_e4_sq (g + h)
  rw [← eg, ← eφ] at hg
  rw [← eh, ← eφ] at hh
  rw [← eφ] at hpos
  rw [← egh, ← eφ, e4_add]
  set G := e4 g
  set H := e4 h
  set F := e4 φ
  have hG : ‖G‖ = Real.sqrt E * ‖F‖ := by
    rw [← Real.sqrt_sq (norm_nonneg G), hg, Real.sqrt_mul hE0, Real.sqrt_sq (norm_nonneg F)]
  have hH : ‖H‖ ≤ dl * ‖F‖ := by
    rw [← Real.sqrt_sq (norm_nonneg H), ← Real.sqrt_sq (mul_nonneg hdl (norm_nonneg F))]
    exact Real.sqrt_le_sqrt (by rw [mul_pow]; exact hh)
  have hF : 0 < ‖F‖ := by
    rcases (norm_nonneg F).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0] at hpos; norm_num at hpos
  have hlt : (Real.sqrt E + dl) * ‖F‖ < 2 * τ * ‖F‖ :=
    mul_lt_mul_of_pos_right (by linarith) hF
  have hhi : ‖G + H‖ < 2 * τ * ‖F‖ := by
    have := norm_add_le G H
    nlinarith
  have hGH := norm_nonneg (G + H)
  nlinarith

/-! ### The criterion -/

variable {j : ℕ} [NeZero j]

set_option maxHeartbeats 1000000 in
/-- **Lemma `lem:criterion`** (the window at scale `τ`, strict on the right). -/
theorem criterion_windowAt (β : ℕ) (hβ : β = 1 ∨ β = 3) (a b c d : ZMod j → ℝ)
    (S : Fin 4 → Finset (ZMod j)) (k : ℝ) (hS : ∀ i, ((S i).card : ℝ) = k) (τ : ℝ) (hτ : 0 < τ)
    (hK : WindowAt (Kmat β ![vsum a, vsum b, vsum c, vsum d] k j) τ)
    (hwin : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      τ + deltaL S ℓ ≤ Real.sqrt (energy a b c d ℓ) ∧
        Real.sqrt (energy a b c d ℓ) < 2 * τ - deltaL S ℓ) :
    WindowAt (Xmat β a b c d S) τ := by
  set σ := sigmaOf β with hσdef
  have hσ2 : σ ^ 2 = 1 := by
    rcases hβ with rfl | rfl <;> simp [hσdef, sigmaOf] <;> norm_num
  set M := Zgs a b c d + Fmat σ S with hMdef
  set r : Fin 4 → ℝ := ![vsum a, vsum b, vsum c, vsum d] with hrdef
  set K0 := quat r - (2 * k * σ) • Pimat with hK0def
  have hj0 : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne j)
  set sj := Real.sqrt (j : ℝ) with hsjdef
  have hsj0 : 0 < sj := Real.sqrt_pos.2 hj0
  have hsj2 : sj ^ 2 = j := Real.sq_sqrt hj0.le
  rw [windowAt_iff_form]
  intro y
  have hypos : y ≠ 0 → 0 < y ⬝ᵥ y := fun hy => dot_self_pos hy
  -- notation
  set w : Fin 4 → ZMod j → ℝ := fun q u => y (.inl (q, u)) with hwdef
  set y' : Fin β → ℝ := fun e => y (.inr e) with hy'def
  set Vy : Fin 4 → ℝ := fun p => ∑ e, Vb β p e * y' e with hVydef
  set φ0 : Fin 4 → ℝ := fun q => vsum (w q) with hφ0def
  set T : Fin 4 → ZMod j → ℝ := fun p v => colOut M w p v + Vy p with hTdef
  set bot : Fin β → ℝ := fun e => ∑ q, Ub β q e * φ0 q + ∑ e', Gb β e' e * y' e' with hbotdef
  set Φ : ZMod j → ℝ := fun ℓ => ∑ q, ‖dft (cx (w q)) ℓ‖ ^ 2 with hΦdef
  set A : ZMod j → ℝ := fun ℓ => ∑ p, ‖dft (cx (T p)) ℓ‖ ^ 2 with hAdef
  have hXy : ((Xmat β a b c d S)ᵀ *ᵥ y) ⬝ᵥ ((Xmat β a b c d S)ᵀ *ᵥ y) =
      ∑ p, ∑ v, T p v ^ 2 + ∑ e, bot e ^ 2 := by
    simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, Xt_inl, Xt_inr, sq]
    rfl
  have hyy : y ⬝ᵥ y = ∑ q, ∑ u, w q u ^ 2 + ∑ e, y' e ^ 2 := by
    simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, sq]
    rfl
  have hparT : ∑ p, ∑ v, T p v ^ 2 = (∑ ℓ, A ℓ) / j := by
    have h1 : ∀ p, ∑ v, T p v ^ 2 = (∑ ℓ, ‖dft (cx (T p)) ℓ‖ ^ 2) / j := fun p => by
      rw [parseval_real, mul_div_cancel_left₀ _ hj0.ne']
    rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.sum_div, Finset.sum_comm]
  have hparw : ∑ q, ∑ u, w q u ^ 2 = (∑ ℓ, Φ ℓ) / j := by
    have h1 : ∀ q, ∑ u, w q u ^ 2 = (∑ ℓ, ‖dft (cx (w q)) ℓ‖ ^ 2) / j := fun q => by
      rw [parseval_real, mul_div_cancel_left₀ _ hj0.ne']
    rw [Finset.sum_congr rfl fun q _ => h1 q, ← Finset.sum_div, Finset.sum_comm]
  have hT : ∀ p ℓ, dft (cx (T p)) ℓ =
      dft (cx (colOut M w p)) ℓ + if ℓ = 0 then (j : ℂ) * (Vy p : ℂ) else 0 := by
    intro p ℓ
    have : cx (T p) = cx (colOut M w p) + fun _ => (Vy p : ℂ) := by
      funext v; simp [cx, hTdef]
    rw [this, dft_add, dft_const]
  -- nonzero frequencies
  have hfreq : ∀ ℓ : ZMod j, ℓ ≠ 0 → τ ^ 2 * Φ ℓ ≤ A ℓ ∧ A ℓ ≤ 4 * τ ^ 2 * Φ ℓ ∧
      (0 < Φ ℓ → A ℓ < 4 * τ ^ 2 * Φ ℓ) := by
    intro ℓ hℓ
    have hval1 : 1 ≤ ℓ.val := Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
    have hcast : ((ℓ.val : ℕ) : ZMod j) = ℓ := ZMod.natCast_zmod_val ℓ
    obtain ⟨hw1, hw2⟩ := hwin ℓ.val hval1 (ZMod.val_lt ℓ)
    have hE : energy a b c d ℓ.val =
        ‖dft (cx a) ℓ‖ ^ 2 + ‖dft (cx b) ℓ‖ ^ 2 + ‖dft (cx c) ℓ‖ ^ 2 + ‖dft (cx d) ℓ‖ ^ 2 := by
      simp only [energy, hat_eq_dft, hcast]
    have hs : ∀ i, 2 * ‖dft (cx (ind (S i))) ℓ‖ ≤ deltaL S ℓ.val := by
      intro i
      simp only [deltaL, Shat_eq_dft, hcast]
      have := mul_le_mul_of_nonneg_left (show ‖dft (cx (ind (S i))) ℓ‖ ≤
        max (max ‖dft (cx (ind (S 0))) ℓ‖ ‖dft (cx (ind (S 1))) ℓ‖)
          (max ‖dft (cx (ind (S 2))) ℓ‖ ‖dft (cx (ind (S 3))) ℓ‖) by
        fin_cases i <;> simp) (by norm_num : (0 : ℝ) ≤ 2)
      exact this
    have hdl : 0 ≤ deltaL S ℓ.val :=
      (by positivity : (0 : ℝ) ≤ 2 * ‖dft (cx (ind (S 0))) ℓ‖).trans (hs 0)
    have hA : A ℓ = ∑ p, ‖(gvec (dft (cx a) ℓ) (dft (cx b) ℓ) (dft (cx c) ℓ) (dft (cx d) ℓ)
        (fun q => dft (cx (w q)) ℓ) (fun q => conj (dft (cx (w q)) ℓ)) +
        hvec σ (fun i => dft (cx (ind (S i))) ℓ) (fun q => dft (cx (w q)) ℓ)
          (fun q => conj (dft (cx (w q)) ℓ))) p‖ ^ 2 := by
      simp only [hAdef]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hT, if_neg hℓ, add_zero, hMdef, dft_col_eq]
      simp only [dft_cx_neg, Pi.add_apply]
    have hg := gvec_norm (dft (cx a) ℓ) (dft (cx b) ℓ) (dft (cx c) ℓ) (dft (cx d) ℓ)
      (fun q => dft (cx (w q)) ℓ)
    have hh := hvec_norm hσ2 (fun i => dft (cx (ind (S i))) ℓ) hs (fun q => dft (cx (w q)) ℓ)
    rw [← hE] at hg
    have hE0 : 0 ≤ energy a b c d ℓ.val := by rw [hE]; positivity
    obtain ⟨l1, l2, l3⟩ := freq_window_tau hE0 hdl hτ.le hg hh hw1 hw2
    rw [hA, hΦdef]
    simp only at l1 l2 l3 ⊢
    exact ⟨l1, l2, l3⟩
  -- frequency zero
  set z : Fin 4 ⊕ Fin β → ℝ := Sum.elim (fun m => φ0 m / sj) y' with hzdef
  have hK0p : ∀ p, dft (cx (colOut M w p)) 0 = ((∑ m, K0 m p * φ0 m : ℝ) : ℂ) := by
    intro p
    rw [hMdef, dft_col_zero a b c d σ k S hS w p]
  have hA0 : A 0 / j + ∑ e, bot e ^ 2 = ((Kmat β r k j)ᵀ *ᵥ z) ⬝ᵥ ((Kmat β r k j)ᵀ *ᵥ z) := by
    simp only [dotProduct, Fintype.sum_sum_type, Kt_inl, Kt_inr, hzdef, Sum.elim_inl,
      Sum.elim_inr, hAdef, hT, ↓reduceIte, hK0p, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      have e1 : (((∑ m, K0 m p * φ0 m : ℝ) : ℂ) + (j : ℂ) * (Vy p : ℂ)) =
          (((∑ m, K0 m p * φ0 m) + j * Vy p : ℝ) : ℂ) := by push_cast; ring
      rw [e1, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have e2 : ∑ m, K0 m p * (φ0 m / sj) = (∑ m, K0 m p * φ0 m) / sj := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun m _ => by ring
      rw [← hK0def, e2]
      simp only [hVydef, hy'def]
      rw [← hsj2]
      field_simp
      ring
    · refine Finset.sum_congr rfl fun e _ => ?_
      have e3 : sj * ∑ m, Ub β m e * (φ0 m / sj) = ∑ m, Ub β m e * φ0 m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by field_simp
      rw [e3]
      simp only [hbotdef, sq]
  have hz : Φ 0 / j + ∑ e, y' e ^ 2 = z ⬝ᵥ z := by
    simp only [dotProduct, Fintype.sum_sum_type, hzdef, Sum.elim_inl, Sum.elim_inr, hΦdef,
      dft_cx_zero_freq, Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [← hsj2]; simp only [hφ0def]; field_simp; ring
    · exact Finset.sum_congr rfl fun e _ => by ring
  obtain ⟨k1, k2⟩ := (windowAt_iff_form _ _).1 hK z
  have k2' : ((Kmat β r k j)ᵀ *ᵥ z) ⬝ᵥ ((Kmat β r k j)ᵀ *ᵥ z) ≤ 4 * τ ^ 2 * (z ⬝ᵥ z) := by
    by_cases hz0 : z = 0
    · rw [hz0]; simp
    · exact (k2 hz0).le
  -- sums over nonzero frequencies
  have hsplitA := Finset.add_sum_erase Finset.univ A (Finset.mem_univ 0)
  have hsplitΦ := Finset.add_sum_erase Finset.univ Φ (Finset.mem_univ 0)
  have hlo : ∑ ℓ ∈ Finset.univ.erase 0, τ ^ 2 * Φ ℓ ≤ ∑ ℓ ∈ Finset.univ.erase 0, A ℓ :=
    Finset.sum_le_sum fun ℓ hℓ => (hfreq ℓ (Finset.ne_of_mem_erase hℓ)).1
  have hhi : ∑ ℓ ∈ Finset.univ.erase 0, A ℓ ≤ ∑ ℓ ∈ Finset.univ.erase 0, 4 * τ ^ 2 * Φ ℓ :=
    Finset.sum_le_sum fun ℓ hℓ => (hfreq ℓ (Finset.ne_of_mem_erase hℓ)).2.1
  have hstrict : 0 < ∑ ℓ ∈ Finset.univ.erase 0, Φ ℓ →
      ∑ ℓ ∈ Finset.univ.erase 0, A ℓ < ∑ ℓ ∈ Finset.univ.erase 0, 4 * τ ^ 2 * Φ ℓ := by
    intro hpos
    have h0 : ∑ _ℓ ∈ Finset.univ.erase (0 : ZMod j), (0 : ℝ) <
        ∑ ℓ ∈ Finset.univ.erase 0, Φ ℓ := by
      rw [Finset.sum_const_zero]; exact hpos
    obtain ⟨ℓ, hℓ, hlt⟩ := Finset.exists_lt_of_sum_lt h0
    exact Finset.sum_lt_sum (fun i hi => (hfreq i (Finset.ne_of_mem_erase hi)).2.1)
      ⟨ℓ, hℓ, (hfreq ℓ (Finset.ne_of_mem_erase hℓ)).2.2 hlt⟩
  rw [← Finset.mul_sum] at hlo hhi hstrict
  rw [hyy, hparw, ← hsplitΦ] at hypos
  rw [hXy, hyy, hparT, hparw, ← hsplitA, ← hsplitΦ]
  set SA := ∑ ℓ ∈ Finset.univ.erase 0, A ℓ
  set SΦ := ∑ ℓ ∈ Finset.univ.erase 0, Φ ℓ
  have eX : (A 0 + SA) / j + ∑ e, bot e ^ 2 = SA / j + (A 0 / j + ∑ e, bot e ^ 2) := by ring
  have eY : (Φ 0 + SΦ) / j + ∑ e, y' e ^ 2 = SΦ / j + (Φ 0 / j + ∑ e, y' e ^ 2) := by ring
  rw [eY, hz] at hypos
  rw [eX, eY, hA0, hz]
  have d1 : τ ^ 2 * SΦ / j ≤ SA / j := div_le_div_of_nonneg_right hlo hj0.le
  have d2 : SA / j ≤ 4 * τ ^ 2 * SΦ / j := div_le_div_of_nonneg_right hhi hj0.le
  have f1 : τ ^ 2 * SΦ / j = τ ^ 2 * (SΦ / j) := by ring
  have f2 : 4 * τ ^ 2 * SΦ / j = 4 * τ ^ 2 * (SΦ / j) := by ring
  refine ⟨by linarith, fun hy => ?_⟩
  have hp := hypos hy
  rcases lt_or_le 0 SΦ with hS | hS
  · have d3 : SA / j < 4 * τ ^ 2 * SΦ / j := div_lt_div_of_pos_right (hstrict hS) hj0
    nlinarith
  · have hSj : SΦ / j ≤ 0 := div_nonpos_of_nonpos_of_nonneg hS hj0.le
    have hzpos : 0 < z ⬝ᵥ z := by linarith
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, dotProduct_zero] at hzpos; exact lt_irrefl _ hzpos
    have := k2 hz0
    nlinarith

/-- **Lemma `lem:criterion`** with the paper's hypotheses (sign sequences, masks of size `k`
satisfying eq. `pools`); the conclusion includes `κ(X) < 2` as `CondLt2`. -/
theorem lem_criterion_tau_aux (β : ℕ) (hβ : β = 1 ∨ β = 3) (a b c d : ZMod j → ℝ)
    (S : Fin 4 → Finset (ZMod j)) (k : ℕ) (hS : ∀ i, (S i).card = k) (τ : ℝ) (hτ : 0 < τ)
    (hK : WindowAt (Kmat β ![vsum a, vsum b, vsum c, vsum d] k j) τ)
    (hwin : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      τ + deltaL S ℓ ≤ Real.sqrt (energy a b c d ℓ) ∧
        Real.sqrt (energy a b c d ℓ) < 2 * τ - deltaL S ℓ) :
    WindowAt (Xmat β a b c d S) τ ∧ CondLt2 (Xmat β a b c d S) := by
  have hW := criterion_windowAt β hβ a b c d S k (fun i => by rw [hS i]) τ hτ hK hwin
  exact ⟨hW, condLt2_of_windowAt hτ hW⟩

/-- **Lemma `lem:criterion`.** "Let `a,b,c,d` be sign sequences of length `j` with sums
`s=(s_0,s_1,s_2,s_3)`, let `S_0,\dots,S_3` be masks of size `k` satisfying \eqref{eq:pools}, and
let `X` be the matrix in \eqref{eq:X}. Put `\delta_\ell=2\max_i|\widehat{S_i}(\ell)|`, and let
`K=\begin{pmatrix}\mathcal{Q}(s)-2k\sigma\Pi&\sqrt{j}\,U_\beta\\\sqrt{j}\,V_\beta^\top&G_\beta
\end{pmatrix}`. Let `\tau>0`, and suppose that `\tau^2I\preceq KK^\top\prec4\tau^2I` and that
`\tau+\delta_\ell\le\sqrt{E_\ell}<2\tau-\delta_\ell` for `1\le\ell<j`. Then
`\tau^2I\preceq XX^\top\prec4\tau^2I`. In particular, `\kappa(X)<2`."

(The hypotheses "sign sequences" and eq. `pools` are kept to mirror the paper; the window does not
need them.) -/
theorem lem_criterion_tau (β : ℕ) (hβ : β = 1 ∨ β = 3) (a b c d : ZMod j → ℝ)
    (_ha : IsSignVec a) (_hb : IsSignVec b) (_hc : IsSignVec c) (_hd : IsSignVec d)
    (S : Fin 4 → Finset (ZMod j)) (k : ℕ) (hS : ∀ i, (S i).card = k)
    (_hpools : Pools (sigmaOf β) a b c d S) (τ : ℝ) (hτ : 0 < τ)
    (hK : WindowAt (Kmat β ![vsum a, vsum b, vsum c, vsum d] k j) τ)
    (hwin : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      τ + deltaL S ℓ ≤ Real.sqrt (energy a b c d ℓ) ∧
        Real.sqrt (energy a b c d ℓ) < 2 * τ - deltaL S ℓ) :
    WindowAt (Xmat β a b c d S) τ ∧ CondLt2 (Xmat β a b c d S) :=
  lem_criterion_tau_aux β hβ a b c d S k hS τ hτ hK hwin

end SignCond
