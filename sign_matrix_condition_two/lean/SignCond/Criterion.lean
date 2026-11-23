import SignCond.CriterionDFT

/-!
# Lemma `lem:criterion`

The paper decomposes `ℝ^{4j}` into the constant space `𝒞` and the real frequency spaces `𝒲_ℓ`.
We use the equivalent complex form: by Parseval (`parseval_real`), `‖Xᵀy‖²` and `‖y‖²` are sums over
all frequencies `ℓ ∈ ℤ/jℤ`; at `ℓ ≠ 0` the border does not contribute and `(Z+F)ᵀ` acts through
`gvec + hvec` (`dft_col_eq`), which gives eq. `sectorbound` (`freq_window`); at `ℓ = 0` the
contributions assemble to `‖Kᵀz‖²` for `z = (φ₀/√j, y')`, where `φ₀` are the block sums of `y`
(the coordinates in the basis `e_u ⊗ 𝟙_j/√j` of `𝒞`).
-/

open Complex ComplexConjugate Matrix Finset
open scoped Real

namespace SignCond

variable {j : ℕ} [NeZero j]

theorem dft_zero_freq (v : ZMod j → ℂ) : dft v 0 = ∑ u, v u := by simp [dft, chi_zero]

theorem dft_cx_zero_freq (x : ZMod j → ℝ) : dft (cx x) 0 = (vsum x : ℂ) := by
  rw [dft_zero_freq]; simp [cx, vsum]

theorem vsum_ind (S : Finset (ZMod j)) : vsum (ind S) = S.card := by
  simp [vsum, ind, Finset.sum_ite_mem]

/-! ### The two halves of `Xᵀ y` -/

theorem Xt_inl (β : ℕ) (a b c d : ZMod j → ℝ) (S : Fin 4 → Finset (ZMod j))
    (y : (Fin 4 × ZMod j) ⊕ Fin β → ℝ) (p : Fin 4) (v : ZMod j) :
    ((Xmat β a b c d S)ᵀ *ᵥ y) (.inl (p, v)) =
      colOut (Zgs a b c d + Fmat (sigmaOf β) S) (fun q u => y (.inl (q, u))) p v +
        ∑ e, Vb β p e * y (.inr e) := by
  simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type, Xmat,
    fromBlocks_apply₁₁, fromBlocks_apply₂₁, of_apply, colOut, Fintype.sum_prod_type]

theorem Xt_inr (β : ℕ) (a b c d : ZMod j → ℝ) (S : Fin 4 → Finset (ZMod j))
    (y : (Fin 4 × ZMod j) ⊕ Fin β → ℝ) (e : Fin β) :
    ((Xmat β a b c d S)ᵀ *ᵥ y) (.inr e) =
      ∑ q, Ub β q e * ∑ u, y (.inl (q, u)) + ∑ e', Gb β e' e * y (.inr e') := by
  simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type, Xmat,
    fromBlocks_apply₁₂, fromBlocks_apply₂₂, of_apply, Fintype.sum_prod_type, Finset.mul_sum]

theorem Kt_inl (β : ℕ) (r : Fin 4 → ℝ) (k : ℝ) (z : Fin 4 ⊕ Fin β → ℝ) (p : Fin 4) :
    ((Kmat β r k j)ᵀ *ᵥ z) (.inl p) =
      ∑ m, (quat r - (2 * k * sigmaOf β) • Pimat) m p * z (.inl m) +
        Real.sqrt j * ∑ e, Vb β p e * z (.inr e) := by
  simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type, Kmat,
    fromBlocks_apply₁₁, fromBlocks_apply₂₁, smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem Kt_inr (β : ℕ) (r : Fin 4 → ℝ) (k : ℝ) (z : Fin 4 ⊕ Fin β → ℝ) (e : Fin β) :
    ((Kmat β r k j)ᵀ *ᵥ z) (.inr e) =
      Real.sqrt j * ∑ m, Ub β m e * z (.inl m) + ∑ e', Gb β e' e * z (.inr e') := by
  simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type, Kmat,
    fromBlocks_apply₁₂, fromBlocks_apply₂₂, smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- At frequency `0`, `(Z + F)ᵀ` acts on the block sums `φ₀` as `(𝒬(r) - 2kσΠ)ᵀ`. -/
theorem dft_col_zero (a b c d : ZMod j → ℝ) (σ k : ℝ) (S : Fin 4 → Finset (ZMod j))
    (hS : ∀ i, ((S i).card : ℝ) = k) (w : Fin 4 → ZMod j → ℝ) (p : Fin 4) :
    dft (cx (colOut (Zgs a b c d + Fmat σ S) w p)) 0 =
      ((∑ m, (quat ![vsum a, vsum b, vsum c, vsum d] - (2 * k * σ) • Pimat) m p *
        vsum (w m) : ℝ) : ℂ) := by
  rw [dft_col_eq]
  simp only [neg_zero, dft_cx_zero_freq, vsum_ind, hS, Complex.conj_ofReal]
  fin_cases p <;>
    simp [gvec, hvec, quat, Pimat, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 1000000 in
/-- **Lemma `lem:criterion`** (the window). -/
theorem criterion_window (β : ℕ) (hβ : β = 1 ∨ β = 3) (a b c d : ZMod j → ℝ)
    (S : Fin 4 → Finset (ZMod j)) (k : ℝ) (hS : ∀ i, ((S i).card : ℝ) = k)
    (hK : Window (Kmat β ![vsum a, vsum b, vsum c, vsum d] k j) j)
    (hwin : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      Real.sqrt (2 * j) + deltaL S ℓ ≤ Real.sqrt (energy a b c d ℓ) ∧
        Real.sqrt (energy a b c d ℓ) ≤ 2 * Real.sqrt (2 * j) - deltaL S ℓ) :
    Window (Xmat β a b c d S) j := by
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
  set ρ := Real.sqrt (2 * (j : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = 2 * j := Real.sq_sqrt (by positivity)
  rw [window_iff_form]
  intro y
  -- notation
  set w : Fin 4 → ZMod j → ℝ := fun q u => y (.inl (q, u)) with hwdef
  set y' : Fin β → ℝ := fun e => y (.inr e) with hy'def
  set Vy : Fin 4 → ℝ := fun p => ∑ e, Vb β p e * y' e with hVydef
  set φ0 : Fin 4 → ℝ := fun q => vsum (w q) with hφ0def
  set T : Fin 4 → ZMod j → ℝ := fun p v => colOut M w p v + Vy p with hTdef
  set bot : Fin β → ℝ := fun e => ∑ q, Ub β q e * φ0 q + ∑ e', Gb β e' e * y' e' with hbotdef
  -- `Φ ℓ = Σ_q |ŵ_q(ℓ)|²` and `A ℓ = Σ_p |T̂_p(ℓ)|²`
  set Φ : ZMod j → ℝ := fun ℓ => ∑ q, ‖dft (cx (w q)) ℓ‖ ^ 2 with hΦdef
  set A : ZMod j → ℝ := fun ℓ => ∑ p, ‖dft (cx (T p)) ℓ‖ ^ 2 with hAdef
  -- `‖Xᵀy‖² = Σ_p Σ_v T² + Σ_e bot²`
  have hXy : ((Xmat β a b c d S)ᵀ *ᵥ y) ⬝ᵥ ((Xmat β a b c d S)ᵀ *ᵥ y) =
      ∑ p, ∑ v, T p v ^ 2 + ∑ e, bot e ^ 2 := by
    simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, Xt_inl, Xt_inr, sq]
    rfl
  have hyy : y ⬝ᵥ y = ∑ q, ∑ u, w q u ^ 2 + ∑ e, y' e ^ 2 := by
    simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, sq]
    rfl
  -- Parseval
  have hparT : ∑ p, ∑ v, T p v ^ 2 = (∑ ℓ, A ℓ) / j := by
    have h1 : ∀ p, ∑ v, T p v ^ 2 = (∑ ℓ, ‖dft (cx (T p)) ℓ‖ ^ 2) / j := fun p => by
      rw [parseval_real, mul_div_cancel_left₀ _ hj0.ne']
    rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.sum_div, Finset.sum_comm]
  have hparw : ∑ q, ∑ u, w q u ^ 2 = (∑ ℓ, Φ ℓ) / j := by
    have h1 : ∀ q, ∑ u, w q u ^ 2 = (∑ ℓ, ‖dft (cx (w q)) ℓ‖ ^ 2) / j := fun q => by
      rw [parseval_real, mul_div_cancel_left₀ _ hj0.ne']
    rw [Finset.sum_congr rfl fun q _ => h1 q, ← Finset.sum_div, Finset.sum_comm]
  -- the transform of `T p`
  have hT : ∀ p ℓ, dft (cx (T p)) ℓ =
      dft (cx (colOut M w p)) ℓ + if ℓ = 0 then (j : ℂ) * (Vy p : ℂ) else 0 := by
    intro p ℓ
    have : cx (T p) = cx (colOut M w p) + fun _ => (Vy p : ℂ) := by
      funext v; simp [cx, hTdef]
    rw [this, dft_add, dft_const]
  -- nonzero frequencies
  have hfreq : ∀ ℓ : ZMod j, ℓ ≠ 0 → 2 * j * Φ ℓ ≤ A ℓ ∧ A ℓ ≤ 8 * j * Φ ℓ := by
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
    have hdl : 0 ≤ deltaL S ℓ.val := (by positivity : (0 : ℝ) ≤ 2 * ‖dft (cx (ind (S 0))) ℓ‖).trans (hs 0)
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
    obtain ⟨l1, l2⟩ := freq_window hE0 hdl hρ0 hg hh hw1 hw2
    rw [hA, hΦdef]
    simp only at l1 l2 ⊢
    rw [hρ2] at l1 l2
    constructor <;> linarith
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
  obtain ⟨k1, k2⟩ := (window_iff_form _ _).1 hK z
  -- sums over nonzero frequencies
  have hsplitA := Finset.add_sum_erase Finset.univ A (Finset.mem_univ 0)
  have hsplitΦ := Finset.add_sum_erase Finset.univ Φ (Finset.mem_univ 0)
  have hlo : ∑ ℓ ∈ Finset.univ.erase 0, 2 * j * Φ ℓ ≤ ∑ ℓ ∈ Finset.univ.erase 0, A ℓ :=
    Finset.sum_le_sum fun ℓ hℓ => (hfreq ℓ (Finset.ne_of_mem_erase hℓ)).1
  have hhi : ∑ ℓ ∈ Finset.univ.erase 0, A ℓ ≤ ∑ ℓ ∈ Finset.univ.erase 0, 8 * j * Φ ℓ :=
    Finset.sum_le_sum fun ℓ hℓ => (hfreq ℓ (Finset.ne_of_mem_erase hℓ)).2
  rw [← Finset.mul_sum] at hlo hhi
  rw [hXy, hyy, hparT, hparw, ← hsplitA, ← hsplitΦ]
  set SA := ∑ ℓ ∈ Finset.univ.erase 0, A ℓ
  set SΦ := ∑ ℓ ∈ Finset.univ.erase 0, Φ ℓ
  have eX : (A 0 + SA) / j + ∑ e, bot e ^ 2 = SA / j + (A 0 / j + ∑ e, bot e ^ 2) := by ring
  have eY : (Φ 0 + SΦ) / j + ∑ e, y' e ^ 2 = SΦ / j + (Φ 0 / j + ∑ e, y' e ^ 2) := by ring
  rw [eX, eY, hA0, hz]
  have d1 : 2 * j * SΦ / j ≤ SA / j := div_le_div_of_nonneg_right hlo hj0.le
  have d2 : SA / j ≤ 8 * j * SΦ / j := div_le_div_of_nonneg_right hhi hj0.le
  have f1 : 2 * (j : ℝ) * SΦ / j = 2 * j * (SΦ / j) := by ring
  have f2 : 8 * (j : ℝ) * SΦ / j = 8 * j * (SΦ / j) := by ring
  constructor <;> linarith

end SignCond
