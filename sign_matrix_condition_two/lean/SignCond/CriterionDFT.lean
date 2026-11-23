import SignCond.Fourier
import SignCond.SectorMatrix

/-!
# The repaired array `Z + F` at one frequency (proof of Lemma `lem:criterion`)

Every block of `Z + F` has entries `κ₁(v-u) + κ₂(-u-v) + κ₃(u+v)` for three kernels taken from the
tables `kern1`, `kern2`, `kern3` (`ZF_apply`). By the rules of `Fourier.lean`, column block `p` of
`(Z+F)ᵀ w` has transform `Σ_q κ̂₁(ℓ)ŵ_q(ℓ) + κ̂₂(-ℓ)ŵ_q(-ℓ) + κ̂₃(ℓ)ŵ_q(-ℓ)` (`dft_col`).
For real data this is `gvec + hvec` (`dft_col_eq`), where `gvec` comes from `Z` and is an isometry up
to the factor `√E_ℓ` (`gvec_norm`, the Goethals–Seidel identity at one frequency), and `hvec` comes
from `F` and has norm at most `δ_ℓ ‖φ‖` (`hvec_norm`). `freq_window` combines them as in eq.
`sectorbound` of the paper.
-/

open Complex ComplexConjugate Matrix Finset
open scoped Real

namespace SignCond

variable {j : ℕ} [NeZero j]

/-! ### Linearity of `cx` -/

omit [NeZero j] in
theorem cx_add (x y : ZMod j → ℝ) : cx (x + y) = cx x + cx y := by
  funext u; simp [cx]

omit [NeZero j] in
theorem cx_neg (x : ZMod j → ℝ) : cx (-x) = -cx x := by
  funext u; simp [cx]

omit [NeZero j] in
theorem cx_sub (x y : ZMod j → ℝ) : cx (x - y) = cx x - cx y := by
  funext u; simp [cx]

omit [NeZero j] in
theorem cx_smul (r : ℝ) (x : ZMod j → ℝ) : cx (r • x) = (r : ℂ) • cx x := by
  funext u; simp [cx]

omit [NeZero j] in
theorem cx_zero : cx (0 : ZMod j → ℝ) = 0 := by
  funext u; simp [cx]

theorem dft_zero (ℓ : ZMod j) : dft (0 : ZMod j → ℂ) ℓ = 0 := by simp [dft]

theorem dft_sub (v w : ZMod j → ℂ) (ℓ : ZMod j) : dft (v - w) ℓ = dft v ℓ - dft w ℓ := by
  rw [sub_eq_add_neg, dft_add, dft_neg, ← sub_eq_add_neg]

/-! ### The kernel tables -/

/-- Kernels `κ₁` (entries `κ₁(v-u)`) of the blocks `(q, p)` of `Z + F`. -/
def kern1 (a : ZMod j → ℝ) (σ : ℝ) (S : Fin 4 → Finset (ZMod j)) : Fin 4 → Fin 4 → ZMod j → ℝ :=
  ![![a + (2 * σ) • ind (S 0), 0, 0, 0], ![0, a, 0, 0], ![0, 0, a, 0], ![0, 0, 0, a]]

/-- Kernels `κ₂` (entries `κ₂(-u-v)`). -/
def kern2 (b c d : ZMod j → ℝ) : Fin 4 → Fin 4 → ZMod j → ℝ :=
  ![![0, b, c, d], ![-b, 0, 0, 0], ![-c, 0, 0, 0], ![-d, 0, 0, 0]]

/-- Kernels `κ₃` (entries `κ₃(u+v)`). -/
def kern3 (b c d : ZMod j → ℝ) (σ : ℝ) (S : Fin 4 → Finset (ZMod j)) :
    Fin 4 → Fin 4 → ZMod j → ℝ :=
  ![![0, 0, 0, 0], ![0, 0, -d, c - (2 * σ) • ind (S 1)],
    ![0, d - (2 * σ) • ind (S 2), 0, -b], ![0, -c, b - (2 * σ) • ind (S 3), 0]]

theorem ZF_apply (a b c d : ZMod j → ℝ) (σ : ℝ) (S : Fin 4 → Finset (ZMod j)) (q p : Fin 4)
    (u v : ZMod j) :
    (Zgs a b c d + Fmat σ S) (q, u) (p, v) =
      kern1 a σ S q p (v - u) + kern2 b c d q p (-u - v) + kern3 b c d σ S q p (u + v) := by
  have e1 : -v - u = -u - v := by ring
  have e2 : u - -v = u + v := by ring
  fin_cases q <;> fin_cases p <;>
    simp only [Zgs, Fmat, Matrix.add_apply, gsArray_apply, gsTable, Matrix.smul_apply,
      Matrix.comp_apply, kern1, kern2, kern3, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.neg_apply, Matrix.zero_apply,
      mul_rev_apply, transpose_apply, circ_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      Pi.sub_apply, Pi.zero_apply, smul_eq_mul, e1, e2] <;> ring

/-! ### One block at one frequency -/

theorem dft_block (k1 k2 k3 w : ZMod j → ℝ) (ℓ : ZMod j) :
    dft (cx fun v => ∑ u, (k1 (v - u) + k2 (-u - v) + k3 (u + v)) * w u) ℓ =
      dft (cx k1) ℓ * dft (cx w) ℓ + dft (cx k2) (-ℓ) * dft (cx w) (-ℓ) +
        dft (cx k3) ℓ * dft (cx w) (-ℓ) := by
  have h : (cx fun v => ∑ u, (k1 (v - u) + k2 (-u - v) + k3 (u + v)) * w u) =
      (fun v => ∑ u, cx k1 (v - u) * cx w u) + (fun v => ∑ u, cx k2 (-u - v) * cx w u) +
        (fun v => ∑ u, cx k3 (u + v) * cx w u) := by
    funext v
    simp only [cx, Pi.add_apply, ← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [h, dft_add, dft_add, dft_conv1, dft_conv2, dft_conv3]

/-- Column block `p` of `(Z + F)ᵀ w` for `w = (w_q)_q`. -/
def colOut (M : Matrix (Fin 4 × ZMod j) (Fin 4 × ZMod j) ℝ) (w : Fin 4 → ZMod j → ℝ) (p : Fin 4) :
    ZMod j → ℝ := fun v => ∑ q, ∑ u, M (q, u) (p, v) * w q u

theorem dft_col (a b c d : ZMod j → ℝ) (σ : ℝ) (S : Fin 4 → Finset (ZMod j))
    (w : Fin 4 → ZMod j → ℝ) (p : Fin 4) (ℓ : ZMod j) :
    dft (cx (colOut (Zgs a b c d + Fmat σ S) w p)) ℓ =
      ∑ q, (dft (cx (kern1 a σ S q p)) ℓ * dft (cx (w q)) ℓ +
        dft (cx (kern2 b c d q p)) (-ℓ) * dft (cx (w q)) (-ℓ) +
        dft (cx (kern3 b c d σ S q p)) ℓ * dft (cx (w q)) (-ℓ)) := by
  rw [← Finset.sum_congr rfl fun q _ => dft_block _ _ _ (w q) ℓ]
  have : cx (colOut (Zgs a b c d + Fmat σ S) w p) =
      ∑ q, cx fun v => ∑ u, (kern1 a σ S q p (v - u) + kern2 b c d q p (-u - v) +
        kern3 b c d σ S q p (u + v)) * w q u := by
    funext v
    simp only [cx, colOut, ZF_apply, Finset.sum_apply]
    push_cast
    rfl
  rw [this]
  simp only [dft, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul]

/-! ### The explicit vectors -/

/-- The `Z`-part at one frequency: with `α = â(ℓ)`, …, `φ_q = ŵ_q(ℓ)`, `ψ_q = ŵ_q(-ℓ)`. -/
def gvec (α β γ δ : ℂ) (φ ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![α * φ 0 - conj β * ψ 1 - conj γ * ψ 2 - conj δ * ψ 3,
    conj β * ψ 0 + α * φ 1 + δ * ψ 2 - γ * ψ 3,
    conj γ * ψ 0 - δ * ψ 1 + α * φ 2 + β * ψ 3,
    conj δ * ψ 0 + γ * ψ 1 - β * ψ 2 + α * φ 3]

/-- The `F`-part at one frequency: `s_i = Ŝ_i(ℓ)`. -/
def hvec (σ : ℝ) (s : Fin 4 → ℂ) (φ ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![2 * σ * s 0 * φ 0, -(2 * σ) * s 2 * ψ 2, -(2 * σ) * s 3 * ψ 3, -(2 * σ) * s 1 * ψ 1]

theorem dft_col_eq (a b c d : ZMod j → ℝ) (σ : ℝ) (S : Fin 4 → Finset (ZMod j))
    (w : Fin 4 → ZMod j → ℝ) (p : Fin 4) (ℓ : ZMod j) :
    dft (cx (colOut (Zgs a b c d + Fmat σ S) w p)) ℓ =
      gvec (dft (cx a) ℓ) (dft (cx b) ℓ) (dft (cx c) ℓ) (dft (cx d) ℓ)
          (fun q => dft (cx (w q)) ℓ) (fun q => dft (cx (w q)) (-ℓ)) p +
        hvec σ (fun i => dft (cx (ind (S i))) ℓ) (fun q => dft (cx (w q)) ℓ)
          (fun q => dft (cx (w q)) (-ℓ)) p := by
  rw [dft_col]
  simp only [Fin.sum_univ_four]
  fin_cases p <;>
    simp only [kern1, kern2, kern3, gvec, hvec, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cx_add, cx_neg, cx_sub, cx_smul, cx_zero,
      dft_add, dft_neg, dft_sub, dft_smul, dft_zero, dft_cx_neg] <;> push_cast <;> ring

/-! ### Norms at one frequency -/

theorem gvec_norm (α β γ δ : ℂ) (φ : Fin 4 → ℂ) :
    ∑ p, ‖gvec α β γ δ φ (fun q => conj (φ q)) p‖ ^ 2 =
      (‖α‖ ^ 2 + ‖β‖ ^ 2 + ‖γ‖ ^ 2 + ‖δ‖ ^ 2) * ∑ q, ‖φ q‖ ^ 2 := by
  simp only [Fin.sum_univ_four, gvec, Complex.sq_norm, Complex.normSq_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem hvec_norm {σ dl : ℝ} (hσ : σ ^ 2 = 1) (s : Fin 4 → ℂ) (hs : ∀ i, 2 * ‖s i‖ ≤ dl)
    (φ : Fin 4 → ℂ) :
    ∑ p, ‖hvec σ s φ (fun q => conj (φ q)) p‖ ^ 2 ≤ dl ^ 2 * ∑ q, ‖φ q‖ ^ 2 := by
  have h2 : ∀ i, (2 * ‖s i‖) ^ 2 ≤ dl ^ 2 := fun i =>
    pow_le_pow_left₀ (by positivity) (hs i) 2
  have e : ∀ (i : Fin 4) (z : ℂ), ‖2 * σ * s i * z‖ ^ 2 = (2 * ‖s i‖) ^ 2 * ‖z‖ ^ 2 := by
    intro i z
    rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, hσ]
    simp
  have e' : ∀ (i : Fin 4) (z : ℂ), ‖-(2 * σ) * s i * z‖ ^ 2 = (2 * ‖s i‖) ^ 2 * ‖z‖ ^ 2 := by
    intro i z
    rw [neg_mul, neg_mul, norm_neg, e]
  simp only [Fin.sum_univ_four, hvec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e, e',
    Complex.norm_conj]
  have := mul_le_mul_of_nonneg_right (h2 0) (sq_nonneg ‖φ 0‖)
  have := mul_le_mul_of_nonneg_right (h2 1) (sq_nonneg ‖φ 1‖)
  have := mul_le_mul_of_nonneg_right (h2 2) (sq_nonneg ‖φ 2‖)
  have := mul_le_mul_of_nonneg_right (h2 3) (sq_nonneg ‖φ 3‖)
  nlinarith

/-- `Fin 4 → ℂ` as a Euclidean space. -/
noncomputable def e4 (g : Fin 4 → ℂ) : EuclideanSpace ℂ (Fin 4) := (WithLp.equiv 2 _).symm g

theorem norm_e4_sq (g : Fin 4 → ℂ) : ‖e4 g‖ ^ 2 = ∑ i, ‖g i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

theorem e4_add (g h : Fin 4 → ℂ) : e4 (g + h) = e4 g + e4 h := rfl

/-- Eq. `sectorbound` at one frequency: if `‖g‖² = E ‖φ‖²`, `‖h‖² ≤ δ² ‖φ‖²` and
`ρ + δ ≤ √E ≤ 2ρ - δ` (with `ρ, δ ≥ 0`), then `ρ² ‖φ‖² ≤ ‖g + h‖² ≤ 4ρ² ‖φ‖²`. -/
theorem freq_window {g h φ : Fin 4 → ℂ} {E dl ρ : ℝ} (hE0 : 0 ≤ E) (hdl : 0 ≤ dl) (hρ : 0 ≤ ρ)
    (hg : ∑ i, ‖g i‖ ^ 2 = E * ∑ i, ‖φ i‖ ^ 2) (hh : ∑ i, ‖h i‖ ^ 2 ≤ dl ^ 2 * ∑ i, ‖φ i‖ ^ 2)
    (hw1 : ρ + dl ≤ Real.sqrt E) (hw2 : Real.sqrt E ≤ 2 * ρ - dl) :
    ρ ^ 2 * ∑ i, ‖φ i‖ ^ 2 ≤ ∑ i, ‖(g + h) i‖ ^ 2 ∧
      ∑ i, ‖(g + h) i‖ ^ 2 ≤ 4 * ρ ^ 2 * ∑ i, ‖φ i‖ ^ 2 := by
  have eg := norm_e4_sq g
  have eh := norm_e4_sq h
  have eφ := norm_e4_sq φ
  have egh := norm_e4_sq (g + h)
  rw [← eg, ← eφ] at hg
  rw [← eh, ← eφ] at hh
  rw [← egh, ← eφ, e4_add]
  set G := e4 g
  set H := e4 h
  set F := e4 φ
  have hG : ‖G‖ = Real.sqrt E * ‖F‖ := by
    rw [← Real.sqrt_sq (norm_nonneg G), hg, Real.sqrt_mul hE0, Real.sqrt_sq (norm_nonneg F)]
  have hH : ‖H‖ ≤ dl * ‖F‖ := by
    rw [← Real.sqrt_sq (norm_nonneg H), ← Real.sqrt_sq (mul_nonneg hdl (norm_nonneg F))]
    exact Real.sqrt_le_sqrt (by rw [mul_pow]; exact hh)
  have hF := norm_nonneg F
  have hlo : ρ * ‖F‖ ≤ ‖G + H‖ := by
    have := norm_sub_norm_le G (-H)
    rw [norm_neg, sub_neg_eq_add] at this
    nlinarith
  have hhi : ‖G + H‖ ≤ 2 * ρ * ‖F‖ := by
    have := norm_add_le G H
    nlinarith
  constructor
  · have := pow_le_pow_left₀ (by positivity) hlo 2
    nlinarith
  · have := pow_le_pow_left₀ (norm_nonneg _) hhi 2
    nlinarith

end SignCond
