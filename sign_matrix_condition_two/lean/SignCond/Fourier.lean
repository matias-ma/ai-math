import SignCond.Defs
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Discrete Fourier analysis on `ℤ/jℤ` (used in the proof of Lemma `lem:criterion`)

* `chi k = ω^{k.val}`, an additive character of `ℤ/jℤ`: `chi_add`, `chi_neg`, `norm_chi`,
  `sum_chi_mul` (orthogonality `Σ_k χ(mk) = j [m = 0]`).
* `dft v ℓ = Σ_u v_u χ(ℓu)` for complex vectors; `hat x ℓ = dft x ℓ` (`hat_eq_dft`).
* `parseval`: `Σ_ℓ |v̂(ℓ)|² = j Σ_u |v_u|²`.
* The three transformation rules for the kernels `κ(v-u)`, `κ(-u-v)`, `κ(u+v)` and the rule for
  constant vectors.
-/

open Complex ComplexConjugate Finset
open scoped Real

namespace SignCond

variable {j : ℕ} [NeZero j]

theorem omega_pow_j : omega j ^ j = 1 := by
  have := exp_pow_eq_one (j := j) 1
  simpa [omega] using this

theorem omega_isPrimitiveRoot : IsPrimitiveRoot (omega j) j :=
  Complex.isPrimitiveRoot_exp j (NeZero.ne j)

theorem norm_omega_pow (n : ℕ) : ‖omega j ^ n‖ = 1 :=
  norm_eq_one_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, omega_pow_j, one_pow])
    (NeZero.ne j)

/-- `ω^n` depends only on `n mod j`. -/
theorem omega_pow_mod (n : ℕ) : omega j ^ n = omega j ^ (n % j) := by
  conv_lhs => rw [← Nat.mod_add_div n j, pow_add, pow_mul, omega_pow_j, one_pow, mul_one]

/-- The character `χ(k) = ω^{k.val}`. -/
noncomputable def chi (k : ZMod j) : ℂ := omega j ^ k.val

theorem omega_pow_eq_chi (n : ℕ) : omega j ^ n = chi (n : ZMod j) := by
  rw [chi, ZMod.val_natCast, ← omega_pow_mod]

theorem chi_add (a b : ZMod j) : chi (a + b) = chi a * chi b :=
  pow_val_add omega_pow_j a b

omit [NeZero j] in
theorem chi_zero : chi (0 : ZMod j) = 1 := by simp [chi]

theorem norm_chi (k : ZMod j) : ‖chi k‖ = 1 := norm_omega_pow _

theorem chi_mul_chi_neg (k : ZMod j) : chi k * chi (-k) = 1 := by
  rw [← chi_add, add_neg_cancel, chi_zero]

theorem chi_neg (k : ZMod j) : chi (-k) = conj (chi k) := by
  have h1 := chi_mul_chi_neg k
  have h2 : chi k * conj (chi k) = 1 := by
    rw [mul_conj', norm_chi]; simp
  have hne : chi k ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem chi_mul_val (m k : ZMod j) : chi (m * k) = (omega j ^ m.val) ^ k.val := by
  rw [chi, ← pow_mul, ZMod.val_mul, ← omega_pow_mod]

/-- Sums over `ℤ/jℤ` of functions of the representative. -/
theorem sum_zmod_val {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ k : ZMod j, f k.val = ∑ i ∈ range j, f i := by
  refine Finset.sum_nbij' (fun k => k.val) (fun i => (i : ZMod j)) ?_ ?_ ?_ ?_ ?_
  · intro k _; simpa using ZMod.val_lt k
  · intro i _; simp
  · intro k _; simp
  · intro i hi; simp only [mem_range] at hi; simp [ZMod.val_cast_of_lt hi]
  · intro k _; rfl

/-- Orthogonality: `Σ_k χ(m k) = j` if `m = 0` and `0` otherwise. -/
theorem sum_chi_mul (m : ZMod j) : ∑ k : ZMod j, chi (m * k) = if m = 0 then (j : ℂ) else 0 := by
  simp_rw [chi_mul_val]
  rw [sum_zmod_val (fun i => (omega j ^ m.val) ^ i)]
  split_ifs with hm
  · subst hm; simp
  · have hpos : 0 < m.val := by
      rcases Nat.eq_zero_or_pos m.val with h | h
      · exact absurd ((ZMod.val_eq_zero m).1 h) hm
      · exact h
    have hne : omega j ^ m.val ≠ 1 :=
      omega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt hpos (ZMod.val_lt m)
    have hgeom := mul_geom_sum (omega j ^ m.val) j
    have hj1 : (omega j ^ m.val) ^ j = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, omega_pow_j, one_pow]
    rw [hj1, sub_self] at hgeom
    exact (mul_eq_zero.1 hgeom).resolve_left (sub_ne_zero.2 hne)

/-! ### The transform -/

/-- `v̂(ℓ) = Σ_u v_u χ(ℓu)` for `v : ℤ/jℤ → ℂ`. -/
noncomputable def dft (v : ZMod j → ℂ) (ℓ : ZMod j) : ℂ := ∑ u, v u * chi (ℓ * u)

/-- The real vector `x` as a complex vector. -/
noncomputable def cx (x : ZMod j → ℝ) : ZMod j → ℂ := fun u => (x u : ℂ)

theorem hat_eq_dft (x : ZMod j → ℝ) (ℓ : ℕ) : hat x ℓ = dft (cx x) (ℓ : ZMod j) := by
  unfold hat dft cx
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [omega_pow_eq_chi]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id]

theorem Shat_eq_dft (S : Finset (ZMod j)) (ℓ : ℕ) : Shat S ℓ = dft (cx (ind S)) (ℓ : ZMod j) := by
  unfold Shat dft cx ind
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_eq_zero (s := Finset.filter (fun x => x ∉ S) Finset.univ) (by
    intro x hx; simp only [Finset.mem_filter] at hx; simp [hx.2]), add_zero]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [if_pos hv, omega_pow_eq_chi]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id, one_mul]

theorem dft_add (v w : ZMod j → ℂ) (ℓ : ZMod j) : dft (v + w) ℓ = dft v ℓ + dft w ℓ := by
  simp [dft, add_mul, Finset.sum_add_distrib]

theorem dft_neg (v : ZMod j → ℂ) (ℓ : ZMod j) : dft (-v) ℓ = -dft v ℓ := by
  simp [dft, Finset.sum_neg_distrib]

theorem dft_smul (c : ℂ) (v : ZMod j → ℂ) (ℓ : ZMod j) : dft (c • v) ℓ = c * dft v ℓ := by
  simp [dft, Finset.mul_sum, mul_assoc]

/-- For a real vector, `x̂(-ℓ) = conj x̂(ℓ)`. -/
theorem dft_cx_neg (x : ZMod j → ℝ) (ℓ : ZMod j) : dft (cx x) (-ℓ) = conj (dft (cx x) ℓ) := by
  simp only [dft, cx, map_sum, map_mul, Complex.conj_ofReal, neg_mul, chi_neg]

/-- The constant vector: `ĉ(ℓ) = j c [ℓ = 0]`. -/
theorem dft_const (c : ℂ) (ℓ : ZMod j) : dft (fun _ => c) ℓ = if ℓ = 0 then (j : ℂ) * c else 0 := by
  rw [dft, ← Finset.mul_sum, sum_chi_mul]
  split_ifs <;> ring

/-- Rule (R1): `v ↦ Σ_u κ(v-u) w(u)` has transform `κ̂(ℓ) ŵ(ℓ)`. -/
theorem dft_conv1 (κ w : ZMod j → ℂ) (ℓ : ZMod j) :
    dft (fun v => ∑ u, κ (v - u) * w u) ℓ = dft κ ℓ * dft w ℓ := by
  simp only [dft, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight u) _ _ fun v => ?_
  simp only [Equiv.subRight_apply]
  rw [show ℓ * v = ℓ * (v - u) + ℓ * u by ring, chi_add]
  ring

/-- Rule (R2): `v ↦ Σ_u κ(-u-v) w(u)` has transform `κ̂(-ℓ) ŵ(-ℓ)`. -/
theorem dft_conv2 (κ w : ZMod j → ℂ) (ℓ : ZMod j) :
    dft (fun v => ∑ u, κ (-u - v) * w u) ℓ = dft κ (-ℓ) * dft w (-ℓ) := by
  simp only [dft, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Fintype.sum_equiv (Equiv.subLeft (-u)) _ _ fun v => ?_
  simp only [Equiv.subLeft_apply]
  rw [show ℓ * v = -ℓ * (-u - v) + -ℓ * u by ring, chi_add]
  ring

/-- Rule (R3): `v ↦ Σ_u κ(u+v) w(u)` has transform `κ̂(ℓ) ŵ(-ℓ)`. -/
theorem dft_conv3 (κ w : ZMod j → ℂ) (ℓ : ZMod j) :
    dft (fun v => ∑ u, κ (u + v) * w u) ℓ = dft κ ℓ * dft w (-ℓ) := by
  simp only [dft, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Fintype.sum_equiv (Equiv.addLeft u) _ _ fun v => ?_
  simp only [Equiv.coe_addLeft]
  rw [show ℓ * v = ℓ * (u + v) + -ℓ * u by ring, chi_add]
  ring

/-! ### Parseval -/

theorem ofReal_normSq_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [mul_conj']; push_cast; rfl

/-- **Parseval.** `Σ_ℓ |v̂(ℓ)|² = j Σ_u |v_u|²`. -/
theorem parseval (v : ZMod j → ℂ) : ∑ ℓ, ‖dft v ℓ‖ ^ 2 = j * ∑ u, ‖v u‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ofReal_normSq_eq]
  calc ∑ ℓ, dft v ℓ * conj (dft v ℓ)
      = ∑ ℓ : ZMod j, ∑ u, ∑ w, v u * conj (v w) * chi ((u - w) * ℓ) := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [dft, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
        rw [map_mul, ← chi_neg, show (u - w) * ℓ = ℓ * u + -(ℓ * w) by ring, chi_add]
        ring
    _ = ∑ u, ∑ w, v u * conj (v w) * ∑ ℓ : ZMod j, chi ((u - w) * ℓ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ u, v u * conj (v u) * (j : ℂ) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp_rw [sum_chi_mul, sub_eq_zero]
        rw [Finset.sum_eq_single u]
        · simp
        · intro w _ hw; rw [if_neg (Ne.symm hw)]; ring
        · simp
    _ = (j : ℂ) * ∑ u, v u * conj (v u) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring

/-- Parseval for a real vector. -/
theorem parseval_real (x : ZMod j → ℝ) : ∑ ℓ, ‖dft (cx x) ℓ‖ ^ 2 = j * ∑ u, x u ^ 2 := by
  rw [parseval]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show cx x u = (x u : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end SignCond
