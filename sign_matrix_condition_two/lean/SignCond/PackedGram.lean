import SignCond.FinitePacking
import SignCond.FiniteGram

namespace SignCond.FiniteGram
open Matrix FinitePacking
variable {n : ℕ} [NeZero n]

/-- Project each matrix row onto the radix powers. -/
def project (z : ℤ) (M : IMat n) (i : Fin n) : ℤ :=
  ∑ j, M i j * z^j.val

private theorem project_add (z : ℤ) (M N : IMat n) (i : Fin n) :
    project z (M+N) i = project z M i + project z N i := by simp [project,add_mul,Finset.sum_add_distrib]

private theorem project_sub (z : ℤ) (M N : IMat n) (i : Fin n) :
    project z (M-N) i = project z M i - project z N i := by simp [project,sub_mul,Finset.sum_sub_distrib]

private theorem project_smul (z k : ℤ) (M : IMat n) (i : Fin n) :
    project z (k • M) i = k * project z M i := by simp [project,mul_assoc,Finset.mul_sum]

private theorem project_one (z : ℤ) (i : Fin n) : project z 1 i = z^i.val := by
  simp [project,Matrix.one_apply,ite_mul]

private theorem project_mul (z : ℤ) (A B : IMat n) (i : Fin n) :
    project z (A*B) i = ∑ k, A i k * project z B k := by
  simp only [project,Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

private theorem project_inj (z : ℤ) (hz : 1 < z) (M N : IMat n)
    (hd : ∀ i j, |M i j - N i j| < z)
    (h : ∀ i, project z M i = project z N i) : M = N := by
  ext i j
  have eq0 : pack z (fun k => M i (k:Fin n) - N i (k:Fin n)) n = 0 := by
    rw [pack_sum, ← Fin.sum_univ_eq_sum_range]
    simpa [project,sub_mul,Finset.sum_sub_distrib] using sub_eq_zero.mpr (h i)
  have hh := pack_zero_digits hz (v := fun k => M i (k:Fin n) - N i (k:Fin n))
    (fun k _ => hd _ _) eq0 j.val j.isLt
  simpa using sub_eq_zero.mp hh

private theorem gram_bound (A : IMat n) (C : ℕ) (h : ∀ i k, |A i k| ≤ (C:ℤ)) (i j : Fin n) :
    |(A*Aᵀ) i j| ≤ n*(C:ℤ)^2 := by
  rw [Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Fin n, (C:ℤ)^2 := Finset.sum_le_sum fun k _ => by
      rw [abs_mul,pow_two]; exact mul_le_mul (h i k) (h j k) (abs_nonneg _) (by positivity)
    _ = _ := by simp [nsmul_eq_mul]

def gramCode (z : ℤ) (A : IMat n) (i : Fin n) := ∑ k, A i k * project z Aᵀ k

/-- Signed multipliers cover both the upper and lower Gram inequalities. -/
theorem gramEq (A B R : IMat n) (m a z : ℤ) (C D : ℕ)
    (hz : 1 < z) (hs : ∀ i k, |A i k| ≤ 1)
    (hB : ∀ i k, |B i k| ≤ (C:ℤ)) (hR : ∀ i k, |R i k| ≤ (D:ℤ))
    (hw : |m| * n + |a| + n*(C:ℤ)^2 + D < z)
    (hcheck : ∀ i, m * gramCode z A i + a * z^i.val = gramCode z B i + project z R i) :
    m • (A*Aᵀ) + a • 1 = B*Bᵀ+R := by
  apply project_inj z hz
  · intro i j
    have ha := gram_bound A 1 hs i j
    have hb := gram_bound B C hB i j
    simp only [Nat.cast_one, one_pow, mul_one] at ha
    have hI : |((1:IMat n) i j)| ≤ 1 := by simp [Matrix.one_apply]; split <;> norm_num
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    apply (abs_sub _ _).trans_lt
    refine lt_of_le_of_lt (add_le_add (abs_add_le _ _) (abs_add_le _ _)) ?_
    simp only [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left ha (abs_nonneg m),
      mul_le_mul_of_nonneg_left hI (abs_nonneg a),hR i j]
  · simpa only [project_add,project_smul,project_one,project_mul,gramCode] using hcheck

end SignCond.FiniteGram
