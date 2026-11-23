import SignCond.Defs

/-!
# The one computational input of the rewritten paper

Proposition `prop:finite` is verified in the paper by a program that checks a data file (Section
`sec:computation`); it is not proved in Lean. It is stated here as the proposition
`PropFiniteTau`, and every theorem that depends on it takes it as an explicit hypothesis.

Compared with `PropFinite` (`Hypotheses.lean`, the older version of the paper): the range of `j`
is `16 ≤ j ≤ 9998` (was `≤ 4094`), the upper energy bound is strict (eq. `finitewindow`), and part
2 excludes `n = 3` and asks for `tI ⪯ AAᵀ ≺ 4tI` (positive definite on the right).
-/

open Matrix

namespace SignCond

/-- **Proposition `prop:finite`** (computational hypothesis).
1. "For every `16\le j\le9998` there are sign sequences `a,b,c,d` of length `j` with sums
   `(-s,s,s,s)`, where `s\ge1` is an integer with `(2s-2)^2\le2j\le(2s+2)^2`, such that, with
   `\rho=\sqrt{2j}`, `(\rho+2)^2\le E_\ell<(2\rho-2)^2` for `1\le\ell<j`."
2. "For every odd `n\le63` with `n\ne3` there are an `n\times n` sign matrix `A` and a rational
   number `t>0` with `tI\preceq AA^\top\prec4tI`."

(Sequences of length `j` are vectors `ZMod j → ℝ`; `t` is a rational number cast to `ℝ`.) -/
def PropFiniteTau : Prop :=
  (∀ (j : ℕ) [NeZero j], 16 ≤ j → j ≤ 9998 →
    ∃ (a b c d : ZMod j → ℝ) (s : ℕ), IsSignVec a ∧ IsSignVec b ∧ IsSignVec c ∧ IsSignVec d ∧
      vsum a = -(s : ℝ) ∧ vsum b = s ∧ vsum c = s ∧ vsum d = s ∧ 1 ≤ s ∧
      (2 * (s : ℝ) - 2) ^ 2 ≤ 2 * j ∧ 2 * (j : ℝ) ≤ (2 * s + 2) ^ 2 ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
        (Real.sqrt (2 * j) + 2) ^ 2 ≤ energy a b c d ℓ ∧
          energy a b c d ℓ < (2 * Real.sqrt (2 * j) - 2) ^ 2) ∧
  (∀ n : ℕ, Odd n → n ≤ 63 → n ≠ 3 →
    ∃ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ), IsSign A ∧ 0 < t ∧
      (A * Aᵀ - (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((4 * (t : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A * Aᵀ).PosDef)

end SignCond
