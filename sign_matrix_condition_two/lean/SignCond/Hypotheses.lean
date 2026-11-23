import SignCond.Defs

/-!
# The computational inputs of the paper, as named propositions

These are the statements the paper verifies by a program rather than by hand. They are not proved
in Lean; every theorem that depends on them takes them as explicit hypotheses.

* `LemSeedsArc`: Lemma `lem:seeds`, part 1 (an interval computation, Section `sec:computation`,
  "Certifying the masks").
* `LemSeedsPools`: Lemma `lem:seeds`, part 3, the pool sizes (a finite check on the explicit
  sequences; the kernel evaluation exceeded this machine's memory budget, see `Seeds.lean`).
* `PropFinite`: Proposition `prop:finite` (a data file of quadruples and matrices checked by a
  program).
-/

open Complex Matrix
open scoped Real

namespace SignCond

/-- Lemma `lem:seeds`, part 1: "We have `|p_{S_7^σ}(e^{iθ})| ≤ 31/5` for `2π/6400 ≤ |θ| ≤ π`, and
`|p_{S_9^σ}(e^{iθ})| ≤ 8` for `2π/16384 ≤ |θ| ≤ π`" (for `σ ∈ {-, +}`). -/
def LemSeedsArc : Prop :=
  ∀ σ : ℤ, (σ = -1 ∨ σ = 1) →
    (∀ θ : ℝ, 2 * π / 6400 ≤ |θ| → |θ| ≤ π → ‖pS (seedSet 7 σ) (exp (θ * I))‖ ≤ 31 / 5) ∧
    (∀ θ : ℝ, 2 * π / 16384 ≤ |θ| → |θ| ≤ π → ‖pS (seedSet 9 σ) (exp (θ * I))‖ ≤ 8)

/-- Lemma `lem:seeds`, part 3 (second half): "both common pools of `(P^{(λ)}, Q^{(λ)})` have at
least `992` elements" for each `λ ∈ {64, 80, 100, 104}`. -/
def LemSeedsPools : Prop :=
  ∀ lam ∈ ({64, 80, 100, 104} : Finset ℕ), ∀ σ : ℤ, (σ = -1 ∨ σ = 1) →
    992 ≤ (pool σ (basePair lam).1 (basePair lam).2).card

/-- Proposition `prop:finite`:
1. "For every `16 ≤ j ≤ 4094` there are sign sequences `a, b, c, d` of length `j` with sums
   `(-s, s, s, s)`, where `s ≥ 1` is an integer with `(2s-2)² ≤ 2j ≤ (2s+2)²`, such that, with
   `ρ = √(2j)`, `(ρ+2)² ≤ E_ℓ ≤ (2ρ-2)²` for `1 ≤ ℓ < j`."
2. "For every odd `n ≤ 63` there are an `n × n` sign matrix `A` and a rational number `t > 0` with
   `tI ⪯ AAᵀ ⪯ 4tI`." -/
def PropFinite : Prop :=
  (∀ (j : ℕ) [NeZero j], 16 ≤ j → j ≤ 4094 →
    ∃ (a b c d : ZMod j → ℝ) (s : ℕ), IsSignVec a ∧ IsSignVec b ∧ IsSignVec c ∧ IsSignVec d ∧
      vsum a = -(s : ℝ) ∧ vsum b = s ∧ vsum c = s ∧ vsum d = s ∧ 1 ≤ s ∧
      (2 * (s : ℝ) - 2) ^ 2 ≤ 2 * j ∧ 2 * (j : ℝ) ≤ (2 * s + 2) ^ 2 ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
        (Real.sqrt (2 * j) + 2) ^ 2 ≤ energy a b c d ℓ ∧
          energy a b c d ℓ ≤ (2 * Real.sqrt (2 * j) - 2) ^ 2) ∧
  (∀ n : ℕ, Odd n → n ≤ 63 → ∃ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ), IsSign A ∧ 0 < t ∧
    (A * Aᵀ - (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
    ((4 * (t : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A * Aᵀ).PosSemidef)

end SignCond
