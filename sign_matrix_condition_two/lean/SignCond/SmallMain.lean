import SignCond.Small7
import SignCond.Small9
import SignCond.Small10
import SignCond.Small13
import SignCond.Small14
import SignCond.SmallMatching

/-!
# Section `sec:small`: Theorem `thm:small`

Paper: "We have `h(7)=\sqrt3`, `h(9)=\frac{1+\sqrt{41}}4`, `h(10)=\frac32`,
`h(13)=\frac5{2\sqrt3}`, `h(14)=\sqrt{\frac{13}6}`."

`HVal n c` (`SmallTools.lean`) is the paper's `h(n) = c`: some `n × n` sign matrix satisfies the
window of ratio `c`, and every `n × n` sign matrix satisfying a window of ratio `c' ≥ 0` has
`c ≤ c'`. The five parts are `hval_7` (`Small7.lean`), `hval_9` (`Small9.lean`), `hval_10`
(`Small10.lean`), `hval_13` (`Small13.lean`), `hval_14` (`Small14.lean`); the upper bounds are in
`SmallUpper.lean`.
-/

namespace SignCond

/-- **Theorem `thm:small`.** -/
theorem thm_small : HVal 7 (Real.sqrt 3) ∧ HVal 9 ((1 + Real.sqrt 41) / 4) ∧ HVal 10 (3 / 2) ∧
    HVal 13 (5 / (2 * Real.sqrt 3)) ∧ HVal 14 (Real.sqrt (13 / 6)) :=
  ⟨hval_7, hval_9, hval_10, hval_13, hval_14⟩

end SignCond
