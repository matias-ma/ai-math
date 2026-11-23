import SignCond

-- Expect only propext, Classical.choice, and Quot.sound on every `#print axioms` line.

-- ============================================================================
-- Paper.lean: one theorem per numbered result of the paper, in the paper's order
-- ============================================================================
#print axioms SignCond.Paper.thm_main
#print axioms SignCond.Paper.thm_small
#print axioms SignCond.Paper.lem_double
#print axioms SignCond.Paper.lem_three
#print axioms SignCond.Paper.lem_GS
#print axioms SignCond.Paper.lem_criterion
#print axioms SignCond.Paper.lem_sector
#print axioms SignCond.Paper.lem_scales
#print axioms SignCond.Paper.lem_square
#print axioms SignCond.Paper.lem_rows
#print axioms SignCond.Paper.lem_tails
#print axioms SignCond.Paper.lem_select
#print axioms SignCond.Paper.prop_large
#print axioms SignCond.Paper.lem_power
#print axioms SignCond.Paper.lem_tools
#print axioms SignCond.Paper.lem_matching

-- Main supporting results (the proof of thm:main and the explicit matrices)
#print axioms SignCond.main_theorem_tau
#print axioms SignCond.finite_windowAt
#print axioms SignCond.odd_case_tau
#print axioms SignCond.even_case_tau
#print axioms SignCond.condLt2_kronecker_iff
#print axioms SignCond.exists_doubling_lt
#print axioms SignCond.condLt2_W2
#print axioms SignCond.condLt2_A6
#print axioms SignCond.H12_mul_transpose
#print axioms SignCond.condLt2_H12
#print axioms SignCond.prop_large_tau
#print axioms SignCond.lem_criterion_tau
#print axioms SignCond.lem_sector_tau
#print axioms SignCond.lem_rows_rule
#print axioms SignCond.lem_tails_rule
#print axioms SignCond.lem_select

-- Section sec:small: the five exact values and their main steps
#print axioms SignCond.hval_7
#print axioms SignCond.hval_9
#print axioms SignCond.hval_10
#print axioms SignCond.hval_13
#print axioms SignCond.hval_14
#print axioms SignCond.order9_lower
#print axioms SignCond.order13_lower
#print axioms SignCond.order14_lower
#print axioms SignCond.comp_cert
#print axioms SignCond.match_sub
#print axioms SignCond.match4
#print axioms SignCond.no_gram_8IJ
#print axioms SignCond.cert14
#print axioms SignCond.graph6

-- The one computational hypothesis, Proposition prop:finite (printed in full)
#print SignCond.PropFiniteTau
