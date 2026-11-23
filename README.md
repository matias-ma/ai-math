# AI math results

I use this repository to collect mathematical results I get from working with AI. My current focus is proving conjectures from [Open Problems in Numerical Linear Algebra](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main), and I may branch into other areas.

**I’d love to collaborate.** If I’m still working through a proof, or if a result is listed as purely AI, you’re welcome to join me or take the proof and write your own exposition. Even for papers I’ve reviewed and written myself, I’d love to hear where an argument could be simpler or an explanation clearer. Email me at [mati@princeton.edu](mailto:mati@princeton.edu).

## Proofs I’m working through and editing

### IS-04 · A condition number of two for a sign matrix in every dimension

For every positive integer $n$, there is an $n \times n$ matrix with entries in $\{-1,1\}$ whose spectral condition number is at most $2$. The bound is sharp only in dimension $3$, where the best possible condition number is exactly $2$. In every other dimension, some sign matrix has condition number strictly below $2$. [Original conjecture](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/eigenvalues-and-inverse-problems/IS-04)

GPT-6.2 Pro discovered the proof autonomously. AI wrote most of the current manuscript, and I’m working through the argument and editing the paper. The Lean formalization proves the main result in its Gram-matrix formulation, including the finite cases. [Paper](sign_matrix_condition_two/paper.pdf) · [Lean theorem](sign_matrix_condition_two/lean/Verified.lean) · [Verification instructions](sign_matrix_condition_two/README.md)

## Proofs I’ve reviewed and written up myself

None yet.

## Purely AI results

None yet. I’ll list results here when AI has produced the proof and write-up and I haven’t begun my own review.
