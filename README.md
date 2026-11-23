# AI math results

I have a broad interest in the problems collected in [Open Problems in Numerical Linear Algebra](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main). I’ve worked with ChatGPT and Claude to obtain the results collected here. My current focus is on conjectures from that collection, and I may branch into other areas of mathematics.

**I’d love to collaborate.** If I’m still working through a proof, or if a result is listed as purely AI, you’re welcome to join me or take the proof and write your own exposition. Even for papers I’ve reviewed and written myself, I’d love to hear where an argument could be simpler or an explanation clearer. If you’re curious how I work with ChatGPT and Claude on mathematical problems, or want to try this on a problem of your own, I’d be happy to share what I’ve learned. Email me at [mati@princeton.edu](mailto:mati@princeton.edu).

## Proofs I’m working through and editing

### IS-04 · A condition number of two for a sign matrix in every dimension

For every positive integer $n$, there is an $n \times n$ matrix with entries in $\{-1,1\}$ whose spectral condition number is at most $2$. The bound is sharp only in dimension $3$, where the best possible condition number is exactly $2$. In every other dimension, some sign matrix has condition number strictly below $2$. [Original conjecture](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/eigenvalues-and-inverse-problems/IS-04)

GPT-6.2 Pro discovered the proof autonomously. AI wrote most of the current manuscript, and I’m working through the argument and editing the paper. The Lean formalization proves the main result in its Gram-matrix formulation, including the finite cases. [Paper](sign_matrix_condition_two/paper.pdf) · [Lean theorem](sign_matrix_condition_two/lean/Verified.lean) · [Verification instructions](sign_matrix_condition_two/README.md)

### A Hadamard matrix with growth factor greater than its order

The conjecture was that every completely pivoted Hadamard matrix has growth factor equal to its order. A row and column permutation of the order-4096 Sylvester Hadamard matrix gives a counterexample. Its 4,089th pivot has magnitude 4,608, and this is the largest pivot. The construction extends to every order $n=2^d$ with $d\ge 12$, giving growth factor $9n/8$. GPT-6 Astra Pro found the counterexample, and I’m continuing to review and edit the paper. [Paper](hadamard_order_4096/paper.pdf)

The [explicit matrix](hadamard_order_4096/matrix.npy) is included. To check it directly, run the following from the repository root with NumPy 2.0 or later. The script verifies row orthogonality and checks all 4,096 complete-pivoting steps in exact arithmetic.

```sh
python3 hadamard_order_4096/verify_dense.py
```

For a separate check using only the Python standard library, run `python3 hadamard_order_4096/verify_construction.py`. It reconstructs the matrix from the paper’s construction, compares every entry with the included file, and certifies all pivots using 124 local checks and four lifts.

## Proofs I’ve reviewed and written up myself

None yet.

## Purely AI results

None yet. I’ll list results here when AI has produced the proof and write-up and I haven’t begun my own review.
