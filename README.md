# AI math results

This repository collects results I’ve obtained by working with ChatGPT and Claude. I’m broadly interested in numerical analysis and numerical linear algebra. For additional problems in this field see [Open Problems in Numerical Linear Algebra](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main).

**I’d love to collaborate.** If a proof is unreviewed or I’m still working through it, feel free to reach out and work through it with me or write your own version. I also welcome suggestions for making papers I’ve written clearer. If you’re curious how I work with ChatGPT and Claude or want to try this on a problem of your own, email me at [mati@princeton.edu](mailto:mati@princeton.edu).

## Conjectures

| Conjecture | Status |
| --- | --- |
| [Does every dimension admit a sign matrix with condition number at most 2?](#sign-matrices) **Yes.** | Working through |
| [Does every completely pivoted Hadamard matrix have growth factor equal to its order?](#hadamard-matrices) **No.** | Written by me |

The status describes my role in the write-up. **Unreviewed** means I haven’t reviewed the AI’s proof. **Working through** means I’m reviewing the argument and editing the draft. **Written by me** means I’ve reviewed the proof and written the paper myself.

### Sign matrices

For every positive integer $n$, there is an $n \times n$ matrix with entries in $\{-1,1\}$ whose spectral condition number is at most $2$. The bound is sharp only in dimension $3$, where the best possible condition number is exactly $2$. In every other dimension, some sign matrix has condition number strictly below $2$. [Original conjecture](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/eigenvalues-and-inverse-problems/IS-04)

GPT-6.2 Pro discovered the proof autonomously. AI wrote most of the current manuscript, and I’m working through the argument and editing the paper. The Lean formalization proves the main result in its Gram-matrix formulation, including the finite cases. [Paper](sign_matrix_condition_two/paper.pdf) · [Lean theorem](sign_matrix_condition_two/lean/Verified.lean) · [Verification instructions](sign_matrix_condition_two/README.md)

### Hadamard matrices

The conjecture was that every completely pivoted Hadamard matrix has growth factor equal to its order. A row and column permutation of the order-4096 Sylvester Hadamard matrix gives a counterexample. Its 4,089th pivot has magnitude 4,608, and this is the largest pivot. The construction extends to every order $n=2^d$ with $d\ge 12$, giving growth factor $9n/8$. GPT-6 Astra Pro found the counterexample, and I wrote the paper. [Paper](hadamard_order_4096/paper.pdf)

The [explicit matrix](hadamard_order_4096/matrix.npy) is included. To check it directly, run the following from the repository root with NumPy 2.0 or later. The script verifies row orthogonality and checks all 4,096 complete-pivoting steps in exact arithmetic.

```sh
python3 hadamard_order_4096/verify_dense.py
```

For a separate check using only the Python standard library, run `python3 hadamard_order_4096/verify_construction.py`. It reconstructs the matrix from the paper’s construction, compares every entry with the included file, and certifies all pivots using 124 local checks and four lifts.
