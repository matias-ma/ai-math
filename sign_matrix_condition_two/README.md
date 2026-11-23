# On the condition number of sign matrices

[Paper](paper.pdf) · [Lean theorem statements](lean/SignCond/Paper.lean)

The least spectral condition number of an order-n sign matrix is strictly below 2 except at order 3, where it equals 2.

## Lean verification

With Elan installed, run from this directory:

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The project pins Lean and Mathlib to v4.20.0. The labels in `Paper.lean` correspond to the numbered results in the paper. Lean expresses condition-number bounds as inequalities on the Gram matrix. The manuscript supplies their interpretation in terms of singular values. For the matching lemma, Lean checks the eigenvectors and the remaining invariant plane, and the paper gives the dimension count.

Some individual arguments differ. For orders 12, 24, 48 and their subsequent doublings, the manuscript doubles its order-6 witness, while Lean doubles an order-12 Hadamard matrix.

The large-order construction and the five exact small-order values are proved in Lean. The main theorem takes the finite-range proposition, `PropFiniteTau`, as an explicit hypothesis. The following exact computation verifies its witnesses.

## Computational verification

From this directory, using Python 3.10 or later with assertions enabled:

```sh
cd numerical
python3 verify.py certificates_9998.json 9998
```

The last argument enables the coverage check for all 9,983 quadruples and 32 small matrices. The verifier uses only the standard library and takes about an hour on the original machine. A successful run prints `All certificates verified.`

For floating-point spot checks, install NumPy and run from the same numerical directory:

```sh
python3 full_matrix_check.py
python3 large_orders_check.py freq 9999 10001 1
```

The first checks the block construction on small matrices. The second checks every Fourier frequency for the first three large-order construction parameters, with both border sizes.
