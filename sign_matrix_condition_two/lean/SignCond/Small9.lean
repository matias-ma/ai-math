import SignCond.SmallGraph

/-!
# Section `sec:small`, paragraph "Order 9": `h(9) = (1 + √41)/4`

Paper: "Suppose that `\kappa(A)^2<\tfrac72`, and negate rows as before. The off-diagonal entries of
`G` are congruent to `1` modulo `4`, and \Cref{lem:tools} excludes `|g|\ge5`, since
`(9+5)/(9-5)=\tfrac72`. Hence `G=8I+J-4N` [...] We have shown that every sign matrix of order `9` has
condition number at least `\sqrt{7/2}` or equal to `\tfrac14(1+\sqrt{41})`, and the second number is
the smaller one."

Formalisation (`Gram9`: symmetric, diagonal `9`, off-diagonal entries `1` or `-3`, Rayleigh form of
ratio `c` with `2c² < 7`; an edge of `Γ` is an entry `-3`). The lower bound is proved as "if
`c² < (21+√41)/8` (which is `< 7/2`) then a contradiction".
* Forbidden induced subgraphs, each by two integer test vectors on a principal submatrix: `no_tri`
  (`K₃`), `no_claw4` (`K_{1,4}`), `no_C4` (`C₄`), `no_P5` (`P₅`), `no_S22` (`S_{2,2}`). Hence all
  degrees are at most `3` (`deg3`), and two vertices have at most one common neighbour (`no_sq`).
* The components `P₃, P₄, K_{1,3}, T, C₅` are excluded by the paper's whole-matrix vectors
  (`comp_cert`), with integer vectors on the component for the exact matrix `8I + J - 4N_Λ`.
* `no_three`: no vertex has three neighbours. For a vertex `b` with neighbours `a, e, f`: if two of
  them have further neighbours there is an induced `P₅` (`two_oth`); if exactly one, there is an
  `S_{2,2}`, a `P₅`, or a component `T` (`one_oth`); if none, `K_{1,3}` is a component.
* `no_deg2`: with all degrees at most `2`, the argument of order `13` (`P₃`, `P₄`, `C₄`, `P₅`, `C₅`).
* So `Γ` is a matching. Its edges are listed one by one (`bound`), and after a relabelling `G` is
  `matchMat 9 k 9` (`match_sub`), the matrix of Lemma `lem:matching` with `x = 8, y = 1, z = -4`.
  `k = 1, 2, 3` are excluded by integer vectors (`k = 1` with quotients `1161/71` and `265/57`, ratio
  `3.517… > 7/2`), and `k = 4` gives `c² ≥ (21+√41)/8` (`match4`): `v = 2·𝟙_E + (√41-3)·𝟙_I` has
  quotient `(21+√41)/2` and `v = e_p + e_q - e_{p'} - e_{q'}` has quotient `4`.
* `k = 0` (`no_gram_8IJ`): the paper uses `det(8I + J) = 17·8⁸`, not a square. Here an elementary
  replacement: every column sum `u` of `A` satisfies `u² ≥ 17` (`col_sum_sq`, from
  `0 ≤ ‖Aᵀβ - 136e_k‖²` with `β = 17a - u𝟙`), hence `u² ≥ 25` since `u` is an integer, while the
  nine squares add up to `𝟙ᵀG𝟙 = 153`.
-/

open Matrix

namespace SignCond

/-- The normalised Gram matrix of order `9` under the assumption `κ(A)² < 7/2`. -/
structure Gram9 (B : Matrix (Fin 9) (Fin 9) ℝ) (c : ℝ) : Prop where
  ray : RayleighLe B c
  symm : ∀ i j, B i j = B j i
  diag : ∀ i, B i i = 9
  vals : ∀ i j, i ≠ j → B i j = 1 ∨ B i j = -3
  small : 2 * c ^ 2 < 7

namespace Gram9

variable {B : Matrix (Fin 9) (Fin 9) ℝ} {c : ℝ}

/-- A principal submatrix with an integer certificate `7 (wᵀMw)(vᵀv) ≤ 2 (vᵀMv)(wᵀw)` contradicts
`2c² < 7`. -/
theorem cert_contra (hG : Gram9 B c) {k : ℕ} {f : Fin k → Fin 9} (hf : Function.Injective f)
    (M : Matrix (Fin k) (Fin k) ℤ) (hM : B.submatrix f f = toR M) (v w : Fin k → ℤ)
    (hv : 0 < v ⬝ᵥ v) (hw : 0 < w ⬝ᵥ w)
    (hcert : 7 * ((w ⬝ᵥ (M *ᵥ w)) * (v ⬝ᵥ v)) ≤ 2 * ((v ⬝ᵥ (M *ᵥ v)) * (w ⬝ᵥ w))) : False := by
  have := rayleigh_cert (rayleighLe_submatrix hG.ray hf) M hM v w 2 7 (by norm_num) hv hw hcert
  push_cast at this
  linarith [hG.small]

theorem le_one (hG : Gram9 B c) (i j : Fin 9) (hij : i ≠ j) : B i j ≤ 1 := by
  rcases hG.vals i j hij with h | h <;> rw [h] <;> norm_num

theorem ne_of_adj (hG : Gram9 B c) {i j : Fin 9} (h : B i j = -3) : i ≠ j := by
  rintro rfl
  rw [hG.diag] at h
  norm_num at h

theorem one_of_ne (hG : Gram9 B c) {i j : Fin 9} (hij : i ≠ j) (h : B i j ≠ -3) : B i j = 1 :=
  (hG.vals i j hij).resolve_right h

/-- **Triangle** (`K₃`): eigenvalues `3` and `12`; `v = (1,-1,0)`, `w = (1,1,1)`. -/
theorem no_tri (hG : Gram9 B c) {i j k : Fin 9}
    (nij : i ≠ j) (nik : i ≠ k) (njk : j ≠ k)
    (hij : B i j = -3) (hik : B i k = -3) (hjk : B j k = -3) : False := by
  have sji : B j i = -3 := by rw [hG.symm]; exact hij
  have ski : B k i = -3 := by rw [hG.symm]; exact hik
  have skj : B k j = -3 := by rw [hG.symm]; exact hjk
  have hM : B.submatrix ![i, j, k] ![i, j, k] = toR !![9, -3, -3; -3, 9, -3; -3, -3, 9] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hij, hik, hjk, sji, ski, skj]
  exact hG.cert_contra (injective_three nij nik njk) _ hM
    ![1, -1, 0] ![1, 1, 1] (by decide) (by decide) (by decide)

/-- **`K_{1,4}`**: eigenvalues `(21 ± √153)/2`; `v = (3,-2,-2,-2,-2)` (quotient `417/25`), `w = (-3,-1,-1,-1,-1)` (`57/13`). -/
theorem no_claw4 (hG : Gram9 B c) {i j k l m : Fin 9}
    (nij : i ≠ j) (nik : i ≠ k) (nil : i ≠ l) (nim : i ≠ m) (njk : j ≠ k) (njl : j ≠ l) (njm : j ≠ m) (nkl : k ≠ l) (nkm : k ≠ m) (nlm : l ≠ m)
    (hij : B i j = -3) (hik : B i k = -3) (hil : B i l = -3) (him : B i m = -3) (hjk : B j k = 1) (hjl : B j l = 1) (hjm : B j m = 1) (hkl : B k l = 1) (hkm : B k m = 1) (hlm : B l m = 1) : False := by
  have sji : B j i = -3 := by rw [hG.symm]; exact hij
  have ski : B k i = -3 := by rw [hG.symm]; exact hik
  have sli : B l i = -3 := by rw [hG.symm]; exact hil
  have smi : B m i = -3 := by rw [hG.symm]; exact him
  have skj : B k j = 1 := by rw [hG.symm]; exact hjk
  have slj : B l j = 1 := by rw [hG.symm]; exact hjl
  have smj : B m j = 1 := by rw [hG.symm]; exact hjm
  have slk : B l k = 1 := by rw [hG.symm]; exact hkl
  have smk : B m k = 1 := by rw [hG.symm]; exact hkm
  have sml : B m l = 1 := by rw [hG.symm]; exact hlm
  have hM : B.submatrix ![i, j, k, l, m] ![i, j, k, l, m] = toR !![9, -3, -3, -3, -3; -3, 9, 1, 1, 1; -3, 1, 9, 1, 1; -3, 1, 1, 9, 1; -3, 1, 1, 1, 9] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hij, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm, sji, ski, sli, smi, skj, slj, smj, slk, smk, sml]
  exact hG.cert_contra (injective_five nij nik nil nim njk njl njm nkl nkm nlm) _ hM
    ![3, -2, -2, -2, -2] ![-3, -1, -1, -1, -1] (by decide) (by decide) (by decide)

/-- **`C₄`** `a-b-d-e-a`: eigenvalues `4` (at `𝟙`) and `16` (at `(1,-1,1,-1)`). -/
theorem no_C4 (hG : Gram9 B c) {a b d e : Fin 9}
    (nab : a ≠ b) (nad : a ≠ d) (nae : a ≠ e) (nbd : b ≠ d) (nbe : b ≠ e) (nde : d ≠ e)
    (hab : B a b = -3) (had : B a d = 1) (hae : B a e = -3) (hbd : B b d = -3) (hbe : B b e = 1) (hde : B d e = -3) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sda : B d a = 1 := by rw [hG.symm]; exact had
  have sea : B e a = -3 := by rw [hG.symm]; exact hae
  have sdb : B d b = -3 := by rw [hG.symm]; exact hbd
  have seb : B e b = 1 := by rw [hG.symm]; exact hbe
  have sed : B e d = -3 := by rw [hG.symm]; exact hde
  have hM : B.submatrix ![a, b, d, e] ![a, b, d, e] = toR !![9, -3, 1, -3; -3, 9, -3, 1; 1, -3, 9, -3; -3, 1, -3, 9] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hab, had, hae, hbd, hbe, hde, sba, sda, sea, sdb, seb, sed]
  exact hG.cert_contra (injective_four nab nad nae nbd nbe nde) _ hM
    ![1, -1, 1, -1] ![1, 1, 1, 1] (by decide) (by decide) (by decide)

/-- **`P₅`** `a-b-d-e-f`: eigenvalue `4` at `(-1,-1,0,1,1)` and quotient `73/5` at `(1,-1,1,-1,1)`. -/
theorem no_P5 (hG : Gram9 B c) {a b d e f : Fin 9}
    (nab : a ≠ b) (nad : a ≠ d) (nae : a ≠ e) (naf : a ≠ f) (nbd : b ≠ d) (nbe : b ≠ e) (nbf : b ≠ f) (nde : d ≠ e) (ndf : d ≠ f) (nef : e ≠ f)
    (hab : B a b = -3) (had : B a d = 1) (hae : B a e = 1) (haf : B a f = 1) (hbd : B b d = -3) (hbe : B b e = 1) (hbf : B b f = 1) (hde : B d e = -3) (hdf : B d f = 1) (hef : B e f = -3) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sda : B d a = 1 := by rw [hG.symm]; exact had
  have sea : B e a = 1 := by rw [hG.symm]; exact hae
  have sfa : B f a = 1 := by rw [hG.symm]; exact haf
  have sdb : B d b = -3 := by rw [hG.symm]; exact hbd
  have seb : B e b = 1 := by rw [hG.symm]; exact hbe
  have sfb : B f b = 1 := by rw [hG.symm]; exact hbf
  have sed : B e d = -3 := by rw [hG.symm]; exact hde
  have sfd : B f d = 1 := by rw [hG.symm]; exact hdf
  have sfe : B f e = -3 := by rw [hG.symm]; exact hef
  have hM : B.submatrix ![a, b, d, e, f] ![a, b, d, e, f] = toR !![9, -3, 1, 1, 1; -3, 9, -3, 1, 1; 1, -3, 9, -3, 1; 1, 1, -3, 9, -3; 1, 1, 1, -3, 9] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hab, had, hae, haf, hbd, hbe, hbf, hde, hdf, hef, sba, sda, sea, sfa, sdb, seb, sfb, sed, sfd, sfe]
  exact hG.cert_contra (injective_five nab nad nae naf nbd nbe nbf nde ndf nef) _ hM
    ![1, -1, 1, -1, 1] ![-1, -1, 0, 1, 1] (by decide) (by decide) (by decide)

/-- **`S_{2,2}`**: `a-b` adjacent, `a` with further neighbours `d, e`, `b` with further neighbours `f, g`; eigenvalues `4` at `(1,-1,1,1,-1,-1)` and `16` at `(2,-2,-1,-1,1,1)`. -/
theorem no_S22 (hG : Gram9 B c) {a b d e f g : Fin 9}
    (nab : a ≠ b) (nad : a ≠ d) (nae : a ≠ e) (naf : a ≠ f) (nag : a ≠ g) (nbd : b ≠ d) (nbe : b ≠ e) (nbf : b ≠ f) (nbg : b ≠ g) (nde : d ≠ e) (ndf : d ≠ f) (ndg : d ≠ g) (nef : e ≠ f) (neg : e ≠ g) (nfg : f ≠ g)
    (hab : B a b = -3) (had : B a d = -3) (hae : B a e = -3) (haf : B a f = 1) (hag : B a g = 1) (hbd : B b d = 1) (hbe : B b e = 1) (hbf : B b f = -3) (hbg : B b g = -3) (hde : B d e = 1) (hdf : B d f = 1) (hdg : B d g = 1) (hef : B e f = 1) (heg : B e g = 1) (hfg : B f g = 1) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sda : B d a = -3 := by rw [hG.symm]; exact had
  have sea : B e a = -3 := by rw [hG.symm]; exact hae
  have sfa : B f a = 1 := by rw [hG.symm]; exact haf
  have sga : B g a = 1 := by rw [hG.symm]; exact hag
  have sdb : B d b = 1 := by rw [hG.symm]; exact hbd
  have seb : B e b = 1 := by rw [hG.symm]; exact hbe
  have sfb : B f b = -3 := by rw [hG.symm]; exact hbf
  have sgb : B g b = -3 := by rw [hG.symm]; exact hbg
  have sed : B e d = 1 := by rw [hG.symm]; exact hde
  have sfd : B f d = 1 := by rw [hG.symm]; exact hdf
  have sgd : B g d = 1 := by rw [hG.symm]; exact hdg
  have sfe : B f e = 1 := by rw [hG.symm]; exact hef
  have sge : B g e = 1 := by rw [hG.symm]; exact heg
  have sgf : B g f = 1 := by rw [hG.symm]; exact hfg
  have hM : B.submatrix ![a, b, d, e, f, g] ![a, b, d, e, f, g] = toR !![9, -3, -3, -3, 1, 1; -3, 9, 1, 1, -3, -3; -3, 1, 9, 1, 1, 1; -3, 1, 1, 9, 1, 1; 1, -3, 1, 1, 9, 1; 1, -3, 1, 1, 1, 9] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hab, had, hae, haf, hag, hbd, hbe, hbf, hbg, hde, hdf, hdg, hef, heg, hfg, sba, sda, sea, sfa, sga, sdb, seb, sfb, sgb, sed, sfd, sgd, sfe, sge, sgf]
  exact hG.cert_contra (injective_six nab nad nae naf nag nbd nbe nbf nbg nde ndf ndg nef neg nfg) _ hM
    ![2, -2, -1, -1, 1, 1] ![1, -1, 1, 1, -1, -1] (by decide) (by decide) (by decide)

/-- **The component `P₃`** `a-b-e`: `w = (2,4,2)` and `-1` elsewhere (quotient at most `58/15`), `v = (-3,4,-3)` (quotient `234/17`). -/
theorem no_P3comp (hG : Gram9 B c) {a b e : Fin 9}
    (nab : a ≠ b) (nae : a ≠ e) (nbe : b ≠ e)
    (hab : B a b = -3) (hae : B a e = 1) (hbe : B b e = -3)
    (hcl : ∀ x, x ≠ a → x ≠ b → x ≠ e →
      B a x = 1 ∧ B b x = 1 ∧ B e x = 1) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sea : B e a = 1 := by rw [hG.symm]; exact hae
  have seb : B e b = -3 := by rw [hG.symm]; exact hbe
  have hin : ∀ u v : Fin 3, B (![a, b, e] u) (![a, b, e] v) =
      (((!![9, -3, 1; -3, 9, -3; 1, -3, 9] : Matrix (Fin 3) (Fin 3) ℤ) u v : ℤ) : ℝ) := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [hG.diag, hab, hae, hbe, sba, sea, seb]
  have hclosed : ∀ u x, (∀ v, x ≠ ![a, b, e] v) → B (![a, b, e] u) x = 1 := by
    intro u x hx
    have x0 : x ≠ a := hx 0
    have x1 : x ≠ b := hx 1
    have x2 : x ≠ e := hx 2
    obtain ⟨y0, y1, y2⟩ := hcl x x0 x1 x2
    fin_cases u <;> simp [y0, y1, y2]
  have := comp_cert (n := 9) (by norm_num) hG.ray hG.symm 9
    (fun i => by rw [hG.diag]; norm_num) hG.le_one ![a, b, e]
    (injective_three nab nae nbe) _ hin hclosed
    ![-3, 4, -3] ![2, 4, 2] (-1) 2 7 (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  push_cast at this
  linarith [hG.small]

/-- **The component `P₄`** `a-b-d-e`: `w = (1,2,2,1)` and `-1` elsewhere (quotient at most `19/5`), `v = (-2,3,-3,2)` (quotient `188/13`). -/
theorem no_P4comp (hG : Gram9 B c) {a b d e : Fin 9}
    (nab : a ≠ b) (nad : a ≠ d) (nae : a ≠ e) (nbd : b ≠ d) (nbe : b ≠ e) (nde : d ≠ e)
    (hab : B a b = -3) (had : B a d = 1) (hae : B a e = 1) (hbd : B b d = -3) (hbe : B b e = 1) (hde : B d e = -3)
    (hcl : ∀ x, x ≠ a → x ≠ b → x ≠ d → x ≠ e →
      B a x = 1 ∧ B b x = 1 ∧ B d x = 1 ∧ B e x = 1) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sda : B d a = 1 := by rw [hG.symm]; exact had
  have sea : B e a = 1 := by rw [hG.symm]; exact hae
  have sdb : B d b = -3 := by rw [hG.symm]; exact hbd
  have seb : B e b = 1 := by rw [hG.symm]; exact hbe
  have sed : B e d = -3 := by rw [hG.symm]; exact hde
  have hin : ∀ u v : Fin 4, B (![a, b, d, e] u) (![a, b, d, e] v) =
      (((!![9, -3, 1, 1; -3, 9, -3, 1; 1, -3, 9, -3; 1, 1, -3, 9] : Matrix (Fin 4) (Fin 4) ℤ) u v : ℤ) : ℝ) := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [hG.diag, hab, had, hae, hbd, hbe, hde, sba, sda, sea, sdb, seb, sed]
  have hclosed : ∀ u x, (∀ v, x ≠ ![a, b, d, e] v) → B (![a, b, d, e] u) x = 1 := by
    intro u x hx
    have x0 : x ≠ a := hx 0
    have x1 : x ≠ b := hx 1
    have x2 : x ≠ d := hx 2
    have x3 : x ≠ e := hx 3
    obtain ⟨y0, y1, y2, y3⟩ := hcl x x0 x1 x2 x3
    fin_cases u <;> simp [y0, y1, y2, y3]
  have := comp_cert (n := 9) (by norm_num) hG.ray hG.symm 9
    (fun i => by rw [hG.diag]; norm_num) hG.le_one ![a, b, d, e]
    (injective_four nab nad nae nbd nbe nde) _ hin hclosed
    ![-2, 3, -3, 2] ![1, 2, 2, 1] (-1) 2 7 (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  push_cast at this
  linarith [hG.small]

/-- **The component `K_{1,3}`** with centre `b` and leaves `a, e, f`: `w = (2,1,1,1)` and `-1` elsewhere (quotient at most `4`), `v = (-3,2,2,2)` (quotient `107/7`). -/
theorem no_K13comp (hG : Gram9 B c) {b a e f : Fin 9}
    (nba : b ≠ a) (nbe : b ≠ e) (nbf : b ≠ f) (nae : a ≠ e) (naf : a ≠ f) (nef : e ≠ f)
    (hba : B b a = -3) (hbe : B b e = -3) (hbf : B b f = -3) (hae : B a e = 1) (haf : B a f = 1) (hef : B e f = 1)
    (hcl : ∀ x, x ≠ b → x ≠ a → x ≠ e → x ≠ f →
      B b x = 1 ∧ B a x = 1 ∧ B e x = 1 ∧ B f x = 1) : False := by
  have sab : B a b = -3 := by rw [hG.symm]; exact hba
  have seb : B e b = -3 := by rw [hG.symm]; exact hbe
  have sfb : B f b = -3 := by rw [hG.symm]; exact hbf
  have sea : B e a = 1 := by rw [hG.symm]; exact hae
  have sfa : B f a = 1 := by rw [hG.symm]; exact haf
  have sfe : B f e = 1 := by rw [hG.symm]; exact hef
  have hin : ∀ u v : Fin 4, B (![b, a, e, f] u) (![b, a, e, f] v) =
      (((!![9, -3, -3, -3; -3, 9, 1, 1; -3, 1, 9, 1; -3, 1, 1, 9] : Matrix (Fin 4) (Fin 4) ℤ) u v : ℤ) : ℝ) := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [hG.diag, hba, hbe, hbf, hae, haf, hef, sab, seb, sfb, sea, sfa, sfe]
  have hclosed : ∀ u x, (∀ v, x ≠ ![b, a, e, f] v) → B (![b, a, e, f] u) x = 1 := by
    intro u x hx
    have x0 : x ≠ b := hx 0
    have x1 : x ≠ a := hx 1
    have x2 : x ≠ e := hx 2
    have x3 : x ≠ f := hx 3
    obtain ⟨y0, y1, y2, y3⟩ := hcl x x0 x1 x2 x3
    fin_cases u <;> simp [y0, y1, y2, y3]
  have := comp_cert (n := 9) (by norm_num) hG.ray hG.symm 9
    (fun i => by rw [hG.diag]; norm_num) hG.le_one ![b, a, e, f]
    (injective_four nba nbe nbf nae naf nef) _ hin hclosed
    ![-3, 2, 2, 2] ![2, 1, 1, 1] (-1) 2 7 (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  push_cast at this
  linarith [hG.small]

/-- **The component `T`** (`a2-a-b-e` and a leaf `f` at `b`): `w = (1,2,2,1,1)` and `-1` elsewhere (quotient at most `49/15`), `v = (-2,3,-3,2,0)` on the induced `P₄` `a2-a-b-e` (quotient `188/13`). -/
theorem no_Tcomp (hG : Gram9 B c) {a2 a b e f : Fin 9}
    (na2a : a2 ≠ a) (na2b : a2 ≠ b) (na2e : a2 ≠ e) (na2f : a2 ≠ f) (nab : a ≠ b) (nae : a ≠ e) (naf : a ≠ f) (nbe : b ≠ e) (nbf : b ≠ f) (nef : e ≠ f)
    (ha2a : B a2 a = -3) (ha2b : B a2 b = 1) (ha2e : B a2 e = 1) (ha2f : B a2 f = 1) (hab : B a b = -3) (hae : B a e = 1) (haf : B a f = 1) (hbe : B b e = -3) (hbf : B b f = -3) (hef : B e f = 1)
    (hcl : ∀ x, x ≠ a2 → x ≠ a → x ≠ b → x ≠ e → x ≠ f →
      B a2 x = 1 ∧ B a x = 1 ∧ B b x = 1 ∧ B e x = 1 ∧ B f x = 1) : False := by
  have saa2 : B a a2 = -3 := by rw [hG.symm]; exact ha2a
  have sba2 : B b a2 = 1 := by rw [hG.symm]; exact ha2b
  have sea2 : B e a2 = 1 := by rw [hG.symm]; exact ha2e
  have sfa2 : B f a2 = 1 := by rw [hG.symm]; exact ha2f
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sea : B e a = 1 := by rw [hG.symm]; exact hae
  have sfa : B f a = 1 := by rw [hG.symm]; exact haf
  have seb : B e b = -3 := by rw [hG.symm]; exact hbe
  have sfb : B f b = -3 := by rw [hG.symm]; exact hbf
  have sfe : B f e = 1 := by rw [hG.symm]; exact hef
  have hin : ∀ u v : Fin 5, B (![a2, a, b, e, f] u) (![a2, a, b, e, f] v) =
      (((!![9, -3, 1, 1, 1; -3, 9, -3, 1, 1; 1, -3, 9, -3, -3; 1, 1, -3, 9, 1; 1, 1, -3, 1, 9] : Matrix (Fin 5) (Fin 5) ℤ) u v : ℤ) : ℝ) := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [hG.diag, ha2a, ha2b, ha2e, ha2f, hab, hae, haf, hbe, hbf, hef, saa2, sba2, sea2, sfa2, sba, sea, sfa, seb, sfb, sfe]
  have hclosed : ∀ u x, (∀ v, x ≠ ![a2, a, b, e, f] v) → B (![a2, a, b, e, f] u) x = 1 := by
    intro u x hx
    have x0 : x ≠ a2 := hx 0
    have x1 : x ≠ a := hx 1
    have x2 : x ≠ b := hx 2
    have x3 : x ≠ e := hx 3
    have x4 : x ≠ f := hx 4
    obtain ⟨y0, y1, y2, y3, y4⟩ := hcl x x0 x1 x2 x3 x4
    fin_cases u <;> simp [y0, y1, y2, y3, y4]
  have := comp_cert (n := 9) (by norm_num) hG.ray hG.symm 9
    (fun i => by rw [hG.diag]; norm_num) hG.le_one ![a2, a, b, e, f]
    (injective_five na2a na2b na2e na2f nab nae naf nbe nbf nef) _ hin hclosed
    ![-2, 3, -3, 2, 0] ![1, 2, 2, 1, 1] (-1) 2 7 (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  push_cast at this
  linarith [hG.small]

/-- **The component `C₅`** `a-b-d-e-f-a`: `w = 𝟙` on the cycle and `-1` elsewhere (quotient at most `11/3`), `v = (-3,2,0,-2,3)` (quotient `188/13`). -/
theorem no_C5comp (hG : Gram9 B c) {a b d e f : Fin 9}
    (nab : a ≠ b) (nad : a ≠ d) (nae : a ≠ e) (naf : a ≠ f) (nbd : b ≠ d) (nbe : b ≠ e) (nbf : b ≠ f) (nde : d ≠ e) (ndf : d ≠ f) (nef : e ≠ f)
    (hab : B a b = -3) (had : B a d = 1) (hae : B a e = 1) (haf : B a f = -3) (hbd : B b d = -3) (hbe : B b e = 1) (hbf : B b f = 1) (hde : B d e = -3) (hdf : B d f = 1) (hef : B e f = -3)
    (hcl : ∀ x, x ≠ a → x ≠ b → x ≠ d → x ≠ e → x ≠ f →
      B a x = 1 ∧ B b x = 1 ∧ B d x = 1 ∧ B e x = 1 ∧ B f x = 1) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sda : B d a = 1 := by rw [hG.symm]; exact had
  have sea : B e a = 1 := by rw [hG.symm]; exact hae
  have sfa : B f a = -3 := by rw [hG.symm]; exact haf
  have sdb : B d b = -3 := by rw [hG.symm]; exact hbd
  have seb : B e b = 1 := by rw [hG.symm]; exact hbe
  have sfb : B f b = 1 := by rw [hG.symm]; exact hbf
  have sed : B e d = -3 := by rw [hG.symm]; exact hde
  have sfd : B f d = 1 := by rw [hG.symm]; exact hdf
  have sfe : B f e = -3 := by rw [hG.symm]; exact hef
  have hin : ∀ u v : Fin 5, B (![a, b, d, e, f] u) (![a, b, d, e, f] v) =
      (((!![9, -3, 1, 1, -3; -3, 9, -3, 1, 1; 1, -3, 9, -3, 1; 1, 1, -3, 9, -3; -3, 1, 1, -3, 9] : Matrix (Fin 5) (Fin 5) ℤ) u v : ℤ) : ℝ) := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [hG.diag, hab, had, hae, haf, hbd, hbe, hbf, hde, hdf, hef, sba, sda, sea, sfa, sdb, seb, sfb, sed, sfd, sfe]
  have hclosed : ∀ u x, (∀ v, x ≠ ![a, b, d, e, f] v) → B (![a, b, d, e, f] u) x = 1 := by
    intro u x hx
    have x0 : x ≠ a := hx 0
    have x1 : x ≠ b := hx 1
    have x2 : x ≠ d := hx 2
    have x3 : x ≠ e := hx 3
    have x4 : x ≠ f := hx 4
    obtain ⟨y0, y1, y2, y3, y4⟩ := hcl x x0 x1 x2 x3 x4
    fin_cases u <;> simp [y0, y1, y2, y3, y4]
  have := comp_cert (n := 9) (by norm_num) hG.ray hG.symm 9
    (fun i => by rw [hG.diag]; norm_num) hG.le_one ![a, b, d, e, f]
    (injective_five nab nad nae naf nbd nbe nbf nde ndf nef) _ hin hclosed
    ![-3, 2, 0, -2, 3] ![1, 1, 1, 1, 1] (-1) 2 7 (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  push_cast at this
  linarith [hG.small]

/-- The neighbours of a vertex are pairwise nonadjacent (no triangle). -/
theorem nonadj (hG : Gram9 B c) {i j k : Fin 9} (hij : B i j = -3) (hik : B i k = -3)
    (hjk : j ≠ k) : B j k = 1 :=
  hG.one_of_ne hjk fun h => hG.no_tri (hG.ne_of_adj hij) (hG.ne_of_adj hik) hjk hij hik h

/-- **Degrees are at most `3`** (`K₃` and `K_{1,4}`). -/
theorem deg3 (hG : Gram9 B c) {i j k l x : Fin 9} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hij : B i j = -3) (hik : B i k = -3) (hil : B i l = -3) (hxj : x ≠ j) (hxk : x ≠ k)
    (hxl : x ≠ l) (hxi : x ≠ i) : B i x = 1 :=
  hG.one_of_ne (Ne.symm hxi) fun h =>
    hG.no_claw4 (hG.ne_of_adj hij) (hG.ne_of_adj hik) (hG.ne_of_adj hil) (hG.ne_of_adj h) hjk hjl
      (Ne.symm hxj) hkl (Ne.symm hxk) (Ne.symm hxl) hij hik hil h (hG.nonadj hij hik hjk)
      (hG.nonadj hij hil hjl) (hG.nonadj hij h (Ne.symm hxj)) (hG.nonadj hik hil hkl)
      (hG.nonadj hik h (Ne.symm hxk)) (hG.nonadj hil h (Ne.symm hxl))

/-- **Two vertices have at most one common neighbour** (`C₄`). -/
theorem no_sq (hG : Gram9 B c) {x y z w : Fin 9} (hxy : B x y = -3) (hyz : B y z = -3)
    (hxw : B x w = -3) (hwz : B w z = -3) (hyw : y ≠ w) (hxz : x ≠ z) : False :=
  hG.no_C4 (hG.ne_of_adj hxy) hxz (hG.ne_of_adj hxw) (hG.ne_of_adj hyz) hyw
    (Ne.symm (hG.ne_of_adj hwz)) hxy (hG.nonadj (by rw [hG.symm]; exact hxy) hyz hxz) hxw hyz
    (hG.nonadj hxy hxw hyw) (by rw [hG.symm]; exact hwz)

/-- **Two leaves with further neighbours.** If `b` has neighbours `a, e, f` and both `a` and `e` have
neighbours other than `b`, there is an induced `P₅`. -/
theorem two_oth (hG : Gram9 B c) {b a e f a2 e2 : Fin 9} (nae : a ≠ e) (naf : a ≠ f) (nef : e ≠ f)
    (hba : B b a = -3) (hbe : B b e = -3) (hbf : B b f = -3) (haa : B a a2 = -3) (na2b : a2 ≠ b)
    (hee : B e e2 = -3) (ne2b : e2 ≠ b) : False := by
  have nba := hG.ne_of_adj hba
  have nbe := hG.ne_of_adj hbe
  have nbf := hG.ne_of_adj hbf
  have hab : B a b = -3 := by rw [hG.symm]; exact hba
  have heb : B e b = -3 := by rw [hG.symm]; exact hbe
  have hfb : B f b = -3 := by rw [hG.symm]; exact hbf
  have hae1 : B a e = 1 := hG.nonadj hba hbe nae
  have haf1 : B a f = 1 := hG.nonadj hba hbf naf
  have hef1 : B e f = 1 := hG.nonadj hbe hbf nef
  have naa2 := hG.ne_of_adj haa
  have nee2 := hG.ne_of_adj hee
  have na2e : a2 ≠ e := by
    intro h; rw [h, hae1] at haa; norm_num at haa
  have na2f : a2 ≠ f := by
    intro h; rw [h, haf1] at haa; norm_num at haa
  have ne2a : e2 ≠ a := by
    intro h; rw [h, hG.symm, hae1] at hee; norm_num at hee
  have ne2f : e2 ≠ f := by
    intro h; rw [h, hef1] at hee; norm_num at hee
  have hba2 : B b a2 = 1 := hG.deg3 nae naf nef hba hbe hbf (Ne.symm naa2) na2e na2f na2b
  have hbe2 : B b e2 = 1 := hG.deg3 nae naf nef hba hbe hbf ne2a (Ne.symm nee2) ne2f ne2b
  have na2e2 : a2 ≠ e2 := by
    intro h
    rw [← h] at hee
    exact hG.no_sq hab hbe haa (by rw [hG.symm]; exact hee) (Ne.symm na2b) nae
  have hae2 : B a e2 = 1 := hG.one_of_ne (Ne.symm ne2a) fun h =>
    hG.no_sq hab hbe h (by rw [hG.symm]; exact hee) (Ne.symm ne2b) nae
  have hea2 : B e a2 = 1 := hG.one_of_ne (Ne.symm na2e) fun h =>
    hG.no_sq heb hba h (by rw [hG.symm]; exact haa) (Ne.symm na2b) (Ne.symm nae)
  have hfa2 : B f a2 = 1 := hG.one_of_ne (Ne.symm na2f) fun h =>
    hG.no_sq hfb hba h (by rw [hG.symm]; exact haa) (Ne.symm na2b) (Ne.symm naf)
  have hfe2 : B f e2 = 1 := hG.one_of_ne (Ne.symm ne2f) fun h =>
    hG.no_sq hfb hbe h (by rw [hG.symm]; exact hee) (Ne.symm ne2b) (Ne.symm nef)
  rcases hG.vals a2 e2 na2e2 with h | h
  · exact hG.no_P5 (Ne.symm naa2) na2b na2e na2e2 (Ne.symm nba) nae (Ne.symm ne2a) nbe
      (Ne.symm ne2b) nee2 (by rw [hG.symm]; exact haa) (by rw [hG.symm]; exact hba2)
      (by rw [hG.symm]; exact hea2) h hab hae1 hae2 hbe hbe2 hee
  · exact hG.no_P5 (Ne.symm nbf) (Ne.symm naf) (Ne.symm na2f) (Ne.symm ne2f) nba (Ne.symm na2b)
      (Ne.symm ne2b) naa2 (Ne.symm ne2a) na2e2 hfb (by rw [hG.symm]; exact haf1) hfa2 hfe2 hba
      hba2 hbe2 haa hae2 h

/-- **One leaf with further neighbours.** If `b` has neighbours `a, e, f`, `a` has a neighbour
`a2 ≠ b`, and `e, f` have no neighbour besides `b`, there is an induced `S_{2,2}` or `P₅`, or the
five vertices form a component `T`. -/
theorem one_oth (hG : Gram9 B c) {b a e f a2 : Fin 9} (nae : a ≠ e) (naf : a ≠ f) (nef : e ≠ f)
    (hba : B b a = -3) (hbe : B b e = -3) (hbf : B b f = -3) (haa : B a a2 = -3) (na2b : a2 ≠ b)
    (he : ∀ x, B e x = -3 → x = b) (hf : ∀ x, B f x = -3 → x = b) : False := by
  have nba := hG.ne_of_adj hba
  have nbe := hG.ne_of_adj hbe
  have nbf := hG.ne_of_adj hbf
  have hab : B a b = -3 := by rw [hG.symm]; exact hba
  have hae1 : B a e = 1 := hG.nonadj hba hbe nae
  have haf1 : B a f = 1 := hG.nonadj hba hbf naf
  have hef1 : B e f = 1 := hG.nonadj hbe hbf nef
  have naa2 := hG.ne_of_adj haa
  have na2e : a2 ≠ e := by
    intro h; rw [h, hae1] at haa; norm_num at haa
  have na2f : a2 ≠ f := by
    intro h; rw [h, haf1] at haa; norm_num at haa
  have hba2 : B b a2 = 1 := hG.deg3 nae naf nef hba hbe hbf (Ne.symm naa2) na2e na2f na2b
  have hea2 : B e a2 = 1 := hG.one_of_ne (Ne.symm na2e) fun h => na2b (he a2 h)
  have hfa2 : B f a2 = 1 := hG.one_of_ne (Ne.symm na2f) fun h => na2b (hf a2 h)
  by_cases h3 : ∃ a3, a3 ≠ b ∧ a3 ≠ a2 ∧ B a a3 = -3
  · obtain ⟨a3, na3b, na3a2, haa3⟩ := h3
    have naa3 := hG.ne_of_adj haa3
    have na3e : a3 ≠ e := by
      intro h; rw [h, hae1] at haa3; norm_num at haa3
    have na3f : a3 ≠ f := by
      intro h; rw [h, haf1] at haa3; norm_num at haa3
    have hba3 : B b a3 = 1 := hG.deg3 nae naf nef hba hbe hbf (Ne.symm naa3) na3e na3f na3b
    have hea3 : B e a3 = 1 := hG.one_of_ne (Ne.symm na3e) fun h => na3b (he a3 h)
    have hfa3 : B f a3 = 1 := hG.one_of_ne (Ne.symm na3f) fun h => na3b (hf a3 h)
    have ha2a3 : B a2 a3 = 1 := hG.nonadj haa haa3 (Ne.symm na3a2)
    exact hG.no_S22 (Ne.symm nba) naa2 naa3 nae naf (Ne.symm na2b) (Ne.symm na3b) nbe nbf
      (Ne.symm na3a2) na2e na2f na3e na3f nef hab haa haa3 hae1 haf1 hba2 hba3 hbe hbf ha2a3
      (by rw [hG.symm]; exact hea2) (by rw [hG.symm]; exact hfa2) (by rw [hG.symm]; exact hea3)
      (by rw [hG.symm]; exact hfa3) hef1
  · push_neg at h3
    by_cases h4 : ∃ a3, a3 ≠ a ∧ B a2 a3 = -3
    · obtain ⟨a3, na3a, h23⟩ := h4
      have na23 := hG.ne_of_adj h23
      have na3b : a3 ≠ b := by
        intro h; rw [h, hG.symm, hba2] at h23; norm_num at h23
      have na3e : a3 ≠ e := by
        intro h; rw [h, hG.symm, hea2] at h23; norm_num at h23
      have haa3 : B a a3 = 1 := hG.one_of_ne (Ne.symm na3a) (h3 a3 na3b (Ne.symm na23))
      have hba3 : B b a3 = 1 := hG.deg3 nae naf nef hba hbe hbf na3a na3e
        (fun h => by rw [h, hG.symm, hfa2] at h23; norm_num at h23) na3b
      have hea3 : B e a3 = 1 := hG.one_of_ne (Ne.symm na3e) fun h => na3b (he a3 h)
      exact hG.no_P5 (Ne.symm na23) na3a na3b na3e (Ne.symm naa2) na2b na2e (Ne.symm nba) nae nbe
        (by rw [hG.symm]; exact h23) (by rw [hG.symm]; exact haa3) (by rw [hG.symm]; exact hba3)
        (by rw [hG.symm]; exact hea3) (by rw [hG.symm]; exact haa)
        (by rw [hG.symm]; exact hba2) (by rw [hG.symm]; exact hea2) hab hae1 hbe
    · push_neg at h4
      refine hG.no_Tcomp (Ne.symm naa2) na2b na2e na2f (Ne.symm nba) nae naf nbe nbf nef
        (by rw [hG.symm]; exact haa) (by rw [hG.symm]; exact hba2)
        (by rw [hG.symm]; exact hea2) (by rw [hG.symm]; exact hfa2) hab hae1 haf1 hbe hbf hef1 ?_
      intro x hxa2 hxa hxb hxe hxf
      exact ⟨hG.one_of_ne (Ne.symm hxa2) (h4 x hxa), hG.one_of_ne (Ne.symm hxa) (h3 x hxb hxa2),
        hG.deg3 nae naf nef hba hbe hbf hxa hxe hxf hxb,
        hG.one_of_ne (Ne.symm hxe) fun h => hxb (he x h),
        hG.one_of_ne (Ne.symm hxf) fun h => hxb (hf x h)⟩

/-- **No vertex has three neighbours.** -/
theorem no_three (hG : Gram9 B c) {b a e f : Fin 9} (nae : a ≠ e) (naf : a ≠ f) (nef : e ≠ f)
    (hba : B b a = -3) (hbe : B b e = -3) (hbf : B b f = -3) : False := by
  have noOth : ∀ y, ¬ (∃ y2, y2 ≠ b ∧ B y y2 = -3) → ∀ x, B y x = -3 → x = b :=
    fun y hy x hx => by
      by_contra hne
      exact hy ⟨x, hne, hx⟩
  by_cases Oa : ∃ a2, a2 ≠ b ∧ B a a2 = -3
  · obtain ⟨a2, na2b, haa⟩ := Oa
    by_cases Oe : ∃ e2, e2 ≠ b ∧ B e e2 = -3
    · obtain ⟨e2, ne2b, hee⟩ := Oe
      exact hG.two_oth nae naf nef hba hbe hbf haa na2b hee ne2b
    · by_cases Of : ∃ f2, f2 ≠ b ∧ B f f2 = -3
      · obtain ⟨f2, nf2b, hff⟩ := Of
        exact hG.two_oth naf nae (Ne.symm nef) hba hbf hbe haa na2b hff nf2b
      · exact hG.one_oth nae naf nef hba hbe hbf haa na2b (noOth e Oe) (noOth f Of)
  · by_cases Oe : ∃ e2, e2 ≠ b ∧ B e e2 = -3
    · obtain ⟨e2, ne2b, hee⟩ := Oe
      by_cases Of : ∃ f2, f2 ≠ b ∧ B f f2 = -3
      · obtain ⟨f2, nf2b, hff⟩ := Of
        exact hG.two_oth nef (Ne.symm nae) (Ne.symm naf) hbe hbf hba hee ne2b hff nf2b
      · exact hG.one_oth (Ne.symm nae) nef naf hbe hba hbf hee ne2b (noOth a Oa) (noOth f Of)
    · by_cases Of : ∃ f2, f2 ≠ b ∧ B f f2 = -3
      · obtain ⟨f2, nf2b, hff⟩ := Of
        exact hG.one_oth (Ne.symm naf) (Ne.symm nef) nae hbf hba hbe hff nf2b (noOth a Oa)
          (noOth e Oe)
      · refine hG.no_K13comp (hG.ne_of_adj hba) (hG.ne_of_adj hbe) (hG.ne_of_adj hbf) nae naf nef
          hba hbe hbf (hG.nonadj hba hbe nae) (hG.nonadj hba hbf naf) (hG.nonadj hbe hbf nef) ?_
        intro x hxb hxa hxe hxf
        exact ⟨hG.deg3 nae naf nef hba hbe hbf hxa hxe hxf hxb,
          hG.one_of_ne (Ne.symm hxa) fun h => hxb (noOth a Oa x h),
          hG.one_of_ne (Ne.symm hxe) fun h => hxb (noOth e Oe x h),
          hG.one_of_ne (Ne.symm hxf) fun h => hxb (noOth f Of x h)⟩

/-- **Degrees are at most `2`**: a vertex with neighbours `j ≠ k` has no further neighbour. -/
theorem deg2 (hG : Gram9 B c) {i j k x : Fin 9} (hij : B i j = -3) (hik : B i k = -3)
    (hjk : j ≠ k) (hxj : x ≠ j) (hxk : x ≠ k) (hxi : x ≠ i) : B i x = 1 :=
  hG.one_of_ne (Ne.symm hxi) fun h => hG.no_three hjk (Ne.symm hxj) (Ne.symm hxk) hij hik h

/-- **One side.** A path `a2-a-b-e` in which `e` has no neighbour besides `b`: if `a2` has a
further neighbour `a3`, then `a3-a2-a-b-e` is an induced `P₅`; otherwise `a2-a-b-e` is a component
`P₄`. -/
theorem side (hG : Gram9 B c) {a b e a2 : Fin 9} (nae : a ≠ e) (hab : B a b = -3)
    (hbe : B b e = -3) (haa : B a a2 = -3) (na2b : a2 ≠ b) (he : ∀ x, B e x = -3 → x = b) :
    False := by
  have nab := hG.ne_of_adj hab
  have nbe := hG.ne_of_adj hbe
  have naa2 := hG.ne_of_adj haa
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have hae : B a e = 1 := hG.nonadj sba hbe nae
  have na2e : a2 ≠ e := by
    rintro rfl
    rw [hae] at haa
    norm_num at haa
  have hba2 : B b a2 = 1 := hG.deg2 sba hbe nae (Ne.symm naa2) na2e na2b
  have hea2 : B e a2 = 1 := hG.one_of_ne (Ne.symm na2e) fun h => na2b (he a2 h)
  by_cases h3 : ∃ a3, a3 ≠ a ∧ B a2 a3 = -3
  · obtain ⟨a3, na3a, h23⟩ := h3
    have na23 := hG.ne_of_adj h23
    have na3b : a3 ≠ b := by
      rintro rfl
      rw [hG.symm, hba2] at h23
      norm_num at h23
    have na3e : a3 ≠ e := by
      rintro rfl
      rw [hG.symm, hea2] at h23
      norm_num at h23
    have haa3 : B a a3 = 1 := hG.deg2 hab haa (Ne.symm na2b) na3b (Ne.symm na23) na3a
    have hba3 : B b a3 = 1 := hG.deg2 sba hbe nae na3a na3e na3b
    have hea3 : B e a3 = 1 := hG.one_of_ne (Ne.symm na3e) fun h => na3b (he a3 h)
    exact hG.no_P5 (Ne.symm na23) na3a na3b na3e naa2.symm na2b na2e nab nae nbe
      (by rw [hG.symm]; exact h23) (by rw [hG.symm]; exact haa3) (by rw [hG.symm]; exact hba3)
      (by rw [hG.symm]; exact hea3) (by rw [hG.symm]; exact haa) (by rw [hG.symm]; exact hba2)
      (by rw [hG.symm]; exact hea2) hab hae hbe
  · push_neg at h3
    refine hG.no_P4comp naa2.symm na2b na2e nab nae nbe (by rw [hG.symm]; exact haa)
      (by rw [hG.symm]; exact hba2) (by rw [hG.symm]; exact hea2) hab hae hbe ?_
    intro x hx2 hxa hxb hxe
    exact ⟨hG.one_of_ne (Ne.symm hx2) (h3 x hxa), hG.deg2 hab haa (Ne.symm na2b) hxb hx2 hxa,
      hG.deg2 sba hbe nae hxa hxe hxb, hG.one_of_ne (Ne.symm hxe) fun h => hxb (he x h)⟩

/-- **No vertex has two neighbours.** -/
theorem no_deg2 (hG : Gram9 B c) {a b e : Fin 9} (nae : a ≠ e) (hab : B a b = -3)
    (hbe : B b e = -3) : False := by
  have nab := hG.ne_of_adj hab
  have nbe := hG.ne_of_adj hbe
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have seb : B e b = -3 := by rw [hG.symm]; exact hbe
  have hae : B a e = 1 := hG.nonadj sba hbe nae
  by_cases ha : ∃ a2, a2 ≠ b ∧ B a a2 = -3
  · obtain ⟨a2, na2b, haa⟩ := ha
    by_cases he : ∃ e2, e2 ≠ b ∧ B e e2 = -3
    · obtain ⟨e2, ne2b, hee⟩ := he
      have naa2 := hG.ne_of_adj haa
      have nee2 := hG.ne_of_adj hee
      have na2e : a2 ≠ e := by
        rintro rfl
        rw [hae] at haa
        norm_num at haa
      have ne2a : e2 ≠ a := by
        rintro rfl
        rw [hG.symm, hae] at hee
        norm_num at hee
      have hba2 : B b a2 = 1 := hG.deg2 sba hbe nae (Ne.symm naa2) na2e na2b
      have hbe2 : B b e2 = 1 := hG.deg2 sba hbe nae ne2a (Ne.symm nee2) ne2b
      by_cases h22 : a2 = e2
      · rw [← h22] at hee
        exact hG.no_C4 nab nae naa2 nbe na2b.symm na2e.symm hab hae haa hbe hba2 hee
      · have hea2 : B e a2 = 1 := hG.deg2 seb hee (Ne.symm ne2b) na2b h22 na2e
        have hae2 : B a e2 = 1 := hG.deg2 hab haa (Ne.symm na2b) ne2b (Ne.symm h22) ne2a
        rcases hG.vals a2 e2 h22 with h | h
        · exact hG.no_P5 naa2.symm na2b na2e h22 nab nae ne2a.symm nbe ne2b.symm nee2
            (by rw [hG.symm]; exact haa) (by rw [hG.symm]; exact hba2)
            (by rw [hG.symm]; exact hea2) h hab hae hae2 hbe hbe2 hee
        · refine hG.no_C5comp nab nae ne2a.symm naa2 nbe ne2b.symm na2b.symm nee2 na2e.symm
            (Ne.symm h22) hab hae hae2 haa hbe hbe2 hba2 hee hea2 (by rw [hG.symm]; exact h) ?_
          intro x hxa hxb hxe hxe2 hxa2
          exact ⟨hG.deg2 hab haa (Ne.symm na2b) hxb hxa2 hxa, hG.deg2 sba hbe nae hxa hxe hxb,
            hG.deg2 seb hee (Ne.symm ne2b) hxb hxe2 hxe,
            hG.deg2 (by rw [hG.symm]; exact hee) (by rw [hG.symm]; exact h) (Ne.symm na2e) hxe
              hxa2 hxe2,
            hG.deg2 (by rw [hG.symm]; exact haa) h ne2a.symm hxa hxe2 hxa2⟩
    · push_neg at he
      exact hG.side nae hab hbe haa na2b fun x hx => by
        by_contra hne
        exact he x hne hx
  · push_neg at ha
    by_cases he : ∃ e2, e2 ≠ b ∧ B e e2 = -3
    · obtain ⟨e2, ne2b, hee⟩ := he
      exact hG.side (Ne.symm nae) seb sba hee ne2b fun x hx => by
        by_contra hne
        exact ha x hne hx
    · push_neg at he
      refine hG.no_P3comp nab nae nbe hab hae hbe fun x hxa hxb hxe => ?_
      exact ⟨hG.one_of_ne (Ne.symm hxa) (ha x hxb), hG.deg2 sba hbe nae hxa hxe hxb,
        hG.one_of_ne (Ne.symm hxe) (he x hxb)⟩


theorem not_partner (hG : Gram9 B c) (hdeg : ∀ x y z, B x y = -3 → B x z = -3 → y = z)
    {v w x y : Fin 9} (hvw : B v w = -3) (hxw : x ≠ w) (hxy : B x y = -3) : y ≠ v :=
  fun e => hxw (hdeg v w x hvw (by rw [hG.symm, ← e]; exact hxy)).symm

end Gram9

/-- **`k = 4`.** For `G = matchMat 9 4 9` (edges `{0,1}, {2,3}, {4,5}, {6,7}`, vertex `8` isolated):
`v = 2·𝟙_E + (√41 - 3)·e₈` has quotient `(21+√41)/2` and `w = e₀ + e₁ - e₂ - e₃` has quotient
`4`, so `c² ≥ (21+√41)/8`. -/
theorem match4 {B : Matrix (Fin 9) (Fin 9) ℝ} {c : ℝ} (hR : RayleighLe B c)
    (hB : B = toR (matchMat 9 4 9)) : (21 + Real.sqrt 41) / 8 ≤ c ^ 2 := by
  set r := Real.sqrt 41 with hr_def
  have hr2 : r ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg 41
  set s := r - 3 with hs_def
  set u1 : Fin 9 → ℤ := ![1, 1, 1, 1, 1, 1, 1, 1, 0] with hu1
  set u2 : Fin 9 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 1] with hu2
  set w : Fin 9 → ℤ := ![1, 1, -1, -1, 0, 0, 0, 0, 0] with hw
  set M := matchMat 9 4 9 with hM
  set V : Fin 9 → ℝ := fun i => 2 * (u1 i : ℝ) + s * (u2 i : ℝ) with hV
  set W : Fin 9 → ℝ := fun i => (w i : ℝ) with hW
  have hWne : W ≠ 0 := fun h => by
    have := congrFun h 0
    simp [hW, hw] at this
  obtain ⟨-, hle⟩ := hR V W hWne
  have eQ : ∀ a b : Fin 9 → ℤ, (((a ⬝ᵥ (M *ᵥ b)) : ℤ) : ℝ) =
      ∑ i, ∑ j, (M i j : ℝ) * ((a i : ℝ) * (b j : ℝ)) := by
    intro a b
    simp only [dotProduct, mulVec, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hQV : V ⬝ᵥ (B *ᵥ V) = 4 * ((u1 ⬝ᵥ (M *ᵥ u1) : ℤ) : ℝ) +
      2 * s * (((u1 ⬝ᵥ (M *ᵥ u2) : ℤ) : ℝ) + ((u2 ⬝ᵥ (M *ᵥ u1) : ℤ) : ℝ)) +
      s ^ 2 * ((u2 ⬝ᵥ (M *ᵥ u2) : ℤ) : ℝ) := by
    rw [hB, quad_eq_sum, eQ, eQ, eQ, eQ]
    simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [toR, map_apply, hV]
    ring
  have q11 : u1 ⬝ᵥ (M *ᵥ u1) = 96 := by rw [hu1, hM]; decide +kernel
  have q12 : u1 ⬝ᵥ (M *ᵥ u2) = 8 := by rw [hu1, hu2, hM]; decide +kernel
  have q21 : u2 ⬝ᵥ (M *ᵥ u1) = 8 := by rw [hu1, hu2, hM]; decide +kernel
  have q22 : u2 ⬝ᵥ (M *ᵥ u2) = 9 := by rw [hu2, hM]; decide +kernel
  have qw : w ⬝ᵥ (M *ᵥ w) = 16 := by rw [hw, hM]; decide +kernel
  have nw : w ⬝ᵥ w = 4 := by rw [hw]; decide +kernel
  have hVV : V ⬝ᵥ V = 32 + s ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, hV, hu1, hu2]
    simp
    ring
  have hQW : W ⬝ᵥ (B *ᵥ W) = 16 := by
    rw [hB, hW, cast_quad, qw]
    norm_num
  have hWW : W ⬝ᵥ W = 4 := by
    rw [hW, cast_dotProduct, nw]
    norm_num
  rw [hQV, q11, q12, q21, q22, hVV, hQW, hWW] at hle
  push_cast at hle
  have hD : 0 < 32 + s ^ 2 := by positivity
  have key : 2 * (21 + r) * (32 + s ^ 2) = (4 * 96 + 2 * s * (8 + 8) + s ^ 2 * 9) * 4 := by
    rw [hs_def]
    linear_combination (2 * r - 6) * hr2
  nlinarith

/-- For one column `k` of a sign matrix with `AAᵀ = 8I + J`, the column sum `u` has `u² ≥ 17`:
with `a` the column and `β = 17a - u𝟙`, one has `Gβ = 136a`, so `0 ≤ ‖Aᵀβ - 136e_k‖² =
136(153 - u²) - 272(153 - u²) + 136²`. -/
theorem col_sum_sq {A : Matrix (Fin 9) (Fin 9) ℝ} (hA : IsSign A)
    (hG : ∀ i j, (A * Aᵀ) i j = if i = j then 9 else 1) (k : Fin 9) :
    17 ≤ (∑ i, A i k) ^ 2 := by
  set a : Fin 9 → ℝ := fun i => A i k with ha
  set u := ∑ i, a i with hu
  have hsq : ∑ i, a i * a i = 9 := by
    have : ∀ i, a i * a i = 1 := fun i => by
      rcases hA i k with h | h <;> simp [ha, h]
    simp [this]
  set β : Fin 9 → ℝ := fun i => 17 * a i - u with hβ
  have hsumβ : ∑ j, β j = 8 * u := by
    simp only [hβ, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← hu]
    ring
  have hGβ : ∀ i, ((A * Aᵀ) *ᵥ β) i = 136 * a i := by
    intro i
    have e : ∀ j, (A * Aᵀ) i j * β j = β j + (if i = j then 8 * β j else 0) := by
      intro j
      rw [hG]
      split_ifs <;> ring
    simp only [mulVec, dotProduct, e, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, hsumβ]
    simp only [hβ]
    ring
  have hy : ∀ (y : Fin 9 → ℝ), y = Aᵀ *ᵥ β → y k = 153 - u ^ 2 := by
    intro y hy
    rw [hy]
    simp only [mulVec, dotProduct, transpose_apply]
    have : ∀ i, A i k * β i = 17 * (a i * a i) - u * a i := fun i => by
      simp only [hβ, ha]; ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hsq]
    rw [← hu]
    ring
  have hyy : (Aᵀ *ᵥ β) ⬝ᵥ (Aᵀ *ᵥ β) = 136 * (153 - u ^ 2) := by
    rw [← dotProduct_gram_mulVec]
    simp only [dotProduct, hGβ]
    have : ∀ i, β i * (136 * a i) = 136 * (17 * (a i * a i) - u * a i) := fun i => by
      simp only [hβ]; ring
    simp only [this, ← Finset.mul_sum, Finset.sum_sub_distrib, hsq]
    rw [← hu]
    ring
  set y := Aᵀ *ᵥ β with hydef
  have hyk := hy y rfl
  have hnn : 0 ≤ ∑ j, (y j - 136 * (if j = k then 1 else 0)) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : ∑ j, (y j - 136 * (if j = k then 1 else 0)) ^ 2 =
      y ⬝ᵥ y - 272 * y k + 18496 := by
    have : ∀ j, (y j - 136 * (if j = k then (1 : ℝ) else 0)) ^ 2 =
        y j * y j + ((if j = k then -272 * y j else 0) + (if j = k then 18496 else 0)) := by
      intro j
      split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      dotProduct]
    ring
  rw [hexp, hyy, hyk] at hnn
  nlinarith

/-- **`k = 0` is impossible.** Paper: "If `k=0`, then `G=8I+J` and `\det G=17\cdot8^8`, which is not
the square of an integer, while `\det G=(\det A)^2`." Here, without determinants: every column sum
`u` of `A` is an integer with `u² ≥ 17` (`col_sum_sq`), hence `u² ≥ 25`, while the squares of the
nine column sums add up to `𝟙ᵀG𝟙 = 153 < 9 · 25`. -/
theorem no_gram_8IJ {A : Matrix (Fin 9) (Fin 9) ℝ} (hA : IsSign A)
    (hG : ∀ i j, (A * Aᵀ) i j = if i = j then 9 else 1) : False := by
  -- the column sums are odd integers with square at least 17, hence at least 25
  have h25 : ∀ k, 25 ≤ (∑ i, A i k) ^ 2 := by
    intro k
    have h17 := col_sum_sq hA hG k
    obtain ⟨z, hz⟩ : ∃ z : ℤ, ∑ i, A i k = z := by
      refine ⟨∑ i, if A i k = 1 then 1 else -1, ?_⟩
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases hA i k with h | h <;> simp [h]
      norm_num
    rw [hz] at h17 ⊢
    have h17' : 17 ≤ z * z := by
      have : ((17 : ℤ) : ℝ) ≤ ((z * z : ℤ) : ℝ) := by push_cast; nlinarith
      exact_mod_cast this
    have : 25 ≤ z * z := by
      rcases le_or_lt |z| 4 with h | h
      · have := mul_le_mul h h (abs_nonneg z) (by norm_num)
        rw [abs_mul_abs_self] at this
        omega
      · have h' : (5 : ℤ) ≤ |z| := Int.lt_iff_add_one_le.mp h
        have := mul_le_mul h' h' (by norm_num) (by positivity)
        rw [abs_mul_abs_self] at this
        exact this
    have : ((25 : ℤ) : ℝ) ≤ ((z * z : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at this
    nlinarith
  -- but the squares of the column sums add up to `𝟙ᵀG𝟙 = 153`
  have hsum : ∑ k, (∑ i, A i k) ^ 2 = 153 := by
    have h1 := dotProduct_gram_mulVec A (fun _ => 1)
    have hl : (fun _ => (1 : ℝ)) ⬝ᵥ ((A * Aᵀ) *ᵥ fun _ => 1) = 153 := by
      have e : ∀ i : Fin 9, ∑ j : Fin 9, (if i = j then (9 : ℝ) else 1) * 1 = 17 := by
        intro i
        have : ∀ j : Fin 9, (if i = j then (9 : ℝ) else 1) * 1 = 1 + (if i = j then 8 else 0) := by
          intro j; split_ifs <;> norm_num
        simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num
      simp only [dotProduct, mulVec, hG, one_mul, e]
      norm_num
    rw [hl] at h1
    rw [h1]
    simp only [dotProduct, mulVec, transpose_apply, mul_one, sq]
  have : ∑ _k : Fin 9, (25 : ℝ) ≤ ∑ k, (∑ i, A i k) ^ 2 := Finset.sum_le_sum fun k _ => h25 k
  rw [hsum] at this
  simp at this
  norm_num at this


namespace Gram9

variable {B : Matrix (Fin 9) (Fin 9) ℝ} {c : ℝ}

/-- **The order-9 bound for the normalised Gram matrix with an edge:** `c² ≥ (21+√41)/8`. -/
theorem bound (hR : RayleighLe B c) (hsym : ∀ i j, B i j = B j i) (hdiag : ∀ i, B i i = 9)
    (hvals : ∀ i j, i ≠ j → B i j = 1 ∨ B i j = -3) (hedge : ∃ p q, B p q = -3) :
    (21 + Real.sqrt 41) / 8 ≤ c ^ 2 := by
  by_contra hlt
  push_neg at hlt
  have hr7 : Real.sqrt 41 < 7 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hG : Gram9 B c := ⟨hR, hsym, hdiag, hvals, by linarith⟩
  have hdeg : ∀ x y z, B x y = -3 → B x z = -3 → y = z := by
    intro x y z h1 h2
    by_contra hyz
    exact hG.no_deg2 hyz (by rw [hsym]; exact h1) h2
  obtain ⟨p1, q1, h1⟩ := hedge
  have s1 : B q1 p1 = -3 := by rw [hsym]; exact h1
  have n_q1_p1 : q1 ≠ p1 := Ne.symm (hG.ne_of_adj h1)
  by_cases E2 : ∃ x y, B x y = -3 ∧ x ≠ p1 ∧ x ≠ q1
  · obtain ⟨p2, q2, h2, n_p2_p1, n_p2_q1⟩ := E2
    have s2 : B q2 p2 = -3 := by rw [hsym]; exact h2
    have n_q2_p2 : q2 ≠ p2 := Ne.symm (hG.ne_of_adj h2)
    have n_q2_p1 : q2 ≠ p1 := hG.not_partner hdeg h1 n_p2_q1 h2
    have n_q2_q1 : q2 ≠ q1 := hG.not_partner hdeg s1 n_p2_p1 h2
    by_cases E3 : ∃ x y, B x y = -3 ∧ x ≠ p1 ∧ x ≠ q1 ∧ x ≠ p2 ∧ x ≠ q2
    · obtain ⟨p3, q3, h3, n_p3_p1, n_p3_q1, n_p3_p2, n_p3_q2⟩ := E3
      have s3 : B q3 p3 = -3 := by rw [hsym]; exact h3
      have n_q3_p3 : q3 ≠ p3 := Ne.symm (hG.ne_of_adj h3)
      have n_q3_p1 : q3 ≠ p1 := hG.not_partner hdeg h1 n_p3_q1 h3
      have n_q3_q1 : q3 ≠ q1 := hG.not_partner hdeg s1 n_p3_p1 h3
      have n_q3_p2 : q3 ≠ p2 := hG.not_partner hdeg h2 n_p3_q2 h3
      have n_q3_q2 : q3 ≠ q2 := hG.not_partner hdeg s2 n_p3_p2 h3
      by_cases E4 : ∃ x y, B x y = -3 ∧ x ≠ p1 ∧ x ≠ q1 ∧ x ≠ p2 ∧ x ≠ q2 ∧ x ≠ p3 ∧ x ≠ q3
      · obtain ⟨p4, q4, h4, n_p4_p1, n_p4_q1, n_p4_p2, n_p4_q2, n_p4_p3, n_p4_q3⟩ := E4
        have s4 : B q4 p4 = -3 := by rw [hsym]; exact h4
        have n_q4_p4 : q4 ≠ p4 := Ne.symm (hG.ne_of_adj h4)
        have n_q4_p1 : q4 ≠ p1 := hG.not_partner hdeg h1 n_p4_q1 h4
        have n_q4_q1 : q4 ≠ q1 := hG.not_partner hdeg s1 n_p4_p1 h4
        have n_q4_p2 : q4 ≠ p2 := hG.not_partner hdeg h2 n_p4_q2 h4
        have n_q4_q2 : q4 ≠ q2 := hG.not_partner hdeg s2 n_p4_p2 h4
        have n_q4_p3 : q4 ≠ p3 := hG.not_partner hdeg h3 n_p4_q3 h4
        have n_q4_q3 : q4 ≠ q3 := hG.not_partner hdeg s3 n_p4_p3 h4
        obtain ⟨f, hf, hBf⟩ := match_sub (n := 9) (k := 4) (by norm_num) hsym 9
          (fun i => by rw [hdiag]; norm_num) hvals hdeg ![p1, q1, p2, q2, p3, q3, p4, q4]
          (injective_eight (Ne.symm n_q1_p1) (Ne.symm n_p2_p1) (Ne.symm n_q2_p1) (Ne.symm n_p3_p1) (Ne.symm n_q3_p1) (Ne.symm n_p4_p1) (Ne.symm n_q4_p1) (Ne.symm n_p2_q1) (Ne.symm n_q2_q1) (Ne.symm n_p3_q1) (Ne.symm n_q3_q1) (Ne.symm n_p4_q1) (Ne.symm n_q4_q1) (Ne.symm n_q2_p2) (Ne.symm n_p3_p2) (Ne.symm n_q3_p2) (Ne.symm n_p4_p2) (Ne.symm n_q4_p2) (Ne.symm n_p3_q2) (Ne.symm n_q3_q2) (Ne.symm n_p4_q2) (Ne.symm n_q4_q2) (Ne.symm n_q3_p3) (Ne.symm n_p4_p3) (Ne.symm n_q4_p3) (Ne.symm n_p4_q3) (Ne.symm n_q4_q3) (Ne.symm n_q4_p4))
          (by intro a ha h; fin_cases a <;> first | exact absurd ha (by decide) | exact h1 | exact h2 | exact h3 | exact h4)
          (fun x y hxy => by
            by_contra hx
            push_neg at hx
            have hy : ∀ a, y ≠ (![p1, q1, p2, q2, p3, q3, p4, q4] : Fin 8 → Fin 9) a := by
              intro a
              fin_cases a
              · exact hG.not_partner hdeg h1 (hx 1) hxy
              · exact hG.not_partner hdeg s1 (hx 0) hxy
              · exact hG.not_partner hdeg h2 (hx 3) hxy
              · exact hG.not_partner hdeg s2 (hx 2) hxy
              · exact hG.not_partner hdeg h3 (hx 5) hxy
              · exact hG.not_partner hdeg s3 (hx 4) hxy
              · exact hG.not_partner hdeg h4 (hx 7) hxy
              · exact hG.not_partner hdeg s4 (hx 6) hxy
            have hxy' := eq_of_not_mem_range (by norm_num) _
              (injective_eight (Ne.symm n_q1_p1) (Ne.symm n_p2_p1) (Ne.symm n_q2_p1) (Ne.symm n_p3_p1) (Ne.symm n_q3_p1) (Ne.symm n_p4_p1) (Ne.symm n_q4_p1) (Ne.symm n_p2_q1) (Ne.symm n_q2_q1) (Ne.symm n_p3_q1) (Ne.symm n_q3_q1) (Ne.symm n_p4_q1) (Ne.symm n_q4_q1) (Ne.symm n_q2_p2) (Ne.symm n_p3_p2) (Ne.symm n_q3_p2) (Ne.symm n_p4_p2) (Ne.symm n_q4_p2) (Ne.symm n_p3_q2) (Ne.symm n_q3_q2) (Ne.symm n_p4_q2) (Ne.symm n_q4_q2) (Ne.symm n_q3_p3) (Ne.symm n_p4_p3) (Ne.symm n_q4_p3) (Ne.symm n_p4_q3) (Ne.symm n_q4_q3) (Ne.symm n_q4_p4)) hx hy
            rw [hxy', hdiag] at hxy
            norm_num at hxy)
        exact absurd (match4 (rayleighLe_submatrix hR hf) hBf) (not_le.2 hlt)
      · obtain ⟨f, hf, hBf⟩ := match_sub (n := 9) (k := 3) (by norm_num) hsym 9
          (fun i => by rw [hdiag]; norm_num) hvals hdeg ![p1, q1, p2, q2, p3, q3]
          (injective_six (Ne.symm n_q1_p1) (Ne.symm n_p2_p1) (Ne.symm n_q2_p1) (Ne.symm n_p3_p1) (Ne.symm n_q3_p1) (Ne.symm n_p2_q1) (Ne.symm n_q2_q1) (Ne.symm n_p3_q1) (Ne.symm n_q3_q1) (Ne.symm n_q2_p2) (Ne.symm n_p3_p2) (Ne.symm n_q3_p2) (Ne.symm n_p3_q2) (Ne.symm n_q3_q2) (Ne.symm n_q3_p3))
          (by intro a ha h; fin_cases a <;> first | exact absurd ha (by decide) | exact h1 | exact h2 | exact h3)
          (fun x y hxy => by
            by_contra hx
            push_neg at hx
            exact E4 ⟨x, y, hxy, hx 0, hx 1, hx 2, hx 3, hx 4, hx 5⟩)
        have := rayleigh_cert (rayleighLe_submatrix hR hf) _ hBf ![5, 5, 5, 5, 5, 5, 8, 8, 8]
          ![1, 1, -1, -1, 0, 0, 0, 0, 0] 2 7 (by norm_num) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        push_cast at this
        linarith [hG.small]
    · obtain ⟨f, hf, hBf⟩ := match_sub (n := 9) (k := 2) (by norm_num) hsym 9
        (fun i => by rw [hdiag]; norm_num) hvals hdeg ![p1, q1, p2, q2]
        (injective_four (Ne.symm n_q1_p1) (Ne.symm n_p2_p1) (Ne.symm n_q2_p1) (Ne.symm n_p2_q1) (Ne.symm n_q2_q1) (Ne.symm n_q2_p2))
        (by intro a ha h; fin_cases a <;> first | exact absurd ha (by decide) | exact h1 | exact h2)
        (fun x y hxy => by
          by_contra hx
          push_neg at hx
          exact E3 ⟨x, y, hxy, hx 0, hx 1, hx 2, hx 3⟩)
      have := rayleigh_cert (rayleighLe_submatrix hR hf) _ hBf ![2, 2, 2, 2, 3, 3, 3, 3, 3]
        ![1, 1, -1, -1, 0, 0, 0, 0, 0] 2 7 (by norm_num) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      push_cast at this
      linarith [hG.small]
  · obtain ⟨f, hf, hBf⟩ := match_sub (n := 9) (k := 1) (by norm_num) hsym 9
      (fun i => by rw [hdiag]; norm_num) hvals hdeg ![p1, q1]
      (injective_two (Ne.symm n_q1_p1))
      (by intro a ha h; fin_cases a <;> first | exact absurd ha (by decide) | exact h1)
      (fun x y hxy => by
        by_contra hx
        push_neg at hx
        exact E2 ⟨x, y, hxy, hx 0, hx 1⟩)
    have := rayleigh_cert (rayleighLe_submatrix hR hf) _ hBf ![2, 2, 3, 3, 3, 3, 3, 3, 3]
      ![-5, -5, 1, 1, 1, 1, 1, 1, 1] 2 7 (by norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
    push_cast at this
    linarith [hG.small]
end Gram9

/-- **Order 9, lower bound.** Every `9 × 9` sign matrix with `κ(A) ≤ c` has `c² ≥ (21+√41)/8`. -/
theorem order9_lower {A : Matrix (Fin 9) (Fin 9) ℝ} (hA : IsSign A) {c : ℝ} (h : CondLe A c) :
    (21 + Real.sqrt 41) / 8 ≤ c ^ 2 := by
  obtain ⟨A', hA', hc', heven⟩ := exists_even_rows (by norm_num) hA
  have h' := hc' c h
  by_contra hlt
  push_neg at hlt
  have hr7 : Real.sqrt 41 < 7 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h7 : 2 * c ^ 2 < 7 := by linarith
  have hR := rayleighLe_of_condLe h'
  have hdiag : ∀ i, (A' * A'ᵀ) i i = 9 := fun i => by rw [gram_diag hA']; norm_num
  have vals : ∀ i j, i ≠ j → (A' * A'ᵀ) i j = 1 ∨ (A' * A'ᵀ) i j = -3 := by
    intro i j hij
    obtain ⟨g, hg, hmod⟩ := lem_tools_one hA' i j (by rw [heven i, heven j])
    obtain ⟨h1, h2⟩ := rayleigh_pair hR (gram_symm A') hdiag hij
    rw [hg] at h1 h2 ⊢
    have hg9 : |g| < 9 := by exact_mod_cast h2
    rw [abs_lt] at hg9
    unfold Int.ModEq at hmod
    have : g = -7 ∨ g = -3 ∨ g = 1 ∨ g = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · norm_num at h1
      nlinarith
    · right; norm_num
    · left; norm_num
    · norm_num at h1
      nlinarith
  by_cases hedge : ∃ p q, (A' * A'ᵀ) p q = -3
  · exact absurd (Gram9.bound hR (gram_symm A') hdiag vals hedge) (not_le.2 hlt)
  · push_neg at hedge
    refine no_gram_8IJ hA' fun i j => ?_
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hdiag]
    · rw [if_neg hij]
      exact (vals i j hij).resolve_right (hedge i j)

/-- **Theorem `thm:small`, `h(9) = (1+√41)/4`.** The matrix `A₉` has `κ(A₉) ≤ (1+√41)/4`, and every
`9 × 9` sign matrix with `κ(A) ≤ c'`, `c' ≥ 0`, has `(1+√41)/4 ≤ c'`. -/
theorem hval_9 : HVal 9 ((1 + Real.sqrt 41) / 4) := by
  refine ⟨⟨A9, isSign_A9, condLe_A9⟩, fun A hA c' hc' h => ?_⟩
  have hb := order9_lower hA h
  have hr2 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have hs : ((1 + Real.sqrt 41) / 4) ^ 2 = (21 + Real.sqrt 41) / 8 := by
    nlinarith
  have hpos : 0 ≤ (1 + Real.sqrt 41) / 4 := by positivity
  nlinarith

end SignCond
