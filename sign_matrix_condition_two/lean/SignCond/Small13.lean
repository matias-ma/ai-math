import SignCond.SmallGraph

/-!
# Section `sec:small`, paragraph "Order 13": `h(13) = 5/(2√3)`

Paper: "Suppose that `\kappa(A)^2<\tfrac{25}{12}`, and negate rows so that every row has an even
number of entries `-1`. The off-diagonal entries of `G` are congruent to `1` modulo `4`, and
\Cref{lem:tools} excludes `|g|\ge5`, since `(13+5)/(13-5)=\tfrac94`. Hence `G=12I+J-4N`, where `N`
is the adjacency matrix of the graph `\Gamma` of pairs of rows with inner product `-3`. [...]
Therefore `\Gamma` consists of `k\le6` disjoint edges and `13-2k` isolated vertices. [...] Hence
`k=0` and `G=12I+J`, with eigenvalues `12` and `25`, which is again a contradiction."

Formalisation (`Gram13`: symmetric, diagonal `13`, off-diagonal entries `1` or `-3`, Rayleigh form
of ratio `c` with `12c² < 25`; an edge of `Γ` is an entry `-3`).
* Forbidden induced subgraphs, each by two integer test vectors on a principal submatrix:
  `no_tri` (`K₃`), `no_claw` (`K_{1,3}`), `no_C4` (`C₄`), `no_P5` (`P₅`). Hence all degrees are at
  most `2` (`no_three`, `deg2`).
* The components `P₃`, `P₄`, `C₅` are excluded by the paper's whole-matrix vectors (`comp_cert`):
  `w` = the paper's vector (scaled: `(3,6,3)` and `-1` elsewhere; `(3,6,6,3)` and `-2`; `2` and
  `-1`), whose quotient is at most `q = 121/16, 52/7, 45/7`, against an integer vector `v` on the
  component with quotient `301/17, 240/13, 240/13` for the exact matrix `12I + J - 4N_Λ` (the paper
  uses `L = 12 - 4λ_min(N_Λ)` and `J ⪰ 0`).
* `no_deg2`: no vertex has two neighbours. The paper's route "components are paths and cycles, hence
  `P₁, …, P₄, C₅`" is followed explicitly from a path `a-b-e`: according to whether `a` and `e`
  have further neighbours, one meets `P₃` (`no_P3comp`), `P₄` (`side`, `no_P4comp`), `C₄`, `P₅` or
  `C₅` (`no_C5comp`).
* So `Γ` is a matching. Instead of Lemma `lem:matching`: if `Γ` has an edge `pq`, every row sum of
  `G` is at least `21` (`rowsum_ge`), so `𝟙` has quotient at least `21`, and `e_p + e_q` has quotient
  `10`; `21/10 > 25/12`. If `Γ` has no edge, `G = 12I + J`, and `v = 𝟙` (`25`), `w = e₀ - e₁`
  (`12`) give `c² ≥ 25/12`.
-/

open Matrix

namespace SignCond

/-- The normalised Gram matrix of order `13` under the assumption `κ(A)² < 25/12`. -/
structure Gram13 (B : Matrix (Fin 13) (Fin 13) ℝ) (c : ℝ) : Prop where
  ray : RayleighLe B c
  symm : ∀ i j, B i j = B j i
  diag : ∀ i, B i i = 13
  vals : ∀ i j, i ≠ j → B i j = 1 ∨ B i j = -3
  small : 12 * c ^ 2 < 25

namespace Gram13

variable {B : Matrix (Fin 13) (Fin 13) ℝ} {c : ℝ}

/-- A principal submatrix with an integer certificate `25 (wᵀMw)(vᵀv) ≤ 12 (vᵀMv)(wᵀw)`
contradicts `12c² < 25`. -/
theorem cert_contra (hG : Gram13 B c) {k : ℕ} {f : Fin k → Fin 13} (hf : Function.Injective f)
    (M : Matrix (Fin k) (Fin k) ℤ) (hM : B.submatrix f f = toR M) (v w : Fin k → ℤ)
    (hv : 0 < v ⬝ᵥ v) (hw : 0 < w ⬝ᵥ w)
    (hcert : 25 * ((w ⬝ᵥ (M *ᵥ w)) * (v ⬝ᵥ v)) ≤ 12 * ((v ⬝ᵥ (M *ᵥ v)) * (w ⬝ᵥ w))) : False := by
  have := rayleigh_cert (rayleighLe_submatrix hG.ray hf) M hM v w 12 25 (by norm_num) hv hw hcert
  push_cast at this
  linarith [hG.small]

theorem le_one (hG : Gram13 B c) (i j : Fin 13) (hij : i ≠ j) : B i j ≤ 1 := by
  rcases hG.vals i j hij with h | h <;> rw [h] <;> norm_num

theorem ne_of_adj (hG : Gram13 B c) {i j : Fin 13} (h : B i j = -3) : i ≠ j := by
  rintro rfl
  rw [hG.diag] at h
  norm_num at h

theorem one_of_ne (hG : Gram13 B c) {i j : Fin 13} (hij : i ≠ j) (h : B i j ≠ -3) : B i j = 1 :=
  (hG.vals i j hij).resolve_right h

/-- **Triangle** (`K₃`): eigenvalues `7` and `16`; `v = (1,-1,0)`, `w = (1,1,1)`. -/
theorem no_tri (hG : Gram13 B c) {i j k : Fin 13}
    (nij : i ≠ j) (nik : i ≠ k) (njk : j ≠ k)
    (hij : B i j = -3) (hik : B i k = -3) (hjk : B j k = -3) : False := by
  have sji : B j i = -3 := by rw [hG.symm]; exact hij
  have ski : B k i = -3 := by rw [hG.symm]; exact hik
  have skj : B k j = -3 := by rw [hG.symm]; exact hjk
  have hM : B.submatrix ![i, j, k] ![i, j, k] = toR !![13, -3, -3; -3, 13, -3; -3, -3, 13] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hij, hik, hjk, sji, ski, skj]
  exact hG.cert_contra (injective_three nij nik njk) _ hM
    ![1, -1, 0] ![1, 1, 1] (by decide) (by decide) (by decide)

/-- **`K_{1,3}`**: eigenvalues `14 ± 2√7`; `v = (3,-2,-2,-2)` (quotient `135/7`), `w = (-4,-2,-2,-2)` (`61/7`). -/
theorem no_claw (hG : Gram13 B c) {i j k l : Fin 13}
    (nij : i ≠ j) (nik : i ≠ k) (nil : i ≠ l) (njk : j ≠ k) (njl : j ≠ l) (nkl : k ≠ l)
    (hij : B i j = -3) (hik : B i k = -3) (hil : B i l = -3) (hjk : B j k = 1) (hjl : B j l = 1) (hkl : B k l = 1) : False := by
  have sji : B j i = -3 := by rw [hG.symm]; exact hij
  have ski : B k i = -3 := by rw [hG.symm]; exact hik
  have sli : B l i = -3 := by rw [hG.symm]; exact hil
  have skj : B k j = 1 := by rw [hG.symm]; exact hjk
  have slj : B l j = 1 := by rw [hG.symm]; exact hjl
  have slk : B l k = 1 := by rw [hG.symm]; exact hkl
  have hM : B.submatrix ![i, j, k, l] ![i, j, k, l] = toR !![13, -3, -3, -3; -3, 13, 1, 1; -3, 1, 13, 1; -3, 1, 1, 13] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hij, hik, hil, hjk, hjl, hkl, sji, ski, sli, skj, slj, slk]
  exact hG.cert_contra (injective_four nij nik nil njk njl nkl) _ hM
    ![3, -2, -2, -2] ![-4, -2, -2, -2] (by decide) (by decide) (by decide)

/-- **`C₄`** `a-b-c-d-a`: eigenvalues `8` (at `𝟙`) and `20` (at `(1,-1,1,-1)`). -/
theorem no_C4 (hG : Gram13 B c) {a b d e : Fin 13}
    (nab : a ≠ b) (nad : a ≠ d) (nae : a ≠ e) (nbd : b ≠ d) (nbe : b ≠ e) (nde : d ≠ e)
    (hab : B a b = -3) (had : B a d = 1) (hae : B a e = -3) (hbd : B b d = -3) (hbe : B b e = 1) (hde : B d e = -3) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sda : B d a = 1 := by rw [hG.symm]; exact had
  have sea : B e a = -3 := by rw [hG.symm]; exact hae
  have sdb : B d b = -3 := by rw [hG.symm]; exact hbd
  have seb : B e b = 1 := by rw [hG.symm]; exact hbe
  have sed : B e d = -3 := by rw [hG.symm]; exact hde
  have hM : B.submatrix ![a, b, d, e] ![a, b, d, e] = toR !![13, -3, 1, -3; -3, 13, -3, 1; 1, -3, 13, -3; -3, 1, -3, 13] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hab, had, hae, hbd, hbe, hde, sba, sda, sea, sdb, seb, sed]
  exact hG.cert_contra (injective_four nab nad nae nbd nbe nde) _ hM
    ![1, -1, 1, -1] ![1, 1, 1, 1] (by decide) (by decide) (by decide)

/-- **`P₅`** `a-b-c-d-e`: eigenvalue `8` at `(-1,-1,0,1,1)` and quotient `93/5` at `(1,-1,1,-1,1)`. -/
theorem no_P5 (hG : Gram13 B c) {a b d e f : Fin 13}
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
  have hM : B.submatrix ![a, b, d, e, f] ![a, b, d, e, f] = toR !![13, -3, 1, 1, 1; -3, 13, -3, 1, 1; 1, -3, 13, -3, 1; 1, 1, -3, 13, -3; 1, 1, 1, -3, 13] := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [toR, hG.diag, hab, had, hae, haf, hbd, hbe, hbf, hde, hdf, hef, sba, sda, sea, sfa, sdb, seb, sfb, sed, sfd, sfe]
  exact hG.cert_contra (injective_five nab nad nae naf nbd nbe nbf nde ndf nef) _ hM
    ![1, -1, 1, -1, 1] ![-1, -1, 0, 1, 1] (by decide) (by decide) (by decide)
/-- The neighbours of a vertex are pairwise nonadjacent (no triangle). -/
theorem nonadj (hG : Gram13 B c) {i j k : Fin 13} (hij : B i j = -3) (hik : B i k = -3)
    (hjk : j ≠ k) : B j k = 1 :=
  hG.one_of_ne hjk fun h => hG.no_tri (hG.ne_of_adj hij) (hG.ne_of_adj hik) hjk hij hik h

/-- No vertex has three neighbours (`K₃` and `K_{1,3}`). -/
theorem no_three (hG : Gram13 B c) {i j k l : Fin 13} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hij : B i j = -3) (hik : B i k = -3) (hil : B i l = -3) : False :=
  hG.no_claw (hG.ne_of_adj hij) (hG.ne_of_adj hik) (hG.ne_of_adj hil) hjk hjl hkl hij hik hil
    (hG.nonadj hij hik hjk) (hG.nonadj hij hil hjl) (hG.nonadj hik hil hkl)

/-- **Degrees are at most `2`**: a vertex with neighbours `j ≠ k` has no further neighbour. -/
theorem deg2 (hG : Gram13 B c) {i j k x : Fin 13} (hij : B i j = -3) (hik : B i k = -3)
    (hjk : j ≠ k) (hxj : x ≠ j) (hxk : x ≠ k) (hxi : x ≠ i) : B i x = 1 :=
  hG.one_of_ne (Ne.symm hxi) fun h => hG.no_three hjk (Ne.symm hxj) (Ne.symm hxk) hij hik h

/-- **The component `P₃`** `a-b-e`: `w = (3,6,3)` on the path and `-1` elsewhere (quotient at most
`121/16`), `v = (2,-3,2)` on the path (quotient `301/17`). -/
theorem no_P3comp (hG : Gram13 B c) {a b e : Fin 13} (nab : a ≠ b) (nae : a ≠ e) (nbe : b ≠ e)
    (hab : B a b = -3) (hae : B a e = 1) (hbe : B b e = -3)
    (hcl : ∀ x, x ≠ a → x ≠ b → x ≠ e → B a x = 1 ∧ B b x = 1 ∧ B e x = 1) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sea : B e a = 1 := by rw [hG.symm]; exact hae
  have seb : B e b = -3 := by rw [hG.symm]; exact hbe
  have hin : ∀ u v : Fin 3, B (![a, b, e] u) (![a, b, e] v) =
      (((!![13, -3, 1; -3, 13, -3; 1, -3, 13] : Matrix (Fin 3) (Fin 3) ℤ) u v : ℤ) : ℝ) := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [hG.diag, hab, hae, hbe, sba, sea, seb]
  have hclosed : ∀ u x, (∀ v, x ≠ ![a, b, e] v) → B (![a, b, e] u) x = 1 := by
    intro u x hx
    have h0 : x ≠ a := hx 0
    have h1 : x ≠ b := hx 1
    have h2 : x ≠ e := hx 2
    obtain ⟨ha, hb, he⟩ := hcl x h0 h1 h2
    fin_cases u <;> simp [ha, hb, he]
  have := comp_cert (n := 13) (by norm_num) hG.ray hG.symm 13
    (fun i => by rw [hG.diag]; norm_num) hG.le_one ![a, b, e] (injective_three nab nae nbe) _ hin
    hclosed ![2, -3, 2] ![3, 6, 3] (-1) 12 25 (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  push_cast at this
  linarith [hG.small]

/-- **The component `P₄`** `a-b-d-e`: `w = (3,6,6,3)` on the path and `-2` elsewhere (quotient at
most `52/7`), `v = (2,-3,3,-2)` on the path (quotient `240/13`). -/
theorem no_P4comp (hG : Gram13 B c) {a b d e : Fin 13}
    (nab : a ≠ b) (nad : a ≠ d) (nae : a ≠ e) (nbd : b ≠ d) (nbe : b ≠ e) (nde : d ≠ e)
    (hab : B a b = -3) (had : B a d = 1) (hae : B a e = 1) (hbd : B b d = -3) (hbe : B b e = 1)
    (hde : B d e = -3)
    (hcl : ∀ x, x ≠ a → x ≠ b → x ≠ d → x ≠ e →
      B a x = 1 ∧ B b x = 1 ∧ B d x = 1 ∧ B e x = 1) : False := by
  have sba : B b a = -3 := by rw [hG.symm]; exact hab
  have sda : B d a = 1 := by rw [hG.symm]; exact had
  have sea : B e a = 1 := by rw [hG.symm]; exact hae
  have sdb : B d b = -3 := by rw [hG.symm]; exact hbd
  have seb : B e b = 1 := by rw [hG.symm]; exact hbe
  have sed : B e d = -3 := by rw [hG.symm]; exact hde
  have hin : ∀ u v : Fin 4, B (![a, b, d, e] u) (![a, b, d, e] v) =
      (((!![13, -3, 1, 1; -3, 13, -3, 1; 1, -3, 13, -3; 1, 1, -3, 13] :
        Matrix (Fin 4) (Fin 4) ℤ) u v : ℤ) : ℝ) := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [hG.diag, hab, had, hae, hbd, hbe, hde, sba, sda, sea,
      sdb, seb, sed]
  have hclosed : ∀ u x, (∀ v, x ≠ ![a, b, d, e] v) → B (![a, b, d, e] u) x = 1 := by
    intro u x hx
    have h0 : x ≠ a := hx 0
    have h1 : x ≠ b := hx 1
    have h2 : x ≠ d := hx 2
    have h3 : x ≠ e := hx 3
    obtain ⟨ha, hb, hd, he⟩ := hcl x h0 h1 h2 h3
    fin_cases u <;> simp [ha, hb, hd, he]
  have := comp_cert (n := 13) (by norm_num) hG.ray hG.symm 13
    (fun i => by rw [hG.diag]; norm_num) hG.le_one ![a, b, d, e]
    (injective_four nab nad nae nbd nbe nde) _ hin hclosed ![2, -3, 3, -2] ![3, 6, 6, 3] (-2) 12 25
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  push_cast at this
  linarith [hG.small]

/-- **The component `C₅`** `a-b-d-e-f-a`: `w = 2` on the cycle and `-1` elsewhere (quotient at most
`45/7`), `v = (3,-2,0,2,-3)` on the cycle (quotient `240/13`). -/
theorem no_C5comp (hG : Gram13 B c) {a b d e f : Fin 13}
    (nab : a ≠ b) (nad : a ≠ d) (nae : a ≠ e) (naf : a ≠ f) (nbd : b ≠ d) (nbe : b ≠ e)
    (nbf : b ≠ f) (nde : d ≠ e) (ndf : d ≠ f) (nef : e ≠ f)
    (hab : B a b = -3) (had : B a d = 1) (hae : B a e = 1) (haf : B a f = -3) (hbd : B b d = -3)
    (hbe : B b e = 1) (hbf : B b f = 1) (hde : B d e = -3) (hdf : B d f = 1) (hef : B e f = -3)
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
      (((!![13, -3, 1, 1, -3; -3, 13, -3, 1, 1; 1, -3, 13, -3, 1; 1, 1, -3, 13, -3;
        -3, 1, 1, -3, 13] : Matrix (Fin 5) (Fin 5) ℤ) u v : ℤ) : ℝ) := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [hG.diag, hab, had, hae, haf, hbd, hbe, hbf, hde, hdf,
      hef, sba, sda, sea, sfa, sdb, seb, sfb, sed, sfd, sfe]
  have hclosed : ∀ u x, (∀ v, x ≠ ![a, b, d, e, f] v) → B (![a, b, d, e, f] u) x = 1 := by
    intro u x hx
    have h0 : x ≠ a := hx 0
    have h1 : x ≠ b := hx 1
    have h2 : x ≠ d := hx 2
    have h3 : x ≠ e := hx 3
    have h4 : x ≠ f := hx 4
    obtain ⟨ha, hb, hd, he, hf⟩ := hcl x h0 h1 h2 h3 h4
    fin_cases u <;> simp [ha, hb, hd, he, hf]
  have := comp_cert (n := 13) (by norm_num) hG.ray hG.symm 13
    (fun i => by rw [hG.diag]; norm_num) hG.le_one ![a, b, d, e, f]
    (injective_five nab nad nae naf nbd nbe nbf nde ndf nef) _ hin hclosed ![3, -2, 0, 2, -3]
    ![2, 2, 2, 2, 2] (-1) 12 25 (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  push_cast at this
  linarith [hG.small]

/-- **One side.** A path `a2-a-b-e` in which `e` has no neighbour besides `b`: if `a2` has a
further neighbour `a3`, then `a3-a2-a-b-e` is an induced `P₅`; otherwise `a2-a-b-e` is a component
`P₄`. -/
theorem side (hG : Gram13 B c) {a b e a2 : Fin 13} (nae : a ≠ e) (hab : B a b = -3)
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
theorem no_deg2 (hG : Gram13 B c) {a b e : Fin 13} (nae : a ≠ e) (hab : B a b = -3)
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


/-- **The order-13 bound for the normalised Gram matrix:** `c² ≥ 25/12`. -/
theorem bound (hR : RayleighLe B c) (hsym : ∀ i j, B i j = B j i) (hdiag : ∀ i, B i i = 13)
    (hvals : ∀ i j, i ≠ j → B i j = 1 ∨ B i j = -3) : 25 ≤ 12 * c ^ 2 := by
  by_contra hlt
  push_neg at hlt
  have hG : Gram13 B c := ⟨hR, hsym, hdiag, hvals, hlt⟩
  by_cases hedge : ∃ p q, B p q = -3
  · obtain ⟨p, q, hpq⟩ := hedge
    have npq := hG.ne_of_adj hpq
    -- `Γ` is a matching
    have hdeg : ∀ i j k, B i j = -3 → B i k = -3 → j = k := by
      intro i j k h1 h2
      by_contra hjk
      exact hG.no_deg2 hjk (by rw [hsym]; exact h1) h2
    -- every row sum is at least `21`
    have hrow : ∀ i, (21 : ℝ) ≤ ∑ j, B i j := by
      intro i
      by_cases hi : ∃ j0, B i j0 = -3
      · obtain ⟨j0, hj0⟩ := hi
        have := rowsum_ge i j0 (hG.ne_of_adj hj0).symm 13 (hdiag i) (by rw [hj0])
          (fun j hji hjj0 => hG.one_of_ne (Ne.symm hji) fun h => hjj0 (hdeg i j j0 h hj0))
        norm_num at this
        linarith
      · push_neg at hi
        obtain ⟨j0, hj0⟩ := exists_ne i
        have := rowsum_ge i j0 hj0 13 (hdiag i)
          (by rcases hvals i j0 (Ne.symm hj0) with h | h <;> rw [h] <;> norm_num)
          (fun j hji _ => hG.one_of_ne (Ne.symm hji) (hi j))
        norm_num at this
        linarith
    have hsum : (273 : ℝ) ≤ ∑ i, ∑ j, B i j := by
      calc (273 : ℝ) = ∑ _i : Fin 13, (21 : ℝ) := by simp; norm_num
        _ ≤ _ := Finset.sum_le_sum fun i _ => hrow i
    have hw : extV ![p, q] ![(1 : ℝ), 1] ≠ 0 :=
      extV_ne_zero (injective_two npq) fun h => by simpa using congrFun h 0
    obtain ⟨-, hle⟩ := hR (fun _ => 1) (extV ![p, q] ![(1 : ℝ), 1]) hw
    have hQv : (fun _ => (1 : ℝ)) ⬝ᵥ (B *ᵥ fun _ => 1) = ∑ i, ∑ j, B i j := by
      simp [dotProduct, mulVec]
    have hvv : (fun _ => (1 : ℝ)) ⬝ᵥ (fun _ => (1 : ℝ) : Fin 13 → ℝ) = 13 := by
      simp [dotProduct]
    have hQw : extV ![p, q] ![(1 : ℝ), 1] ⬝ᵥ (B *ᵥ extV ![p, q] ![(1 : ℝ), 1]) = 20 := by
      rw [quad_extV, quad_two, hdiag, hdiag, hpq, hsym q p, hpq]
      norm_num
    have hww : extV ![p, q] ![(1 : ℝ), 1] ⬝ᵥ extV ![p, q] ![(1 : ℝ), 1] = 2 := by
      rw [norm_extV (injective_two npq)]
      simp [dotProduct, Fin.sum_univ_two]
      norm_num
    rw [hQv, hvv, hQw, hww] at hle
    nlinarith
  · push_neg at hedge
    have hB : B = toR (Matrix.of fun i j : Fin 13 => if i = j then (13 : ℤ) else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [toR, hdiag]
      · simp [toR, hij, hG.one_of_ne hij (hedge i j)]
    have := rayleigh_cert hR _ hB (fun _ => 1) ![1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 12 25
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    push_cast at this
    linarith

end Gram13

/-- **Order 13, lower bound.** Every `13 × 13` sign matrix with `κ(A) ≤ c` has `c² ≥ 25/12`. -/
theorem order13_lower {A : Matrix (Fin 13) (Fin 13) ℝ} (hA : IsSign A) {c : ℝ}
    (h : CondLe A c) : 25 ≤ 12 * c ^ 2 := by
  obtain ⟨A', hA', hc', heven⟩ := exists_even_rows (by norm_num) hA
  have h' := hc' c h
  by_contra hlt
  push_neg at hlt
  have hR := rayleighLe_of_condLe h'
  have hdiag : ∀ i, (A' * A'ᵀ) i i = 13 := fun i => by rw [gram_diag hA']; norm_num
  have vals : ∀ i j, i ≠ j → (A' * A'ᵀ) i j = 1 ∨ (A' * A'ᵀ) i j = -3 := by
    intro i j hij
    obtain ⟨g, hg, hmod⟩ := lem_tools_one hA' i j (by rw [heven i, heven j])
    obtain ⟨h1, h2⟩ := rayleigh_pair hR (gram_symm A') hdiag hij
    rw [hg] at h1 h2 ⊢
    have hg13 : |g| < 13 := by exact_mod_cast h2
    rw [abs_lt] at hg13
    unfold Int.ModEq at hmod
    have : g = -11 ∨ g = -7 ∨ g = -3 ∨ g = 1 ∨ g = 5 ∨ g = 9 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num at h1
      nlinarith
    · norm_num at h1
      nlinarith
    · right; norm_num
    · left; norm_num
    · norm_num at h1
      nlinarith
    · norm_num at h1
      nlinarith
  exact absurd (Gram13.bound hR (gram_symm A') hdiag vals) (not_le.2 hlt)

/-- **Theorem `thm:small`, `h(13) = 5/(2√3)`.** The circulant `A₁₃` has `κ(A₁₃) ≤ 5/(2√3)`, and
every `13 × 13` sign matrix with `κ(A) ≤ c'`, `c' ≥ 0`, has `5/(2√3) ≤ c'`. -/
theorem hval_13 : HVal 13 (5 / (2 * Real.sqrt 3)) := by
  refine ⟨⟨A13, isSign_A13, condLe_A13⟩, fun A hA c' hc' h => ?_⟩
  have h25 := order13_lower hA h
  have hs : (5 / (2 * Real.sqrt 3)) ^ 2 = 25 / 12 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hpos : 0 ≤ 5 / (2 * Real.sqrt 3) := by positivity
  nlinarith

end SignCond
