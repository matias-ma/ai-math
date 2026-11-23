import SignCond.Basic
import SignCond.Doubling
import SignCond.OrderThree
import SignCond.GoethalsSeidel
import SignCond.PowerCertificate
import SignCond.Sector
import SignCond.Golay
import SignCond.MaskLift
import SignCond.Rows
import SignCond.Tails
import SignCond.LargeArith

/-!
# The paper's objects, under the paper's names

Every definition quotes the paper (`../paper/main.tex`). Objects that already existed in the
development are reused and only listed here:

* `IsSign A` (sign matrix), `CondLe A c` (the window `tI ⪯ AAᵀ ⪯ c²tI` for some `t > 0`, i.e.
  `κ(A) ≤ c`) — `Basic.lean`;
* `W2` (`W₂`) — `Doubling.lean`;
* `circ x` (`C(x)`, entries `x_{v-u}`), `rev` (`R`, `R e_u = e_{-u}`), `gsArray` (the block array of
  eq. `GS`), `quat r` (`𝒬(r)`) — `GoethalsSeidel.lean`;
* `peval x z` (the polynomial `x(z) = Σ_v x_v z^v` of a sequence `x : Fin n → ℤ`), `IsSignSeq`,
  `IsGolay` (`|P(z)|² + |Q(z)|² = 2n` on `|z| = 1`), `seqRev` (`x^rev`), `liftP`/`liftQ`
  (coefficients of the lift), `sqP`/`sqQ` (coefficients of Lemma `lem:square`), `halfSum`/`halfDiff`
  (`U = ½(A+B)`, `V = ½(A-B)`) — `Golay.lean`;
* `pS S z` (`p_S(z) = Σ_{x∈S} z^x`), `maskLift S` (`4S ∪ (4S+1)`) — `MaskLift.lean`;
* `InG n` (`n ∈ 𝒢`), `TailPair r B` (a balanced pair of length `r` with energy at most `B`),
  `golayA10`, `golayB10`, `golayA26`, `golayB26` (`A₁₀, B₁₀, A₂₆, B₂₆`) — `Tails.lean`;
* `ev`, `conv`, `convPow` (`q̂`, cyclic convolution, `q^{*k}`) — `PowerCertificate.lean`.
-/

open Matrix Complex
open scoped Real

namespace SignCond

/-! ## Section 3: circulants, the Goethals–Seidel array, the border -/

section Circulants

variable {j : ℕ} [NeZero j]

/-- `ω = e^{2πi/j}`. -/
noncomputable def omega (j : ℕ) : ℂ := exp (2 * π * I / j)

/-- Paper: "`x̂(ℓ) := Σ_v x_v ω^{ℓ v}`" for `x ∈ ℝ^j` indexed by `ℤ/jℤ` (the exponent uses the
representative `v.val ∈ {0, …, j-1}`; `ω^j = 1`). -/
noncomputable def hat (x : ZMod j → ℝ) (ℓ : ℕ) : ℂ := ∑ v : ZMod j, (x v : ℂ) * omega j ^ (ℓ * v.val)

/-- A sign vector of length `j`: every entry is `±1`. -/
def IsSignVec (x : ZMod j → ℝ) : Prop := ∀ v, x v = 1 ∨ x v = -1

/-- The sum of the entries of `x`. -/
def vsum (x : ZMod j → ℝ) : ℝ := ∑ v, x v

/-- Paper, eq. `GS`: `Z = [[A, BR, CR, DR], [-BR, A, -DᵀR, CᵀR], [-CR, DᵀR, A, -BᵀR],
[-DR, -CᵀR, BᵀR, A]]` with `A = C(a), …, D = C(d)`, as a matrix indexed by `Fin 4 × ℤ/jℤ`
(block `p`, position `u`). -/
def Zgs (a b c d : ZMod j → ℝ) : Matrix (Fin 4 × ZMod j) (Fin 4 × ZMod j) ℝ :=
  gsArray (circ a) (circ b) (circ c) (circ d) rev

/-- Paper: "we define its *energy* at frequency `ℓ` by
`E_ℓ := |â(ℓ)|² + |b̂(ℓ)|² + |ĉ(ℓ)|² + |d̂(ℓ)|²`". -/
noncomputable def energy (a b c d : ZMod j → ℝ) (ℓ : ℕ) : ℝ :=
  ‖hat a ℓ‖ ^ 2 + ‖hat b ℓ‖ ^ 2 + ‖hat c ℓ‖ ^ 2 + ‖hat d ℓ‖ ^ 2

/-- The indicator vector `𝟙_S` of `S ⊆ ℤ/jℤ`. -/
def ind (S : Finset (ZMod j)) : ZMod j → ℝ := fun x => if x ∈ S then 1 else 0

/-- Paper: "`Ŝ(ℓ) = Σ_{x∈S} ω^{ℓx}`". -/
noncomputable def Shat (S : Finset (ZMod j)) (ℓ : ℕ) : ℂ := ∑ x ∈ S, omega j ^ (ℓ * x.val)

/-- Paper (Lemma `lem:criterion`): "`δ_ℓ = 2 max_i |Ŝ_i(ℓ)|`". -/
noncomputable def deltaL (S : Fin 4 → Finset (ZMod j)) (ℓ : ℕ) : ℝ :=
  2 * max (max ‖Shat (S 0) ℓ‖ ‖Shat (S 1) ℓ‖) (max ‖Shat (S 2) ℓ‖ ‖Shat (S 3) ℓ‖)

/-- Paper, eq. `pools`: "`a_x = -σ` for `x ∈ S₀`, `c_x = σ` for `x ∈ S₁`, `d_x = σ` for `x ∈ S₂`,
`b_x = σ` for `x ∈ S₃`" (the masks). -/
def Pools (σ : ℝ) (a b c d : ZMod j → ℝ) (S : Fin 4 → Finset (ZMod j)) : Prop :=
  (∀ x ∈ S 0, a x = -σ) ∧ (∀ x ∈ S 1, c x = σ) ∧ (∀ x ∈ S 2, d x = σ) ∧ (∀ x ∈ S 3, b x = σ)

/-- Paper: the repair `F = 2σ [[C₀, 0, 0, 0], [0, 0, 0, -C₁ᵀR], [0, -C₂ᵀR, 0, 0], [0, 0, -C₃ᵀR, 0]]`
with `C_i = C(𝟙_{S_i})`. -/
def Fmat (σ : ℝ) (S : Fin 4 → Finset (ZMod j)) : Matrix (Fin 4 × ZMod j) (Fin 4 × ZMod j) ℝ :=
  (2 * σ) • Matrix.comp (Fin 4) (Fin 4) (ZMod j) (ZMod j) ℝ
    !![circ (ind (S 0)), 0, 0, 0;
      0, 0, 0, -((circ (ind (S 1)))ᵀ * rev);
      0, -((circ (ind (S 2)))ᵀ * rev), 0, 0;
      0, 0, -((circ (ind (S 3)))ᵀ * rev), 0]

end Circulants

/-! ### The `4 × 4` matrices and the borders -/

/-- Paper: `H = 𝒬(-1, 1, 1, 1)`. -/
def Hmat : Matrix (Fin 4) (Fin 4) ℝ := quat ![-1, 1, 1, 1]

/-- Paper: `O = ½ H` (orthogonal). -/
noncomputable def Omat : Matrix (Fin 4) (Fin 4) ℝ := (1 / 2 : ℝ) • Hmat

/-- Paper: `Π = [[-1,0,0,0],[0,0,0,1],[0,1,0,0],[0,0,1,0]]`. -/
def Pimat : Matrix (Fin 4) (Fin 4) ℝ := !![-1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

/-- Paper: `σ = β - 2 ∈ {-1, 1}`. -/
def sigmaOf (β : ℕ) : ℝ := (β : ℝ) - 2

/-- Paper: `V₁ = 𝟙₄` and `V₃ = [[1,1,1],[-1,1,-1],[1,-1,-1],[-1,-1,1]]` (other `β`: zero, unused). -/
def Vb : (β : ℕ) → Matrix (Fin 4) (Fin β) ℝ
  | 1 => !![1; 1; 1; 1]
  | 3 => !![1, 1, 1; -1, 1, -1; 1, -1, -1; -1, -1, 1]
  | _ => 0

/-- Paper: `G₁ = (1)` and `G₃ = [[1,1,1],[-1,1,1],[-1,-1,1]]` (other `β`: zero, unused). -/
def Gb : (β : ℕ) → Matrix (Fin β) (Fin β) ℝ
  | 1 => !![1]
  | 3 => !![1, 1, 1; -1, 1, 1; -1, -1, 1]
  | _ => 0

/-- Paper: `U_β = -O V_β`. -/
noncomputable def Ub (β : ℕ) : Matrix (Fin 4) (Fin β) ℝ := -(Omat * Vb β)

section Border

variable {j : ℕ} [NeZero j]

/-- Paper, eq. `X`: the matrix of order `4j + β`
`X = [[Z + F, U_β ⊗ 𝟙_j], [V_βᵀ ⊗ 𝟙_jᵀ, G_β]]`, with `σ = β - 2`, indexed by
`(Fin 4 × ℤ/jℤ) ⊕ Fin β`. -/
noncomputable def Xmat (β : ℕ) (a b c d : ZMod j → ℝ) (S : Fin 4 → Finset (ZMod j)) :
    Matrix ((Fin 4 × ZMod j) ⊕ Fin β) ((Fin 4 × ZMod j) ⊕ Fin β) ℝ :=
  Matrix.fromBlocks (Zgs a b c d + Fmat (sigmaOf β) S) (Matrix.of fun pu e => Ub β pu.1 e)
    (Matrix.of fun e qv => Vb β qv.1 e) (Gb β)

end Border

/-- Paper (Lemma `lem:criterion`):
`K = [[𝒬(r) - 2kσΠ, √j U_β], [√j V_βᵀ, G_β]]`, indexed by `Fin 4 ⊕ Fin β`. -/
noncomputable def Kmat (β : ℕ) (r : Fin 4 → ℝ) (k : ℝ) (j : ℕ) :
    Matrix (Fin 4 ⊕ Fin β) (Fin 4 ⊕ Fin β) ℝ :=
  Matrix.fromBlocks (quat r - (2 * k * sigmaOf β) • Pimat) (Real.sqrt j • Ub β)
    (Real.sqrt j • (Vb β)ᵀ) (Gb β)

/-- The window `2jI ⪯ MMᵀ ⪯ 8jI` used throughout the paper. -/
def Window {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (j : ℝ) : Prop :=
  (M * Mᵀ - (2 * j) • (1 : Matrix n n ℝ)).PosSemidef ∧
    ((8 * j) • (1 : Matrix n n ℝ) - M * Mᵀ).PosSemidef

/-! ## Section 4: sequences, Golay pairs, the base pairs, tails, masks -/

/-- Paper: "A pair `(P, Q)` of sign sequences of length `n` is a *Golay pair* if
`|P(z)|² + |Q(z)|² = 2n` for all `|z| = 1`." -/
def IsGolayPair {n : ℕ} (P Q : Fin n → ℤ) : Prop := IsSignSeq P ∧ IsSignSeq Q ∧ IsGolay P Q

/-- Paper: "a Golay pair `(P, Q)` of length `l²` is *regular* if `P(1) = Q(1) = l`". -/
def IsRegular (l : ℕ) (P Q : Fin (l ^ 2) → ℤ) : Prop :=
  IsGolayPair P Q ∧ peval P 1 = l ∧ peval Q 1 = l

/-- Paper: *doubling*, `(P, Q) ↦ (P|Q, P|-Q)`. -/
def golayDouble {n : ℕ} (p : (Fin n → ℤ) × (Fin n → ℤ)) : (Fin (n + n) → ℤ) × (Fin (n + n) → ℤ) :=
  (Fin.append p.1 p.2, Fin.append p.1 (-p.2))

/-- `k`-fold doubling. -/
def golayDoubleIter : (k : ℕ) → {n : ℕ} → (Fin n → ℤ) × (Fin n → ℤ) →
    (Fin (2 ^ k * n) → ℤ) × (Fin (2 ^ k * n) → ℤ)
  | 0, n, p => (p.1 ∘ Fin.cast (by ring), p.2 ∘ Fin.cast (by ring))
  | k + 1, n, p =>
    let q := golayDouble (golayDoubleIter k p)
    (q.1 ∘ Fin.cast (by ring), q.2 ∘ Fin.cast (by ring))

/-- Lemma `lem:square` as a construction: the sequences `P`, `Q` of length `l²` with
`P_{x+ly} = U_x B_y + V_x A^rev_y`, `Q_{x+ly} = U_x A_y - V_x B^rev_y`, i.e.
`P(z) = U(z)B(z^l) + V(z)A^rev(z^l)`, `Q(z) = U(z)A(z^l) - V(z)B^rev(z^l)`. -/
def golaySquare {l : ℕ} (A B : Fin l → ℤ) : (Fin (l ^ 2) → ℤ) × (Fin (l ^ 2) → ℤ) :=
  (sqP A B ∘ Fin.cast (by ring), sqQ A B ∘ Fin.cast (by ring))

/-- Lemma `lem:lift` as a construction: `P'(z) = (1+z²)P(z⁴) + (z-z³)Q(z⁴)`,
`Q'(z) = (1-z²)P(z⁴) + (z+z³)Q(z⁴)` (length `4n`). -/
def golayLift {n : ℕ} (p : (Fin n → ℤ) × (Fin n → ℤ)) : (Fin (4 * n) → ℤ) × (Fin (4 * n) → ℤ) :=
  (liftP p.1 p.2 ∘ Fin.cast (by ring), liftQ p.1 p.2 ∘ Fin.cast (by ring))

/-- The pair `((1), (1))` of length one. -/
def golayOne : (Fin 1 → ℤ) × (Fin 1 → ℤ) := (fun _ => 1, fun _ => 1)

/-- Paper ("The base pairs"): for `λ ∈ {64, 80, 100, 104}` the regular Golay pair
`(P^{(λ)}, Q^{(λ)})` of length `λ²` (the argument is written `lam`):
* `λ = 64`: double `((1),(1))` six times and apply Lemma `lem:square`;
* `λ = 80`: double `(A₁₀, B₁₀)` three times, apply Lemma `lem:square`, then replace `Q` by `Q^rev`;
* `λ = 100`: apply Lemma `lem:square` to `(A₁₀, B₁₀)`, and again to the resulting pair of length `100`;
* `λ = 104`: double `(A₂₆, B₂₆)` twice and apply Lemma `lem:square`.
(Other `λ`: an arbitrary constant pair, never used.) -/
def basePair : (d : ℕ) → (Fin (d ^ 2) → ℤ) × (Fin (d ^ 2) → ℤ)
  | 64 =>
    let p := golayDoubleIter 6 golayOne
    golaySquare p.1 p.2
  | 80 =>
    let p := golayDoubleIter 3 (golayA10, golayB10)
    let q := golaySquare p.1 p.2
    (q.1, seqRev q.2)
  | 100 =>
    let p := golaySquare golayA10 golayB10
    golaySquare p.1 p.2
  | 104 =>
    let p := golayDoubleIter 2 (golayA26, golayB26)
    golaySquare p.1 p.2
  | _ => (fun _ => 1, fun _ => 1)

/-- Paper: "`(P^{(λ,h)}, Q^{(λ,h)})` is the pair obtained from `(P^{(λ)}, Q^{(λ)})` by `h` lifts",
of length `(2^h λ)²`. -/
def liftedPair (lam : ℕ) : (h : ℕ) → (Fin ((2 ^ h * lam) ^ 2) → ℤ) × (Fin ((2 ^ h * lam) ^ 2) → ℤ)
  | 0 => ((basePair lam).1 ∘ Fin.cast (by ring), (basePair lam).2 ∘ Fin.cast (by ring))
  | h + 1 =>
    let p := golayLift (liftedPair lam h)
    (p.1 ∘ Fin.cast (by ring), p.2 ∘ Fin.cast (by ring))

/-- Paper: `𝓛 = {2^h λ : h ≥ 0, λ ∈ {64, 80, 100, 104}}`. -/
def InL (l : ℕ) : Prop := ∃ h lam : ℕ, lam ∈ ({64, 80, 100, 104} : Finset ℕ) ∧ l = 2 ^ h * lam

/-- The coefficient `P_x` of a sequence, with `0` outside the range `0 ≤ x < n`. -/
def coeff {n : ℕ} (P : Fin n → ℤ) (x : ℕ) : ℤ := if h : x < n then P ⟨x, h⟩ else 0

/-- Paper: "For a pair `(P, Q)` and a sign `σ`, we call `𝒫_σ(P, Q) = {x : P_x = Q_x = σ}` its
*common pool*." -/
def pool (σ : ℤ) {n : ℕ} (P Q : Fin n → ℤ) : Finset ℕ :=
  (Finset.range n).filter fun x => coeff P x = σ ∧ coeff Q x = σ

/-- Paper: `S₇^- = {22, 67, 307, 370, 1147, 1167, 1314}`, `S₇^+ = {2, 110, 191, 513, 1087, 1277, 1287}`,
`S₉^- = {510, 1098, 1465, 1526, 1676, 4150, 4210, 4595, 4808}`,
`S₉^+ = {102, 360, 652, 770, 822, 1872, 4115, 4380, 4818}` (`σ = -1` is `-`, otherwise `+`;
`q ∉ {7, 9}`: empty). -/
def seedSet (q : ℕ) (σ : ℤ) : Finset ℕ :=
  if q = 7 then
    (if σ = -1 then {22, 67, 307, 370, 1147, 1167, 1314} else {2, 110, 191, 513, 1087, 1277, 1287})
  else if q = 9 then
    (if σ = -1 then {510, 1098, 1465, 1526, 1676, 4150, 4210, 4595, 4808}
      else {102, 360, 652, 770, 822, 1872, 4115, 4380, 4818})
  else ∅

/-- Paper: "We say that a pair `(R, T)` of sign sequences of the same even length is *balanced* if
`R(1) = T(1) = 0`, and that it has *energy at most* `B` if `|R(z)|² + |T(z)|² ≤ B` for all
`|z| = 1`." (`TailPair r B` of `Tails.lean` is the existence of such a pair.) -/
def IsBalanced {r : ℕ} (R T : Fin r → ℤ) : Prop :=
  IsSignSeq R ∧ IsSignSeq T ∧ Even r ∧ peval R 1 = 0 ∧ peval T 1 = 0

/-- Paper, eq. `tail`: `R(1) = T(1) = 0` and `|R(z)|² + |T(z)|² ≤ 6r` for all `|z| = 1`. -/
def TailCond {r : ℕ} (R T : Fin r → ℤ) : Prop :=
  peval R 1 = 0 ∧ peval T 1 = 0 ∧ ∀ z : ℂ, ‖z‖ = 1 → ‖peval R z‖ ^ 2 + ‖peval T z‖ ^ 2 ≤ 6 * r

/-- Paper: "`P̄` is obtained from `P` by deleting the first coefficient when `ε = 1`". -/
def dropFirst (ε : ℕ) {n : ℕ} (P : Fin n → ℤ) : Fin (n - ε) → ℤ :=
  fun i => P ⟨i + ε, by omega⟩

/-- A sequence of length `m` regarded as a sequence of length `j` when `m = j`. -/
def castLen {m j : ℕ} (h : m = j) (x : Fin m → ℤ) : Fin j → ℤ := x ∘ Fin.cast h.symm

/-- A sequence `x = (x_0, …, x_{j-1})` regarded as a vector of `ℝ^j` indexed by `ℤ/jℤ`. -/
def toVec {j : ℕ} [NeZero j] (x : Fin j → ℤ) : ZMod j → ℝ := fun v => (x ⟨v.val, ZMod.val_lt v⟩ : ℝ)

/-- Paper (Lemma `lem:rows`): with `n = l² - ε` and `r = j - l² + ε`,
`a = -(P̄|R)`, `b = P̄|-R`, `c = Q̄|T`, `d = Q̄|-T`, of length `j`. -/
def rowsSeqs {l j ε : ℕ} (h : l ^ 2 - ε + (j + ε - l ^ 2) = j) (P Q : Fin (l ^ 2) → ℤ)
    (R T : Fin (j + ε - l ^ 2) → ℤ) : (Fin j → ℤ) × (Fin j → ℤ) × (Fin j → ℤ) × (Fin j → ℤ) :=
  (castLen h (-Fin.append (dropFirst ε P) R), castLen h (Fin.append (dropFirst ε P) (-R)),
    castLen h (Fin.append (dropFirst ε Q) T), castLen h (Fin.append (dropFirst ε Q) (-T)))

end SignCond
