import SignCond.RowsRule
import SignCond.LargeTauMasks
import SignCond.SectorTau
import SignCond.Large

/-!
# Proposition `prop:large` (rewritten paper): `j ≥ 9999`, no hypotheses

"For every `j ≥ 9999` and each `β ∈ {1,3}`, there are a sign matrix `X` of order `4j+β` and a
number `τ > 0` with `τ²I ⪯ XXᵀ ≺ 4τ²I`."

The proof follows the paper step by step:
* the choice of `l` (`choose_l_tau`): `l` is the largest element of `𝒢` with `l² ≤ j + ε`, so
  `l ≥ 100`; the next element `l⁺` of `𝒢` has `(l⁺)² > j + ε` and `l⁺ ≤ 5l/4`, and
  `2(l - 13)² > (l⁺)²`;
* the regular pair of Lemma `lem:square` from the fixed Golay pair `golayG l` (first coefficients
  `1` by `golayG_first`, `lem_square_first`), the tails `Φ_r, Ψ_r` of Lemma `lem:tails`
  (`lem_tails_rule`) and the sequences of Lemma `lem:rows` (`lem_rows_rule`), eq. `energies`;
* the parameters (`exists_even_near`, `k_pos_arith`; `LargeTauArith.lean`);
* the constant sector (`sector_arith`, Lemma `lem:scales` part 2, Lemma `lem:sector`);
* the upper end of the window, eq. `upper` (`upper_arith`);
* the masks (`masks_step`, `masks_arith`, `energy_lt_arith`, `bias_arith`, `card_arith`;
  `LargeTauMasks.lean`, Lemma `lem:select`);
* the window, eq. `window` (`window_arith`), and Lemma `lem:criterion` (`lem_criterion_tau`).
Finally `X` is transported from the index type `(Fin 4 × ℤ/jℤ) ⊕ Fin β` to `Fin (4j + β)`
(`exists_fin_windowAt`).
-/

open Matrix Complex
open scoped Real

namespace SignCond

/-! ### The choice of `l` -/

/-- Paper: "Let `l` be the largest element of `𝒢` with `l² ≤ j + ε`, so that `l ≥ 100`, and let
`l⁺` be the next element of `𝒢`. Thus `(l⁺)² > j + ε` and `l⁺ ≤ 5l/4`." Also "`2(l-13)² > (l⁺)²`:
for `(l, l⁺) = (100, 104)` and `(104, 128)` the two sides are `15138 > 10816` and
`16562 > 16384`, and for `l ≥ 128` we have `l - 13 ≥ 8l/9` and `2(8/9)² > (5/4)²`."
(Here `N = j + ε`; "largest with `l² ≤ N`" is `IsMaxG (Nat.sqrt N) l`.) -/
theorem choose_l_tau {N : ℕ} (hN : 10000 ≤ N) :
    ∃ l lp : ℕ, IsMaxG (Nat.sqrt N) l ∧ InG lp ∧ 100 ≤ l ∧ l ^ 2 ≤ N ∧ N < lp ^ 2 ∧
      4 * lp ≤ 5 * l ∧ lp ^ 2 < 2 * (l - 13) ^ 2 := by
  have hs : 100 ≤ Nat.sqrt N := Nat.le_sqrt'.2 (by norm_num; omega)
  obtain ⟨l, hl⟩ := exists_isMaxG (h := Nat.sqrt N) (by omega)
  have h100 : 100 ≤ l := hl.2.2 100 (by simpa using inG_100 0) hs
  obtain ⟨lp, hlpG, hllp, h45, hnext⟩ := next_inG hl.1 (by omega)
  have hl2 : l ^ 2 ≤ N := Nat.le_sqrt'.1 hl.2.1
  have hN2 : N < lp ^ 2 := by
    by_contra hc
    push_neg at hc
    have := hl.2.2 lp hlpG (Nat.le_sqrt'.2 hc)
    omega
  refine ⟨l, lp, hl, hlpG, h100, hl2, hN2, h45, ?_⟩
  rcases lt_or_ge l 128 with h128 | h128
  · have hmem := (inG_iff_of_le_160 (n := l) (by omega) (by omega)).1 hl.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h <;> try omega
    · subst h
      have h1 : lp ≤ 104 := hnext 104 (by simpa using inG_104 0) (by norm_num)
      have := Nat.pow_le_pow_left h1 2
      norm_num at this ⊢
      omega
    · subst h
      have h1 : lp ≤ 128 := hnext 128 (by simpa using inG_128 0) (by norm_num)
      have := Nat.pow_le_pow_left h1 2
      norm_num at this ⊢
      omega
  · obtain ⟨t, rfl⟩ : ∃ t, l = t + 13 := ⟨l - 13, by omega⟩
    rw [Nat.add_sub_cancel]
    have h1 : 16 * lp ^ 2 ≤ 25 * (t + 13) ^ 2 := by nlinarith [Nat.mul_le_mul h45 h45]
    have ht : 115 ≤ t := by omega
    nlinarith

/-! ### Relabelling -/

/-- `WindowAt` is invariant under relabelling rows and columns simultaneously. -/
theorem windowAt_reindex {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {M : Matrix n n ℝ} (e : n ≃ m) {τ : ℝ} (h : WindowAt M τ) : WindowAt (reindex e e M) τ := by
  rw [windowAt_iff_form] at h ⊢
  intro x
  have hd : ∀ f : n → ℝ, (f ∘ e.symm) ⬝ᵥ (f ∘ e.symm) = f ⬝ᵥ f := fun f => by
    simp only [dotProduct, Function.comp_apply]
    exact Equiv.sum_comp e.symm (fun i => f i * f i)
  have hx : (x ∘ e) ⬝ᵥ (x ∘ e) = x ⬝ᵥ x := by
    simp only [dotProduct, Function.comp_apply]
    exact Equiv.sum_comp e (fun i => x i * x i)
  have hT : (reindex e e M)ᵀ *ᵥ x = (Mᵀ *ᵥ (x ∘ e)) ∘ e.symm := by
    rw [reindex_apply, transpose_submatrix, submatrix_mulVec_equiv, Equiv.symm_symm]
  obtain ⟨h1, h2⟩ := h (x ∘ e)
  rw [hT, hd, ← hx]
  refine ⟨h1, fun hx0 => h2 ?_⟩
  intro hc
  apply hx0
  funext i
  have := congrFun hc (e.symm i)
  simpa using this

/-- A sign matrix with `τ²I ⪯ XXᵀ ≺ 4τ²I`, indexed by `(Fin 4 × ℤ/jℤ) ⊕ Fin β`, gives one of
order `4j + β`. -/
theorem exists_fin_windowAt {j : ℕ} [NeZero j] {β : ℕ}
    {X : Matrix ((Fin 4 × ZMod j) ⊕ Fin β) ((Fin 4 × ZMod j) ⊕ Fin β) ℝ} {τ : ℝ}
    (hX : IsSign X) (hW : WindowAt X τ) :
    ∃ A : Matrix (Fin (4 * j + β)) (Fin (4 * j + β)) ℝ, IsSign A ∧ WindowAt A τ := by
  let e := Fintype.equivFinOfCardEq (card_index (j := j) β)
  exact ⟨reindex e e X, isSign_reindex e hX, windowAt_reindex e hW⟩

/-! ### The proposition -/

theorem len_arith {L j ε : ℕ} (h : L ≤ j + ε) (hε : ε ≤ 1) (hL : 1 ≤ L) :
    L - ε + (j + ε - L) = j := by omega


set_option maxHeartbeats 1600000 in
/-- **Proposition `prop:large`** (rewritten paper). "For every `j\ge9999` and each
`\beta\in\{1,3\}`, there are a sign matrix `X` of order `4j+\beta` and a number `\tau>0` with
`\tau^2I\preceq XX^\top\prec4\tau^2I`." No hypotheses. -/
theorem prop_large_tau : ∀ j : ℕ, 9999 ≤ j → ∀ β : ℕ, (β = 1 ∨ β = 3) →
    ∃ X : Matrix (Fin (4 * j + β)) (Fin (4 * j + β)) ℝ, IsSign X ∧ ∃ τ : ℝ, 0 < τ ∧ WindowAt X τ := by
  intro j hj β hβ
  haveI : NeZero j := ⟨by omega⟩
  -- `ε`, `l`, `l⁺`
  set ε := j % 2 with hεdef
  have hε : ε = 0 ∨ ε = 1 := Nat.mod_two_eq_zero_or_one j
  have hεj : ε % 2 = j % 2 := Nat.mod_mod j 2
  have hev : Even (j + ε) := Nat.even_iff.2 (by omega)
  obtain ⟨l, lp, hlmax, -, hl100, hlo, hhi, hratio, h13⟩ := choose_l_tau (N := j + ε) (by omega)
  have hlG : InG l := hlmax.1
  have hlev : Even l := inG_even hlG
  -- the regular pair of Lemma `lem:square` from the Golay pair of length `l`
  have hAB := isGolayPair_golayG l (Or.inl hlG)
  set PQ := golaySquare (golayG l).1 (golayG l).2 with hPQ
  have hreg : IsRegular l PQ.1 PQ.2 := golaySquare_regular hAB
  obtain ⟨hA0, hB0⟩ := golayG_first l (Or.inl hlG)
  obtain ⟨hP0, hQ0⟩ := lem_square_first (by omega) _ _ hAB hA0 hB0
  -- the tails and the rows (Lemmas `lem:tails`, `lem:rows`), eq. `energies`
  have hr : Even (j + ε - l ^ 2) := by
    rw [Nat.even_sub hlo]; exact ⟨fun _ => (Nat.even_pow' two_ne_zero).2 hlev, fun _ => hev⟩
  obtain ⟨hRs, hTs, htail⟩ := lem_tails_rule (j + ε - l ^ 2) hr
  have hlen : l ^ 2 - ε + (j + ε - l ^ 2) = j :=
    len_arith hlo (by omega) (Nat.one_le_pow _ _ (by omega))
  have hrows := lem_rows_rule (by omega) hlev PQ.1 PQ.2 hreg hP0 hQ0 hε hεj hlo hlen
    (tailPhi' (j + ε - l ^ 2)) (tailPsi' (j + ε - l ^ 2)) hRs hTs htail
  set abcd := rowsSeqs hlen PQ.1 PQ.2 (tailPhi' (j + ε - l ^ 2)) (tailPsi' (j + ε - l ^ 2))
    with habcd
  obtain ⟨⟨sa, sb, sc, sd⟩, hE⟩ := hrows
  set a := toVec abcd.1
  set b := toVec abcd.2.1
  set c := toVec abcd.2.2.1
  set d := toVec abcd.2.2.2
  have hPs : IsSignSeq PQ.1 := hreg.1.1
  have hQs : IsSignSeq PQ.2 := hreg.1.2.1
  have ha : IsSignVec a := isSignVec_toVec (isSignSeq_castLen hlen
    (isSignSeq_neg (isSignSeq_append (isSignSeq_dropFirst (ε := ε) hPs) hRs)))
  have hb : IsSignVec b := isSignVec_toVec (isSignSeq_castLen hlen
    (isSignSeq_append (isSignSeq_dropFirst (ε := ε) hPs) (isSignSeq_neg hRs)))
  have hc : IsSignVec c := isSignVec_toVec (isSignSeq_castLen hlen
    (isSignSeq_append (isSignSeq_dropFirst (ε := ε) hQs) hTs))
  have hd : IsSignVec d := isSignVec_toVec (isSignSeq_castLen hlen
    (isSignSeq_append (isSignSeq_dropFirst (ε := ε) hQs) (isSignSeq_neg hTs)))
  -- real quantities: `q = √j`, `ρ = √(2j)`, `s = l - ε`
  obtain ⟨m, hm⟩ := exists_even_near j
  have hjR : (9999 : ℝ) ≤ j := by exact_mod_cast hj
  set ρ := Real.sqrt (2 * (j : ℝ)) with hρdef
  have hρ2 : ρ ^ 2 = 2 * j := Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set q := Real.sqrt (j : ℝ) with hqdef
  have hq2 : q ^ 2 = j := Real.sq_sqrt (by positivity)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq99 : 99 < q := by nlinarith
  obtain ⟨hρq1, hρq2⟩ := rho_q_bounds (q := q) hρ0 (by linarith) (by rw [hρ2, ← hq2])
  set sR : ℝ := (l : ℝ) - ε with hsRdef
  set sN : ℕ := l - ε with hsNdef
  have hsN : (sN : ℝ) = sR := by rw [hsNdef, Nat.cast_sub (by omega)]
  have hlR : (100 : ℝ) ≤ l := by exact_mod_cast hl100
  have hεR : (ε : ℝ) = 0 ∨ (ε : ℝ) = 1 := by rcases hε with h | h <;> simp [h]
  have hloR : (l : ℝ) ^ 2 ≤ j + ε := by exact_mod_cast hlo
  have hhiR : (j : ℝ) + ε < lp ^ 2 := by exact_mod_cast hhi
  have hjlpR : (j : ℝ) < lp ^ 2 := by
    have : (0 : ℝ) ≤ ε := Nat.cast_nonneg _
    linarith
  have hratioR : 4 * (lp : ℝ) ≤ 5 * l := by exact_mod_cast hratio
  have h13R : (lp : ℝ) ^ 2 < 2 * ((l : ℝ) - 13) ^ 2 := by
    have : ((lp ^ 2 : ℕ) : ℝ) < ((2 * (l - 13) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h13
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub (by omega)] at this
    simpa using this
  -- eq. `sbounds`
  have hsb := s_bounds (l := (l : ℝ)) (lp := (lp : ℝ)) (j := (j : ℝ)) (ε := (ε : ℝ)) (s := sR)
    hεR rfl (by linarith) (by positivity) hloR hhiR (by positivity) hratioR
  have hsl : (l : ℝ) - 1 ≤ sR := by
    have : (ε : ℝ) ≤ 1 := by exact_mod_cast (show ε ≤ 1 by omega)
    rw [hsRdef]; linarith
  -- the parameters: `α = 2m`, `k = s - m`, `τ = (3ρ + α)/4`
  set α : ℝ := 2 * (m : ℝ) with hαdef
  have hmk : (m : ℝ) < sN := by
    rw [hsN]; have := k_pos_arith hρq2 hq99 hsb.1 hm; linarith
  have hmsN : m ≤ sN := by exact_mod_cast hmk.le
  set kN : ℕ := sN - m with hkNdef
  have hkN : (kN : ℝ) = sR - m := by rw [hkNdef, Nat.cast_sub hmsN, hsN]
  have hαk : α = 2 * ((sN : ℝ) - kN) := by rw [hkN, hsN, hαdef]; ring
  have hαk' : α = 2 * (sR - kN) := by rw [← hsN]; exact hαk
  set τ := (3 * ρ + α) / 4 with hτdef
  -- the constant sector
  obtain ⟨hτlo, hτhi, hγ1, hγ2, hτ0, hρ14⟩ := sector_arith (j := (j : ℝ)) (s := (sN : ℝ))
    (k := (kN : ℝ)) hq0 hq2 hρ0 hρ2 hq99 (by rw [hsN]; exact hsb.1) (by rw [hsN]; exact hsb.2) hm
    hαk hτdef
  have hp : ∀ ν : ℝ, (ν = 1 ∨ ν = 4) → 0 ≤ pnu j (2 * ((sN : ℝ) - kN)) ν (τ ^ 2) ∧
      0 < pnu j (2 * ((sN : ℝ) - kN)) ν (4 * τ ^ 2) := by
    intro ν hν
    rw [← hαk]
    have := lem_scales_two (j := j) (α := α) hρ14 hm hν
    exact ⟨this.1.le, this.2⟩
  have hsec := lem_sector_tau (j := j) (s := sN) (k := kN) (by omega) (Nat.sub_le _ _) τ hτ0
    hτlo hτhi hγ1 hγ2 hp
  -- the upper end of the window, eq. `upper`
  have hup := upper_arith (j := (j : ℝ)) (l := (l : ℝ)) (lp := (lp : ℝ)) (s := sR) (q := q) hlR hsl
    hsb.2 hρ0 hρ2 hjlpR (by positivity) hratioR hρq1
  -- the masks
  have hσ : sigmaOf β = 1 ∨ sigmaOf β = -1 := by
    rcases hβ with rfl | rfl <;> simp [sigmaOf] <;> norm_num
  have hs0 : 0 ≤ sR := by linarith
  have hkcard : (kN : ℝ) ≤ ((j : ℝ) - sR) / 2 :=
    card_arith (q := q) (by linarith) hq2 hsb.2 (alpha_pos_arith hρq1 hq99 hm) hαk'
  obtain ⟨hM1, hM2⟩ := masks_step (sigmaOf β) hσ a b c d ha hb hc hd sR hs0 sa sb sc sd kN hkcard
  have hmasks : ∃ S : Fin 4 → Finset (ZMod j), (∀ i, (S i).card = kN) ∧
      Pools (sigmaOf β) a b c d S ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
        (ρ ≤ α ∧ deltaL S ℓ ≤ 2 * kN) ∨ (α < ρ ∧ deltaL S ℓ ≤ 2 * kN - 3 / 4) := by
    by_cases hαρ : ρ ≤ α
    · obtain ⟨S, h1, h2, h3⟩ := hM1
      exact ⟨S, h1, h2, fun ℓ _ _ => Or.inl ⟨hαρ, h3 ℓ⟩⟩
    · push_neg at hαρ
      obtain ⟨h12, h196⟩ := masks_arith (j := (j : ℝ)) (l := (l : ℝ)) (lp := (lp : ℝ)) (s := sR)
        (ρ := ρ) (q := q) (α := α) (k := (kN : ℝ)) hlR hsl hsb.1 hq99 hq0 hq2 hρ0 hρ2 hjlpR h13R
        hαρ hαk' hρq2
      have hk13 : 13 ≤ kN := by
        have : 12 < kN := by exact_mod_cast h12
        omega
      have hj196 : j ≤ 196 * kN ^ 2 := by
        have : ((j : ℕ) : ℝ) < ((196 * kN ^ 2 : ℕ) : ℝ) := by push_cast; exact h196
        exact_mod_cast this.le
      have hbias : ∀ ℓ : ℕ, Real.sqrt (energy a b c d ℓ) / 2 ≤ ((j : ℝ) - sR) / 2 / 33 :=
        fun ℓ => bias_arith hq99 hq2 hsb.2
          (energy_lt_arith hlR hsl hjlpR (by positivity) hratioR (hE ℓ).2)
      obtain ⟨S, h1, h2, h3⟩ := hM2 hk13 hj196 hbias
      exact ⟨S, h1, h2, fun ℓ h1' h2' => Or.inr ⟨hαρ, h3 ℓ h1' h2'⟩⟩
  obtain ⟨S, hScard, hpools, hδ⟩ := hmasks
  -- the window, eq. `window`
  have hwin : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      τ + deltaL S ℓ ≤ Real.sqrt (energy a b c d ℓ) ∧
        Real.sqrt (energy a b c d ℓ) < 2 * τ - deltaL S ℓ := by
    intro ℓ h1 h2
    obtain ⟨hE1, hE2⟩ := hE ℓ
    have h2s : 2 * sR ≤ Real.sqrt (energy a b c d ℓ) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * sR)]
      exact Real.sqrt_le_sqrt (by linarith)
    have he : Real.sqrt (energy a b c d ℓ) < 3 * ρ - 2 * sR - 3 / 4 :=
      lt_of_le_of_lt (Real.sqrt_le_sqrt hE2) hup
    exact window_arith h2s he hαk' hτdef hm (hδ ℓ h1 h2)
  -- Lemma `lem:criterion`
  have hK : WindowAt (Kmat β ![vsum a, vsum b, vsum c, vsum d] kN j) τ := by
    rw [sa, sb, sc, sd, ← hsN]
    rcases hβ with rfl | rfl
    · exact hsec.1
    · exact hsec.2
  have hX := lem_criterion_tau β hβ a b c d ha hb hc hd S kN hScard hpools τ hτ0 hK hwin
  have hXS := Xmat_isSign hβ ha hb hc hd hpools
  obtain ⟨A, hA, hAW⟩ := exists_fin_windowAt hXS hX.1
  exact ⟨A, hA, τ, hτ0, hAW⟩

end SignCond
