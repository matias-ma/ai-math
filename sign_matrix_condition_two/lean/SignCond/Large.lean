import SignCond.LargeMasks
import SignCond.RowsPaper
import SignCond.XFacts

/-!
# Proposition `prop:large`

`large_window`: for every `j ≥ 4095` and `β ∈ {1, 3}` there is a sign matrix `X` of order `4j + β`
with `2jI ⪯ XXᵀ ⪯ 8jI`, assuming the computational inputs `LemSeedsArc` and `LemSeedsPools`.
The proof follows the paper paragraph by paragraph (the choice of `l`, the size of the masks, the
sums, the constant sector, the masks, the window).
-/

open Complex
open scoped Real

namespace SignCond

/-- The entries of `a, b, c, d` in the prefix: `a_i = -P_{i+ε}`, `b_i = P_{i+ε}`,
`c_i = d_i = Q_{i+ε}` for `i < l² - ε`. -/
theorem rowsSeqs_toVec {l j ε : ℕ} [NeZero j] (hlen : l ^ 2 - ε + (j + ε - l ^ 2) = j)
    (P Q : Fin (l ^ 2) → ℤ) (R T : Fin (j + ε - l ^ 2) → ℤ) (i : ℕ) (hi : i < l ^ 2 - ε) :
    toVec (rowsSeqs hlen P Q R T).1 (i : ZMod j) = -(coeff P (i + ε) : ℝ) ∧
      toVec (rowsSeqs hlen P Q R T).2.1 (i : ZMod j) = (coeff P (i + ε) : ℝ) ∧
      toVec (rowsSeqs hlen P Q R T).2.2.1 (i : ZMod j) = (coeff Q (i + ε) : ℝ) ∧
      toVec (rowsSeqs hlen P Q R T).2.2.2 (i : ZMod j) = (coeff Q (i + ε) : ℝ) := by
  have hij : i < j := by omega
  have hv : (i : ZMod j).val = i := ZMod.val_cast_of_lt hij
  have key : ∀ (x : Fin (l ^ 2 - ε) → ℤ) (y : Fin (j + ε - l ^ 2) → ℤ),
      castLen hlen (Fin.append x y) ⟨(i : ZMod j).val, ZMod.val_lt _⟩ = x ⟨i, hi⟩ := by
    intro x y
    simp only [castLen, Function.comp_apply]
    have : (Fin.cast hlen.symm ⟨(i : ZMod j).val, ZMod.val_lt _⟩ : Fin (l ^ 2 - ε + (j + ε - l ^ 2))) =
        Fin.castAdd (j + ε - l ^ 2) ⟨i, hi⟩ := by ext; simp [hv]
    rw [this, Fin.append_left]
  have keyneg : ∀ (x : Fin (l ^ 2 - ε) → ℤ) (y : Fin (j + ε - l ^ 2) → ℤ),
      castLen hlen (-Fin.append x y) ⟨(i : ZMod j).val, ZMod.val_lt _⟩ = -x ⟨i, hi⟩ := by
    intro x y
    have := key x y
    simp only [castLen, Function.comp_apply, Pi.neg_apply] at this ⊢
    rw [this]
  have hP : (dropFirst ε P ⟨i, hi⟩ : ℤ) = coeff P (i + ε) := by
    simp [dropFirst, coeff, show i + ε < l ^ 2 by omega]
  have hQ : (dropFirst ε Q ⟨i, hi⟩ : ℤ) = coeff Q (i + ε) := by
    simp [dropFirst, coeff, show i + ε < l ^ 2 by omega]
  simp only [toVec, rowsSeqs]
  rw [keyneg, key, key, key, hP, hQ]
  push_cast
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem isSignSeq_dropFirst {ε n : ℕ} {P : Fin n → ℤ} (h : IsSignSeq P) :
    IsSignSeq (dropFirst ε P) := fun _ => h _

theorem isSignSeq_castLen {m n : ℕ} (hmn : m = n) {x : Fin m → ℤ} (h : IsSignSeq x) :
    IsSignSeq (castLen hmn x) := fun _ => h _

/-- The facts about `(λ, λ⁺)` used in the proof. -/
theorem pair_facts {lam lamp : ℕ}
    (hpair : (lam, lamp) ∈ ({(64, 80), (80, 100), (100, 104), (104, 128)} : Finset (ℕ × ℕ))) :
    lam ∈ ({64, 80, 100, 104} : Finset ℕ) ∧
      (lamp : ℝ) ^ 2 < 2 * ((lam : ℝ) - seedSize lam - 1 / 5) ^ 2 ∧
      0 < (lam : ℝ) - seedSize lam - 1 / 5 ∧ 4 * lamp ≤ 5 * lam ∧ (lamp : ℝ) ^ 2 ≤ seedArc lam ∧
      64 ≤ lam ∧ lam ≤ 104 ∧ Even lam := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine ⟨by simp, ?_, ?_, by norm_num, ?_, by norm_num, by norm_num, by decide⟩ <;>
    norm_num [seedSize, seedArc]

set_option maxHeartbeats 8000000 in
/-- **Proposition `prop:large`.** -/
theorem large_window (hArc : LemSeedsArc) (hPools : LemSeedsPools) {j : ℕ} (hj : 4095 ≤ j)
    {β : ℕ} (hβ : β = 1 ∨ β = 3) :
    ∃ A : Matrix (Fin (4 * j + β)) (Fin (4 * j + β)) ℝ, IsSign A ∧ Window A j := by
  haveI : NeZero j := ⟨by omega⟩
  set ε := j % 2 with hεdef
  have hε : ε = 0 ∨ ε = 1 := Nat.mod_two_eq_zero_or_one j
  have hε1 : ε ≤ 1 := by omega
  have hεj : ε % 2 = j % 2 := Nat.mod_mod j 2
  have hev : Even (j + ε) := Nat.even_iff.2 (by omega)
  -- the choice of `l`
  obtain ⟨h, lam, lamp, hpair, hlo, hhi⟩ := choose_l (N := j + ε) (by omega)
  obtain ⟨hlamS, hd, hc, hratio, harc, h64, h104, hlamev⟩ := pair_facts hpair
  set l := 2 ^ h * lam with hldef
  set lp := 2 ^ h * lamp with hlpdef
  have hpow1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hl64 : 64 ≤ l := le_trans h64 (Nat.le_mul_of_pos_left lam (by positivity))
  have hl4 : 4 ≤ l := by omega
  have hlev : Even l := hlamev.mul_left _
  have hl2 : 4096 ≤ l ^ 2 := by
    have := Nat.pow_le_pow_left hl64 2; simpa using this
  -- the pair, the tails and the rows
  set PQ := liftedPair lam h
  have hreg : IsRegular l PQ.1 PQ.2 := liftedPair_regular lam hlamS h
  obtain ⟨hP0, hQ0⟩ := liftedPair_coeff_zero lam h (by omega)
    (seeds_part3_coeff lam hlamS).1 (seeds_part3_coeff lam hlamS).2
  have hr : Even (j + ε - l ^ 2) := by
    rw [Nat.even_sub hlo]; exact ⟨fun _ => (Nat.even_pow' two_ne_zero).2 hlev, fun _ => hev⟩
  obtain ⟨R, T, hRs, hTs, hR1, hT1, hRT⟩ := lem_tails (j + ε - l ^ 2) hr
  have hlen : l ^ 2 - ε + (j + ε - l ^ 2) = j := by omega
  have hrows := rows_paper hl4 hlev PQ.1 PQ.2 hreg hP0 hQ0 hε hεj hlo hlen R T hRs hTs
    ⟨hR1, hT1, hRT⟩
  set abcd := rowsSeqs hlen PQ.1 PQ.2 R T with habcd
  obtain ⟨⟨sa, sb, sc, sd⟩, hE⟩ := hrows
  -- real quantities
  have hjR : (4095 : ℝ) ≤ j := by exact_mod_cast hj
  set sR : ℝ := (l : ℝ) - ε with hsRdef
  set sN : ℕ := l - ε with hsNdef
  have hsN : (sN : ℝ) = sR := by rw [hsNdef, Nat.cast_sub (by omega)]
  set ρ := Real.sqrt (2 * (j : ℝ)) with hρdef
  have hρ2 : ρ ^ 2 = 2 * j := Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ90 : 90 ≤ ρ := by nlinarith only [hρ2, hρ0, hjR]
  -- the size of the masks: `m` is the integer in `(ρ/2 - 4/5, ρ/2 + 1/5)`
  set m := ⌊ρ / 2 + 1 / 5⌋₊ with hmdef
  have hm_le : (m : ℝ) ≤ ρ / 2 + 1 / 5 := Nat.floor_le (by positivity)
  have hm_gt : ρ / 2 + 1 / 5 < m + 1 := Nat.lt_floor_add_one _
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith only [hm_gt, hρ90]
    exact_mod_cast this
  have hm2 : (m : ℝ) < ρ / 2 + 1 / 5 := by
    refine lt_of_le_of_ne hm_le fun heq => no_endpoint_real j (m - 1) ?_
    rw [Nat.cast_sub hm1, ← hρdef]; push_cast; linarith only [heq]
  have hm1' : ρ / 2 - 4 / 5 < m := by linarith only [hm_gt]
  have hjlp : (j : ℝ) < (lp : ℝ) ^ 2 := by
    have : j < lp ^ 2 := by omega
    exact_mod_cast this
  have hhalf := half_rho_lt (j := (j : ℝ)) (lp := (lp : ℝ)) (by positivity) (by positivity) hjlp
  have hlR : (l : ℝ) = 2 ^ h * lam := by rw [hldef]; push_cast; ring
  have hlpR : (lp : ℝ) = 2 ^ h * lamp := by rw [hlpdef]; push_cast; ring
  have hX : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have hεR1 : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hεR0 : (0 : ℝ) ≤ ε := Nat.cast_nonneg _
  have hklow := k_lower (s := sR) (m := (m : ℝ)) (ρ := ρ) (l := (l : ℝ)) (d := (lam : ℝ))
    (dp := (lamp : ℝ)) (q := (seedSize lam : ℝ)) (X := (2 : ℝ) ^ h) hX hlR (by rw [hsRdef]; linarith only [hεR1]) hm2
    (by rw [← hlpR]; exact hhalf) hd hc (Nat.cast_nonneg _)
  have hms : m ≤ sN := by
    have : (m : ℝ) < sN := by
      rw [hsN]
      have hq1 : (1 : ℝ) ≤ seedSize lam := by
        unfold seedSize; split_ifs <;> norm_num
      have : (1 : ℝ) ≤ 2 ^ h * seedSize lam := one_le_mul_of_one_le_of_one_le hX hq1
      linarith only [hklow, this]
    exact_mod_cast this.le
  set kN := sN - m with hkNdef
  have hkN : (kN : ℝ) = sR - m := by rw [hkNdef, Nat.cast_sub hms, hsN]
  have hkq : 2 ^ h * seedSize lam ≤ kN := by
    have h1 : ((2 ^ h * seedSize lam : ℕ) : ℝ) < (kN : ℝ) + 1 := by push_cast; linarith only [hklow, hkN]
    have h2 : 2 ^ h * seedSize lam < kN + 1 := by exact_mod_cast h1
    omega
  -- the sums
  have hsb := s_bounds (l := (l : ℝ)) (lp := (lp : ℝ)) (j := (j : ℝ)) (ε := (ε : ℝ)) (s := sR)
    (by rcases hε with h0 | h0 <;> simp [h0]) rfl (by exact_mod_cast (by omega : 1 ≤ l)) (by positivity)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi) (by positivity)
    (by
      rw [hlR, hlpR]
      have h1 : (4 * lamp : ℝ) ≤ 5 * lam := by exact_mod_cast hratio
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ h)
      linarith only [this])
  -- the constant sector
  have hsj : Real.sqrt j = ρ / Real.sqrt 2 := by
    rw [hρdef, Real.sqrt_mul (by norm_num)]; field_simp
  have hγ := gamma_bounds hρ90 hsj hsb.1 hsb.2 hm1' hm2
  have hsec := sector_window (j := j) (s := sN) (k := kN) (by omega) (Nat.sub_le _ _)
    (by rw [← hρdef, hsN, hkN]; linarith only [hγ.1]) (by rw [← hρdef, hsN, hkN]; linarith only [hγ.2])
    (Or.inr ⟨by rw [← hρdef]; linarith only [hρ90], by rw [← hρdef, hsN, hkN]; linarith only [hm2]⟩)
  -- the masks
  set σZ : ℤ := if β = 1 then -1 else 1 with hσZdef
  have hσZ : σZ = -1 ∨ σZ = 1 := by rw [hσZdef]; split_ifs <;> simp
  have hsig : sigmaOf β = (σZ : ℝ) := by
    rcases hβ with rfl | rfl <;> simp [hσZdef, sigmaOf] <;> norm_num
  set pl := pool σZ PQ.1 PQ.2 with hpldef
  have hpool_base := hPools lam hlamS σZ hσZ
  have hpool_card : 2 ^ h * 992 ≤ pl.card := by
    have := Finset.card_le_card (pool_liftedPair σZ lam h)
    rw [card_maskLiftIter] at this
    have h2 : 2 ^ h * 992 ≤ 2 ^ h * (pool σZ (basePair lam).1 (basePair lam).2).card :=
      Nat.mul_le_mul_left _ hpool_base
    exact h2.trans this
  set Sh := maskLiftIter (seedSet (seedSize lam) σZ) h with hShdef
  have hSh_pool : Sh ⊆ pl :=
    (maskLiftIter_mono (seeds_part2 σZ hσZ lam hlamS) h).trans (pool_liftedPair σZ lam h)
  have hSh0 : 0 ∉ Sh := zero_not_mem_maskLiftIter (zero_not_mem_seedSet _ _) h
  have hSh_sub : Sh ⊆ pl.erase 0 := fun x hx =>
    Finset.mem_erase.2 ⟨fun h0 => hSh0 (h0 ▸ hx), hSh_pool hx⟩
  have hShcard : Sh.card = 2 ^ h * seedSize lam := by
    rw [hShdef, card_maskLiftIter, card_seedSet]
    unfold seedSize; split_ifs <;> simp
  have hk_le : kN ≤ (pl.erase 0).card := by
    have h1 := Finset.pred_card_le_card_erase (s := pl) (a := 0)
    have h2 : kN ≤ l := by omega
    have h3 : l ≤ 2 ^ h * 104 := Nat.mul_le_mul_left _ h104
    omega
  obtain ⟨S, hShS, hSpl, hScard⟩ :=
    Finset.exists_subsuperset_card_eq hSh_sub (by rw [hShcard]; exact hkq) hk_le
  have hSmem : ∀ x ∈ S, x < l ^ 2 ∧ 1 ≤ x ∧ coeff PQ.1 x = σZ ∧ coeff PQ.2 x = σZ := by
    intro x hx
    have h1 := hSpl hx
    rw [Finset.mem_erase] at h1
    have h2 := h1.2
    simp only [hpldef, pool, Finset.mem_filter, Finset.mem_range] at h2
    exact ⟨h2.1, Nat.one_le_iff_ne_zero.2 h1.1, h2.2.1, h2.2.2⟩
  have hSpos : ∀ x ∈ S, ε ≤ x ∧ x - ε < j := by
    intro x hx
    obtain ⟨h1, h2, -, -⟩ := hSmem x hx
    exact ⟨by omega, by omega⟩
  set Smask : Fin 4 → Finset (ZMod j) := fun _ => shiftMask j ε S with hSmaskdef
  have hScardk : ∀ i, ((Smask i).card : ℝ) = kN := by
    intro i; simp only [hSmaskdef]; rw [card_shiftMask hSpos, hScard]
  -- the four sequences
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
  have hcs : IsSignVec c := isSignVec_toVec (isSignSeq_castLen hlen
    (isSignSeq_append (isSignSeq_dropFirst (ε := ε) hQs) hTs))
  have hds : IsSignVec d := isSignVec_toVec (isSignSeq_castLen hlen
    (isSignSeq_append (isSignSeq_dropFirst (ε := ε) hQs) (isSignSeq_neg hTs)))
  have hpools : Pools (sigmaOf β) a b c d Smask := by
    have entry : ∀ t ∈ shiftMask j ε S, a t = -(σZ : ℝ) ∧ b t = σZ ∧ c t = σZ ∧ d t = σZ := by
      intro t ht
      simp only [shiftMask, Finset.mem_image] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      obtain ⟨h1, h2, h3, h4⟩ := hSmem x hx
      have hi : x - ε < l ^ 2 - ε := by omega
      obtain ⟨e1, e2, e3, e4⟩ := rowsSeqs_toVec hlen PQ.1 PQ.2 R T (x - ε) hi
      rw [Nat.sub_add_cancel (hSpos x hx).1, h3] at e1 e2
      rw [Nat.sub_add_cancel (hSpos x hx).1, h4] at e3 e4
      exact ⟨e1, e2, e3, e4⟩
    rw [hsig]
    exact ⟨fun t ht => (entry t ht).1, fun t ht => (entry t ht).2.2.1,
      fun t ht => (entry t ht).2.2.2, fun t ht => (entry t ht).2.1⟩
  -- the window, eq. `window`
  have hwin : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < j →
      Real.sqrt (2 * j) + deltaL Smask ℓ ≤ Real.sqrt (energy a b c d ℓ) ∧
        Real.sqrt (energy a b c d ℓ) ≤ 2 * Real.sqrt (2 * j) - deltaL Smask ℓ := by
    intro ℓ hℓ1 hℓ2
    have hdl : deltaL Smask ℓ = 2 * ‖pS S (omega j ^ ℓ)‖ := by
      simp only [deltaL, hSmaskdef, max_self, norm_Shat_shiftMask hSpos]
    obtain ⟨θ, hθ, hθ1, hθ2⟩ := omega_pow_arc hℓ1 hℓ2
    have hJ : (j : ℝ) ≤ 4 ^ h * seedArc lam := by
      have : (lp : ℝ) ^ 2 = 4 ^ h * (lamp : ℝ) ^ 2 := by
        rw [hlpR, mul_pow, ← pow_mul, mul_comm h 2, pow_mul]; norm_num
      calc (j : ℝ) ≤ (lp : ℝ) ^ 2 := hjlp.le
        _ = 4 ^ h * (lamp : ℝ) ^ 2 := this
        _ ≤ 4 ^ h * seedArc lam := mul_le_mul_of_nonneg_left harc (by positivity)
    have hθ1' : 2 * π / (4 ^ h * seedArc lam) ≤ |θ| := by
      refine le_trans ?_ hθ1
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hJ
    have hmask := mask_bound hArc σZ hσZ lam h S hShS θ hθ1' hθ2
    rw [← hθ, hScard] at hmask
    have hδ : deltaL Smask ℓ < 2 * sR - ρ := by
      rw [hdl]; rw [hkN] at hmask
      clear_value ρ sR m
      have h1 : 2 * ‖pS S (omega j ^ ℓ)‖ ≤ 2 * (sR - m - 4 / 5) := by linarith only [hmask]
      have h2 : ρ - 8 / 5 < 2 * (m : ℝ) := by linarith only [hm1']
      linarith only [h1, h2]
    obtain ⟨hE1, hE2⟩ := hE ℓ
    have hE0 : 0 ≤ energy a b c d ℓ := le_trans (by positivity) hE1
    have hs0 : 0 ≤ sR := by
      rw [hsRdef]; have : (64 : ℝ) ≤ l := by exact_mod_cast hl64
      linarith only [this, hεR1]
    have h2s : 2 * sR ≤ Real.sqrt (energy a b c d ℓ) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * sR)]
      exact Real.sqrt_le_sqrt (by linarith only [hE1])
    have he : Real.sqrt (energy a b c d ℓ) ^ 2 ≤ 12 * j - 8 * sR ^ 2 := by
      rw [Real.sq_sqrt hE0]; exact hE2
    have := window_bounds hρdef (by linarith only [hρ90]) hsb.2 h2s he hδ
    rw [← hρdef]
    exact ⟨this.1.le, this.2.le⟩
  -- Lemma `lem:criterion`
  have hK : Window (Kmat β ![vsum a, vsum b, vsum c, vsum d] kN j) j := by
    rw [sa, sb, sc, sd, ← hsN]
    rcases hβ with rfl | rfl
    · exact hsec.1
    · exact hsec.2
  have hXW := criterion_window β hβ a b c d Smask kN hScardk hK hwin
  have hXS := Xmat_isSign hβ ha hb hcs hds hpools
  exact exists_fin_window hXS hXW

end SignCond
