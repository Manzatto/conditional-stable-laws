import ConditionedStableLaws.L2Variance
import ConditionedStableLaws.UniformSmallTargets

/-!
# The conditional CLT in `L²(μ)`

The remaining input of the truncation argument is the conditioned large-observation estimate
`ℙ_{x,n}(|g(X_j)| > ε√n for some 0 ≤ j < n) → 0`. The one-time marginals are bounded by mixing
across the final gap for `1 ≤ j ≤ n/2` (where the error carries `sup_z 𝒫(z, A_{n,ε})`, which
vanishes by uniform smallness of targets) and across the initial gap for `n/2 < j < n`; the leading
terms are `O(n μ(A_{n,ε})) → 0`, and the term `j = 0` vanishes because `g(x)` is finite.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.L2Variance

noncomputable section

open StandingHypothesis CanonicalChain ConditionalCLT

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {rho : Measure M} (C : CanonicalChain M)

theorem geom_shift_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (m : ℕ) :
    ∑ j ∈ Finset.range m, θ ^ (j + 1 - 2) ≤ 1 + (1 - θ)⁻¹ := by
  have h1θ : 0 < 1 - θ := by linarith
  rcases m with _ | m
  · simp only [Finset.range_zero, Finset.sum_empty]; positivity
  · rw [Finset.sum_range_succ']
    have : ∀ j ∈ Finset.range m, θ ^ (j + 1 + 1 - 2) = θ ^ j := fun j _ => by
      congr 1
    rw [Finset.sum_congr rfl this]
    rw [show (0 : ℕ) + 1 - 2 = 0 from rfl, pow_zero]
    linarith [SecondMoment.geom_le hθ0 hθ1 m]

set_option maxHeartbeats 2000000 in
/-- The deterministic bound behind the conditional large-observation estimate, for a target `U` not
containing the starting point. -/
theorem large_observation_sum_le {mu : Measure M} [IsProbabilityMeasure mu]
    (D : SecondMoment.Data0 C mu) (x : M) (n : ℕ) (U : Set M) (hU : MeasurableSet U)
    (hx : x ∉ U) {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hden : c ≤ SecondMoment.nkp C D.r n (fun _ => 1) x)
    (hsmall : ∀ y, SecondMoment.nkp C D.r 1 (U.indicator D.η) y ≤ δ) :
    (∑ i ∈ Finset.range n, (C.conditionedMeasure x n).real
        {omega | omega i ∈ Option.some '' U}) ≤
      ((n : ℝ) * ((D.Bη + D.E) * D.η x * mu.real U) +
        (D.A + 1) * δ * (1 + (1 - D.θ)⁻¹) +
        D.E * D.S * (D.θ ^ (n - n / 2 - 1) * (1 - D.θ)⁻¹) +
        D.E * D.A * (D.θ ^ (n / 2) * (1 - D.θ)⁻¹)) / c := by
  have : Nonempty M := ⟨x⟩
  have hθ0 := D.θ_nonneg
  have hθ1 := D.θ_lt_one
  have h1θ : 0 < (1 - D.θ)⁻¹ := inv_pos.2 (by linarith)
  have hA := D.A_nonneg
  have hS := D.S_nonneg
  have hE := D.E_nonneg
  have hBη := D.Bη_nonneg
  have hηx := D.η_nonneg x
  have hμU : 0 ≤ mu.real U := measureReal_nonneg
  have hνU0 : 0 ≤ ∫ y, U.indicator D.η y ∂mu :=
    integral_nonneg fun y => indicator_nonneg (fun z _ => D.η_nonneg z) y
  have hνU : ∫ y, U.indicator D.η y ∂mu ≤ D.Bη * mu.real U := by
    calc ∫ y, U.indicator D.η y ∂mu ≤ ∫ y, U.indicator (fun _ => D.Bη) y ∂mu :=
          integral_mono_of_nonneg (ae_of_all _ fun y => indicator_nonneg
            (fun z _ => D.η_nonneg z) y) ((integrable_const _).indicator hU)
            (ae_of_all _ fun y => indicator_le_indicator (D.η_le y))
      _ = D.Bη * mu.real U := by rw [integral_indicator_const _ hU, smul_eq_mul, mul_comm]
  have hRHS0 : 0 ≤ ((n : ℝ) * ((D.Bη + D.E) * D.η x * mu.real U) +
        (D.A + 1) * δ * (1 + (1 - D.θ)⁻¹) +
        D.E * D.S * (D.θ ^ (n - n / 2 - 1) * (1 - D.θ)⁻¹) +
        D.E * D.A * (D.θ ^ (n / 2) * (1 - D.θ)⁻¹)) / c := by positivity
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simpa using hRHS0
  set m := n / 2 with hm_def
  set l := n - 1 - m with hl_def
  have hmn : m < n := by omega
  have hn : n = m + 1 + l := by omega
  set q : ℕ → ℝ := fun i => (C.conditionedMeasure x n).real {omega | omega i ∈ Option.some '' U}
  have hsplit : (∑ i ∈ Finset.range n, q i) =
      q 0 + (∑ j ∈ Finset.range m, q (j + 1)) + ∑ j ∈ Finset.range l, q (m + 1 + j) := by
    conv_lhs => rw [hn, Finset.sum_range_add, Finset.sum_range_succ']
    ring
  have hq0 : q 0 = 0 := C.conditioned_target_zero x n U hU hx
  have hearly : ∀ j ∈ Finset.range m, q (j + 1) ≤
      ((∫ y, U.indicator D.η y ∂mu) * D.η x + (D.A + 1) * D.θ ^ (j + 1 - 2) * δ +
        D.E * (D.S * D.θ ^ (n - (j + 1) - 1))) / c := by
    intro j hj
    have hjm := Finset.mem_range.1 hj
    exact conditioned_target_early_le C D x (by omega) (by omega) U hU hc hδ hden hsmall
  have hlate : ∀ j ∈ Finset.range l, q (m + 1 + j) ≤
      (D.E * ((mu.real U) * D.η x + D.A * D.θ ^ (m + 1 + j - 1))) / c := by
    intro j hj
    have hjl := Finset.mem_range.1 hj
    exact conditioned_target_late_le C D x (by omega) (by omega) U hU hc hden
  have hE1 := Finset.sum_le_sum hearly
  have hE2 := Finset.sum_le_sum hlate
  simp only [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_add] at hE1 hE2
  have hg1 := geom_shift_le hθ0 hθ1 m
  have hg2 := reverse_geometric_tail_le hθ0 hθ1 hmn
  have hg3 := forward_geometric_tail_le hθ0 hθ1 m l
  rw [div_eq_mul_inv] at hg2 hg3
  rw [hsplit, hq0, zero_add]
  refine (add_le_add hE1 hE2).trans ?_
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hc.le
  have hml : (m : ℝ) + l ≤ n := by exact_mod_cast (show m + l ≤ n by omega)
  have k1 : (m : ℝ) * ((∫ y, U.indicator D.η y ∂mu) * D.η x) ≤
      (m : ℝ) * (D.Bη * D.η x * mu.real U) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    nlinarith
  have k2 : (D.A + 1) * (∑ j ∈ Finset.range m, D.θ ^ (j + 1 - 2)) * δ ≤
      (D.A + 1) * δ * (1 + (1 - D.θ)⁻¹) := by
    have := mul_le_mul_of_nonneg_left hg1 (mul_nonneg (by linarith : 0 ≤ D.A + 1) hδ)
    linarith
  have k3 : D.E * (D.S * ∑ j ∈ Finset.range m, D.θ ^ (n - (j + 1) - 1)) ≤
      D.E * D.S * (D.θ ^ (n - m - 1) * (1 - D.θ)⁻¹) := by
    have := mul_le_mul_of_nonneg_left hg2 (mul_nonneg hE hS)
    linarith
  have k4 : D.E * (D.A * ∑ j ∈ Finset.range l, D.θ ^ (m + 1 + j - 1)) ≤
      D.E * D.A * (D.θ ^ m * (1 - D.θ)⁻¹) := by
    have := mul_le_mul_of_nonneg_left hg3 (mul_nonneg hE hA)
    linarith
  have k5 : (m : ℝ) * (D.Bη * D.η x * mu.real U) + (l : ℝ) * (D.E * (mu.real U * D.η x)) ≤
      (n : ℝ) * ((D.Bη + D.E) * D.η x * mu.real U) := by
    have hp1 : 0 ≤ D.Bη * D.η x * mu.real U := by positivity
    have hp2 : 0 ≤ D.E * D.η x * mu.real U := by positivity
    have e : (n : ℝ) * ((D.Bη + D.E) * D.η x * mu.real U) =
        (n : ℝ) * (D.Bη * D.η x * mu.real U) + (n : ℝ) * (D.E * D.η x * mu.real U) := by ring
    rw [e]
    have hm' : (m : ℝ) ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) l]
    have hl' : (l : ℝ) ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have := mul_le_mul_of_nonneg_right hm' hp1
    have := mul_le_mul_of_nonneg_right hl' hp2
    nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
/-- Targets `Uₙ` with `ρ(Uₙ) → 0`, `n μ(Uₙ) → 0` and eventually avoiding the
starting point are visited before time `n` with vanishing conditioned
probability (summed over the visiting times). -/
theorem sum_targets_tendsto_zero (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ y, d.weight y ∂mu = 1)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (hρU : Tendsto (fun n => rho (U n)) atTop (𝓝 0))
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * mu.real (U n)) atTop (𝓝 0))
    (hxU : ∀ᶠ n in atTop, x.val ∉ U n) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (C.conditionedMeasure x.val n).real
      {omega | omega i ∈ Option.some '' U n}) atTop (𝓝 0) := by
  have : Nonempty M := ⟨x.val⟩
  have := h.reference_probability
  obtain ⟨D, hDr, hDη, -⟩ := SecondMoment.exists_data0 C h d s mu hleft hnorm 0 zero_lt_one
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  -- The normalized survival masses at `x` are bounded below.
  set a : ℕ → ℝ := fun N => SecondMoment.nkp C D.r N (fun _ => 1) x.val with ha_def
  have ha_pos : ∀ N, 0 < a N := fun N => by
    have hp := C.pathMeasure_survival_pos x.val hx N
    have hpos : 0 < (C.pathMeasure x.val (survival N)).toReal :=
      ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
    have : IsFiniteKernel (C.killedTransition ^ N) :=
      killedKernel_power_isFinite C.toKilledKernel N
    rw [C.pathMeasure_survival] at hpos
    have e : ((C.killedTransition ^ N) x.val univ).toReal = D.r ^ N * a N := by
      simp only [ha_def, SecondMoment.nkp, SecondMoment.kpow, integral_const, smul_eq_mul,
        mul_one]
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ D.r_pos.ne', one_pow, one_mul]
      rfl
    rw [e] at hpos
    exact pos_of_mul_pos_right hpos (pow_pos D.r_pos N).le
  have hηx : 0 < (d.weight x.val).toReal := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  have ha_lim : Tendsto a atTop (𝓝 (d.weight x.val).toReal) := by
    have := s.normalized_survival_tendstoUniformly.tendsto_at x.val
    refine this.congr fun N => ?_
    rw [normalized_survival_toReal (K := C.toKilledKernel) d N x.val]
    have : IsFiniteKernel (C.killedTransition ^ N) :=
      killedKernel_power_isFinite C.toKilledKernel N
    simp only [ha_def, SecondMoment.nkp, SecondMoment.kpow, integral_const, smul_eq_mul,
      mul_one, hDr]
    rfl
  obtain ⟨c, hc, hca⟩ := SecondMoment.exists_pos_lower ha_pos hηx ha_lim
  have hunif := (h.uniform_small_targets_lemma).1 U hU hρU
  -- Deterministic bounds.
  have hθ0 := D.θ_nonneg
  have hθ1 := D.θ_lt_one
  have hBη := D.Bη_nonneg
  have hE := D.E_nonneg
  have hS := D.S_nonneg
  have hA := D.A_nonneg
  set K1 : ℝ := (D.A + 1) * (D.r⁻¹ * D.Bη) * (1 + (1 - D.θ)⁻¹) / c with hK1_def
  have h1θ : 0 < (1 - D.θ)⁻¹ := inv_pos.2 (by linarith)
  have hK1 : 0 ≤ K1 := by
    have := D.r_pos
    positivity
  set V : ℕ → ℝ := fun n => ((n : ℝ) * ((D.Bη + D.E) * D.η x.val * mu.real (U n)) +
      D.E * D.S * (D.θ ^ (n - n / 2 - 1) * (1 - D.θ)⁻¹) +
      D.E * D.A * (D.θ ^ (n / 2) * (1 - D.θ)⁻¹)) / c with hV_def
  have hhalf : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop two_ne_zero
  have hhalf' : Tendsto (fun n : ℕ => n - n / 2 - 1) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) ((tendsto_sub_atTop_nat 1).comp hhalf)
    change n / 2 - 1 ≤ n - n / 2 - 1
    omega
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
  have hV : Tendsto V atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) * ((D.Bη + D.E) * D.η x.val * mu.real (U n)))
        atTop (𝓝 0) := by
      have := hscaled.const_mul ((D.Bη + D.E) * D.η x.val)
      rw [mul_zero] at this
      exact this.congr fun n => by ring
    have h2 := ((hpow.comp hhalf').mul_const (1 - D.θ)⁻¹).const_mul (D.E * D.S)
    have h3 := ((hpow.comp hhalf).mul_const (1 - D.θ)⁻¹).const_mul (D.E * D.A)
    have := ((h1.add h2).add h3).div_const c
    simp only [zero_mul, mul_zero, add_zero, zero_div] at this
    exact this
  refine tendsto_order.2 ⟨fun t ht => Eventually.of_forall fun n =>
    lt_of_lt_of_le ht (Finset.sum_nonneg fun _ _ => measureReal_nonneg), fun t ht => ?_⟩
  set η' : ℝ := t / (2 * (K1 + 1)) with hη'_def
  have hη' : 0 < η' := by positivity
  have hK1η : K1 * η' < t / 2 := by
    rw [hη'_def]
    rw [show K1 * (t / (2 * (K1 + 1))) = t / 2 * (K1 / (K1 + 1)) by field_simp]
    have : K1 / (K1 + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  filter_upwards [hunif η' hη', hxU, hV.eventually (gt_mem_nhds (half_pos ht))]
    with n hsm hxn hVn
  have hsmall : ∀ y, SecondMoment.nkp C D.r 1 ((U n).indicator D.η) y ≤
      D.r⁻¹ * D.Bη * η' := by
    intro y
    have hfin : IsFiniteKernel (C.killedTransition ^ 1) :=
      killedKernel_power_isFinite C.toKilledKernel 1
    rw [pow_one] at hfin
    have hint : ∫ w, (U n).indicator D.η w ∂C.killedTransition y ≤
        D.Bη * (C.killedTransition y).real (U n) := by
      calc ∫ w, (U n).indicator D.η w ∂C.killedTransition y
            ≤ ∫ w, (U n).indicator (fun _ => D.Bη) w ∂C.killedTransition y :=
            integral_mono_of_nonneg (ae_of_all _ fun w => indicator_nonneg
              (fun z _ => D.η_nonneg z) w) ((integrable_const _).indicator (hU n))
              (ae_of_all _ fun w => indicator_le_indicator (D.η_le w))
        _ = D.Bη * (C.killedTransition y).real (U n) := by
            rw [integral_indicator_const _ (hU n), smul_eq_mul, mul_comm]
    have hP : (C.killedTransition y).real (U n) ≤ η' := (hsm y).le
    have e : SecondMoment.nkp C D.r 1 ((U n).indicator D.η) y =
        D.r⁻¹ * ∫ w, (U n).indicator D.η w ∂C.killedTransition y := by
      simp [SecondMoment.nkp, SecondMoment.kpow]
    rw [e, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hint.trans ?_) (inv_nonneg.2 D.r_pos.le)
    exact mul_le_mul_of_nonneg_left hP hBη
  have hδ : 0 ≤ D.r⁻¹ * D.Bη * η' := by have := D.r_pos; positivity
  have hsum := large_observation_sum_le C D x.val n (U n) (hU n) hxn hc hδ (hca n) hsmall
  have hle := hsum
  have hsplit : ((n : ℝ) * ((D.Bη + D.E) * D.η x.val * mu.real (U n)) +
        (D.A + 1) * (D.r⁻¹ * D.Bη * η') * (1 + (1 - D.θ)⁻¹) +
        D.E * D.S * (D.θ ^ (n - n / 2 - 1) * (1 - D.θ)⁻¹) +
        D.E * D.A * (D.θ ^ (n / 2) * (1 - D.θ)⁻¹)) / c = K1 * η' + V n := by
    rw [hK1_def, hV_def]
    field_simp
    ring
  rw [hsplit] at hle
  linarith

/-- **Conditional large-observation estimate**: under `ℙ_x(· | τ > n)`, some observation among the
first `n` exceeds `ε√n` with vanishing probability. -/
theorem large_observation_tendsto_zero (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ y, d.weight y ∂mu = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 mu) (x : d.State)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (C.conditionedMeasure x.val n).real
      (largeObservationEvent g ε n)) atTop (𝓝 0) := by
  have := h.reference_probability
  -- The targets shrink to the empty set, hence are uniformly small for the kernel.
  set U : ℕ → Set M := fun n => largeObservationTarget g ε n with hU_def
  have hU : ∀ n, MeasurableSet (U n) := fun n => measurableSet_largeObservationTarget hgm ε n
  have hanti : Antitone U := by
    intro m n hmn y hy
    change ε * Real.sqrt m < |g y|
    have hy' : ε * Real.sqrt n < |g y| := hy
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hmn)) hε.le) hy'
  have hempty : ∀ y, ∀ᶠ n in atTop, y ∉ U n := by
    intro y
    obtain ⟨N, hN⟩ := exists_nat_gt ((|g y| / ε) ^ 2)
    filter_upwards [eventually_ge_atTop N] with n hn hy
    have hy' : ε * Real.sqrt n < |g y| := hy
    have h1 : |g y| / ε < Real.sqrt n := by
      rw [Real.lt_sqrt (by positivity)]
      exact hN.trans_le (by exact_mod_cast hn)
    rw [div_lt_iff₀ hε] at h1
    linarith
  have hρU : Tendsto (fun n => rho (U n)) atTop (𝓝 0) := by
    have h0 := tendsto_measure_iInter_atTop (μ := rho) (fun n => (hU n).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    have hI : (⋂ n, U n) = ∅ := by
      ext y
      simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := (hempty y).exists
      exact ⟨n, hn⟩
    rwa [hI, measure_empty] at h0
  have hsum := sum_targets_tendsto_zero C h d s hlive mu hleft hnorm x U hU hρU
    (scaled_largeObservationTarget_tendsto_zero hgm hg2 hε) (hempty x.val)
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => largeObservation_probability_le_sum C hε.le n x.val) hsum

/-- **Conditional CLT in `L²(μ)`.** For a finite-valued measurable `g ∈ L²(μ)`, the covariance
series converges absolutely, `σ_g² ≥ 0`, and under `ℙ_x(· | τ > n)` the normalized centred Birkhoff
sums converge in law to `𝒩(0, σ_g²)`. -/
theorem conditional_clt_l2 (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ y, d.weight y ∂mu = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 mu) (x : d.State) :
    Summable (fun m => |correlation C mu d g m|) ∧
      0 ≤ asymptoticVariance C mu d g ∧
      TendstoInDistribution
        (fun (n : ℕ) omega => (Real.sqrt (n : ℝ))⁻¹ *
          pathBirkhoffSum (centered C mu d g) n omega)
        atTop id (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
        (gaussianReal 0 (asymptoticVariance C mu d g).toNNReal) :=
  conditional_clt_l2_of_truncation_negligible C h d s hlive mu hleft hnorm hgm hg2 x
    (truncation_negligible_of_large_observations C h d s hlive mu hleft hnorm hgm hg2 x
      fun _ hε => large_observation_tendsto_zero C h d s hlive mu hleft hnorm hgm hg2 x hε)

end

end ConditionedStableLaws.L2Variance
