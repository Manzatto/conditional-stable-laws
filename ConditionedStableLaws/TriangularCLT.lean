import ConditionedStableLaws.TriangularExpansion

/-!
# The conditional triangular-array central limit theorem

Let `gₙ` be bounded measurable with `ν(gₙ) = 0` and `aₙ → ∞`, and assume

* (i) `‖gₙ‖∞ / aₙ → 0`,
* (ii) `n (ν(gₙ²) + μ(gₙ²)) / aₙ² = O(1)`,
* (iii) `n σₙ² / aₙ² → σ²`, `σₙ² = ν(gₙ²) + 2 ∑_{m ≥ 1} μ(gₙ λ^{-m} 𝒫ᵐ(η gₙ))`.

Then for every `x ∈ M \ Z`, under `ℙₓ(· | τ > n)`, `aₙ⁻¹ ∑_{j<n} gₙ(X_j) → 𝒩(0, σ²)` (for `σ = 0`,
`δ₀`).

The proof uses real exponential twists: the twisted operators `P̂ ∘ e^{(s/aₙ) gₙ}` are uniformly
close to `P̂` on `L∞(ρ)`, so the rank-one perturbation theorem gives eigenpairs `(Λₙ, Πₙ)` with
uniform remainder bounds; the eigenvalue expansion of Steps 1–2 and assumptions (i)–(iii) give `n
(Λₙ - 1) → σ² s²/2` (Step 3); the spectral decomposition evaluated at `x` gives `E_x[e^{s Sₙ/aₙ} | τ
> n] → e^{σ² s²/2}` (Step 4, summing directly over `0 ≤ j < n`, so Step 5 is not needed); and the
continuity theorem for moment generating functions concludes.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.TriangularCLT

noncomputable section

open StandingHypothesis CanonicalChain TwistedOperators Concentration L2Bridge
  ConditionalCLT

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

set_option maxHeartbeats 8000000 in
/-- **Conditional triangular-array CLT.** -/
theorem conditional_triangular_clt (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (g : ℕ → M → ℝ) (hgm : ∀ n, Measurable (g n))
    (G : ℕ → ℝ) (hgG : ∀ n y, |g n y| ≤ G n)
    (hν : ∀ n, ∫ y, g n y ∂μ.withDensity d.weight = 0) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (_ha_lim : Tendsto a atTop atTop) (hi : Tendsto (fun n => G n / a n) atTop (𝓝 0))
    (hii : ∃ B : ℝ, ∀ n : ℕ, n * (∫ y, g n y ^ 2 ∂μ.withDensity d.weight +
      ∫ y, g n y ^ 2 ∂μ) / a n ^ 2 ≤ B)
    {σ2 : ℝ} (hiii : Tendsto (fun n : ℕ => n * asymptoticVariance C μ d (g n) / a n ^ 2) atTop
      (𝓝 σ2))
    (x : d.State) :
    0 ≤ σ2 ∧
    TendstoInDistribution (fun (n : ℕ) ω => (a n)⁻¹ * pathBirkhoffSum (g n) n ω) atTop id
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (gaussianReal 0 σ2.toNNReal) := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hKfin : IsFiniteKernel C.killedTransition := by
    simpa using killedKernel_power_isFinite C.toKilledKernel 1
  obtain ⟨s', hmean⟩ := h.exists_survivalGapData_with_mean d s.continuous_weight μ hleft hnorm
  set r := d.rate.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  set Top : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := h.transitionOperator with hTop_def
  set T₀ : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := r⁻¹ • Top with hT₀_def
  set ν := μ.withDensity d.weight with hν_def
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hμρ : μ ≪ ρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  have hη : ∫ y, (d.weight y).toReal ∂μ = 1 :=
    L2Compactness.integral_eta (K := C.toKilledKernel) d μ hnorm
  obtain ⟨Bη', hBη'⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d s.continuous_weight
  set Bη := max Bη' 0 with hBη_def
  have hBη0 : 0 ≤ Bη := le_max_right _ _
  have hηB : ∀ y, (d.weight y).toReal ≤ Bη := fun y => by
    have := hBη' y; rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hη0 : ∀ y, 0 ≤ (d.weight y).toReal := fun y => ENNReal.toReal_nonneg
  have hηm : Measurable fun y => (d.weight y).toReal := d.measurable_weight.ennreal_toReal
  set v := s'.eigenvector
  set ℓ := s'.mean
  have hℓv : ℓ v = 1 := by
    rw [hmean, integral_congr_ae (hμρ.ae_eq s'.eigenvector_ae)]; exact hη
  have hℓT : ∀ w, ℓ (T₀ w) = ℓ w := SurvivalGapData.mean_normalizedOperator h d s' μ hleft hmean
  have hTv : T₀ v = v :=
    StandingHypothesis.SurvivalGapData.normalizedOperator_eigenvector h d s'
  have hT₀P : T₀ * ℓ.smulRight v = ℓ.smulRight v := by
    ext1 w
    simp only [mul_apply_eq_comp, ContinuousLinearMap.smulRight_apply, map_smul, hTv]
  have hPT₀ : ℓ.smulRight v * T₀ = ℓ.smulRight v := by
    ext1 w
    simp only [mul_apply_eq_comp, ContinuousLinearMap.smulRight_apply, hℓT]
  have hgap : ∀ n : ℕ, 1 ≤ n → ‖T₀ ^ n - ℓ.smulRight v‖ ≤ s'.constant * s'.decay ^ n :=
    fun n hn => s'.gap n hn
  have hG0 : ∀ n, 0 ≤ G n := fun n => (abs_nonneg _).trans (hgG n x.val)
  set q : ℕ → Multiplier M := fun n =>
    { toFun := g n, measurable := hgm n, bound := G n, bound_nonneg := hG0 n,
      le_bound := hgG n } with hq_def
  obtain ⟨Cop, L, κ, hCop0, hL, hκ0, hκ1, hCop, hdec⟩ :=
    l2_bridge C h d s.continuous_weight μ hleft hnorm hμρ ℓ hmean
  obtain ⟨ε₀, hε₀, K₀, hK₀, χ, hχ0, hχ1, C', hC', hstab⟩ :=
    OperatorPerturbation.stability_of_rank_one_gap T₀ v ℓ hℓv hT₀P hPT₀
      s'.decay_nonneg s'.decay_lt_one hgap
  set P0 := ℓ.smulRight v with hP0_def
  set Csp := 2 * ((‖P0‖ + K₀ * ε₀) * ‖v‖) with hCsp_def
  have hCsp0 : 0 ≤ Csp := by positivity
  obtain ⟨δ₀, hδ₀, Kx, hKx, hexp⟩ := TriangularExpansion.eigenvalue_expansion hμρ T₀ ℓ v hηm hBη0
    hη0 hηB s'.eigenvector_ae hmean hℓT hTv hℓv hCop0 hL hκ0 hκ1 hCop hdec s'.decay_nonneg
    s'.decay_lt_one hgap hCsp0
  -- The variance in operator form.
  have hcen : ∀ n, centered C μ d (g n) = g n := fun n => by
    funext y
    show g n y - ∫ z, g n z ∂μ.withDensity d.weight = g n y
    rw [show ∫ z, g n z ∂μ.withDensity d.weight = 0 from hν n, sub_zero]
  have hwithDensity : ∀ f : M → ℝ, ∫ y, f y ∂ν = ∫ y, f y * (d.weight y).toReal ∂μ := by
    intro f
    rw [hν_def, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
    congr 1; funext y; rw [smul_eq_mul, mul_comm]
  have hηb : ∀ y, |(d.weight y).toReal| ≤ Bη := fun y => by rw [abs_of_nonneg (hη0 y)]; exact hηB y
  have hvar : ∀ n, asymptoticVariance C μ d (g n) =
      ∫ y, (q n).toFun y ^ 2 * (d.weight y).toReal ∂μ +
        2 * ∑' m : ℕ, ℓ (mulL (q n) ((T₀ ^ (m + 1)) (mulL (q n) v))) := by
    intro n
    rw [asymptoticVariance, hcen, hwithDensity]
    congr 2
    refine tsum_congr fun m => ?_
    have hΓv : (mulL (q n) v : M → ℝ) =ᵐ[ρ] fun z => (d.weight z).toReal * centered C μ d (g n) z :=
      (mulL_ae (q n) v).trans (by
        filter_upwards [s'.eigenvector_ae] with y hy
        show g n y * v y = _
        rw [hy, hcen, mul_comm])
    have hwm : Measurable fun z => (d.weight z).toReal * centered C μ d (g n) z := by
      rw [hcen]; exact hηm.mul (hgm n)
    have hwb : ∀ z, |(d.weight z).toReal * centered C μ d (g n) z| ≤ Bη * G n := fun z => by
      rw [hcen, abs_mul]; exact mul_le_mul (hηb z) (hgG n z) (abs_nonneg _) hBη0
    have hpow := normalized_pow_ae C h r (mulL (q n) v) hwm hwb hΓv (m + 1)
    rw [hmean, correlation]
    refine (integral_congr_ae (hμρ.ae_eq ?_)).symm
    filter_upwards [mulL_ae (q n) ((T₀ ^ (m + 1)) (mulL (q n) v)), hpow] with y h1 h2
    rw [h1, h2, hcen]
  obtain ⟨B, hB⟩ := hii
  -- The conditioned moment generating functions.
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  set am : ℕ → ℝ := fun n => r⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ with ham_def
  have ham_pos : ∀ n, 0 < am n := fun n => by
    refine mul_pos (pow_pos (inv_pos.2 hr) _) ?_
    have hp := C.pathMeasure_survival_pos x.val hx n
    rw [C.pathMeasure_survival] at hp
    have : IsFiniteKernel (C.killedTransition ^ n) := killedKernel_power_isFinite C.toKilledKernel n
    exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  set ηx := (d.weight x.val).toReal with hηx_def
  have hηx : 0 < ηx := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  have ham_lim : Tendsto am atTop (𝓝 ηx) := by
    have := s.normalized_survival_tendstoUniformly.tendsto_at x.val
    exact this.congr fun n => normalized_survival_toReal (K := C.toKilledKernel) d n x.val
  set Lx : Lp ℝ ∞ ρ →L[ℝ] ℝ := h.stepEvaluation r⁻¹ x.val with hLx_def
  have hLv : Lx v = ηx := by
    rw [hLx_def, h.stepEvaluation_apply]
    have h1 : ∫ y, v y ∂C.toKilledKernel.kernel x.val =
        ∫ y, (d.weight y).toReal ∂C.toKilledKernel.kernel x.val :=
      integral_congr_ae ((h.absolutelyContinuous x.val).ae_eq s'.eigenvector_ae)
    have h2 := L2Compactness.kint_eta (K := C.toKilledKernel) d x.val
    rw [h1]
    change r⁻¹ * KernelLp.kint C.toKilledKernel.kernel
      (L2Compactness.eta (K := C.toKilledKernel) d) x.val = _
    rw [h2]
    change r⁻¹ * (r * ηx) = ηx
    field_simp
  set one : Lp ℝ ∞ ρ := (memLp_top_const (μ := ρ) (1 : ℝ)).toLp _ with hone_def
  have hone : (one : M → ℝ) =ᵐ[ρ] fun _ => 1 := (memLp_top_const (1 : ℝ)).coeFn_toLp
  have hℓone : ℓ one = 1 := by
    rw [hmean, integral_congr_ae (hμρ.ae_eq hone)]; simp
  have hLnorm : ∀ f, |Lx f| ≤ r⁻¹ * ‖f‖ := fun f => by
    rw [hLx_def, h.stepEvaluation_apply, abs_mul, abs_of_pos (inv_pos.2 hr)]
    exact mul_le_mul_of_nonneg_left (by simpa using h.kernel_integral_norm_le f x.val)
      (inv_nonneg.2 hr.le)
  have hΦ0 : Lx ((1 * P0 * T₀) one) = ηx := by
    simp only [one_mul, mul_apply_eq_comp, hP0_def, ContinuousLinearMap.smulRight_apply,
      hℓT, hℓone, one_smul, hLv]
  have hmgf : ∀ s₀ : ℝ, Tendsto (fun (n : ℕ) => ∫ ω, Real.exp (s₀ * ((a n)⁻¹ *
      pathBirkhoffSum (g n) n ω))
        ∂(C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) atTop
      (𝓝 (Real.exp (σ2 * s₀ ^ 2 / 2))) := by
    intro s₀
    set u : ℕ → ℝ := fun n => s₀ / a n with hu_def
    have hδn : Tendsto (fun n => |u n| * G n) atTop (𝓝 0) := by
      have := hi.const_mul |s₀|
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      simp only [hu_def, abs_div, abs_of_pos (ha n)]
      ring
    set Mn : ℕ → Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := fun n => mulL (expMultiplier (q n) (u n)) with hMn_def
    set Tn : ℕ → Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := fun n => T₀ * Mn n with hTn_def
    have hMdiff : ∀ n, |u n| * G n ≤ 1 → ‖Mn n - 1‖ ≤ 3 * (|u n| * G n) := by
      intro n hn
      refine opNorm_le_of_ae _ (fun y => Real.exp (u n * g n y) - 1)
        (mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) (hG0 n)))
        (fun y => ?_) (fun f => ?_)
      · have hx1 : |u n * g n y| ≤ 1 := by
          rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hgG n y) (abs_nonneg _)).trans hn
        refine (TriangularExpansion.abs_exp_sub_one_le hx1).trans ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgG n y) (abs_nonneg _))
          (by norm_num)
      · filter_upwards [Lp.coeFn_sub (Mn n f) f, mulL_ae (expMultiplier (q n) (u n)) f]
          with y h1 h2
        rw [sub_apply, one_apply_eq_self, h1, Pi.sub_apply, h2]
        simp only [expMultiplier, hq_def]
        ring
    have hTdiff : ∀ n, ‖Tn n - T₀‖ ≤ ‖T₀‖ * ‖Mn n - 1‖ := fun n => by
      rw [show Tn n - T₀ = T₀ * (Mn n - 1) by simp [hTn_def, mul_sub]]
      exact norm_mul_le _ _
    have hMlim : Tendsto (fun n => ‖Mn n - 1‖) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
        (by simpa using hδn.const_mul 3)
      filter_upwards [hδn.eventually (ge_mem_nhds one_pos)] with n hn
      exact hMdiff n hn
    have hTlim : Tendsto (fun n => ‖Tn n - T₀‖) atTop (𝓝 0) :=
      squeeze_zero (fun n => norm_nonneg _) hTdiff (by simpa using hMlim.const_mul ‖T₀‖)
    -- The eigen-data of the perturbed operators.
    have hEx : ∀ n, ∃ (Λ : ℝ) (Pr : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ), ‖Tn n - T₀‖ ≤ ε₀ →
        (Tn n * Pr = Λ • Pr ∧ Pr * Tn n = Λ • Pr ∧ |Λ - 1| ≤ K₀ * ‖Tn n - T₀‖ ∧
          ‖Pr - P0‖ ≤ K₀ * ‖Tn n - T₀‖ ∧ χ < Λ ∧
          ∀ k : ℕ, 1 ≤ k → ‖Tn n ^ k - Λ ^ k • Pr‖ ≤ C' * χ ^ k) := by
      intro n
      by_cases hn : ‖Tn n - T₀‖ ≤ ε₀
      · obtain ⟨Λ, Pr, H⟩ := hstab (Tn n) hn
        exact ⟨Λ, Pr, fun _ => H⟩
      · exact ⟨0, 0, fun h' => absurd h' hn⟩
    choose Λ Pr hΛPr using hEx
    set E := Real.exp (σ2 * s₀ ^ 2 / 2) with hE_def
    -- The good event.
    have hgood : ∀ᶠ n in atTop, ‖Tn n - T₀‖ ≤ ε₀ ∧ |u n| * G n ≤ δ₀ ∧ |u n| * G n ≤ 1 ∧
        K₀ * ‖Tn n - T₀‖ * (‖ℓ‖ * ‖v‖) ≤ 1 / 2 := by
      have h1 := hTlim.eventually (ge_mem_nhds hε₀)
      have h2 := hδn.eventually (ge_mem_nhds hδ₀)
      have h3 := hδn.eventually (ge_mem_nhds one_pos)
      have h4 : Tendsto (fun n => K₀ * ‖Tn n - T₀‖ * (‖ℓ‖ * ‖v‖)) atTop (𝓝 0) := by
        simpa using (hTlim.const_mul K₀).mul_const (‖ℓ‖ * ‖v‖)
      filter_upwards [h1, h2, h3, h4.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1 / 2))]
        with n e1 e2 e3 e4
      exact ⟨e1, e2, e3, e4⟩
    -- Step 3: `n (Λₙ - 1) → σ² s²/2`.
    have hΛn : Tendsto (fun n : ℕ => (n : ℝ) * (Λ n - 1)) atTop (𝓝 (σ2 * s₀ ^ 2 / 2)) := by
      have hmain : Tendsto (fun n : ℕ => s₀ ^ 2 / 2 * (n * asymptoticVariance C μ d (g n) / a n ^ 2))
          atTop (𝓝 (σ2 * s₀ ^ 2 / 2)) := by
        have := hiii.const_mul (s₀ ^ 2 / 2)
        rwa [show s₀ ^ 2 / 2 * σ2 = σ2 * s₀ ^ 2 / 2 by ring] at this
      have herr : Tendsto (fun n => Kx * |s₀| ^ 3 * B * (G n / a n)) atTop (𝓝 0) := by
        simpa using hi.const_mul (Kx * |s₀| ^ 3 * B)
      have hdiff : ∀ᶠ n : ℕ in atTop, |(n : ℝ) * (Λ n - 1) -
          s₀ ^ 2 / 2 * (n * asymptoticVariance C μ d (g n) / a n ^ 2)| ≤
          |Kx * |s₀| ^ 3 * B * (G n / a n)| := by
        filter_upwards [hgood] with n hn
        obtain ⟨hn1, hn2, hn3, hn4⟩ := hn
        obtain ⟨hTP, hPT, hΛ1, hPr, hχΛ, hrem⟩ := hΛPr n hn1
        set N := ℓ (Pr n v) with hN_def
        have hN : |N - 1| ≤ 1 / 2 := by
          have e : N - 1 = ℓ ((Pr n - P0) v) := by
            rw [hN_def, sub_apply, map_sub, hP0_def,
              ContinuousLinearMap.smulRight_apply, map_smul, hℓv, smul_eq_mul, mul_one]
          rw [e, ← Real.norm_eq_abs]
          calc ‖ℓ ((Pr n - P0) v)‖ ≤ ‖ℓ‖ * (‖Pr n - P0‖ * ‖v‖) :=
                (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
                  ((Pr n - P0).le_opNorm v) (norm_nonneg _))
            _ ≤ ‖ℓ‖ * (K₀ * ‖Tn n - T₀‖ * ‖v‖) := by gcongr
            _ = K₀ * ‖Tn n - T₀‖ * (‖ℓ‖ * ‖v‖) := by ring
            _ ≤ 1 / 2 := hn4
        have hNpos : 1 / 2 ≤ N := by linarith [(abs_le.1 hN).1]
        set η' := N⁻¹ • Pr n v with hη'_def
        have heig : T₀ (mulL (expMultiplier (q n) (u n)) η') = Λ n • η' := by
          have := congrArg (fun A : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ => A v) hTP
          simp only [mul_apply_eq_comp, smul_apply,
            hTn_def, hMn_def] at this
          rw [hη'_def, map_smul, map_smul, this, smul_comm]
        have hℓη' : ℓ η' = 1 := by
          rw [hη'_def, map_smul, smul_eq_mul, ← hN_def]
          exact inv_mul_cancel₀ (by linarith)
        have hη'b : ‖η'‖ ≤ Csp := by
          rw [hη'_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith : (0:ℝ) < N)]
          have hPrn : ‖Pr n‖ ≤ ‖P0‖ + K₀ * ε₀ := by
            have := norm_le_norm_add_norm_sub' (Pr n) P0
            have := hPr.trans (mul_le_mul_of_nonneg_left hn1 hK₀)
            linarith
          have h1 : ‖Pr n v‖ ≤ (‖P0‖ + K₀ * ε₀) * ‖v‖ :=
            ((Pr n).le_opNorm v).trans (mul_le_mul_of_nonneg_right hPrn (norm_nonneg _))
          have h2 : N⁻¹ ≤ 2 := by
            rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
          calc N⁻¹ * ‖Pr n v‖ ≤ 2 * ((‖P0‖ + K₀ * ε₀) * ‖v‖) :=
                mul_le_mul h2 h1 (norm_nonneg _) (by norm_num)
            _ = Csp := rfl
        have hqη : ∫ y, (q n).toFun y * (d.weight y).toReal ∂μ = 0 := by
          rw [← hwithDensity]; exact hν n
        have hE := hexp (q n) hqη (u n) hn2 (Λ n) η' heig hℓη' hη'b
        rw [← hvar n] at hE
        have hS := hB n
        have han := ha n
        set S := ∫ y, (q n).toFun y ^ 2 * (d.weight y).toReal ∂μ + ∫ y, (q n).toFun y ^ 2 ∂μ
          with hS_def
        have hSν : S = ∫ y, g n y ^ 2 ∂ν + ∫ y, g n y ^ 2 ∂μ := by
          rw [hS_def, hwithDensity]
        have hS0 : 0 ≤ S := by
          rw [hS_def]
          exact add_nonneg (integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hη0 y))
            (integral_nonneg fun y => sq_nonneg _)
        have hnS : (n : ℝ) * S / a n ^ 2 ≤ B := by rw [hSν]; exact hS
        have hun : u n = s₀ / a n := rfl
        have e1 : (n : ℝ) * (Λ n - 1) - s₀ ^ 2 / 2 * (n * asymptoticVariance C μ d (g n) / a n ^ 2) =
            n * (Λ n - 1 - u n ^ 2 / 2 * asymptoticVariance C μ d (g n)) := by
          rw [hun]; field_simp
        rw [e1, abs_mul, Nat.abs_cast]
        have hG := hG0 n
        calc (n : ℝ) * |Λ n - 1 - u n ^ 2 / 2 * asymptoticVariance C μ d (g n)|
            ≤ n * (Kx * |u n| ^ 3 * (q n).bound * S) :=
              mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg n)
          _ = Kx * |s₀| ^ 3 * (G n / a n) * (n * S / a n ^ 2) := by
              simp only [hun, abs_div, abs_of_pos han, hq_def]
              field_simp
          _ ≤ |Kx * |s₀| ^ 3 * B * (G n / a n)| := by
              refine le_trans ?_ (le_abs_self _)
              have hK : 0 ≤ Kx * |s₀| ^ 3 * (G n / a n) := by
                have := hG0 n; positivity
              have := mul_le_mul_of_nonneg_left hnS hK
              linarith
      have hf : Tendsto (fun n : ℕ => (n : ℝ) * (Λ n - 1) -
          s₀ ^ 2 / 2 * (n * asymptoticVariance C μ d (g n) / a n ^ 2)) atTop (𝓝 0) :=
        squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hdiff) (by simpa using herr.abs)
      have := hmain.add hf
      simpa using this
    have hΛt : Tendsto Λ atTop (𝓝 1) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2
        (squeeze_zero_norm' ?_ (by simpa using hTlim.const_mul K₀))
      filter_upwards [hgood] with n hn
      rw [norm_norm, Real.norm_eq_abs]
      exact (hΛPr n hn.1).2.2.1
    have hpow : Tendsto (fun n => Λ n ^ n) atTop (𝓝 E) := by
      have := Real.tendsto_one_add_pow_exp_of_tendsto hΛn
      simpa [hE_def] using this
    have h2 : Tendsto (fun n => Λ n ^ (n - 2)) atTop (𝓝 E) := by
      have hsq : Tendsto (fun n => Λ n ^ 2) atTop (𝓝 1) := by simpa using hΛt.pow 2
      have := hpow.div hsq one_ne_zero
      rw [div_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 2, hΛt.eventually (isOpen_ne.mem_nhds
        (show (1 : ℝ) ≠ 0 from one_ne_zero))] with n hn hne
      simp only [Pi.div_apply]
      rw [div_eq_iff (pow_ne_zero _ hne), ← pow_add, Nat.sub_add_cancel hn]
    have hPrlim : Tendsto (fun n => ‖Pr n - P0‖) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
        (by simpa using hTlim.const_mul K₀)
      filter_upwards [hgood] with n hn
      exact (hΛPr n hn.1).2.2.2.1
    have h3 : Tendsto (fun n => Lx ((Mn n * Pr n * T₀) one)) atTop (𝓝 ηx) := by
      rw [← hΦ0]
      have hM : Tendsto Mn atTop (𝓝 1) := tendsto_iff_norm_sub_tendsto_zero.2 hMlim
      have hP : Tendsto Pr atTop (𝓝 P0) := tendsto_iff_norm_sub_tendsto_zero.2 hPrlim
      have hop : Tendsto (fun n => Mn n * Pr n * T₀) atTop (𝓝 (1 * P0 * T₀)) :=
        (hM.mul hP).mul tendsto_const_nhds
      have happ : Tendsto (fun n => (Mn n * Pr n * T₀) one) atTop (𝓝 ((1 * P0 * T₀) one)) := by
        refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
          (fun n => ?_) (by simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hop).mul_const ‖one‖))
        rw [← sub_apply]
        exact ContinuousLinearMap.le_opNorm _ _
      exact (Lx.continuous.tendsto _).comp happ
    set Ψ : ℕ → ℝ := fun n => Lx ((Mn n * ((T₀ * Mn n) ^ (n - 2) - Λ n ^ (n - 2) • Pr n) * T₀) one)
      with hΨ_def
    have h4 : Tendsto Ψ atTop (𝓝 0) := by
      have hχn : Tendsto (fun n : ℕ => r⁻¹ * 4 * C' * χ ^ (n - 2) * ‖T₀‖ * ‖one‖) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => χ ^ (n - 2)) atTop (𝓝 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one hχ0 hχ1).comp (tendsto_sub_atTop_nat 2)
        have := ((this.const_mul (r⁻¹ * 4 * C')).mul_const ‖T₀‖).mul_const ‖one‖
        simpa [mul_assoc] using this
      refine squeeze_zero_norm' ?_ hχn
      filter_upwards [hgood, eventually_ge_atTop 3] with n hn hn3
      have hrem := (hΛPr n hn.1).2.2.2.2.2 (n - 2) (by omega)
      have hMn : ‖Mn n‖ ≤ 4 := by
        have := norm_le_norm_add_norm_sub' (Mn n) 1
        have h1 := hMdiff n hn.2.2.1
        have h2 : ‖(1 : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        linarith [hn.2.2.1]
      rw [Real.norm_eq_abs]
      refine (hLnorm _).trans ?_
      have hop := ContinuousLinearMap.le_opNorm
        ((Mn n * ((T₀ * Mn n) ^ (n - 2) - Λ n ^ (n - 2) • Pr n) * T₀)) one
      have hmul : ‖Mn n * ((T₀ * Mn n) ^ (n - 2) - Λ n ^ (n - 2) • Pr n) * T₀‖ ≤
          4 * (C' * χ ^ (n - 2)) * ‖T₀‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
          (mul_le_mul hMn hrem (norm_nonneg _) (by norm_num))) (norm_nonneg _))
      calc r⁻¹ * ‖(Mn n * ((T₀ * Mn n) ^ (n - 2) - Λ n ^ (n - 2) • Pr n) * T₀) one‖
          ≤ r⁻¹ * (4 * (C' * χ ^ (n - 2)) * ‖T₀‖ * ‖one‖) :=
            mul_le_mul_of_nonneg_left (hop.trans (mul_le_mul_of_nonneg_right hmul
              (norm_nonneg _))) (inv_nonneg.2 hr.le)
        _ = r⁻¹ * 4 * C' * χ ^ (n - 2) * ‖T₀‖ * ‖one‖ := by ring
    have h1 : Tendsto (fun n => Real.exp (u n * g n x.val)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n => u n * g n x.val) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => ?_) hδn
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hgG n x.val) (abs_nonneg _)
      have := (Real.continuous_exp.tendsto 0).comp h0
      simpa [Function.comp_def] using this
    -- The normalized Feynman–Kac word.
    set F : ℕ → ℝ := fun n => r⁻¹ ^ n *
      (step C (fun y => Real.exp (u n * (q n).toFun y)))^[n] (fun _ => 1) x.val with hF_def
    have hdecomp : ∀ᶠ n in atTop, F n = Real.exp (u n * g n x.val) *
        (Λ n ^ (n - 2) * Lx ((Mn n * Pr n * T₀) one) + Ψ n) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      simp only [show m + 2 - 2 = m by omega]
      set gt := expMultiplier (q (m + 2)) (u (m + 2)) with hgt_def
      set A : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := mulL gt with hA_def
      have hAM : Mn (m + 2) = A := rfl
      have hrepr := iterate_step_ae C h gt one hone (m + 1)
      have hATop : ∀ k : ℕ, (A * Top) ^ k = r ^ k • (A * T₀) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ (A * Top), ih, pow_succ (A * T₀), pow_succ r]
          ext1 w
          simp only [mul_apply_eq_comp, smul_apply, hT₀_def,
            map_smul, smul_smul]
          congr 1
          field_simp
      have hint : ∫ z, (step C gt.toFun)^[m + 1] (fun _ => 1) z ∂C.killedTransition x.val =
          r * Lx (((A * Top) ^ (m + 1)) one) := by
        rw [hLx_def, h.stepEvaluation_apply, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
        exact integral_congr_ae ((h.absolutelyContinuous x.val).ae_eq hrepr.symm)
      have hsplit : (A * T₀) ^ (m + 1) = A * (Λ (m + 2) ^ m • Pr (m + 2) +
          ((T₀ * A) ^ m - Λ (m + 2) ^ m • Pr (m + 2))) * T₀ := by
        rw [mul_pow_succ_eq, add_sub_cancel]
      simp only [hF_def]
      rw [Function.iterate_succ_apply']
      change r⁻¹ ^ (m + 2) * (gt.toFun x.val * ∫ z, (step C gt.toFun)^[m + 1] (fun _ => 1) z
        ∂C.killedTransition x.val) = _
      rw [hint, hATop, hsplit, smul_apply, map_smul, smul_eq_mul]
      simp only [mul_add, add_mul, add_apply, map_add,
        mul_apply_eq_comp, smul_apply, map_smul, smul_eq_mul,
        hΨ_def, hAM, show m + 2 - 2 = m by omega]
      have hgx : gt.toFun x.val = Real.exp (u (m + 2) * g (m + 2) x.val) := rfl
      rw [hgx]
      have hr0 : r ≠ 0 := hr.ne'
      have key : r * (1 / r) ^ (m + 2) * r ^ (m + 1) = 1 := by
        rw [one_div, inv_pow]; field_simp; try ring
      field_simp
      rw [key, one_mul]
    have hFlim : Tendsto F atTop (𝓝 (E * ηx)) := by
      have := h1.mul ((h2.mul h3).add h4)
      rw [one_mul, add_zero] at this
      exact this.congr' (hdecomp.mono fun n hn => hn.symm)
    have hratio := hFlim.div ham_lim hηx.ne'
    rw [mul_div_assoc, div_self hηx.ne', mul_one] at hratio
    refine hratio.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn0
    have hval := integral_conditioned_exp C (q n).measurable (q n).bound_nonneg (q n).le_bound
      (u n) x.val n
    have hden : (C.pathMeasure x.val (survival n)).toReal = r ^ n * am n := by
      rw [C.pathMeasure_survival, ham_def]
      simp only
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul]
      rfl
    have hint_eq : ∫ ω, Real.exp (s₀ * ((a n)⁻¹ * pathBirkhoffSum (g n) n ω))
        ∂(C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) =
        ∫ ω, Real.exp (u n * pathBirkhoffSum (q n).toFun n ω) ∂C.conditionedMeasure x.val n := by
      congr 1
      funext ω
      congr 1
      simp only [hu_def, hq_def]
      ring
    rw [hint_eq, hval, hden]
    simp only [hF_def, Pi.div_apply]
    have han := ham_pos n
    have hr0 : r ≠ 0 := hr.ne'
    field_simp
    rw [one_div, inv_pow]
    field_simp
  -- `σ² ≥ 0` and the conclusion.
  have hYb : ∀ n : ℕ, ∀ ω, |(a n)⁻¹ * pathBirkhoffSum (g n) n ω| ≤ (a n)⁻¹ * (n * G n) := by
    intro n ω
    rw [abs_mul, abs_of_pos (inv_pos.2 (ha n))]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (ha n).le)
    unfold pathBirkhoffSum birkhoffSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range n, |zeroExtension (g n) (ω i)| ≤ ∑ _i ∈ Finset.range n, G n :=
          Finset.sum_le_sum fun i _ => SecondMoment.abs_zeroExtension_le (hG0 n) (hgG n) _
      _ = n * G n := by simp
  have hYm : ∀ n : ℕ, Measurable fun ω => (a n)⁻¹ * pathBirkhoffSum (g n) n ω := fun n =>
    (measurable_pathBirkhoffSum (hgm n) n).const_mul _
  have hYint : ∀ (n : ℕ) (c : ℝ), Integrable (fun ω => Real.exp (c * ((a n)⁻¹ *
      pathBirkhoffSum (g n) n ω))) (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) :=
    fun n c => Integrable.of_bound ((hYm n).const_mul c).exp.aestronglyMeasurable
      (Real.exp (|c| * ((a n)⁻¹ * (n * G n)))) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
        calc c * ((a n)⁻¹ * pathBirkhoffSum (g n) n ω)
            ≤ |c * ((a n)⁻¹ * pathBirkhoffSum (g n) n ω)| := le_abs_self _
          _ = |c| * |(a n)⁻¹ * pathBirkhoffSum (g n) n ω| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hYb n ω) (abs_nonneg c))
  have hσ0 : 0 ≤ σ2 := by
    have hsum := (hmgf 1).add (hmgf (-1))
    have hge : ∀ n : ℕ, 2 ≤ (∫ ω, Real.exp (1 * ((a n)⁻¹ * pathBirkhoffSum (g n) n ω))
          ∂(C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) +
        ∫ ω, Real.exp (-1 * ((a n)⁻¹ * pathBirkhoffSum (g n) n ω))
          ∂(C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) := by
      intro n
      rw [← integral_add (hYint n 1) (hYint n (-1))]
      calc (2 : ℝ) = ∫ _ω, (2 : ℝ)
            ∂(C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) := by simp
        _ ≤ _ := integral_mono (integrable_const _) ((hYint n 1).add (hYint n (-1))) fun ω => by
            simp only [Pi.add_apply, one_mul, neg_one_mul]
            have := Real.add_one_le_exp ((a n)⁻¹ * pathBirkhoffSum (g n) n ω)
            have := Real.add_one_le_exp (-((a n)⁻¹ * pathBirkhoffSum (g n) n ω))
            linarith
    have hlim2 := ge_of_tendsto' hsum hge
    have : 1 ≤ Real.exp (σ2 * 1 ^ 2 / 2) := by
      simp only [neg_one_sq, one_pow] at hlim2 ⊢; linarith
    have := Real.one_le_exp_iff.1 this
    linarith
  refine ⟨hσ0, ?_⟩
  refine tendstoInDistribution_gaussian_of_mgf_tendsto _ _ (fun n => (hYm n).aemeasurable)
    _ (fun n s₀ => hYint n s₀) (fun s₀ => ?_)
  rw [Real.coe_toNNReal _ hσ0]
  exact hmgf s₀

end

end ConditionedStableLaws.TriangularCLT
