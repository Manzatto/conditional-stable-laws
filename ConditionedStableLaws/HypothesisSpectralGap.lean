import ConditionedStableLaws.SmoothingGap

/-!
# The L∞ spectral gap from Hypothesis H

The continuous-function gap transfers through the strong Feller smoothing factorization. The
resulting data satisfy the spectral input used by the uniform survival and canonical Q-process limit
theorems.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Inclusion into L∞ using the probability reference measure supplied by H. -/
def HypothesisH.continuousEmbedding (h : HypothesisH ρ K) :
    (M →ᵇ ℝ) →L[ℝ] Lp ℝ ∞ ρ := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  exact BoundedContinuousFunction.toLp ∞ ρ ℝ

theorem HypothesisH.continuousEmbedding_ae (h : HypothesisH ρ K) (f : M →ᵇ ℝ) :
    h.continuousEmbedding f =ᵐ[ρ] f := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  exact BoundedContinuousFunction.coeFn_toLp ∞ ρ ℝ f

theorem HypothesisH.smoothing_factorization (h : HypothesisH ρ K) (c : ℝ) :
    let J := h.continuousEmbedding
    J.comp (h.smoothedOperator c) = c • h.transitionOperator ∧
      (h.smoothedOperator c).comp J = c • h.continuousKernelOperator := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  constructor
  · ext f
    simp [HypothesisH.smoothedOperator, HypothesisH.transitionOperator, HypothesisH.continuousEmbedding,
      transitionLInfinityOperator]
  · ext f x
    simp [HypothesisH.smoothedOperator, HypothesisH.continuousKernelOperator, HypothesisH.continuousEmbedding]

/-- The left integration functional transported through one normalized
smoothing step. -/
def HypothesisH.normalizedMean (h : HypothesisH ρ K) (μ : Measure M) [IsFiniteMeasure μ]
    (r : ℝ) : Lp ℝ ∞ ρ →L[ℝ] ℝ :=
  (LeftSimplicity.integralFunctional μ).comp (h.smoothedOperator r⁻¹)

/-- The transported functional is exactly integration against the left eigenmeasure, including on
arbitrary L∞ equivalence classes. -/
theorem HypothesisH.normalizedMean_eq_integral (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ) (f : Lp ℝ ∞ ρ) :
    h.normalizedMean μ r f = ∫ x, f x ∂μ := by
  have hμρ := h.eigenmeasure_absolutelyContinuous μ (ENNReal.ofReal_pos.mpr hr).ne' hleft
  have hfi : Integrable (f : M → ℝ) μ := Integrable.of_bound
    ((Lp.aestronglyMeasurable f).mono_ac hμρ) ‖f‖ (hμρ.ae_le (lp_infinity_ae_norm_le f))
  have hfic : Integrable (f : M → ℝ) (K.kernel ∘ₘ μ) := by
    rw [hleft]
    exact hfi.smul_measure ENNReal.ofReal_ne_top
  have hi : (∫ y, f y ∂(K.kernel ∘ₘ μ)) = ∫ x, ∫ y, f y ∂K.kernel x ∂μ := by
    rw [Measure.comp_eq_comp_const_apply] at hfic ⊢
    exact Kernel.integral_comp hfic
  change (∫ x, h.smoothedOperator r⁻¹ f x ∂μ) = ∫ x, f x ∂μ
  simp_rw [h.smoothedOperator_apply, h.stepEvaluation_apply]
  rw [integral_const_mul, ← hi, hleft, integral_smul_measure,
    ENNReal.toReal_ofReal hr.le, smul_eq_mul, inv_mul_cancel_left₀ hr.ne']

theorem HypothesisH.normalizedMean_continuousEmbedding (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ) (f : M →ᵇ ℝ) :
    h.normalizedMean μ r (h.continuousEmbedding f) = ∫ x, f x ∂μ := by
  rw [h.normalizedMean_eq_integral μ hr hleft]
  exact integral_congr_ae ((h.eigenmeasure_absolutelyContinuous μ
    (ENNReal.ofReal_pos.mpr hr).ne' hleft).ae_eq (h.continuousEmbedding_ae f))

/-- The normalized killed operator preserves its left mean. -/
theorem HypothesisH.normalizedMean_normalizedOperator (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ) (f : Lp ℝ ∞ ρ) :
    h.normalizedMean μ r ((r⁻¹ • h.transitionOperator) f) = h.normalizedMean μ r f := by
  rw [← (h.smoothing_factorization r⁻¹).1]
  change h.normalizedMean μ r (h.continuousEmbedding (h.smoothedOperator r⁻¹ f)) = _
  rw [h.normalizedMean_continuousEmbedding μ hr hleft]
  rfl

/-- The full positive-time L∞ rank-one gap for the killed operator. -/
theorem HypothesisH.lp_normalized_power_gap (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η) (hnorm : (∫ x, η x ∂μ) = 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖(r⁻¹ • h.transitionOperator)^n -
        (h.normalizedMean μ r).smulRight (h.continuousEmbedding η)‖ ≤ C*θ^n := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  obtain ⟨θ, hθ, hθone, C, hC, hgap⟩ :=
    h.continuous_normalized_power_gap μ hr hleft η hηne hηpos hηeq hnorm
  obtain ⟨D, hD, htransfer⟩ := SmoothingGap.transfer (h.smoothedOperator r⁻¹)
    (h.continuousEmbedding) (LeftSimplicity.integralFunctional μ) η hθ hC (by
      rwa [(h.smoothing_factorization r⁻¹).2])
  refine ⟨θ, hθ, hθone, D, hD, fun n hn => ?_⟩
  simpa only [(h.smoothing_factorization r⁻¹).1, HypothesisH.normalizedMean] using htransfer n hn

theorem HypothesisH.normalizedMean_one (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ) :
    h.normalizedMean μ r (h.continuousEmbedding (1 : M →ᵇ ℝ)) = 1 := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hA := congrArg (fun L => L (1 : M →ᵇ ℝ)) (h.smoothing_factorization r⁻¹).2
  change h.smoothedOperator r⁻¹ (h.continuousEmbedding (1 : M →ᵇ ℝ)) =
    r⁻¹ • h.continuousKernelOperator 1 at hA
  change (∫ x, h.smoothedOperator r⁻¹ (h.continuousEmbedding (1 : M →ᵇ ℝ)) x ∂μ) = 1
  rw [hA]
  change (∫ x, r⁻¹ * h.continuousKernelOperator 1 x ∂μ) = 1
  rw [integral_const_mul, h.integral_continuousKernelOperator_of_eigenmeasure μ hr.le hleft]
  simp [hr.ne']

/-- The spectral-gap package used by the canonical survival theorems exists
for any normalized eigen-data furnished by H. -/
theorem HypothesisH.exists_survivalGapData_with_mean (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : (∫⁻ x, d.weight x ∂μ) = 1) :
    ∃ s : SurvivalGapData h d, ∀ f : Lp ℝ ∞ ρ, s.mean f = ∫ x, f x ∂μ := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hcont : Continuous (fun x => (d.weight x).toReal) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (ENNReal.continuousAt_toReal (d.weight_ne_top x)).comp hc.continuousAt)
  let η : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨_, hcont⟩
  have hηpos (x : M) : 0 ≤ η x := ENNReal.toReal_nonneg
  have hηnorm : (∫ x, η x ∂μ) = 1 := by
    change (∫ x, (d.weight x).toReal ∂μ) = 1
    rw [integral_toReal d.measurable_weight.aemeasurable
      (ae_of_all _ (fun x => lt_top_iff_ne_top.mpr (d.weight_ne_top x))), hnorm]
    simp
  have hηne : η ≠ 0 := by
    intro he
    simp [he] at hηnorm
  have hr : 0 < d.rate.toReal := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  have hleft' : K.kernel ∘ₘ μ = ENNReal.ofReal d.rate.toReal • μ := by
    rwa [ENNReal.ofReal_toReal d.rate_ne_top]
  have hηeq : h.continuousKernelOperator η = d.rate.toReal • η := by
    ext x
    rw [h.continuousKernelOperator_apply]
    change (∫ y, (d.weight y).toReal ∂K.kernel x) = d.rate.toReal * (d.weight x).toReal
    rw [integral_toReal d.measurable_weight.aemeasurable
      (ae_of_all _ (fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y))), d.right_eigen,
      ENNReal.toReal_mul]
  obtain ⟨θ, hθ, hθone, C, hC, hgap⟩ := h.lp_normalized_power_gap μ hr hleft' η hηne hηpos hηeq hηnorm
  refine ⟨{
    mean := h.normalizedMean μ d.rate.toReal
    eigenvector := h.continuousEmbedding η
    one := h.continuousEmbedding (1 : M →ᵇ ℝ)
    one_ae := h.continuousEmbedding_ae _
    mean_one := h.normalizedMean_one μ hr hleft'
    eigenvector_ae := h.continuousEmbedding_ae η
    constant := C
    constant_nonneg := hC
    decay := θ
    decay_nonneg := hθ.le
    decay_lt_one := hθone
    gap := hgap
  }, fun f => h.normalizedMean_eq_integral μ hr hleft' f⟩

/-- Any spectral package whose mean is integration against the left measure has the normalized
left-eigenfunctional identity. -/
theorem SurvivalGapData.mean_normalizedOperator (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (s : SurvivalGapData h d)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ)
    (hmean : ∀ f : Lp ℝ ∞ ρ, s.mean f = ∫ x, f x ∂μ) (f : Lp ℝ ∞ ρ) :
    s.mean (((d.rate.toReal)⁻¹ • h.transitionOperator) f) = s.mean f := by
  have hr : 0 < d.rate.toReal := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  have hl : K.kernel ∘ₘ μ = ENNReal.ofReal d.rate.toReal • μ := by
    rwa [ENNReal.ofReal_toReal d.rate_ne_top]
  have he (v : Lp ℝ ∞ ρ) : s.mean v = h.normalizedMean μ d.rate.toReal v := by
    rw [hmean, h.normalizedMean_eq_integral μ hr hl]
  rw [he, he]
  exact h.normalizedMean_normalizedOperator μ hr hl f

/-- The spectral package obtained from H has mean given by integration against the eigenmeasure, and
is left invariant. -/
theorem HypothesisH.exists_survivalGapData_with_mean_invariant (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : (∫⁻ x, d.weight x ∂μ) = 1) :
    ∃ s : SurvivalGapData h d,
      (∀ f : Lp ℝ ∞ ρ, s.mean f = ∫ x, f x ∂μ) ∧
      ∀ f : Lp ℝ ∞ ρ,
        s.mean (((d.rate.toReal)⁻¹ • h.transitionOperator) f) = s.mean f := by
  obtain ⟨s, hs⟩ := h.exists_survivalGapData_with_mean d hc μ hleft hnorm
  exact ⟨s, hs, s.mean_normalizedOperator h d μ hleft hs⟩

/-- The spectral package exists for every normalized continuous eigen-data. -/
theorem HypothesisH.nonempty_survivalGapData (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : (∫⁻ x, d.weight x ∂μ) = 1) :
    Nonempty (SurvivalGapData h d) := by
  obtain ⟨s, _hs⟩ := h.exists_survivalGapData_with_mean d hc μ hleft hnorm
  exact ⟨s⟩

/-- H alone gives normalized eigen-data and its L∞ spectral gap. -/
theorem HypothesisH.exists_eigenData_survivalGap (h : HypothesisH ρ K) :
    ∃ d : DoobTransform.EigenData K.kernel, d.rate ≤ 1 ∧ Continuous d.weight ∧
      d.liveSet = survivingSet K.kernel ∧ ∃ μ : ProbabilityMeasure M,
      K.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) ∧
      (∫⁻ x, d.weight x ∂(μ : Measure M)) = 1 ∧ Nonempty (SurvivalGapData h d) := by
  obtain ⟨d, hdr, hc, hlive, μ, hleft, hnorm⟩ := h.exists_normalized_eigenData
  exact ⟨d, hdr, hc, hlive, μ, hleft, hnorm, h.nonempty_survivalGapData d hc μ hleft hnorm⟩

end
end ConditionedStableLaws.StandingHypothesis
