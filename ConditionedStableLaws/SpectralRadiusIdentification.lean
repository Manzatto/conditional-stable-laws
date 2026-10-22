import ConditionedStableLaws.HypothesisSpectralGap

/-!
Identification of the positive eigenvalue with the spectral radius of the real L∞ killed operator.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

theorem HypothesisH.continuousEmbedding_transition (h : HypothesisH ρ K) (f : M →ᵇ ℝ) :
    h.transitionOperator (h.continuousEmbedding f) =
      h.continuousEmbedding (h.continuousKernelOperator f) := by
  obtain ⟨hP, hT⟩ := h.smoothing_factorization 1
  simp only [one_smul] at hP hT
  rw [← hP, ← hT]
  rfl

/-- Every real spectral value of the L∞ operator has modulus at most the positive left eigenvalue.
-/
theorem HypothesisH.real_spectrum_abs_le_rate (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    {a : ℝ} (ha : a ∈ spectrum ℝ h.transitionOperator) : |a| ≤ r := by
  by_cases ha0 : a = 0
  · simpa [ha0] using hr.le
  obtain ⟨f, hf, heq⟩ := h.exists_continuous_eigenfunction_of_mem_spectrum a ha0 ha
  have hfC : ComplexKernel.ofReal f ≠ 0 := by
    intro hz
    apply hf
    ext x
    have hx := congrArg (fun g : M →ᵇ ℂ => (g x).re) hz
    simpa using hx
  have heqC : h.complexKernelOperator (ComplexKernel.ofReal f) = (a : ℂ) • ComplexKernel.ofReal f := by
    ext x
    rw [h.complexKernelOperator_apply]
    change (∫ y, (f y : ℂ) ∂K.kernel x) = (a : ℂ)*(f x : ℂ)
    rw [integral_complex_ofReal, heq, Complex.ofReal_mul]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    h.complex_eigenvalue_norm_le μ hr hleft _ hfC heqC

/-- The positive normalized eigenvalue is the spectral radius of the real L∞ operator. -/
theorem HypothesisH.transitionOperator_spectralRadius_eq (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηeq : h.continuousKernelOperator η = r • η)
    (hnorm : (∫ x, η x ∂μ) = 1) :
    spectralRadius ℝ h.transitionOperator = ENNReal.ofReal r := by
  have hηne : h.continuousEmbedding η ≠ 0 := by
    intro hz
    have he := h.normalizedMean_continuousEmbedding μ hr hleft η
    rw [hz, map_zero, hnorm] at he
    exact zero_ne_one he
  have hηeig : h.transitionOperator (h.continuousEmbedding η) = r • h.continuousEmbedding η := by
    rw [h.continuousEmbedding_transition, hηeq, map_smul]
  have hhas : Module.End.HasEigenvector (h.transitionOperator : Module.End ℝ (Lp ℝ ∞ ρ))
      r (h.continuousEmbedding η) :=
    ⟨Module.End.mem_eigenspace_iff.mpr hηeig, hηne⟩
  have hrmem : r ∈ spectrum ℝ h.transitionOperator := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector hhas).mem_spectrum
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · apply iSup₂_le
    intro a ha
    rw [ENNReal.coe_nnreal_eq]
    exact ENNReal.ofReal_le_ofReal (h.real_spectrum_abs_le_rate μ hr hleft ha)
  · have hb : (↑‖r‖₊ : ℝ≥0∞) ≤ ⨆ a ∈ spectrum ℝ h.transitionOperator, (↑‖a‖₊ : ℝ≥0∞) :=
      le_iSup_of_le r (le_iSup_of_le hrmem le_rfl)
    simpa only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hr] using hb

end
end ConditionedStableLaws.StandingHypothesis
