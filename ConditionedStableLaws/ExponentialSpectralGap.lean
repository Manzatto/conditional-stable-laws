import ConditionedStableLaws.KernelSpectralGap
import ConditionedStableLaws.SpectralPowerBound

/-! Exponential decay of the normalized operator error. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws.CompactRankOneGap
noncomputable section

theorem normalized_power_gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (η : E) (ℓ : E →L[ℂ] ℂ) (hℓη : ℓ η = 1)
    (hTη : T η = (r : ℂ) • η) (hℓT : ∀ f, ℓ (T f) = (r : ℂ) * ℓ f)
    (hspec : spectralRadius ℂ (remainder T r η ℓ) < ENNReal.ofReal r) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖((r : ℂ)⁻¹ • T)^n - ℓ.smulRight η‖ ≤ C*θ^n := by
  obtain ⟨q, hq, hqr, C, hC, hb⟩ := SpectralPowerBound.exists_geometric_bound _ hr hspec
  refine ⟨q/r, div_pos hq hr, (div_lt_one hr).mpr hqr, C, hC, fun n hn => ?_⟩
  rw [normalized_power_error T hr.ne' η ℓ hℓη hTη hℓT n hn, norm_smul, norm_pow,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  calc
    r⁻¹^n * ‖(remainder T r η ℓ)^n‖ ≤ r⁻¹^n * (C*q^n) :=
      mul_le_mul_of_nonneg_left (hb n) (pow_nonneg (inv_nonneg.mpr hr.le) n)
    _ = C*(q/r)^n := by rw [div_eq_mul_inv, mul_pow]; ring

end
end ConditionedStableLaws.CompactRankOneGap

namespace ConditionedStableLaws.ComplexKernel
noncomputable section
variable {M : Type*} [TopologicalSpace M]

theorem norm_ofReal (f : M →ᵇ ℝ) : ‖ofReal f‖ = ‖f‖ := by
  simp only [BoundedContinuousFunction.norm_eq_iSup_norm, ofReal_apply, Complex.norm_real]

end
end ConditionedStableLaws.ComplexKernel

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Exponential rank-one convergence for the complex operator. -/
theorem HypothesisH.complex_normalized_power_gap (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η) (hnorm : (∫ x, η x ∂μ) = 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖((r : ℂ)⁻¹ • h.complexKernelOperator)^n -
        (ComplexKernel.integralFunctional μ).smulRight (ComplexKernel.ofReal η)‖ ≤ C*θ^n := by
  apply CompactRankOneGap.normalized_power_gap _ hr
  · change (∫ x, (η x : ℂ) ∂μ) = 1
    rw [integral_complex_ofReal, hnorm, Complex.ofReal_one]
  · rw [h.complexKernelOperator_ofReal, hηeq]
    ext x
    simp
  · exact h.integral_complexKernelOperator_of_eigenmeasure μ hr.le hleft
  · exact h.complex_remainder_spectralRadius_lt μ hr hleft η hηne hηpos hηeq hnorm

/-- Complexification commutes with every normalized power of the real operator. -/
theorem HypothesisH.normalized_power_ofReal (h : HypothesisH ρ K)
    (r : ℝ) (n : ℕ) (f : M →ᵇ ℝ) :
    (((r : ℂ)⁻¹ • h.complexKernelOperator)^n) (ComplexKernel.ofReal f) =
      ComplexKernel.ofReal (((r⁻¹ • h.continuousKernelOperator)^n) f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih]
    change (r : ℂ)⁻¹ • h.complexKernelOperator (ComplexKernel.ofReal _) =
      ComplexKernel.ofReal (r⁻¹ • h.continuousKernelOperator _)
    rw [h.complexKernelOperator_ofReal, map_smul]
    ext x
    simp

/-- The real continuous-function operator has the same exponential rank-one gap. -/
theorem HypothesisH.continuous_normalized_power_gap (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η) (hnorm : (∫ x, η x ∂μ) = 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖(r⁻¹ • h.continuousKernelOperator)^n -
        (LeftSimplicity.integralFunctional μ).smulRight η‖ ≤ C*θ^n := by
  obtain ⟨θ, hθ, hθone, C, hC, hgap⟩ := h.complex_normalized_power_gap μ hr hleft η hηne hηpos hηeq hnorm
  refine ⟨θ, hθ, hθone, C, hC, fun n hn => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hθ.le n))
  intro f
  have heq : ComplexKernel.ofReal (((r⁻¹ • h.continuousKernelOperator)^n -
      (LeftSimplicity.integralFunctional μ).smulRight η) f) =
      ((((r : ℂ)⁻¹ • h.complexKernelOperator)^n -
        (ComplexKernel.integralFunctional μ).smulRight (ComplexKernel.ofReal η)) (ComplexKernel.ofReal f)) := by
    rw [sub_apply, sub_apply, map_sub, h.normalized_power_ofReal]
    congr 1
    ext x
    change (((∫ y, f y ∂μ) * η x : ℝ) : ℂ) =
      (∫ y, (f y : ℂ) ∂μ) * (η x : ℂ)
    rw [integral_complex_ofReal, Complex.ofReal_mul]
  rw [← ComplexKernel.norm_ofReal, heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [ComplexKernel.norm_ofReal]
    exact mul_le_mul_of_nonneg_right (hgap n hn) (norm_nonneg f))

end
end ConditionedStableLaws.StandingHypothesis
