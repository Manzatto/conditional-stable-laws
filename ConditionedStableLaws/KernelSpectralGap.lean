import ConditionedStableLaws.ComplexKernelOperator
import ConditionedStableLaws.CompactRankOneGap

/-!
# The killed kernel has a strict complex spectral gap

The left functional is integration against the probability eigenmeasure, and the right vector is the
normalized continuous positive eigenfunction. The gap is obtained from H1–H3.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace ConditionedStableLaws.ComplexKernel
noncomputable section
variable {M : Type*} [MeasurableSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]

/-- Integration of bounded continuous complex functions. -/
def integralFunctional (μ : Measure M) [IsFiniteMeasure μ] : (M →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous {
    toFun f := ∫ x, f x ∂μ
    map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
    map_smul' c f := by simpa only [RingHom.id_apply, BoundedContinuousFunction.smul_apply]
      using integral_smul c (f : M → ℂ)
  } (μ.real univ) (fun f => f.norm_integral_le_mul_norm μ)

@[simp] theorem integralFunctional_apply (μ : Measure M) [IsFiniteMeasure μ] (f : M →ᵇ ℂ) :
    integralFunctional μ f = ∫ x, f x ∂μ := rfl

end
end ConditionedStableLaws.ComplexKernel

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

theorem HypothesisH.integral_complexKernelOperator_of_eigenmeasure
    (h : HypothesisH ρ K) (μ : Measure M) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ) (f : M →ᵇ ℂ) :
    (∫ x, h.complexKernelOperator f x ∂μ) = (r : ℂ) * ∫ x, f x ∂μ := by
  have hi : (∫ y, f y ∂(K.kernel ∘ₘ μ)) = ∫ x, ∫ y, f y ∂K.kernel x ∂μ := by
    rw [Measure.comp_eq_comp_const_apply]
    exact Kernel.integral_comp (f.integrable _)
  rw [hleft, integral_smul_measure, ENNReal.toReal_ofReal hr, Complex.real_smul] at hi
  simpa only [h.complexKernelOperator_apply] using hi.symm

/-- The compact complex operator, with its integration functional, has a rank-one remainder with
spectral radius strictly below r. -/
theorem HypothesisH.complex_remainder_spectralRadius_lt (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η) (hnorm : (∫ x, η x ∂μ) = 1) :
    spectralRadius ℂ (CompactRankOneGap.remainder h.complexKernelOperator r
      (ComplexKernel.ofReal η) (ComplexKernel.integralFunctional μ)) < ENNReal.ofReal r := by
  obtain ⟨x, _hx⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  have : Nontrivial (M →ᵇ ℂ) := ⟨⟨0, 1, by
    intro he
    have hh := congrArg (fun f : M →ᵇ ℂ => f x) he
    exact zero_ne_one hh⟩⟩
  apply CompactRankOneGap.spectralRadius_remainder_lt _ h.complexKernelOperator_isCompact hr
  · change (∫ x, (η x : ℂ) ∂μ) = 1
    rw [integral_complex_ofReal, hnorm, Complex.ofReal_one]
  · intro f
    exact h.integral_complexKernelOperator_of_eigenmeasure μ hr.le hleft f
  · intro f hf z heq
    exact h.complex_eigenvalue_norm_le μ hr hleft f hf heq
  · intro f hf z heq hz
    apply h.complex_peripheral_eigenvalue_eq μ hr hleft f hf hz
    intro y
    rw [← h.complexKernelOperator_apply, heq]
    rfl
  · exact h.complex_eigenfunction_eq_smul μ hr hleft η hηne hηpos hηeq

end
end ConditionedStableLaws.StandingHypothesis
