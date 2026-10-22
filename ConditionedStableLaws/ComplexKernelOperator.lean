import ConditionedStableLaws.PeripheralCyclic
import ConditionedStableLaws.LeftSimplicity
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# The compact complex killed operator

Complexification is performed by real and imaginary parts, keeping the kernel integral at every
state. Compactness is inherited from the real strong Feller operator.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws.ComplexKernel
noncomputable section
variable {M : Type*} [TopologicalSpace M]

def realPart : (M →ᵇ ℂ) →L[ℝ] (M →ᵇ ℝ) := Complex.reCLM.compLeftContinuousBounded M
def imagPart : (M →ᵇ ℂ) →L[ℝ] (M →ᵇ ℝ) := Complex.imCLM.compLeftContinuousBounded M
def ofReal : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℂ) := Complex.ofRealCLM.compLeftContinuousBounded M

@[simp] theorem realPart_apply (f : M →ᵇ ℂ) (x : M) : realPart f x = (f x).re := rfl
@[simp] theorem imagPart_apply (f : M →ᵇ ℂ) (x : M) : imagPart f x = (f x).im := rfl
@[simp] theorem ofReal_apply (f : M →ᵇ ℝ) (x : M) : ofReal f x = (f x : ℂ) := rfl

def complexificationReal (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) :
    (M →ᵇ ℂ) →L[ℝ] (M →ᵇ ℂ) :=
  ofReal.comp (T.comp realPart) + Complex.I • ofReal.comp (T.comp imagPart)

theorem complexificationReal_apply (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (f : M →ᵇ ℂ) (x : M) :
    complexificationReal T f x = (T (realPart f) x : ℂ) + Complex.I * (T (imagPart f) x : ℂ) := rfl

theorem complexificationReal_isCompact (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hT : IsCompactOperator T) : IsCompactOperator (complexificationReal T) := by
  exact ((hT.comp_clm realPart).clm_comp ofReal).add
    (((hT.comp_clm imagPart).clm_comp ofReal).smul Complex.I)

end
end ConditionedStableLaws.ComplexKernel

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

theorem HypothesisH.complexificationReal_integral (h : HypothesisH ρ K)
    (f : M →ᵇ ℂ) (x : M) :
    ComplexKernel.complexificationReal h.continuousKernelOperator f x = ∫ y, f y ∂K.kernel x := by
  rw [ComplexKernel.complexificationReal_apply, h.continuousKernelOperator_apply,
    h.continuousKernelOperator_apply, mul_comm Complex.I]
  exact integral_re_add_im (f.integrable _)

/-- The compact complex-linear kernel operator. -/
def HypothesisH.complexKernelOperator (h : HypothesisH ρ K) :
    (M →ᵇ ℂ) →L[ℂ] (M →ᵇ ℂ) where
  toFun := ComplexKernel.complexificationReal h.continuousKernelOperator
  map_add' := map_add _
  map_smul' c f := by
    ext x
    simp only [h.complexificationReal_integral, BoundedContinuousFunction.smul_apply,
      smul_eq_mul, integral_const_mul, RingHom.id_apply]
  cont := (ComplexKernel.complexificationReal h.continuousKernelOperator).continuous

theorem HypothesisH.complexKernelOperator_apply (h : HypothesisH ρ K)
    (f : M →ᵇ ℂ) (x : M) : h.complexKernelOperator f x = ∫ y, f y ∂K.kernel x :=
  h.complexificationReal_integral f x

theorem HypothesisH.complexKernelOperator_isCompact (h : HypothesisH ρ K) :
    IsCompactOperator h.complexKernelOperator :=
  ComplexKernel.complexificationReal_isCompact _ h.continuousKernelOperator_isCompact

theorem HypothesisH.realPart_complexKernelOperator (h : HypothesisH ρ K) (f : M →ᵇ ℂ) :
    ComplexKernel.realPart (h.complexKernelOperator f) = h.continuousKernelOperator (ComplexKernel.realPart f) := by
  ext x
  rw [ComplexKernel.realPart_apply, h.complexKernelOperator_apply, h.continuousKernelOperator_apply]
  exact (integral_re (f.integrable _)).symm

theorem HypothesisH.imagPart_complexKernelOperator (h : HypothesisH ρ K) (f : M →ᵇ ℂ) :
    ComplexKernel.imagPart (h.complexKernelOperator f) = h.continuousKernelOperator (ComplexKernel.imagPart f) := by
  ext x
  rw [ComplexKernel.imagPart_apply, h.complexKernelOperator_apply, h.continuousKernelOperator_apply]
  exact (integral_im (f.integrable _)).symm

theorem HypothesisH.complexKernelOperator_ofReal (h : HypothesisH ρ K) (f : M →ᵇ ℝ) :
    h.complexKernelOperator (ComplexKernel.ofReal f) = ComplexKernel.ofReal (h.continuousKernelOperator f) := by
  ext x
  rw [h.complexKernelOperator_apply, ComplexKernel.ofReal_apply, h.continuousKernelOperator_apply]
  exact integral_complex_ofReal

/-- A nonzero complex eigenfunction pairs positively, in norm, with the
positive left probability eigenmeasure. -/
theorem HypothesisH.integral_norm_complex_eigenfunction_pos (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (f : M →ᵇ ℂ) (hf : f ≠ 0) {z : ℂ} (hz : z ≠ 0)
    (heq : h.complexKernelOperator f = z • f) : 0 < ∫ x, ‖f x‖ ∂μ := by
  have hactual (x : M) : (∫ y, f y ∂K.kernel x) = z * f x := by
    rw [← h.complexKernelOperator_apply, heq]
    rfl
  by_contra hnot
  have hzero : (∫ x, ‖f x‖ ∂μ) = 0 := le_antisymm (le_of_not_gt hnot)
    (integral_nonneg (fun x => norm_nonneg (f x)))
  have hae : (f.normComp : M → ℝ) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (f x)) (f.integrable μ).norm).mp hzero
  apply hf
  ext x
  by_cases hx : x ∈ survivingSet K.kernel
  · apply norm_eq_zero.mp
    exact Measure.support_subset_of_isClosed
      (isClosed_eq f.normComp.continuous continuous_const) hae
      (h.eigenmeasure_full_surviving_support μ hr hleft hx)
  · exact complex_eigenfunction_zero_on_escaping f hz hactual
      (by simpa only [survivingSet, mem_compl_iff, not_not] using hx)

/-- The left eigenmeasure bounds the modulus of every complex eigenvalue by its positive eigenvalue.
-/
theorem HypothesisH.complex_eigenvalue_norm_le (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (f : M →ᵇ ℂ) (hf : f ≠ 0) {z : ℂ}
    (heq : h.complexKernelOperator f = z • f) : ‖z‖ ≤ r := by
  by_cases hz : z = 0
  · simpa [hz] using hr.le
  have hp := h.integral_norm_complex_eigenfunction_pos μ hr hleft f hf hz heq
  have hle (x : M) : ‖z‖ * f.normComp x ≤ h.continuousKernelOperator f.normComp x := by
    have hi := norm_integral_le_integral_norm (f := (f : M → ℂ)) (μ := K.kernel x)
    rw [← h.complexKernelOperator_apply, heq] at hi
    simpa only [h.continuousKernelOperator_apply, BoundedContinuousFunction.smul_apply,
      smul_eq_mul, norm_mul, BoundedContinuousFunction.coe_normComp, Function.comp_apply] using hi
  have hi := integral_mono ((f.normComp.integrable μ).const_mul ‖z‖)
    ((h.continuousKernelOperator f.normComp).integrable μ) hle
  rw [integral_const_mul, h.integral_continuousKernelOperator_of_eigenmeasure μ hr.le hleft] at hi
  exact (mul_le_mul_iff_of_pos_right hp).mp hi

/-- Real geometric simplicity upgrades to complex geometric simplicity at
the positive eigenvalue by taking real and imaginary parts. -/
theorem HypothesisH.complex_eigenfunction_eq_smul (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η)
    (f : M →ᵇ ℂ) (heq : h.complexKernelOperator f = (r : ℂ) • f) :
    ∃ c : ℂ, f = c • ComplexKernel.ofReal η := by
  have hre : h.continuousKernelOperator (ComplexKernel.realPart f) = r • ComplexKernel.realPart f := by
    rw [← h.realPart_complexKernelOperator, heq]
    ext x
    simp
  have him : h.continuousKernelOperator (ComplexKernel.imagPart f) = r • ComplexKernel.imagPart f := by
    rw [← h.imagPart_complexKernelOperator, heq]
    ext x
    simp
  obtain ⟨a, ha⟩ := h.real_eigenfunction_eq_smul μ hr hleft η hηne hηpos hηeq _ hre
  obtain ⟨b, hb⟩ := h.real_eigenfunction_eq_smul μ hr hleft η hηne hηpos hηeq _ him
  refine ⟨(a : ℂ) + (b : ℂ)*Complex.I, ?_⟩
  ext x
  apply Complex.ext
  · have hx := congrArg (fun g : M →ᵇ ℝ => g x) ha
    simpa [Complex.mul_re] using hx
  · have hx := congrArg (fun g : M →ᵇ ℝ => g x) hb
    simpa [Complex.mul_im] using hx

end
end ConditionedStableLaws.StandingHypothesis
