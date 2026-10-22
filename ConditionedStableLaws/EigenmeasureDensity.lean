import ConditionedStableLaws.StandingHypothesis
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Densities of eigenmeasures

The left eigenidentity and H1 force absolute continuity with respect to the reference measure.
Radon–Nikodym then supplies a nonnegative L1 real density.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

theorem HypothesisH.eigenmeasure_absolutelyContinuous (h : HypothesisH ρ K)
    (μ : Measure M) {rate : ℝ≥0∞} (hr : rate ≠ 0)
    (hleft : K.kernel ∘ₘ μ = rate • μ) : μ ≪ ρ := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hρ
  have hzero : (K.kernel ∘ₘ μ) A = 0 := by
    rw [Measure.bind_apply hA K.kernel.aemeasurable]
    have hz : (fun x => K.kernel x A) = fun _ => 0 :=
      funext (fun x => h.absolutelyContinuous x hρ)
    rw [hz, lintegral_zero]
  rw [hleft, Measure.smul_apply, smul_eq_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hr

/-- The density is a real nonnegative integrable function, and reconstructs the original measure by
`withDensity`. -/
theorem HypothesisH.exists_eigenmeasure_density (h : HypothesisH ρ K)
    (μ : Measure M) [IsFiniteMeasure μ] {rate : ℝ≥0∞} (hr : rate ≠ 0)
    (hleft : K.kernel ∘ₘ μ = rate • μ) :
    ∃ m : M → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ Integrable m ρ ∧
      μ = ρ.withDensity (fun x => ENNReal.ofReal (m x)) := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hac := h.eigenmeasure_absolutelyContinuous μ hr hleft
  refine ⟨fun x => (μ.rnDeriv ρ x).toReal, (μ.measurable_rnDeriv ρ).ennreal_toReal,
    (fun _ => ENNReal.toReal_nonneg), ?_, ?_⟩
  · exact integrable_toReal_of_lintegral_ne_top (μ.measurable_rnDeriv ρ).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top μ ρ).ne
  · calc
      μ = ρ.withDensity (μ.rnDeriv ρ) := (Measure.withDensity_rnDeriv_eq μ ρ hac).symm
      _ = ρ.withDensity (fun x => ENNReal.ofReal (μ.rnDeriv ρ x).toReal) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_lt_top μ ρ] with x hx
        exact (ENNReal.ofReal_toReal hx.ne).symm

end
end ConditionedStableLaws.StandingHypothesis
