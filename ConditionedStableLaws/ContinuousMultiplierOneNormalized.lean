import ConditionedStableLaws.ContinuousMultiplierOne
import ConditionedStableLaws.ContinuousMultiplierAbsoluteCenter

/-! Exact absolute-value centering at exponent one for g(x₀)=1. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open CanonicalChain StandingHypothesis NormalizationBridge AnnularPoissonClouds
  SmallJumpMoment MultiplierReflection

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The exact index-one multiplier law with absolute truncation centering.
Normalizing g(x₀) to one is sufficient before the exact scalar-reflection step. -/
theorem stable_law_one_multiplier_normalized (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : dimension / β = 1)
    {g : M → ℝ} (hg : Continuous g) (hg0 : g x₀ = 1) :
    TendstoInDistribution
      (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n)⁻¹ *
        (pathBirkhoffSum (observable x₀ β g) n ω - n * ∫ y,
          absTrunc (observable x₀ β g)
            (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n) y
              ∂μ.withDensity d.weight)) atTop
      (unitCompensatedStable 1 one_pos)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw 1 one_pos) := by
  have : IsProbabilityMeasure (μ.withDensity d.weight) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hC : 0 < volumeConstant * (d.weight x₀).toReal * m x₀ := mul_pos
    (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  rw [hα1] at htail
  have heq : (fun y => singularObservable x₀ β y + residual x₀ β g y) = observable x₀ β g := by
    funext y
    dsimp [residual, observable]
    rw [hg0]
    ring
  have he := absolute_center_residual_tendsto (μ.withDensity d.weight)
    (measurable_singularObservable x₀ β) (measurable_residual x₀ β hg)
    (fun y => (singularObservable_pos x₀ β y).le)
    (fun η hη => residual_bound hβ hg hη) hC htail
  rw [heq] at he
  apply stable_law_one_multiplier_of_center C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ hα1 hg hg0
  exact he.congr (fun n => by ring)

end
end ConditionedStableLaws.ContinuousMultiplier
