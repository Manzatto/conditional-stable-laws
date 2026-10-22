import ConditionedStableLaws.GaussianBoundary
import ConditionedStableLaws.StableIdentification

/-!
# Theorem B — Stable and Gaussian limits

The four regimes of the singular observable: positive stable (i), unit-compensated stable (ii),
fully compensated stable (iii), and the Gaussian boundary (iv).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws

noncomputable section

open StandingHypothesis CanonicalChain NormalizationBridge AnnularPoissonClouds

/-- Part (i): 0 < α < 1, without centering. -/
alias TheoremB.part_i := StableLawSmall.stable_law_small

/-- Part (ii): α = 1, with truncated-mean centering. -/
alias TheoremB.part_ii := StableLawCompensated.stable_law_one

/-- Part (iii): 1 < α < 2, with full-mean centering. -/
alias TheoremB.part_iii := StableLawCompensated.stable_law_mid

/-- Part (iv): α = 2, with √(C n log n) normalization. -/
alias TheoremB.part_iv := GaussianBoundary.stable_law_boundary

/-- The Laplace transform of the positive stable limit. -/
alias TheoremB.laplace_i := AnnularPoissonClouds.positiveIntegral_laplace

/-- The characteristic function of the unit-compensated stable limit. -/
alias TheoremB.characteristic_ii := AnnularPoissonClouds.unitCompensatedStable_characteristic_real

/-- The characteristic function of the fully compensated stable limit. -/
alias TheoremB.characteristic_iii := AnnularPoissonClouds.fullyCompensatedStable_characteristic_real

/-- Stability of the limit in part (i). -/
alias TheoremB.stable_i := StableIdentification.positiveIntegral_isStable

/-- Stability of the limit in part (ii). -/
alias TheoremB.stable_ii := StableIdentification.unitCompensatedStable_isStable

/-- Stability of the limit in part (iii). -/
alias TheoremB.stable_iii := StableIdentification.fullyCompensatedStable_isStable

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Theorem B.** All four conditional limit regimes under the common standing assumptions and
local admissibility. -/
theorem TheoremB
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) :
    (dimension / β < 1 →
      TendstoInDistribution
        (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
          (dimension / β) n)⁻¹ * pathBirkhoffSum (singularObservable x₀ β) n ω) atTop
        positiveIntegral
        (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
        (powerLaw (dimension / β) (div_pos hadm.1.1 hβ))) ∧
    (dimension / β = 1 →
      TendstoInDistribution
        (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n)⁻¹ *
          (pathBirkhoffSum (singularObservable x₀ β) n ω - n * ∫ y,
            {y | singularObservable x₀ β y ≤
              positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n}.indicator
              (singularObservable x₀ β) y ∂μ.withDensity d.weight)) atTop
        (unitCompensatedStable 1 one_pos)
        (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
        (powerLaw 1 one_pos)) ∧
    (∀ hα1 : 1 < dimension / β, dimension / β < 2 →
      Integrable (singularObservable x₀ β) (μ.withDensity d.weight) ∧
      TendstoInDistribution
        (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
            (dimension / β) n)⁻¹ *
          (pathBirkhoffSum (singularObservable x₀ β) n ω -
            n * ∫ y, singularObservable x₀ β y ∂μ.withDensity d.weight)) atTop
        (fullyCompensatedStable (dimension / β) (zero_lt_one.trans hα1))
        (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
        (powerLaw (dimension / β) (zero_lt_one.trans hα1))) ∧
    (dimension / β = 2 →
      Integrable (singularObservable x₀ β) (μ.withDensity d.weight) ∧
      TendstoInDistribution
        (fun n ω => (GaussianBoundary.bScale (volumeConstant * (d.weight x₀).toReal * m x₀) n)⁻¹ *
          (pathBirkhoffSum (singularObservable x₀ β) n ω -
            n * ∫ y, singularObservable x₀ β y ∂μ.withDensity d.weight)) atTop id
        (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
        (gaussianReal 0 1)) := by
  exact ⟨
    (fun hα1 => TheoremB.part_i C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ hα1),
    (fun hα1 => TheoremB.part_ii C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ hα1),
    (fun hα1 hα2 => TheoremB.part_iii C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ hα1 hα2),
    (fun hα2 => TheoremB.part_iv C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ hα2)⟩

end

end ConditionedStableLaws
