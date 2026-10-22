import ConditionedStableLaws.Concentration

/-!
# Theorem D — Conditional exponential concentration

For every bounded measurable observable, a positive quadratic deviation rate is uniform in epsilon
and time. Only the prefactor depends on the live initial state.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws

noncomputable section

open StandingHypothesis CanonicalChain NormalizationBridge AnnularPoissonClouds

/-- The explicit rate min{t_h/4, ε²/(16 K_h)} form of Theorem D. -/
alias TheoremD.explicitRate := Concentration.conditional_exponential_concentration

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Theorem D.** Conditional exponential concentration. -/
theorem TheoremD
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) {f : M → ℝ} (hfm : Measurable f) {F : ℝ}
    (hF : ∀ y, |f y| ≤ F) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : d.State, ∃ Cx : ℝ, 0 < Cx ∧
      ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
        (C.conditionedMeasure x.val n).real
          {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - ∫ y, f y ∂μ.withDensity d.weight|} ≤
        Cx * Real.exp (-(a * ε ^ 2 * n)) :=
  Concentration.conditional_exponential_concentration_sq C h d s hlive μ hleft hnorm hfm hF

end

end ConditionedStableLaws
