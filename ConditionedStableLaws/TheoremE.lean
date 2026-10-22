import ConditionedStableLaws.ShrinkingTargetPoisson

/-!
# Theorem E — Conditional Poisson law for shrinking targets

For measurable neighborhoods shrinking to a live target, normalized target mass gives the Poisson
parameter. The starting point is distinct from the target. The parameter may be zero.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws

noncomputable section

open StandingHypothesis CanonicalChain NormalizationBridge AnnularPoissonClouds

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Theorem E.** Conditional Poisson law for shrinking targets. -/
theorem TheoremE
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {x₁ : M} (hx₁ : d.weight x₁ ≠ 0) (hxx₁ : x.val ≠ x₁)
    (U : ℕ → Set M) (hU : ShrinkingNeighborhoods U x₁) (rate : ℝ≥0)
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n))
      atTop (𝓝 (rate : ℝ))) :
    Tendsto (fun n => ProbabilityMeasure.map (C.liveConditionedProbabilityMeasure d x n)
      (fun ω : Path M => (visitTimes (fun i : Fin n => ω i.val) (Option.some '' U n)).card))
      atTop (𝓝 (poissonProbabilityMeasure rate)) :=
  CanonicalChain.conditional_poisson_shrinking_targets C h d hc μ hleft hnorm x hx₁ hxx₁ U hU rate hscale

end

end ConditionedStableLaws
