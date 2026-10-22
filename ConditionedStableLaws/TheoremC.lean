import ConditionedStableLaws.L2CLT

/-!
# Theorem C — Conditional central limit theorem

For finite-valued measurable observables in L2(mu), the covariance series converges absolutely, the
asymptotic variance is nonnegative, and the centered sums satisfy the survival-conditioned Gaussian
limit.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws

noncomputable section

open StandingHypothesis CanonicalChain NormalizationBridge AnnularPoissonClouds

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Theorem C.** Conditional central limit theorem. -/
theorem TheoremC
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 μ) (x : d.State) :
    Summable (fun m => |ConditionalCLT.correlation C μ d g m|) ∧
      0 ≤ ConditionalCLT.asymptoticVariance C μ d g ∧
      TendstoInDistribution
        (fun (n : ℕ) omega => (Real.sqrt (n : ℝ))⁻¹ *
          pathBirkhoffSum (ConditionalCLT.centered C μ d g) n omega)
        atTop id (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
        (gaussianReal 0 (ConditionalCLT.asymptoticVariance C μ d g).toNNReal) :=
  L2Variance.conditional_clt_l2 C h d s hlive μ hleft hnorm hgm hg2 x

end

end ConditionedStableLaws
