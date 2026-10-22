import ConditionedStableLaws.ChainPoissonProcess

/-!
# Theorem A — Poisson point-process limit

The normalized empirical point measures converge vaguely in distribution to the power-intensity
Poisson random measure. All finite disjoint interval count vectors converge jointly. The limiting
measure has Poisson counts and independent counts on disjoint measurable sets.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws

noncomputable section

open StandingHypothesis CanonicalChain NormalizationBridge AnnularPoissonClouds

/-- The vague point-process conclusion of Theorem A. -/
alias TheoremA.pointProcess := CanonicalChain.poisson_point_process_of_admissibility

/-- The joint interval-count conclusion of Theorem A. -/
alias TheoremA.intervalCounts := CanonicalChain.poisson_interval_counts_of_admissibility

/-- The Poisson characterization of the limiting random measure. -/
alias TheoremA.poissonLaw := power_poisson_limit_isPoissonRandomMeasure

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Theorem A.** Point-process convergence, joint interval-count convergence,
and the Poisson law of the limit, under H and local admissibility. -/
theorem TheoremA
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) :
    (TendstoInDistribution (fun n => (pathEmpirical (singularObservable x₀ β)
      (measurable_singularObservable x₀ β) (singularObservable_pos x₀ β) n
      (positivePowerScale (volumeConstant*(d.weight x₀).toReal*m x₀) (dimension/β) n)
      (positivePowerScale_pos (mul_pos (mul_pos hadm.1.2.1
        (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1) n)).toFun) atTop
      AnnularPoissonClouds.randomMeasure.toFun
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (AnnularPoissonClouds.law (powerIntensity (dimension/β))
        (powerIntensity_tail_lt_top (div_pos hadm.1.1 hβ)))) ∧
    (∀ (k : ℕ) (a b : Fin k → ExtremeState),
      (∀ j, a j < b j) →
      Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      TendstoInDistribution (fun n ω j => ((pathEmpirical (singularObservable x₀ β)
        (measurable_singularObservable x₀ β) (singularObservable_pos x₀ β) n
        (positivePowerScale (volumeConstant*(d.weight x₀).toReal*m x₀) (dimension/β) n)
        (positivePowerScale_pos (mul_pos (mul_pos hadm.1.2.1
          (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1) n)).toFun ω).countOn
          (Ioc (a j) (b j))) atTop
        (fun ω j => (AnnularPoissonClouds.randomMeasure.toFun ω).countOn (Ioc (a j) (b j)))
        (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
        (AnnularPoissonClouds.law (powerIntensity (dimension/β))
          (powerIntensity_tail_lt_top (div_pos hadm.1.1 hβ)))) ∧
    IsPoissonRandomMeasure randomMeasure
      (law (powerIntensity (dimension / β)) (powerIntensity_tail_lt_top (div_pos hadm.1.1 hβ)))
      (powerIntensity (dimension / β)) := by
  refine ⟨TheoremA.pointProcess C h d hc μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ, ?_,
    TheoremA.poissonLaw (div_pos hadm.1.1 hβ)⟩
  intro k a b hab hdis
  exact TheoremA.intervalCounts C h d hc μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ
    k a b hab hdis

end

end ConditionedStableLaws
