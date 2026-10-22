import ConditionedStableLaws.RefinedLLNMain

/-!
# Theorem F — Refined conditional laws of large numbers

Part (i) is conditional L1 convergence for every live initial state and bounded observable. Part
(ii) is conditional L1 convergence for L1(mu) observables. Part (iii) is conditional probability
convergence for L1(nu) observables. The unbounded parts vanish on Z and hold for nu-almost every
initial state.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws

noncomputable section

open StandingHypothesis CanonicalChain NormalizationBridge AnnularPoissonClouds

/-- Part (i): bounded observables, every live initial state. -/
alias TheoremF.part_i := RefinedLLN.lln_bounded

/-- Part (ii): L1(mu) observables, nu-almost every initial state. -/
alias TheoremF.part_ii := RefinedLLN.lln_L1

/-- Part (iii): L1(nu) observables, nu-almost every initial state. -/
alias TheoremF.part_iii := RefinedLLN.lln_probability

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Theorem F.** The three refined conditional laws of large numbers. -/
theorem TheoremF
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1) :
    (∀ (f : M → ℝ), Measurable f → ∀ B : ℝ, (∀ y, |f y| ≤ B) → ∀ x : d.State,
      Tendsto (fun n : ℕ => ∫ ω, |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω -
        ∫ y, f y ∂μ.withDensity d.weight| ∂C.conditionedMeasure x.val n) atTop (𝓝 0)) ∧
    (∀ (f : M → ℝ), Measurable f →
      (∀ z ∈ escapingSet C.killedTransition, f z = 0) → Integrable f μ →
      ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M),
        Tendsto (fun n : ℕ => ∫ ω, |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω -
          ∫ y, f y ∂μ.withDensity d.weight| ∂C.conditionedMeasure x.val n) atTop (𝓝 0)) ∧
    (∀ (f : M → ℝ), Measurable f →
      (∀ z ∈ escapingSet C.killedTransition, f z = 0) →
      Integrable f (μ.withDensity d.weight) →
      ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M), ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => C.conditionedMeasure x.val n
          {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - ∫ y, f y ∂μ.withDensity d.weight|})
          atTop (𝓝 0)) := by
  exact ⟨
    (fun f hf B hB x => TheoremF.part_i C h d s hlive μ hleft hnorm hf hB x),
    (fun f hf hZ hfi => TheoremF.part_ii C h d s hlive μ hleft hnorm hf hZ hfi),
    (fun f hf hZ hfi => TheoremF.part_iii C h d s hlive μ hleft hnorm hf hZ hfi)⟩

end

end ConditionedStableLaws
