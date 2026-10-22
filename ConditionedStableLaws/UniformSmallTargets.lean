import ConditionedStableLaws.EigenfunctionSupport
import ConditionedStableLaws.NormalizedEigenData
import ConditionedStableLaws.KernelSmallTargets

/-!
# Uniformly small targets from Hypothesis H

Both assertions, with the quasi-stationary data `(λ, η, μ)` given by H. `survivingSet K` is `M \ Z`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.StandingHypothesis

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- **Uniformly small targets.** Under H: (1) `ρ(Uₙ) → 0` implies `sup_z 𝒫(z, Uₙ) → 0`; (2) for the
normalized quasi-stationary data `(λ, η, μ)` given by H, `ν(Uₙ) → 0` with `Uₙ ⊆ M \ Z` eventually
implies `sup_z 𝒫(z, Uₙ) → 0`. -/
theorem HypothesisH.uniform_small_targets_lemma (h : HypothesisH ρ K) :
    (∀ U : ℕ → Set M, (∀ n, MeasurableSet (U n)) → Tendsto (fun n => ρ (U n)) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x : M, (K.kernel x (U n)).toReal < ε) ∧
    ∃ (d : DoobTransform.EigenData K.kernel) (μ : ProbabilityMeasure M),
      Continuous d.weight ∧ d.liveSet = survivingSet K.kernel ∧
      K.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) ∧
      (∫⁻ x, d.weight x ∂(μ : Measure M)) = 1 ∧
      ∀ U : ℕ → Set M, (∀ n, MeasurableSet (U n)) →
        (∀ᶠ n in atTop, U n ⊆ survivingSet K.kernel) →
        Tendsto (fun n => (μ : Measure M).withDensity d.weight (U n)) atTop (𝓝 0) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x : M, (K.kernel x (U n)).toReal < ε := by
  refine ⟨fun U hU hρ => h.uniform_small_targets U hU hρ, ?_⟩
  obtain ⟨d, -, hc, hlive, μ, hleft, hnorm⟩ := h.exists_normalized_eigenData
  exact ⟨d, μ, hc, hlive, hleft, hnorm, fun U hU hUS hν =>
    h.uniform_small_targets_of_eigenData d hc μ hleft hnorm U hU hUS hν⟩

end ConditionedStableLaws.StandingHypothesis
