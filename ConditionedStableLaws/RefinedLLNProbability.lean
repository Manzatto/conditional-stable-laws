import ConditionedStableLaws.ConditionalTransfer
import ConditionedStableLaws.QProcessIntegrable

/-!
# Theorem F(iii): the L1(nu) conditional probability LLN

Truncation gives the Q-process LLN in mean; the endpoint-weight transfer gives convergence under
survival conditioning. For an arbitrary left eigenmeasure, its weighted invariant probability is
identified with that of the canonical probability eigenmeasure.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.RefinedLLN

noncomputable section

open StandingHypothesis CanonicalChain

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

set_option backward.isDefEq.respectTransparency false in
/-- **Refined conditional LLN (iii).** For measurable `h` vanishing on `Z` with `h ∈ L¹(ν)`, for
`ν`-almost every `x ∈ M \ Z` and every `ε > 0`, `ℙₓ(|Γₙ - ν(h)| > ε | τ > n) → 0`. -/
theorem lln_probability (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {f : M → ℝ} (hf : Measurable f) (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0)
    (hfi : Integrable f (μ.withDensity d.weight)) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M), ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => C.conditionedMeasure x.val n
        {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - ∫ y, f y ∂μ.withDensity d.weight|})
        atTop (𝓝 0) := by
  set ν := (μ.withDensity d.weight).comap (Subtype.val : d.State → M)
  have : IsProbabilityMeasure ν := d.isProbabilityMeasure_weightedMeasure μ hnorm
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure ν
  obtain ⟨μ₀, hleft₀, hnorm₀⟩ := QProcessReference.exists_probability_reference h d s
    ⟨x₀.val, x₀.property⟩
  change C.killedTransition ∘ₘ (μ₀ : Measure M) = d.rate • (μ₀ : Measure M) at hleft₀
  have hν := QProcessReference.invariant_probability_eq h d s.continuous_weight
    (μ₀ : Measure M) hleft₀ hnorm₀ ν (d.invariant_weightedMeasure μ hleft)
  have hw : μ.withDensity d.weight = (μ₀ : Measure M).withDensity d.weight := by
    have hh := congrArg (fun m : Measure d.State => m.map (Subtype.val : d.State → M)) hν
    change ((μ.withDensity d.weight).comap (Subtype.val : d.State → M)).map Subtype.val =
      (((μ₀ : Measure M).withDensity d.weight).comap (Subtype.val : d.State → M)).map Subtype.val at hh
    exact (RefinedLLN.map_comap_withDensity d μ).symm.trans
      (hh.trans (RefinedLLN.map_comap_withDensity d μ₀))
  have hfi₀ : Integrable f ((μ₀ : Measure M).withDensity d.weight) := hw ▸ hfi
  have hQ := QProcessIntegrable.lln_mean h d s.continuous_weight (μ₀ : Measure M)
    hleft₀ hnorm₀ hf hfi₀
  rw [← hw] at hQ
  filter_upwards [hQ] with x hx
  apply ConditionalTransfer.conditional_transfer C h d s hlive x hf hZ
    (∫ y, f y ∂μ.withDensity d.weight)
  intro ε hε
  have hp := BoundedConvergence.tendsto_in_probability_of_integral_abs
    (fun _ => QProcessLimit.pathMeasure d.kernel x)
    (fun n ω => Cited.doobAverage d f n ω - ∫ y, f y ∂μ.withDensity d.weight)
    hx.1 hx.2 ε hε
  exact (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) ENNReal.zero_ne_top).1 hp

end

end ConditionedStableLaws.RefinedLLN
