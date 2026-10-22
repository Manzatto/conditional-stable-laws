import ConditionedStableLaws.Cited.QProcess
import ConditionedStableLaws.NormalizedEigenData

/-!
# Ergodicity of the Q-process

The quasi-ergodic measure `ν = η μ` is the unique stationary probability of the Q-process, and `ℚ_ν`
is stationary and ergodic. Uniqueness and ergodicity come from the cited result of Castro et al.;
the identification of the stationary law with `η μ` follows from the left-eigenmeasure relation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ConditionedStableLaws.StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- The weighted measure `ν = η μ` on the live states. -/
noncomputable abbrev quasiErgodicLaw (d : DoobTransform.EigenData K.kernel) (μ : Measure M) :
    Measure d.State :=
  (μ.withDensity d.weight).comap (Subtype.val : d.State → M)

/-- For normalized eigen-data, `η μ` is the unique stationary probability of the Doob kernel and
`ℚ_{ημ}` is ergodic. -/
theorem HypothesisH.qProcess_stationary_ergodic (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hcont : Continuous d.weight)
    (hlive : d.liveSet = survivingSet K.kernel) (μ : Measure M)
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    IsProbabilityMeasure (quasiErgodicLaw d μ) ∧
      d.kernel ∘ₘ quasiErgodicLaw d μ = quasiErgodicLaw d μ ∧
      (∀ ν' : Measure d.State, IsProbabilityMeasure ν' → d.kernel ∘ₘ ν' = ν' →
        ν' = quasiErgodicLaw d μ) ∧
      Ergodic Cited.pathShift (Cited.stationaryQLaw d (quasiErgodicLaw d μ)) := by
  obtain ⟨ν, _, _, huniq, herg⟩ := Cited.castro_qProcess_stationary_ergodic h d hcont hlive
  have hprob := d.isProbabilityMeasure_weightedMeasure μ hnorm
  have hinv := d.invariant_weightedMeasure μ hleft
  have hν : quasiErgodicLaw d μ = ν := huniq _ hprob hinv
  refine ⟨hprob, hinv, fun ν' hp' hinv' => (huniq ν' hp' hinv').trans hν.symm, ?_⟩
  rw [hν]
  exact herg

/-- Under H, normalized eigen-data exist, and their quasi-ergodic law is the unique stationary
probability, with ergodic `ℚ_ν`. -/
theorem HypothesisH.exists_qProcess_stationary_ergodic (h : HypothesisH ρ K) :
    ∃ d : DoobTransform.EigenData K.kernel, Continuous d.weight ∧
      d.liveSet = survivingSet K.kernel ∧ ∃ μ : ProbabilityMeasure M,
      K.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) ∧
      (∫⁻ x, d.weight x ∂(μ : Measure M)) = 1 ∧
      IsProbabilityMeasure (quasiErgodicLaw d μ) ∧
      d.kernel ∘ₘ quasiErgodicLaw d μ = quasiErgodicLaw d μ ∧
      (∀ ν' : Measure d.State, IsProbabilityMeasure ν' → d.kernel ∘ₘ ν' = ν' →
        ν' = quasiErgodicLaw d μ) ∧
      Ergodic Cited.pathShift (Cited.stationaryQLaw d (quasiErgodicLaw d μ)) := by
  obtain ⟨d, _, hc, hlive, μ, hleft, hnorm⟩ := h.exists_normalized_eigenData
  exact ⟨d, hc, hlive, μ, hleft, hnorm,
    h.qProcess_stationary_ergodic d hc hlive μ hleft hnorm⟩

end ConditionedStableLaws.StandingHypothesis
