import ConditionedStableLaws.HypothesisQProcess
import ConditionedStableLaws.Cited.PointwiseErgodic

/-!
# Stationary Q-process ergodicity

Castro, Chemnitz, Chu, Engel, Lamb and Rasmussen, *The conditioned Lyapunov spectrum for random
dynamical systems* (Ann. Inst. Henri Poincaré Probab. Stat.), Proposition 2.6(iii), stated as an
axiom: the stationary law of the Q-process is unique, and `ℚ_ν` is stationary and ergodic.

## Which Doob kernel

The axiom quantifies over the eigen-data produced by H: a continuous finite nonnegative right
eigenfunction positive exactly on `M \ Z`. Under H such an eigenfunction is unique up to a positive
scalar, and the Doob kernel does not depend on that scalar, so this is the Q-process.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.Cited

open StandingHypothesis CanonicalChain

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M}

/-- The stationary trajectory law `ℚ_ν` of the Doob kernel started from `ν`. -/
noncomputable def stationaryQLaw {K : Kernel M M} [IsSFiniteKernel K]
    (d : DoobTransform.EigenData K) (ν : Measure d.State) : Measure (ℕ → d.State) :=
  Kernel.trajMeasure ν (QProcessLimit.historyKernel d.kernel)

/-- **Cited: Castro et al., Proposition 2.6(iii).** Under H, the Q-process has a unique stationary
probability, and the corresponding stationary trajectory law is shift-invariant and ergodic. (This
probability is `ν = η μ`, by invariance of `η μ`.) -/
axiom castro_qProcess_stationary_ergodic {K : KilledKernel M}
    (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel)
    (hcont : Continuous d.weight) (hlive : d.liveSet = survivingSet K.kernel) :
    ∃ ν : Measure d.State, IsProbabilityMeasure ν ∧ d.kernel ∘ₘ ν = ν ∧
      (∀ ν' : Measure d.State, IsProbabilityMeasure ν' → d.kernel ∘ₘ ν' = ν' → ν' = ν) ∧
      Ergodic pathShift (stationaryQLaw d ν)

/-- The live states `M \ Z` through time `n - 1`, i.e. the event `{τ̃ > n - 1}`
for the first exit time `τ̃` from `M \ Z`. For `n = 0` it is the whole space. -/
def liveThrough (K : Kernel M M) (n : ℕ) : Set (Path M) :=
  {ω | ∀ i < n, ∃ y ∈ survivingSet K, ω i = some y}

instance isFiniteKernel_killedTransition (C : CanonicalChain M) :
    IsFiniteKernel C.killedTransition :=
  inferInstanceAs (IsFiniteKernel C.toKilledKernel.kernel)

/-- Birkhoff averages `Γₙ = n⁻¹ ∑_{i<n} h(Xᵢ)` along trajectories of the
Doob chain on `M \ Z`. -/
noncomputable def doobAverage {K : Kernel M M} (d : DoobTransform.EigenData K) (f : M → ℝ)
    (n : ℕ) (ω : ℕ → d.State) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (ω i).val

end ConditionedStableLaws.Cited
