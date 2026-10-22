import ConditionedStableLaws.StandingHypothesis
import ConditionedStableLaws.SmallTargets

/-!
# Uniformly small targets for the killed transition kernel

Reference-measure-small sets have uniformly small one-step transition probabilities under (H1), by
the compact L¹ family argument and the density equation.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ConditionedStableLaws

/-- The first small-target assertion needs only (H1): a continuous compact family of nonnegative L¹
transition densities. Irreducibility, aperiodicity, spectral data and probability normalization are
not needed. -/
theorem uniform_small_targets_of_kernel_density
    {M Y : Type*} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [MeasurableSpace Y]
    (ρ : Measure Y) (K : Kernel M Y) (κ : M → Lp ℝ 1 ρ)
    (hκ : Continuous κ) (hκnonneg : ∀ x, ∀ᵐ y ∂ρ, 0 ≤ κ x y)
    (hK : ∀ x (A : Set Y), MeasurableSet A →
      K x A = ENNReal.ofReal (∫ y in A, κ x y ∂ρ))
    (U : ℕ → Set Y) (hUmeas : ∀ n, MeasurableSet (U n))
    (hU : Tendsto (fun n => ρ (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x : M, (K x (U n)).toReal < ε := by
  intro ε hε
  filter_upwards [uniform_small_targets_of_continuous_L1 κ hκ U hU ε hε]
    with n hn x
  rw [hK x (U n) (hUmeas n),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae (hκnonneg x)))]
  exact (le_abs_self _).trans_lt (hn x)

namespace StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
variable {ρ : Measure M} {K : KilledKernel M}

/-- Uniformly small one-step transitions to reference-small sets, in epsilon/eventually form, for
the killed kernel. -/
theorem HypothesisH.uniform_small_targets (h : HypothesisH ρ K)
    (U : ℕ → Set M) (hUmeas : ∀ n, MeasurableSet (U n))
    (hU : Tendsto (fun n => ρ (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x : M, (K.kernel x (U n)).toReal < ε := by
  exact uniform_small_targets_of_kernel_density ρ K.kernel h.density
    h.continuous_density h.density_nonneg h.kernel_eq_integral U hUmeas hU

end StandingHypothesis

end ConditionedStableLaws
