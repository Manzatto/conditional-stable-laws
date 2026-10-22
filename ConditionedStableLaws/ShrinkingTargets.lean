import ConditionedStableLaws.Birkhoff
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Shrinking targets

The definition and elementary consequences used in the conditional Poisson proof. Each target is
measurable and contains its center; the targets need not be nested or themselves contain an open
neighborhood. The asymptotic intensity hypothesis `n * ν.real (U n) → t` gives vanishing target mass
and a null center. No positivity of `t` is needed for these conclusions.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ConditionedStableLaws

noncomputable section

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-- Measurable sets containing the center and eventually lying in each of its neighborhoods. -/
structure ShrinkingNeighborhoods (U : ℕ → Set M) (x₁ : M) : Prop where
  center_mem : ∀ n, x₁ ∈ U n
  measurableSet : ∀ n, MeasurableSet (U n)
  eventually_subset : ∀ V ∈ 𝓝 x₁, ∀ᶠ n in atTop, U n ⊆ V

namespace ShrinkingNeighborhoods

variable {U : ℕ → Set M} {x₁ : M} (hU : ShrinkingNeighborhoods U x₁)

include hU

/-- A fixed point other than the center eventually lies outside every target. -/
theorem eventually_not_mem [T1Space M] {x : M} (hx : x ≠ x₁) :
    ∀ᶠ n in atTop, x ∉ U n := by
  filter_upwards [hU.eventually_subset {x}ᶜ (compl_singleton_mem_nhds hx.symm)] with n hn
  intro hxn
  exact hn hxn rfl

/-- Positivity of a continuous function at the center eventually holds on the whole target. This
applies to the eigenfunction η. -/
theorem eventually_subset_positive {η : M → ℝ} (hη : Continuous η) (hηx : 0 < η x₁) :
    ∀ᶠ n in atTop, U n ⊆ {y | 0 < η y} :=
  hU.eventually_subset _ ((isOpen_lt continuous_const hη).mem_nhds hηx)

/-- A continuous positive eigenfunction is bounded away from zero on all
sufficiently late targets. This is the comparison used for μ(Uₙ) and ν(Uₙ). -/
theorem eventually_lower_bound {η : M → ℝ} (hη : Continuous η) (hηx : 0 < η x₁) :
    ∀ᶠ n in atTop, ∀ y ∈ U n, η x₁ / 2 < η y := by
  have hx : η x₁ / 2 < η x₁ := half_lt_self hηx
  exact hU.eventually_subset _ ((isOpen_lt continuous_const hη).mem_nhds hx)

/-- The deterministic initial contribution to a visit count eventually vanishes
when the initial state differs from the target center. -/
theorem eventually_initial_indicator_zero [T1Space M] {x : M} (hx : x ≠ x₁) :
    ∀ᶠ n in atTop, (U n).indicator (fun _ : M => (1 : ℕ)) x = 0 := by
  filter_upwards [hU.eventually_not_mem hx] with n hn
  exact Set.indicator_of_notMem hn _

/-- Starting at the center always contributes exactly one visit at time zero. -/
theorem initial_indicator_center (n : ℕ) :
    (U n).indicator (fun _ : M => (1 : ℕ)) x₁ = 1 :=
  Set.indicator_of_mem (hU.center_mem n) _

end ShrinkingNeighborhoods

omit [TopologicalSpace M] [MeasurableSpace M] in
/-- A finite limit of `n * a n` forces `a n` to tend to zero. -/
theorem tendsto_zero_of_nat_mul_tendsto {a : ℕ → ℝ} {t : ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 t)) :
    Tendsto a atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod := ha.mul hinv
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

omit [TopologicalSpace M] in
/-- The intensity scaling used in the Poisson theorem implies vanishing real
target masses. -/
theorem target_measureReal_tendsto_zero (ν : Measure M) {U : ℕ → Set M} {t : ℝ}
    (hscale : Tendsto (fun n : ℕ => (n : ℝ) * ν.real (U n)) atTop (𝓝 t)) :
    Tendsto (fun n => ν.real (U n)) atTop (𝓝 0) :=
  tendsto_zero_of_nat_mul_tendsto hscale

omit [TopologicalSpace M] in
/-- For a finite measure the same conclusion holds for ENNReal masses. -/
theorem target_measure_tendsto_zero (ν : Measure M) [IsFiniteMeasure ν]
    {U : ℕ → Set M} {t : ℝ}
    (hscale : Tendsto (fun n : ℕ => (n : ℝ) * ν.real (U n)) atTop (𝓝 t)) :
    Tendsto (fun n => ν (U n)) atTop (𝓝 0) := by
  have hreal := ENNReal.tendsto_ofReal (target_measureReal_tendsto_zero ν hscale)
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_zero] using hreal

namespace ShrinkingNeighborhoods

variable {U : ℕ → Set M} {x₁ : M} (hU : ShrinkingNeighborhoods U x₁)

include hU

/-- A target center included in every target is nonatomic whenever the target
intensity has a finite limit. -/
theorem measure_singleton_eq_zero (ν : Measure M) [IsFiniteMeasure ν] {t : ℝ}
    (hscale : Tendsto (fun n : ℕ => (n : ℝ) * ν.real (U n)) atTop (𝓝 t)) :
    ν {x₁} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto (target_measureReal_tendsto_zero ν hscale)
  exact Filter.Eventually.of_forall fun n =>
    measureReal_mono (singleton_subset_iff.mpr (hU.center_mem n))

end ShrinkingNeighborhoods

end

end ConditionedStableLaws
