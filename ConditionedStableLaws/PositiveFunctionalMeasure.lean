import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Tactic

/-!
Normalized positive functionals on bounded continuous functions give probability measures on a
compact metric space.
-/

open MeasureTheory Set
open scoped Topology BoundedContinuousFunction CompactlySupported

namespace ConditionedStableLaws.PositiveFunctionalMeasure
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]

def restrictPositive (L : (M →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f) : C_c(M, ℝ) →ₚ[ℝ] ℝ where
  toFun f := L f.toBoundedContinuousFunction
  map_add' f g := by
    change L (f.toBoundedContinuousFunction + g.toBoundedContinuousFunction) = _
    exact map_add L _ _
  map_smul' c f := by
    change L (c • f.toBoundedContinuousFunction) = _
    exact map_smul L c _
  monotone' f g hfg := by
    have hp := hL (g.toBoundedContinuousFunction-f.toBoundedContinuousFunction)
      (fun x => sub_nonneg.mpr (hfg x))
    simpa only [map_sub, sub_nonneg] using hp

def measure (L : (M →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f) : Measure M :=
  RealRMK.rieszMeasure (restrictPositive L hL)

instance measure_isFinite (L : (M →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f) : IsFiniteMeasure (measure L hL) := by
  unfold measure
  infer_instance

theorem integral_measure (L : (M →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f) (f : M →ᵇ ℝ) :
    ∫ x, f x ∂measure L hL = L f := by
  let g : C_c(M, ℝ) := ⟨f.toContinuousMap, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (restrictPositive L hL) g

theorem measure_isProbability (L : (M →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f) (hone : L 1 = 1) :
    IsProbabilityMeasure (measure L hL) := by
  constructor
  have hm := integral_measure L hL 1
  have hmreal : ((measure L hL) univ).toReal = 1 := by simpa only
    [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const, smul_eq_mul,
      mul_one, measureReal_def, hone] using hm
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
    (by simpa only [ENNReal.toReal_one] using hmreal)

def probabilityMeasure (L : (M →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f) (hone : L 1 = 1) :
    ProbabilityMeasure M := ⟨measure L hL, measure_isProbability L hL hone⟩

theorem integral_probabilityMeasure (L : (M →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f) (hone : L 1 = 1)
    (f : M →ᵇ ℝ) :
    ∫ x, f x ∂(probabilityMeasure L hL hone : Measure M) = L f := integral_measure L hL f

end
end ConditionedStableLaws.PositiveFunctionalMeasure
