import ConditionedStableLaws.PointMeasures
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Poisson random measures

The definition uses point measures, the Poisson distribution and independence of the evaluation
random variables on disjoint sets. Counts are ENNReal-valued. Their Poisson law forces finite,
integer-valued counts almost surely on sets of finite intensity.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal

namespace ConditionedStableLaws

noncomputable section

/-- A Poisson law regarded as a law of measure evaluations in ENNReal. -/
def poissonCountLaw (r : ℝ≥0∞) : Measure ℝ≥0∞ :=
  (poissonMeasure r.toNNReal).map (fun k : ℕ => (k : ℝ≥0∞))

theorem poissonCountLaw_singleton (r : ℝ≥0∞) (k : ℕ) :
    poissonCountLaw r {(k : ℝ≥0∞)} =
      ENNReal.ofReal (Real.exp (-(r.toNNReal : ℝ)) * (r.toNNReal : ℝ) ^ k / k.factorial) := by
  have hm : Measurable (fun j : ℕ => (j : ℝ≥0∞)) := by fun_prop
  rw [poissonCountLaw, Measure.map_apply hm (measurableSet_singleton _)]
  have hpre : (fun j : ℕ => (j : ℝ≥0∞)) ⁻¹' {(k : ℝ≥0∞)} = {k} := by
    ext j
    simp
  rw [hpre, poissonMeasure_singleton]

@[simp]
theorem poissonCountLaw_infinity (r : ℝ≥0∞) : poissonCountLaw r {∞} = 0 := by
  have hm : Measurable (fun j : ℕ => (j : ℝ≥0∞)) := by fun_prop
  rw [poissonCountLaw, Measure.map_apply hm (measurableSet_singleton _)]
  have hpre : (fun j : ℕ => (j : ℝ≥0∞)) ⁻¹' {∞} = ∅ := by
    ext j
    simp
  rw [hpre, measure_empty]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Poisson random measure with locally finite intensity, relative to a given
probability law on its sample space. -/
structure IsPoissonRandomMeasure (N : RandomPointMeasure Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] (υ : Measure ExtremeState) : Prop where
  intensity_locally_finite : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞
  count_law : ∀ A : Set ExtremeState, MeasurableSet A → υ A ≠ ∞ →
    HasLaw (fun ω => (N.toFun ω).toMeasure A) (poissonCountLaw (υ A)) P
  independent_counts : ∀ (n : ℕ) (A : Fin n → Set ExtremeState),
    (∀ j, MeasurableSet (A j)) → Pairwise (fun i j => Disjoint (A i) (A j)) →
    (∀ j, υ (A j) ≠ ∞) →
    iIndepFun (fun j ω => (N.toFun ω).toMeasure (A j)) P

namespace IsPoissonRandomMeasure

variable {N : RandomPointMeasure Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {υ : Measure ExtremeState} (hN : IsPoissonRandomMeasure N P υ)

include hN

/-- The explicit Poisson count probabilities. -/
theorem count_probability (A : Set ExtremeState) (hA : MeasurableSet A) (hυ : υ A ≠ ∞)
    (k : ℕ) :
    P {ω | (N.toFun ω).toMeasure A = (k : ℝ≥0∞)} =
      ENNReal.ofReal
        (Real.exp (-((υ A).toNNReal : ℝ)) * ((υ A).toNNReal : ℝ) ^ k / k.factorial) := by
  have h := (hN.count_law A hA hυ).measure_eq
    (p := fun y : ℝ≥0∞ => y = (k : ℝ≥0∞)) (measurableSet_singleton _)
  exact h.trans (poissonCountLaw_singleton (υ A) k)

/-- Finite-intensity sets have finite counts almost surely. -/
theorem count_ne_top_ae (A : Set ExtremeState) (hA : MeasurableSet A) (hυ : υ A ≠ ∞) :
    ∀ᵐ ω ∂P, (N.toFun ω).toMeasure A ≠ ∞ := by
  rw [ae_iff]
  simp only [not_not]
  have h := (hN.count_law A hA hυ).measure_eq
    (p := fun y : ℝ≥0∞ => y = ∞) (measurableSet_singleton _)
  exact h.trans (poissonCountLaw_infinity (υ A))

end IsPoissonRandomMeasure

end

end ConditionedStableLaws
