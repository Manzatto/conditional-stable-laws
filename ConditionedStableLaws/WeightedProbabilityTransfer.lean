import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Transfer of small probabilities through uniformly integrable weights

Both the reference laws and the weights may depend on the time index.
Uniform integrability, not a uniform pointwise bound on the weights, is
enough to transfer probabilities tending to zero. Normalization is handled
separately by a positive limit of the total weighted mass.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace ConditionedStableLaws.WeightedProbabilityTransfer

variable {X : Type*} [MeasurableSpace X]

theorem integral_on_event_le_cutoff (q : Measure X) [IsFiniteMeasure q]
    {w : X → ℝ} (hw : Measurable w) (hwi : Integrable w q) (hw0 : ∀ x, 0 ≤ w x)
    (A : Set X) (hA : MeasurableSet A) {B : ℝ} (hB : 0 ≤ B) :
    (∫ x in A, w x ∂q) ≤ B * q.real A + ∫ x in {x | B < w x}, w x ∂q := by
  have htail : MeasurableSet {x | B < w x} := measurableSet_lt measurable_const hw
  have hleft := hwi.indicator hA
  have hright := ((integrable_const B).indicator hA).add (hwi.indicator htail)
  have hbound : A.indicator w ≤ᵐ[q]
      fun x => A.indicator (fun _ => B) x + {x | B < w x}.indicator w x := by
    apply ae_of_all
    intro x
    change A.indicator w x ≤ A.indicator (fun _ => B) x + {x | B < w x}.indicator w x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      by_cases hxt : B < w x
      · rw [indicator_of_mem (show x ∈ {x | B < w x} from hxt)]
        linarith
      · rw [indicator_of_notMem (show x ∉ {x | B < w x} from hxt), add_zero]
        exact le_of_not_gt hxt
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_add]
      exact indicator_nonneg (fun x _ => hw0 x) x
  have hi := integral_mono_ae hleft hright hbound
  change (∫ x, A.indicator w x ∂q) ≤
    ∫ x, A.indicator (fun _ => B) x + {x | B < w x}.indicator w x ∂q at hi
  rw [integral_add ((integrable_const B).indicator hA) (hwi.indicator htail),
    integral_indicator hA, integral_indicator htail, integral_indicator_const B hA] at hi
  simpa only [smul_eq_mul, mul_comm] using hi

/-- A uniformly integrable family of nonnegative densities preserves convergence
of event probabilities to zero, even with varying reference measures. -/
theorem tendsto_weighted_event_mass
    (q : ℕ → Measure X) [∀ n, IsFiniteMeasure (q n)] (w : ℕ → X → ℝ)
    (hw : ∀ n, Measurable (w n)) (hwi : ∀ n, Integrable (w n) (q n))
    (hw0 : ∀ n x, 0 ≤ w n x) (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hprob : Tendsto (fun n => (q n).real (A n)) atTop (𝓝 0))
    (hUI : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      (∫ x in {x | B < w n x}, w n x ∂q n) ≤ ε) :
    Tendsto (fun n => ∫ x in A n, w n x ∂q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨B, hB, htail⟩ := hUI (ε / 2) (half_pos hε)
  have hlim : Tendsto (fun n => B * (q n).real (A n)) atTop (𝓝 0) := by
    simpa using hprob.const_mul B
  have hsmall := (tendsto_order.1 hlim).2 (ε / 2) (half_pos hε)
  filter_upwards [htail, hsmall] with n hn hsn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (hw0 n))]
  have hb := integral_on_event_le_cutoff (q n) (hw n) (hwi n) (hw0 n) (A n) (hA n) hB
  linarith

/-- Normalizing the weighted masses preserves the limit when the total masses
converge to a strictly positive number. -/
theorem tendsto_normalized_weighted_event_mass
    (q : ℕ → Measure X) [∀ n, IsFiniteMeasure (q n)] (w : ℕ → X → ℝ)
    (hw : ∀ n, Measurable (w n)) (hwi : ∀ n, Integrable (w n) (q n))
    (hw0 : ∀ n x, 0 ≤ w n x) (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hprob : Tendsto (fun n => (q n).real (A n)) atTop (𝓝 0))
    (hUI : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      (∫ x in {x | B < w n x}, w n x ∂q n) ≤ ε)
    {m : ℝ} (hm : 0 < m) (hmass : Tendsto (fun n => ∫ x, w n x ∂q n) atTop (𝓝 m)) :
    Tendsto (fun n => (∫ x in A n, w n x ∂q n) / (∫ x, w n x ∂q n))
      atTop (𝓝 0) := by
  have ht := (tendsto_weighted_event_mass q w hw hwi hw0 A hA hprob hUI).div
    hmass (ne_of_gt hm)
  rw [zero_div] at ht
  convert ht using 1

end ConditionedStableLaws.WeightedProbabilityTransfer
