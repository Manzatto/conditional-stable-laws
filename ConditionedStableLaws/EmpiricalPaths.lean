import ConditionedStableLaws.PointMeasures
import ConditionedStableLaws.PathSurvival
import ConditionedStableLaws.Tails

/-!
# Empirical point measures on canonical killed paths

The normalized empirical point measure is a measurable random point measure on the path space. A
positive cemetery extension defines it on every path and agrees with the observable on the survival
event.
-/

open MeasureTheory ProbabilityTheory Set
open Classical
open scoped ENNReal

namespace ConditionedStableLaws

noncomputable section

variable {M : Type*} [MeasurableSpace M]

/-- A positive extension used only to define empirical points off survival. -/
def positiveExtension (f : M → ℝ) : Option M → ℝ
  | none => 1
  | some x => f x

theorem measurable_positiveExtension {f : M → ℝ} (hf : Measurable f) :
    Measurable (positiveExtension f) := by
  intro A hA
  change MeasurableSet (Option.some ⁻¹' (positiveExtension f ⁻¹' A))
  exact hf hA

omit [MeasurableSpace M] in
theorem positiveExtension_pos {f : M → ℝ} (hf : ∀ x, 0 < f x) (z : Option M) :
    0 < positiveExtension f z := by
  cases z with
  | none => norm_num [positiveExtension]
  | some x => exact hf x

omit [MeasurableSpace M] in
theorem positiveExtension_eq_zeroExtension {f : M → ℝ} {z : Option M}
    (hz : z ≠ none) : positiveExtension f z = zeroExtension f z := by
  cases z with
  | none => exact (hz rfl).elim
  | some x => rfl

/-- The random point measure of observations at times `0,...,n-1`. -/
def pathEmpirical (f : M → ℝ) (hm : Measurable f) (hf : ∀ x, 0 < f x)
    (n : ℕ) (B : ℝ) (hB : 0 < B) : RandomPointMeasure (CanonicalChain.Path M) :=
  RandomPointMeasure.normalizedEmpirical
    (fun i : Fin n => fun ω => positiveExtension f (ω i))
    (fun i => (measurable_positiveExtension hm).comp (measurable_pi_apply i.val))
    (fun i ω => positiveExtension_pos hf (ω i)) B hB

/-- Empirical counts are the cardinality of the normalized observations falling in the target, as an
equality of ENNReal-valued measures. -/
theorem pathEmpirical_apply (f : M → ℝ) (hm : Measurable f) (hf : ∀ x, 0 < f x)
    (n : ℕ) (B : ℝ) (hB : 0 < B) (ω : CanonicalChain.Path M) (A : Set ExtremeState) :
    ((pathEmpirical f hm hf n B hB).toFun ω).toMeasure A =
      ∑ i : Fin n, if
        (⟨ENNReal.ofReal (positiveExtension f (ω i) / B),
          ENNReal.ofReal_pos.mpr (div_pos (positiveExtension_pos hf _) hB)⟩ : ExtremeState) ∈ A
        then (1 : ℝ≥0∞) else 0 :=
  RandomPointMeasure.normalizedEmpirical_apply _ _ _ B hB ω A

omit [MeasurableSpace M] in
/-- On every surviving path the chosen extension equals the killed observable
at every empirical observation time. -/
theorem positiveExtension_on_survival (f : M → ℝ) (n : ℕ)
    (ω : CanonicalChain.Path M) (hω : ω ∈ CanonicalChain.survival n) (i : Fin n) :
    positiveExtension f (ω i) = zeroExtension f (ω i) :=
  positiveExtension_eq_zeroExtension (hω i (Nat.le_of_lt i.isLt))

/-- The empirical upper-tail count agrees with the normalized killed-path
observable almost surely under the survival-conditioned law. -/
theorem pathEmpirical_tail_count_ae
    (C : CanonicalChain M) (x : M) (f : M → ℝ) (hm : Measurable f)
    (hf : ∀ x, 0 < f x) (n : ℕ) (B : ℝ) (hB : 0 < B) (t : ℝ) :
    ∀ᵐ ω ∂C.conditionedMeasure x n,
      ((pathEmpirical f hm hf n B hB).toFun ω).toMeasure
        {y | ENNReal.ofReal t < y.val} =
      ∑ i : Fin n, if t * B < zeroExtension f (ω i) then (1 : ℝ≥0∞) else 0 := by
  classical
  filter_upwards [C.ae_survival_conditionedMeasure x n] with ω hω
  rw [pathEmpirical_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  apply propext
  change ENNReal.ofReal t < ENNReal.ofReal (positiveExtension f (ω i) / B) ↔ _
  rw [ENNReal.ofReal_lt_ofReal_iff (div_pos (positiveExtension_pos hf _) hB), lt_div_iff₀ hB,
    positiveExtension_on_survival f n ω hω i]

/-- The singular-observable empirical measure, with an explicit scale. -/
def singularPathEmpirical [MetricSpace M] [BorelSpace M]
    (x₀ : M) (β : ℝ) (n : ℕ) (B : ℝ) (hB : 0 < B) :
    RandomPointMeasure (CanonicalChain.Path M) :=
  pathEmpirical (singularObservable x₀ β) (measurable_singularObservable x₀ β)
    (singularObservable_pos x₀ β) n B hB

end
end ConditionedStableLaws
