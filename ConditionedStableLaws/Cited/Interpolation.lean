import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compatibility of Lebesgue-space operator realizations

Compatible bounded operators agree almost everywhere on common representatives.
-/

open MeasureTheory
open scoped ENNReal

namespace ConditionedStableLaws.Cited

variable {R S : Type*} [MeasurableSpace R] [MeasurableSpace S]

/-- Two operators between Lebesgue spaces are compatible when they agree
almost everywhere on every function lying in both of their domains. -/
def LpCompatible {p₀ q₀ p₁ q₁ : ℝ≥0∞} {μ : Measure R} {ν : Measure S}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ q₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₁)]
    (T₀ : Lp ℝ p₀ μ →L[ℝ] Lp ℝ q₀ ν) (T₁ : Lp ℝ p₁ μ →L[ℝ] Lp ℝ q₁ ν) : Prop :=
  ∀ (f₀ : Lp ℝ p₀ μ) (f₁ : Lp ℝ p₁ μ),
    (f₀ : R → ℝ) =ᵐ[μ] f₁ → (T₀ f₀ : S → ℝ) =ᵐ[ν] T₁ f₁

end ConditionedStableLaws.Cited
