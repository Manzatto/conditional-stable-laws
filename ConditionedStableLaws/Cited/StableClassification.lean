import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stable laws

`IsStableLaw α μ` is the classical definition (Feller; Sato, Def. 13.1, with the index `α`): for
every `n ≥ 1` the sum of `n` independent copies has the law of `n^{1/α} X + dₙ`, expressed through
characteristic functions.
-/

open MeasureTheory Complex Set
open scoped Real

namespace ConditionedStableLaws.Cited

/-- A probability law on `ℝ` is stable with index `α`: `φ(t)ⁿ = φ(n^{1/α} t) e^{i dₙ t}`. -/
def IsStableLaw (α : ℝ) (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ d : ℝ, ∀ t : ℝ,
    charFun μ t ^ n = charFun μ (((n : ℝ) ^ (1 / α)) * t) * exp (I * (d * t))

/-- The Lévy–Khintchine exponent with Lévy measure `α y^{-α-1} dy` on `(0,∞)`
and truncation at one. -/
noncomputable def powerLevyExponent (α t : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ),
    (exp (I * (t * y)) - 1 - I * (t * y) * (Icc (0 : ℝ) 1).indicator 1 y) *
      ((α * y ^ (-α - 1) : ℝ) : ℂ)

end ConditionedStableLaws.Cited
