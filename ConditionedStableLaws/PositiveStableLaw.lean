import ConditionedStableLaws.PositivePoissonIntegral
import ConditionedStableLaws.PoissonLaplace
import ConditionedStableLaws.StableLaplaceExponent

/-!
The positive Poisson integral has the stable Laplace transform `exp(-Γ(1-α) t^α)`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.AnnularPoissonClouds
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

/-- The positive Poisson integral has Laplace transform `exp(-Γ(1-α)t^α)` for every `t≥0`. -/
theorem positiveIntegral_laplace {α : ℝ} (hα : 0 < α) (ha : α < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω : Sample, Real.exp (-t * positiveIntegral ω) ∂powerLaw α hα) =
      Real.exp (-Real.Gamma (1 - α) * t ^ α) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [Real.zero_rpow hα.ne']
  have he (ω : Sample) :
      (∫⁻ y : ExtremeState, ENNReal.ofReal (t * y.val.toReal) ∂(randomMeasure.toFun ω).toMeasure) =
      ENNReal.ofReal t * ∫⁻ y, positiveMark y ∂(randomMeasure.toFun ω).toMeasure := by
    simp_rw [ENNReal.ofReal_mul ht.le]
    exact lintegral_const_mul _ measurable_positiveMark
  have hfinite : ∀ᵐ ω ∂powerLaw α hα,
      (∫⁻ y : ExtremeState, ENNReal.ofReal (t * y.val.toReal) ∂(randomMeasure.toFun ω).toMeasure) < ∞ := by
    filter_upwards [total_positiveMark_finite hα ha] with ω hω
    rw [he]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hω
  have hL := laplace_functional (powerIntensity α) (powerIntensity_tail_lt_top hα)
    (fun y : ExtremeState => t * y.val.toReal) (by fun_prop)
    (fun _ => mul_nonneg ht.le ENNReal.toReal_nonneg)
    (stable_laplace_exponent_integrable hα ha ht) hfinite
  rw [stable_laplace_exponent hα ha ht] at hL
  calc
    _ = ∫ ω : Sample, Real.exp
        (-((∫⁻ y : ExtremeState, ENNReal.ofReal (t * y.val.toReal)
          ∂(randomMeasure.toFun ω).toMeasure).toReal)) ∂powerLaw α hα := by
      apply integral_congr_ae
      filter_upwards [mark_integral_eq_ae hα] with ω hω
      rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
        ← hω, ← neg_mul]
      rfl
    _ = _ := by simpa only [neg_mul, powerLaw] using hL

end
end ConditionedStableLaws.AnnularPoissonClouds
