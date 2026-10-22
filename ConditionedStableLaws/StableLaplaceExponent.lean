import ConditionedStableLaws.PowerIntensityMoments
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Evaluation of the positive stable Laplace exponent by layer cake. -/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem powerIntensity_realTail {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    powerIntensity α {y : ExtremeState | s < y.val.toReal} = ENNReal.ofReal (s ^ (-α)) := by
  have hzero : ∀ᵐ y ∂powerIntensity α, y.val ≠ ∞ := by
    rw [ae_iff]
    simpa only [not_not] using powerIntensity_infinity α
  rw [← powerIntensity_Ioi hα hs]
  apply measure_congr
  filter_upwards [hzero] with y hy
  rw [← ENNReal.ofReal_toReal hy, ENNReal.ofReal_lt_ofReal_iff
    (ENNReal.toReal_pos y.property.ne' hy)]
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

private theorem exponential_primitive {t : ℝ} (ht : 0 < t) (b : ℝ) :
    (∫ s in 0..b, t * Real.exp (-(t * s))) = 1 - Real.exp (-(t * b)) := by
  rw [intervalIntegral.integral_const_mul]
  have he : (fun s : ℝ => Real.exp (-(t * s))) = (fun s => Real.exp ((-t) * s)) := by
    funext s
    rw [neg_mul]
  rw [he, intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr ht.ne'),
    integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul, inv_neg]
  field_simp
  ring

/-- The exact integral of `1-exp(-t y)` against the power-law Lévy measure.
The nonnegative integral also proves its finiteness. -/
theorem stable_laplace_exponent_lintegral {α t : ℝ}
    (hα : 0 < α) (ha : α < 1) (ht : 0 < t) :
    (∫⁻ y : ExtremeState, ENNReal.ofReal (1 - Real.exp (-(t * y.val.toReal)))
      ∂powerIntensity α) = ENNReal.ofReal (Real.Gamma (1 - α) * t ^ α) := by
  have hg : ∀ b > 0, IntervalIntegrable (fun s : ℝ => t * Real.exp (-(t * s))) volume 0 b :=
    fun _ _ => (by fun_prop : Continuous (fun s : ℝ => t * Real.exp (-(t * s)))).intervalIntegrable _ _
  have hl := lintegral_comp_eq_lintegral_meas_lt_mul (powerIntensity α)
    (f := fun y : ExtremeState => y.val.toReal)
    (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    (measurable_subtype_coe.ennreal_toReal.aemeasurable) hg
    (ae_of_all _ (fun s => mul_nonneg ht.le (Real.exp_pos _).le))
  simp_rw [exponential_primitive ht] at hl
  rw [hl]
  have he : (fun s : ℝ => powerIntensity α {y : ExtremeState | s < y.val.toReal} *
      ENNReal.ofReal (t * Real.exp (-(t * s)))) =ᵐ[volume.restrict (Ioi 0)]
      (fun s => ENNReal.ofReal (t * (s ^ (-α) * Real.exp (-(t * s))))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [powerIntensity_realTail hα hs, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    congr 1
    ring
  rw [lintegral_congr_ae he]
  have hi : IntegrableOn (fun s : ℝ => s ^ (-α) * Real.exp (-(t * s))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -α) (b := t)
        (by linarith) (by norm_num) ht
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul t)]
  · congr 1
    rw [integral_const_mul]
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - α) (by linarith) ht
    rw [show 1 - α - 1 = -α by ring] at hh
    rw [hh, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    rw [show -(1 - α) = α - 1 by ring]
    calc
      t * (t ^ (α - 1) * Real.Gamma (1 - α)) =
          (t ^ (1 : ℝ) * t ^ (α - 1)) * Real.Gamma (1 - α) := by rw [Real.rpow_one]; ring
      _ = Real.Gamma (1 - α) * t ^ α := by
        rw [← Real.rpow_add ht, show (1 : ℝ) + (α - 1) = α by ring]
        ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg ht.le (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le)

theorem stable_laplace_exponent_integrable {α t : ℝ}
    (hα : 0 < α) (ha : α < 1) (ht : 0 < t) :
    Integrable (fun y : ExtremeState => 1 - Real.exp (-(t * y.val.toReal))) (powerIntensity α) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (show Measurable (fun y : ExtremeState => 1 - Real.exp (-(t * y.val.toReal))) by fun_prop).aestronglyMeasurable
    (ae_of_all _ (fun y => sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg ht.le ENNReal.toReal_nonneg)))))).mp
  rw [stable_laplace_exponent_lintegral hα ha ht]
  exact ENNReal.ofReal_ne_top

theorem stable_laplace_exponent {α t : ℝ}
    (hα : 0 < α) (ha : α < 1) (ht : 0 < t) :
    (∫ y : ExtremeState, 1 - Real.exp (-(t * y.val.toReal)) ∂powerIntensity α) =
      Real.Gamma (1 - α) * t ^ α := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun y => sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg ht.le ENNReal.toReal_nonneg)))) )
    (show Measurable (fun y : ExtremeState => 1 - Real.exp (-(t * y.val.toReal))) by fun_prop).aestronglyMeasurable,
    stable_laplace_exponent_lintegral hα ha ht, ENNReal.toReal_ofReal]
  exact mul_nonneg (Real.Gamma_pos_of_pos (sub_pos.mpr ha)).le (Real.rpow_nonneg ht.le _)

end
end ConditionedStableLaws
