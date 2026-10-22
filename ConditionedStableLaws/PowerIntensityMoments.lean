import ConditionedStableLaws.PowerIntensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact small- and large-jump moments of the power-law intensity. -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem powerIntensity_lintegral (α : ℝ) (f : ExtremeState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂powerIntensity α) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (α * x ^ (-α - 1)) * f (extremeOfReal x) := by
  rw [powerIntensity, lintegral_map hf measurable_extremeOfReal]
  exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (show Measurable (fun x => f (extremeOfReal x)) from hf.comp measurable_extremeOfReal)

theorem powerIntensity_setLIntegral (α : ℝ) (A : Set ExtremeState) (hA : MeasurableSet A)
    (f : ExtremeState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in A, f y ∂powerIntensity α) =
      ∫⁻ x in extremeOfReal ⁻¹' A ∩ Ioi (0 : ℝ),
        ENNReal.ofReal (α * x ^ (-α - 1)) * f (extremeOfReal x) := by
  rw [← lintegral_indicator hA, powerIntensity_lintegral α _ (hf.indicator hA)]
  have he : (fun x => ENNReal.ofReal (α * x ^ (-α - 1)) * A.indicator f (extremeOfReal x)) =
      (extremeOfReal ⁻¹' A).indicator
        (fun x => ENNReal.ofReal (α * x ^ (-α - 1)) * f (extremeOfReal x)) := by
    funext x
    by_cases hx : extremeOfReal x ∈ A <;> simp [hx]
  rw [he, lintegral_indicator (measurable_extremeOfReal hA),
    Measure.restrict_restrict (measurable_extremeOfReal hA)]

private theorem power_moment_integrand (α p x : ℝ) (hα : 0 ≤ α) (hx : 0 < x) :
    ENNReal.ofReal (α * x ^ (-α - 1)) * ENNReal.ofReal ((extremeOfReal x).val.toReal ^ p) =
      ENNReal.ofReal (α * x ^ (p - α - 1)) := by
  rw [extremeOfReal_val_of_pos hx, ENNReal.toReal_ofReal hx.le,
    ← ENNReal.ofReal_mul (mul_nonneg hα (Real.rpow_nonneg hx.le _))]
  congr 1
  rw [mul_assoc, ← Real.rpow_add hx]
  congr 2
  ring

/-- The exact positive power moment below a finite cutoff. In particular
`p=1` controls uncompensated small jumps and `p=2` controls their variance. -/
theorem powerIntensity_small_moment {α p ε : ℝ}
    (hα : 0 < α) (hp : α < p) (hε : 0 < ε) :
    (∫⁻ y in {y : ExtremeState | y.val ≤ ENNReal.ofReal ε},
      ENNReal.ofReal (y.val.toReal ^ p) ∂powerIntensity α) =
      ENNReal.ofReal (α / (p - α) * ε ^ (p - α)) := by
  rw [powerIntensity_setLIntegral α _ (measurableSet_le measurable_subtype_coe measurable_const)
    _ (by fun_prop)]
  have hs : extremeOfReal ⁻¹' {y : ExtremeState | y.val ≤ ENNReal.ofReal ε} ∩ Ioi 0 =
      Ioc (0 : ℝ) ε := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      refine ⟨hx0, ?_⟩
      change (extremeOfReal x).val ≤ ENNReal.ofReal ε at hx
      rw [extremeOfReal_val_of_pos hx0, ENNReal.ofReal_le_ofReal_iff hε.le] at hx
      exact hx
    · rintro ⟨hx0, hxε⟩
      exact ⟨by change (extremeOfReal x).val ≤ ENNReal.ofReal ε
                rw [extremeOfReal_val_of_pos hx0]
                exact ENNReal.ofReal_le_ofReal hxε, hx0⟩
  rw [hs]
  have he : (fun x => ENNReal.ofReal (α * x ^ (-α - 1)) *
      ENNReal.ofReal ((extremeOfReal x).val.toReal ^ p)) =ᵐ[volume.restrict (Ioc 0 ε)]
      (fun x => ENNReal.ofReal (α * x ^ (p - α - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact power_moment_integrand α p x hα.le hx.1
  rw [lintegral_congr_ae he]
  have hi : IntegrableOn (fun x : ℝ => α * x ^ (p - α - 1)) (Ioc 0 ε) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε)
      (by linarith : -1 < p - α - 1)).1).const_mul α
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hε.le,
      integral_rpow (Or.inl (by linarith)), show p - α - 1 + 1 = p - α by ring,
      Real.zero_rpow (sub_ne_zero.mpr hp.ne'), sub_zero]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg hα.le (Real.rpow_nonneg hx.1.le _)

/-- The exact power moment of the large-jump tail when its exponent is
below the tail index. -/
theorem powerIntensity_large_moment {α p R : ℝ}
    (hα : 0 < α) (hp : p < α) (hR : 0 < R) :
    (∫⁻ y in {y : ExtremeState | ENNReal.ofReal R < y.val},
      ENNReal.ofReal (y.val.toReal ^ p) ∂powerIntensity α) =
      ENNReal.ofReal (α / (α - p) * R ^ (p - α)) := by
  rw [powerIntensity_setLIntegral α _ (measurableSet_lt measurable_const measurable_subtype_coe)
    _ (by fun_prop)]
  have hs : extremeOfReal ⁻¹' {y : ExtremeState | ENNReal.ofReal R < y.val} ∩ Ioi 0 =
      Ioi R := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      change ENNReal.ofReal R < (extremeOfReal x).val at hx
      rw [extremeOfReal_val_of_pos hx0, ENNReal.ofReal_lt_ofReal_iff hx0] at hx
      exact hx
    · intro hx
      have hx0 := hR.trans hx
      refine ⟨?_, hx0⟩
      change ENNReal.ofReal R < (extremeOfReal x).val
      rw [extremeOfReal_val_of_pos hx0, ENNReal.ofReal_lt_ofReal_iff hx0]
      exact hx
  rw [hs]
  have he : (fun x => ENNReal.ofReal (α * x ^ (-α - 1)) *
      ENNReal.ofReal ((extremeOfReal x).val.toReal ^ p)) =ᵐ[volume.restrict (Ioi R)]
      (fun x => ENNReal.ofReal (α * x ^ (p - α - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact power_moment_integrand α p x hα.le (hR.trans hx)
  rw [lintegral_congr_ae he]
  have hi : IntegrableOn (fun x : ℝ => α * x ^ (p - α - 1)) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : p - α - 1 < -1) hR).const_mul α
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hR,
      show p - α - 1 + 1 = p - α by ring]
    rw [show α - p = -(p - α) by ring, div_neg]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hα.le (Real.rpow_nonneg (hR.trans hx).le _)

end
end ConditionedStableLaws
