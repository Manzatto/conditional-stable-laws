import ConditionedStableLaws.CompensatedPoissonIntegral
import ConditionedStableLaws.CompensatedCharacteristic
import ConditionedStableLaws.PositivePoissonIntegral

/-!
Compensated small jumps of the power-law Poisson measure.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

/-- The small-mark integrand `y ↦ y 1_{y ≤ ε}`. -/
def smallMark (ε : ℝ) : ExtremeState → ℝ :=
  {y : ExtremeState | y.val ≤ ENNReal.ofReal ε}.indicator (fun y => y.val.toReal)

theorem measurable_smallMark (ε : ℝ) : Measurable (smallMark ε) :=
  (by fun_prop : Measurable (fun y : ExtremeState => y.val.toReal)).indicator
    (measurableSet_le measurable_subtype_coe measurable_const)

theorem smallMark_nonneg (ε : ℝ) (y : ExtremeState) : 0 ≤ smallMark ε y := by
  apply Set.indicator_nonneg
  intro y _
  exact ENNReal.toReal_nonneg

theorem norm_smallMark_le {ε : ℝ} (hε : 0 ≤ ε) (y : ExtremeState) :
    ‖smallMark ε y‖ ≤ ε := by
  rw [Real.norm_eq_abs, abs_of_nonneg (smallMark_nonneg ε y)]
  by_cases hy : y.val ≤ ENNReal.ofReal ε
  · rw [smallMark, Set.indicator_of_mem (show y ∈
      {z : ExtremeState | z.val ≤ ENNReal.ofReal ε} from hy)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hy).trans_eq (ENNReal.toReal_ofReal hε)
  · simpa [smallMark, hy] using hε

theorem smallMark_square_lintegral {α ε : ℝ} (hα : 0 < α) (ha : α < 2)
    (hε : 0 < ε) :
    (∫⁻ y, ENNReal.ofReal ((smallMark ε y)^2) ∂powerIntensity α) =
      ENNReal.ofReal (α / (2 - α) * ε ^ (2 - α)) := by
  have he : (fun y => ENNReal.ofReal ((smallMark ε y)^2)) =
      {y : ExtremeState | y.val ≤ ENNReal.ofReal ε}.indicator
        (fun y => ENNReal.ofReal (y.val.toReal ^ (2 : ℝ))) := by
    funext y
    by_cases hy : y.val ≤ ENNReal.ofReal ε <;> simp [smallMark, hy]
  rw [he, lintegral_indicator (measurableSet_le measurable_subtype_coe measurable_const)]
  exact powerIntensity_small_moment hα ha hε

theorem smallMark_square_integrable {α ε : ℝ} (hα : 0 < α) (ha : α < 2)
    (hε : 0 < ε) : Integrable (fun y => (smallMark ε y)^2) (powerIntensity α) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_smallMark ε).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun _ => sq_nonneg _))).mp
  rw [smallMark_square_lintegral hα ha hε]
  exact ENNReal.ofReal_ne_top

theorem smallMark_square_integral {α ε : ℝ} (hα : 0 < α) (ha : α < 2)
    (hε : 0 < ε) :
    (∫ y, (smallMark ε y)^2 ∂powerIntensity α) = α / (2 - α) * ε ^ (2 - α) := by
  have he := smallMark_square_lintegral hα ha hε
  rw [← ofReal_integral_eq_lintegral_ofReal (smallMark_square_integrable hα ha hε)
    (ae_of_all _ (fun _ => sq_nonneg _))] at he
  exact ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _)) (by positivity) |>.mp he

namespace AnnularPoissonClouds

/-- A centered random variable for jumps of size at most ε. -/
def compensatedSmallJumps (α ε : ℝ) (hα : 0 < α) (hε : 0 ≤ ε) : Sample → ℝ :=
  compensatedIntegral (powerIntensity α) (powerIntensity_tail_lt_top hα)
    (smallMark ε) (measurable_smallMark ε) hε (norm_smallMark_le hε)

theorem compensatedSmallJumps_memLp (α ε : ℝ) (hα : 0 < α) (hε : 0 ≤ ε) :
    MemLp (compensatedSmallJumps α ε hα hε) 2 (powerLaw α hα) :=
  compensatedIntegral_memLp _ _ _ _ _ _

theorem compensatedSmallJumps_mean {α ε : ℝ} (hα : 0 < α) (ha : α < 2) (hε : 0 < ε) :
    (∫ ω, compensatedSmallJumps α ε hα hε.le ω ∂powerLaw α hα) = 0 :=
  compensatedIntegral_mean _ _ _ _ _ _ (smallMark_square_integrable hα ha hε)

/-- Exact small-jump variance, valid throughout 0<α<2. -/
theorem compensatedSmallJumps_second_moment {α ε : ℝ}
    (hα : 0 < α) (ha : α < 2) (hε : 0 < ε) :
    (∫ ω, (compensatedSmallJumps α ε hα hε.le ω)^2 ∂powerLaw α hα) =
      α / (2 - α) * ε ^ (2 - α) := by
  rw [compensatedSmallJumps, show powerLaw α hα = law (powerIntensity α)
    (powerIntensity_tail_lt_top hα) from rfl,
    compensatedIntegral_second_moment _ _ _ _ _ _ (smallMark_square_integrable hα ha hε)]
  exact smallMark_square_integral hα ha hε

theorem compensatedSmallJumps_probability_le {α ε t : ℝ}
    (hα : 0 < α) (ha : α < 2) (hε : 0 < ε) (ht : 0 < t) :
    powerLaw α hα {ω | t ≤ |compensatedSmallJumps α ε hα hε.le ω|} ≤
      ENNReal.ofReal ((α / (2 - α) * ε ^ (2 - α)) / t^2) := by
  have hv : Var[compensatedSmallJumps α ε hα hε.le; powerLaw α hα] =
      α / (2 - α) * ε ^ (2 - α) := by
    rw [variance_eq_integral (compensatedSmallJumps_memLp α ε hα hε.le).aestronglyMeasurable.aemeasurable,
      compensatedSmallJumps_mean hα ha hε]
    simpa only [sub_zero] using compensatedSmallJumps_second_moment hα ha hε
  simpa only [compensatedSmallJumps_mean hα ha hε, sub_zero, hv] using
    meas_ge_le_variance_div_sq (compensatedSmallJumps_memLp α ε hα hε.le) ht

theorem compensatedSmallJumps_characteristic {α ε : ℝ}
    (hα : 0 < α) (ha : α < 2) (hε : 0 < ε) (t : ℝ) :
    (∫ ω, Complex.exp ((t * compensatedSmallJumps α ε hα hε.le ω : ℝ) * Complex.I)
      ∂powerLaw α hα) = Complex.exp
      (∫ y in {y : ExtremeState | y.val ≤ ENNReal.ofReal ε},
        Complex.exp ((t*y.val.toReal : ℝ) * Complex.I) - 1 -
          (t*y.val.toReal : ℝ) * Complex.I ∂powerIntensity α) := by
  rw [compensatedSmallJumps, show powerLaw α hα = law (powerIntensity α)
    (powerIntensity_tail_lt_top hα) from rfl,
    compensatedIntegral_characteristic _ _ _ _ _ _ _ (smallMark_square_integrable hα ha hε)]
  congr 1
  rw [← integral_indicator (measurableSet_le measurable_subtype_coe measurable_const)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    by_cases hy : y.val ≤ ENNReal.ofReal ε <;> simp [compensatedExponent, smallMark, hy])

/-- The exact second moment vanishes as any positive sequence of cutoffs
tends to zero, including the critical index α=1. -/
theorem compensatedSmallJumps_second_moment_tendsto_zero {ι : Type*} {l : Filter ι} {α : ℝ}
    (hα : 0 < α) (ha : α < 2) (ε : ι → ℝ) (hε : ∀ n, 0 < ε n)
    (he : Tendsto ε l (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (compensatedSmallJumps α (ε n) hα (hε n).le ω)^2
      ∂powerLaw α hα) l (𝓝 0) := by
  simp_rw [compensatedSmallJumps_second_moment hα ha (hε _)]
  have hp := (Real.continuousAt_rpow_const (0 : ℝ) (2-α) (Or.inr (by linarith))).tendsto.comp he
  simpa only [Function.comp_def, Real.zero_rpow (by linarith : 2-α ≠ 0), mul_zero]
    using hp.const_mul (α/(2-α))

theorem compensatedSmallJumps_tendstoInMeasure {ι : Type*} {l : Filter ι} {α : ℝ}
    (hα : 0 < α) (ha : α < 2) (ε : ι → ℝ) (hε : ∀ n, 0 < ε n)
    (he : Tendsto ε l (𝓝 0)) :
    TendstoInMeasure (powerLaw α hα)
      (fun n => compensatedSmallJumps α (ε n) hα (hε n).le) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro t ht
  have hp := (compensatedSmallJumps_second_moment_tendsto_zero hα ha ε hε he).div_const (t^2)
  simp_rw [compensatedSmallJumps_second_moment hα ha (hε _)] at hp
  have hp' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp
  simp only [zero_div, ENNReal.ofReal_zero] at hp'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp'
    (fun _ => zero_le) (fun n => ?_)
  simpa only [Function.comp_def, Real.dist_eq, sub_zero] using
    compensatedSmallJumps_probability_le hα ha (hε n) ht

end AnnularPoissonClouds
end
end ConditionedStableLaws
