import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Truncated moments from the layer-cake formula

The truncated second-moment identity used in the Gaussian boundary argument follows from the
layer-cake theorem. The untruncated square need not be integrable: boundedness of the
clipped/truncated observables supplies every required finite integral.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace ConditionedStableLaws

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- The tail function is measurable as a real function of the threshold. -/
theorem measurable_real_tail (f : Ω → ℝ) :
    Measurable (fun s : ℝ => μ.real {x | s < f x}) := by
  apply Measurable.ennreal_toReal
  exact Antitone.measurable (fun _ _ hst => measure_mono (fun _ hx => lt_of_le_of_lt hst hx))

/-- A nonnegative observable clipped at a finite level has an integrable square,
even when its original second moment is infinite. -/
theorem integrable_clipped_square (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => (min (f x) t) ^ 2) μ := by
  apply Integrable.of_bound ((hf.min measurable_const).pow_const 2).aestronglyMeasurable (t ^ 2)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hlo : 0 ≤ min (f x) t := le_min (hf0 x) ht
  have hhi : min (f x) t ≤ t := min_le_right _ _
  nlinarith

/-- The truncated square itself is integrable without an untruncated-moment assumption. -/
theorem integrable_truncated_square (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 ≤ t) :
    Integrable ({x | f x ≤ t}.indicator (fun x => f x ^ 2)) μ := by
  apply Integrable.of_bound
    ((hf.pow_const 2).indicator (measurableSet_le hf measurable_const)).aestronglyMeasurable
    (t ^ 2)
  apply Eventually.of_forall
  intro x
  by_cases hx : f x ≤ t
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hx,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))]
    have := hf0 x
    nlinarith
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hx, norm_zero]
    positivity

/-- Layer cake for the clipped square, with the original strict superlevel
sets on the right-hand side. -/
theorem integral_clipped_square_eq_tail (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) :
    (∫ x, (min (f x) t) ^ 2 ∂μ) =
      2 * ∫ s in Ioo 0 t, s * μ.real {x | s < f x} := by
  have hmin0 : 0 ≤ᵐ[μ] (fun x => min (f x) t) :=
    Eventually.of_forall (fun x => le_min (hf0 x) ht.le)
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ hmin0
    (hf.min measurable_const).aemeasurable (show (0 : ℝ) < 2 by norm_num)
  norm_num only [Real.rpow_two, sub_self, show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, ENNReal.ofReal_ofNat] at hlayer
  have htail : (∫⁻ s in Ioi (0 : ℝ),
      μ {x | s < min (f x) t} * ENNReal.ofReal s) =
      ∫⁻ s in Ioo 0 t, μ {x | s < f x} * ENNReal.ofReal s := by
    have heq : (fun s : ℝ => μ {x | s < min (f x) t} * ENNReal.ofReal s) =
        (Iio t).indicator (fun s => μ {x | s < f x} * ENNReal.ofReal s) := by
      funext s
      by_cases hs : s < t
      · simp [hs, lt_min_iff]
      · have hempty : {x | s < min (f x) t} = ∅ := by
          ext x
          simp only [Set.mem_ofPred_eq, lt_min_iff, hs, and_false, Set.mem_empty_iff_false]
        rw [hempty]
        simp [hs]
    rw [heq, lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  rw [htail] at hlayer
  have hmeas : Measurable (fun s : ℝ => μ {x | s < f x}) :=
    Antitone.measurable (fun _ _ hst => measure_mono (fun _ hx => lt_of_le_of_lt hst hx))
  have htailmeas : Measurable (fun s : ℝ => μ {x | s < f x} * ENNReal.ofReal s) :=
    hmeas.mul measurable_id.ennreal_ofReal
  have hfinite : ∀ᵐ s ∂volume.restrict (Ioo 0 t),
      μ {x | s < f x} * ENNReal.ofReal s < ∞ :=
    Eventually.of_forall (fun s => ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => sq_nonneg (min (f x) t))
    ((hf.min measurable_const).pow_const 2).aestronglyMeasurable,
    hlayer, ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← integral_toReal htailmeas.aemeasurable hfinite]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  dsimp only
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.1.le]
  exact mul_comm _ _

/-- The exact truncated-second-moment identity. The strict tail `{f > t}` compensates for clipping
above `t`, retaining atoms at `f=t` in the truncated square. -/
theorem truncated_second_moment (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) :
    (∫ x, {x | f x ≤ t}.indicator (fun x => f x ^ 2) x ∂μ) =
      2 * (∫ s in (0 : ℝ)..t, s * μ.real {x | s < f x}) -
        t ^ 2 * μ.real {x | t < f x} := by
  have htailint : Integrable ({x | t < f x}.indicator (fun _ => t ^ 2)) μ :=
    (integrable_const _).indicator (measurableSet_lt measurable_const hf)
  have hsplit : (∫ x, (min (f x) t) ^ 2 ∂μ) =
      (∫ x, {x | f x ≤ t}.indicator (fun x => f x ^ 2) x ∂μ) +
        t ^ 2 * μ.real {x | t < f x} := by
    have heq : (fun x => (min (f x) t) ^ 2) =
        (fun x => {x | f x ≤ t}.indicator (fun x => f x ^ 2) x +
          {x | t < f x}.indicator (fun _ => t ^ 2) x) := by
      funext x
      by_cases hx : f x ≤ t
      · simp [hx, not_lt.mpr hx]
      · simp [hx, lt_of_not_ge hx, min_eq_right (le_of_not_ge hx)]
    rw [heq, integral_add (integrable_truncated_square μ f hf hf0 t ht.le) htailint,
      integral_indicator (measurableSet_lt measurable_const hf), setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  have hlayer := integral_clipped_square_eq_tail μ f hf hf0 t ht
  rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
  linarith

/-- Dropping the nonnegative clipping correction gives the standard tail-integral bound. -/
theorem truncated_second_moment_le_tailIntegral (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) :
    (∫ x, {x | f x ≤ t}.indicator (fun x => f x ^ 2) x ∂μ) ≤
      2 * ∫ s in Ioo 0 t, s * μ.real {x | s < f x} := by
  rw [truncated_second_moment μ f hf hf0 t ht,
    intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
  exact sub_le_self _ (by positivity)

/-- A power-law tail bound with exponent below two gives the expected `t^(2-α)`
truncated-second-moment bound. The second moment need not be finite, and the tail bound only needs
to hold up to the truncation level. -/
theorem truncated_second_moment_le_of_power_tail (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) (C α : ℝ)
    (hα : α < 2)
    (htail : ∀ s ∈ Ioo 0 t, μ.real {x | s < f x} ≤ C * s ^ (-α)) :
    (∫ x, {x | f x ≤ t}.indicator (fun x => f x ^ 2) x ∂μ) ≤
      (2 * C / (2 - α)) * t ^ (2 - α) := by
  have hp : -1 < 1 - α := by linarith
  have hpowint : IntervalIntegrable (fun s : ℝ => s ^ (1 - α)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hmajor : IntegrableOn (fun s : ℝ => C * s ^ (1 - α)) (Ioo 0 t) :=
    (hpowint.1.const_mul C).mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  have hcompare : (∫ s in Ioo 0 t, s * μ.real {x | s < f x}) ≤
      ∫ s in Ioo 0 t, C * s ^ (1 - α) := by
    refine integral_mono_of_nonneg ?_ hmajor ?_
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
      exact mul_nonneg hs.1.le (measureReal_nonneg)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
      calc
        s * μ.real {x | s < f x} ≤ s * (C * s ^ (-α)) :=
          mul_le_mul_of_nonneg_left (htail s hs) hs.1.le
        _ = C * s ^ (1 - α) := by
          rw [sub_eq_add_neg, Real.rpow_add hs.1, Real.rpow_one]
          ring
  have hformula : (∫ s in Ioo 0 t, C * s ^ (1 - α)) =
      C * t ^ (2 - α) / (2 - α) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl hp)]
    have he : 1 - α + 1 = 2 - α := by ring
    rw [he, Real.zero_rpow (by linarith : 2 - α ≠ 0), sub_zero]
    ring
  calc
    _ ≤ 2 * ∫ s in Ioo 0 t, s * μ.real {x | s < f x} :=
      truncated_second_moment_le_tailIntegral μ f hf hf0 t ht
    _ ≤ 2 * ∫ s in Ioo 0 t, C * s ^ (1 - α) :=
      mul_le_mul_of_nonneg_left hcompare (by norm_num)
    _ = (2 * C / (2 - α)) * t ^ (2 - α) := by rw [hformula]; ring

end ConditionedStableLaws
