import ConditionedStableLaws.TruncatedAsymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# First moments and centering of power-tailed observables

Layer cake gives exact truncated first moments and their power/logarithmic asymptotics.
Integrability above tail exponent one follows from the tail bound.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem intervalIntegrable_real_tail (f : Ω → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => μ.real {x | s < f x}) volume a b := by
  apply Antitone.intervalIntegrable
  intro s t hst
  exact measureReal_mono (fun x hx => lt_of_le_of_lt hst hx)

theorem integrable_clipped (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => min (f x) t) μ := by
  apply Integrable.of_bound (hf.min measurable_const).aestronglyMeasurable t
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf0 x) ht)]
    exact min_le_right _ _

theorem integrable_truncated (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 ≤ t) :
    Integrable ({x | f x ≤ t}.indicator f) μ := by
  apply Integrable.of_bound
    (hf.indicator (measurableSet_le hf measurable_const)).aestronglyMeasurable t
  apply Eventually.of_forall
  intro x
  by_cases hx : f x ≤ t
  · simp [hx, Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
  · simpa [Set.indicator_apply, hx] using ht

theorem integral_clipped_eq_tail (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) :
    (∫ x, min (f x) t ∂μ) = ∫ s in (0 : ℝ)..t, μ.real {x | s < f x} := by
  rw [(integrable_clipped μ f hf hf0 t ht.le).integral_eq_integral_meas_lt
    (Eventually.of_forall fun x => le_min (hf0 x) ht.le)]
  have heq : (fun s : ℝ => μ.real {x | s < min (f x) t}) =
      (Iio t).indicator (fun s => μ.real {x | s < f x}) := by
    funext s
    by_cases hs : s < t
    · simp [hs, lt_min_iff]
    · have hempty : {x | s < min (f x) t} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, lt_min_iff, hs, and_false, Set.mem_empty_iff_false]
      rw [hempty]
      simp [hs]
  rw [heq, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi,
    intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]

/-- Exact truncated first-moment formula, including atoms at the threshold. -/
theorem truncated_first_moment (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) :
    (∫ x, {x | f x ≤ t}.indicator f x ∂μ) =
      (∫ s in (0 : ℝ)..t, μ.real {x | s < f x}) - t * μ.real {x | t < f x} := by
  have heq : (fun x => min (f x) t) = fun x =>
      {x | f x ≤ t}.indicator f x + {x | t < f x}.indicator (fun _ => t) x := by
    funext x
    by_cases hx : f x ≤ t
    · simp [hx, not_lt.mpr hx]
    · simp [hx, lt_of_not_ge hx, min_eq_right (le_of_not_ge hx)]
  have hi := integral_clipped_eq_tail μ f hf hf0 t ht
  rw [heq, integral_add (integrable_truncated μ f hf hf0 t ht.le)
    ((integrable_const t).indicator (measurableSet_lt measurable_const hf)),
    integral_indicator (measurableSet_lt measurable_const hf), setIntegral_const] at hi
  simp only [smul_eq_mul] at hi
  linarith

/-- The logarithmic centering scale at tail exponent one. -/
theorem truncated_first_moment_div_log_tendsto (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (C : ℝ) (hC : 0 < C)
    (htail : Tendsto (fun t : ℝ => μ.real {x | t < f x} / (C * t ^ (-1 : ℝ)))
      atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => (∫ x, {x | f x ≤ t}.indicator f x ∂μ) / Real.log t)
      atTop (𝓝 C) := by
  have hs : Tendsto (fun t : ℝ => t * μ.real {x | t < f x}) atTop (𝓝 C) := by
    simpa only [Real.rpow_one] using scaled_power_tail_tendsto μ f C 1 hC htail
  have hi := integral_div_log_tendsto (fun t => μ.real {x | t < f x}) C
    (fun t _ => intervalIntegrable_real_tail μ f 0 t) hs
  have hc := hs.div_atTop Real.tendsto_log_atTop
  have h := hi.sub hc
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [truncated_first_moment μ f hf hf0 t ht]
  ring

/-- The power centering scale below tail exponent one. -/
theorem truncated_first_moment_div_rpow_tendsto (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (C α : ℝ) (hC : 0 < C) (hα : α < 1)
    (htail : Tendsto (fun t : ℝ => μ.real {x | t < f x} / (C * t ^ (-α)))
      atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => (∫ x, {x | f x ≤ t}.indicator f x ∂μ) / t ^ (1 - α))
      atTop (𝓝 (α * C / (1 - α))) := by
  have hs := scaled_power_tail_tendsto μ f C α hC htail
  have hi : Tendsto (fun t : ℝ => (∫ s in (0 : ℝ)..t, μ.real {x | s < f x}) /
      t ^ (1 - α)) atTop (𝓝 (C / (1 - α))) := by
    apply integral_div_rpow_tendsto _ C (1 - α) (by linarith)
      (fun t _ => intervalIntegrable_real_tail μ f 0 t)
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [show 1 - α - 1 = -α by ring, Real.rpow_neg ht.le]
    field_simp
  have hc : Tendsto (fun t : ℝ => t * μ.real {x | t < f x} / t ^ (1 - α))
      atTop (𝓝 C) := by
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.rpow_sub ht, Real.rpow_one]
    field_simp
  have h := hi.sub hc
  have hvalue : C / (1 - α) - C = α * C / (1 - α) := by
    field_simp [ne_of_gt (sub_pos.mpr hα)]
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [truncated_first_moment μ f hf hf0 t ht]
  ring

/-- Integrability of a nonnegative observable follows from integrability of its real tail on the
positive line. -/
theorem integrable_of_integrable_tail (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (htail : IntegrableOn (fun t : ℝ => μ.real {x | t < f x}) (Ioi 0)) :
    Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0),
    lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hf0) hf.aemeasurable]
  have heq : (fun t : ℝ => μ {x | t < f x}) =
      (fun t => ENNReal.ofReal (μ.real {x | t < f x})) := by
    funext t
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [heq]
  exact htail.lintegral_lt_top

/-- A power bound above exponent one gives finite first moment. Only the
large-threshold bound is needed; finite total mass controls small thresholds. -/
theorem integrable_of_power_tail_bound (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (C α A : ℝ) (hα : 1 < α) (hA : 0 < A)
    (htail : ∀ t : ℝ, A < t → μ.real {x | t < f x} ≤ C * t ^ (-α)) :
    Integrable f μ := by
  have hmajor : IntegrableOn (fun t : ℝ => C * t ^ (-α)) (Ioi A) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -α < -1) hA).const_mul C
  have hfar : IntegrableOn (fun t : ℝ => μ.real {x | t < f x}) (Ioi A) := by
    apply hmajor.mono' (measurable_real_tail μ f).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact htail t ht
  have hnear : IntegrableOn (fun t : ℝ => μ.real {x | t < f x}) (Ioc 0 A) :=
    (intervalIntegrable_real_tail μ f 0 A).1
  apply integrable_of_integrable_tail μ f hf hf0
  have hu : Ioc (0 : ℝ) A ∪ Ioi A = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact hA.trans ht
    · intro ht
      by_cases htA : t ≤ A
      · exact Or.inl ⟨ht, htA⟩
      · exact Or.inr (lt_of_not_ge htA)
  rw [← hu]
  exact hnear.union hfar

/-- The centering mean exists whenever the original tail exponent exceeds
one. This conclusion is derived directly from the ratio asymptotic. -/
theorem integrable_of_power_tail_asymptotic (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (C α : ℝ) (hC : 0 < C) (hα : 1 < α)
    (htail : Tendsto (fun t : ℝ => μ.real {x | t < f x} / (C * t ^ (-α)))
      atTop (𝓝 1)) : Integrable f μ := by
  have hscaled := scaled_power_tail_tendsto μ f C α hC htail
  obtain ⟨A, hbound⟩ := eventually_atTop.mp (hscaled.eventually_lt_const (lt_add_one C))
  apply integrable_of_power_tail_bound μ f hf hf0 (C + 1) α (max A 1) hα
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ((le_max_right A 1).trans ht.le)
  have hb := (hbound t ((le_max_left A 1).trans ht.le)).le
  rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ht0 α)).mpr (by simpa [mul_comm] using hb)

end
end ConditionedStableLaws
