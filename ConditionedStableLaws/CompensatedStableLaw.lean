import ConditionedStableLaws.InitialPoissonJump
import ConditionedStableLaws.PowerCompensation

/-! The large-jump plus compensated-small-jump stable random variables. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem powerIntensity_integral_complex {α : ℝ} (hα : 0 ≤ α)
    (f : ExtremeState → ℂ) (hf : Measurable f) :
    (∫ y, f y ∂powerIntensity α) =
      ∫ x in Ioi (0 : ℝ), (α*x^(-α-1) : ℝ) • f (extremeOfReal x) := by
  rw [powerIntensity, integral_map measurable_extremeOfReal.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (mul_nonneg hα (Real.rpow_nonneg hx.le _))]

/-- The exponent for compensation only below the unit cutoff. -/
def unitStableExponent (t : ℝ) (y : ExtremeState) : ℂ :=
  Complex.exp ((t*y.val.toReal : ℝ) * Complex.I) - 1 - (t*smallMark 1 y : ℝ) * Complex.I

theorem measurable_unitStableExponent (t : ℝ) : Measurable (unitStableExponent t) := by
  have := measurable_smallMark (1 : ℝ)
  unfold unitStableExponent
  fun_prop

theorem unitStableExponent_split (t : ℝ) : unitStableExponent t =
    (AnnularPoissonClouds.annulus 0).indicator
      (fun y : ExtremeState => Complex.exp ((t*y.val.toReal : ℝ) * Complex.I)-1) +
      compensatedExponent t (smallMark 1) := by
  funext y
  by_cases hy : y.val ≤ 1
  · simp [unitStableExponent, compensatedExponent, smallMark,
      AnnularPoissonClouds.annulus_zero, hy, not_lt.mpr hy]
  · have hy' : 1 < y.val := not_le.mp hy
    simp [unitStableExponent, compensatedExponent, smallMark,
      AnnularPoissonClouds.annulus_zero, hy, hy']

theorem unitStableExponent_integrable {α : ℝ} (hα : 0 < α) (ha : α < 2) (t : ℝ) :
    Integrable (unitStableExponent t) (powerIntensity α) := by
  rw [unitStableExponent_split]
  apply Integrable.add _ (compensatedExponent_integrable _ t (smallMark 1)
    (measurable_smallMark 1) (smallMark_square_integrable hα ha zero_lt_one))
  rw [integrable_indicator_iff (AnnularPoissonClouds.measurableSet_annulus 0)]
  have : IsFiniteMeasure ((powerIntensity α).restrict (AnnularPoissonClouds.annulus 0)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact AnnularPoissonClouds.annulus_measure_lt_top _ (powerIntensity_tail_lt_top hα) 0⟩
  apply (Integrable.of_bound (show AEStronglyMeasurable
    (fun y : ExtremeState => Complex.exp ((t*y.val.toReal : ℝ) * Complex.I))
    ((powerIntensity α).restrict (AnnularPoissonClouds.annulus 0)) from
      (show Measurable _ by fun_prop).aestronglyMeasurable) 1 ?_).sub (integrable_const 1)
  exact ae_of_all _ (fun y => by rw [Complex.norm_exp]; simp)

def largeMark : ExtremeState → ℝ :=
  {y : ExtremeState | 1 < y.val}.indicator (fun y => y.val.toReal)

theorem measurable_largeMark : Measurable largeMark :=
  (by fun_prop : Measurable (fun y : ExtremeState => y.val.toReal)).indicator
    (measurableSet_lt measurable_const measurable_subtype_coe)

theorem largeMark_nonneg (y : ExtremeState) : 0 ≤ largeMark y := by
  apply Set.indicator_nonneg
  exact fun _ _ => ENNReal.toReal_nonneg

theorem largeMark_lintegral {α : ℝ} (ha : 1 < α) :
    (∫⁻ y, ENNReal.ofReal (largeMark y) ∂powerIntensity α) = ENNReal.ofReal (α/(α-1)) := by
  have he : (fun y => ENNReal.ofReal (largeMark y)) =
      {y : ExtremeState | 1 < y.val}.indicator (fun y => ENNReal.ofReal y.val.toReal) := by
    funext y
    by_cases hy : 1 < y.val <;> simp [largeMark, hy]
  rw [he, lintegral_indicator (measurableSet_lt measurable_const measurable_subtype_coe)]
  simpa only [ENNReal.ofReal_one, Real.rpow_one, Real.one_rpow, mul_one] using
    powerIntensity_large_moment (zero_lt_one.trans ha) ha (show (0 : ℝ) < 1 by norm_num)

theorem largeMark_integrable {α : ℝ} (ha : 1 < α) : Integrable largeMark (powerIntensity α) := by
  apply (lintegral_ofReal_ne_top_iff_integrable measurable_largeMark.aestronglyMeasurable
    (ae_of_all _ largeMark_nonneg)).mp
  rw [largeMark_lintegral ha]
  exact ENNReal.ofReal_ne_top

theorem largeMark_integral {α : ℝ} (ha : 1 < α) :
    (∫ y, largeMark y ∂powerIntensity α) = α/(α-1) := by
  have he := largeMark_lintegral ha
  rw [← ofReal_integral_eq_lintegral_ofReal (largeMark_integrable ha)
    (ae_of_all _ largeMark_nonneg)] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg largeMark_nonneg)
    (div_nonneg (zero_lt_one.trans ha).le (sub_pos.mpr ha).le)).mp he

theorem smallMark_add_largeMark (y : ExtremeState) : smallMark 1 y + largeMark y = y.val.toReal := by
  by_cases hy : y.val ≤ 1
  · simp [smallMark, largeMark, hy, not_lt.mpr hy]
  · simp [smallMark, largeMark, hy, not_le.mp hy]

theorem fullStableExponent_split (t : ℝ) : compensatedExponent t (fun y => y.val.toReal) =
    unitStableExponent t - (fun y => (t*largeMark y : ℝ) * Complex.I) := by
  funext y
  simp only [compensatedExponent, unitStableExponent, Pi.sub_apply]
  rw [← smallMark_add_largeMark y]
  push_cast
  ring

theorem fullStableExponent_integrable {α : ℝ} (ha : 1 < α) (hb : α < 2) (t : ℝ) :
    Integrable (compensatedExponent t (fun y => y.val.toReal)) (powerIntensity α) := by
  rw [fullStableExponent_split]
  exact (unitStableExponent_integrable (zero_lt_one.trans ha) hb t).sub
    (((largeMark_integrable ha).const_mul t).ofReal.mul_const Complex.I)

namespace AnnularPoissonClouds

/-- The random variable compensated at the unit cutoff. -/
def unitCompensatedStable (α : ℝ) (hα : 0 < α) (ω : Sample) : ℝ :=
  FinitePoissonCloud.testIntegral (fun y => y.val.toReal) (ω 0) +
    compensatedSmallJumps α 1 hα zero_le_one ω

theorem measurable_unitCompensatedStable (α : ℝ) (hα : 0 < α) :
    Measurable (unitCompensatedStable α hα) :=
  ((FinitePoissonCloud.measurable_testIntegral (fun y => y.val.toReal) (by fun_prop)).comp
    (measurable_pi_apply 0)).add (measurable_compensatedIntegral _ _ _ _ _ _)

theorem unitCompensatedStable_characteristic {α : ℝ} (hα : 0 < α) (ha : α < 2) (t : ℝ) :
    (∫ ω, Complex.exp ((t*unitCompensatedStable α hα ω : ℝ) * Complex.I) ∂powerLaw α hα) =
      Complex.exp (∫ y, unitStableExponent t y ∂powerIntensity α) := by
  have hz : ∀ y ∈ annulus 0, smallMark 1 y = 0 := by
    intro y hy
    rw [annulus_zero] at hy
    change 1 < y.val at hy
    simp [smallMark, not_le.mpr hy]
  have hh := initial_add_compensated_characteristic (powerIntensity α) (powerIntensity_tail_lt_top hα)
    t (smallMark 1) (fun y => y.val.toReal) (measurable_smallMark 1) (by fun_prop)
    zero_le_one (norm_smallMark_le zero_le_one) (smallMark_square_integrable hα ha zero_lt_one) hz
  change (∫ ω, Complex.exp ((t*unitCompensatedStable α hα ω : ℝ) * Complex.I) ∂powerLaw α hα) = _ at hh
  rw [hh]
  congr 1
  rw [unitStableExponent_split]
  have hs := compensatedExponent_integrable (powerIntensity α) t (smallMark 1)
    (measurable_smallMark 1) (smallMark_square_integrable hα ha zero_lt_one)
  have hi : Integrable ((annulus 0).indicator
      (fun y : ExtremeState => Complex.exp ((t*y.val.toReal : ℝ) * Complex.I)-1)) (powerIntensity α) := by
    have he := unitStableExponent_integrable hα ha t
    rw [unitStableExponent_split] at he
    exact (integrable_add_iff_integrable_left hs).mp he
  simp only [Pi.add_apply]
  rw [integral_add hi hs, integral_indicator (measurableSet_annulus 0)]

/-- The characteristic exponent, expressed against the Lebesgue power density. -/
theorem unitCompensatedStable_characteristic_real {α : ℝ}
    (hα : 0 < α) (ha : α < 2) (t : ℝ) :
    (∫ ω, Complex.exp ((t*unitCompensatedStable α hα ω : ℝ) * Complex.I) ∂powerLaw α hα) =
      Complex.exp (∫ y in Ioi (0 : ℝ), (α*y^(-α-1) : ℝ) •
        (Complex.exp ((t*y : ℝ) * Complex.I) - 1 -
          (t * (if y ≤ 1 then y else 0) : ℝ) * Complex.I)) := by
  rw [unitCompensatedStable_characteristic hα ha,
    powerIntensity_integral_complex hα.le _ (measurable_unitStableExponent t)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [unitStableExponent, smallMark, Set.indicator_apply,
    extremeOfReal_val_of_pos hy, ENNReal.toReal_ofReal hy.le, Set.mem_ofPred_eq, ENNReal.ofReal_one]
  have he : ENNReal.ofReal y ≤ 1 ↔ y ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_le_ofReal_iff (p := y) zero_le_one)
  simp only [he]

/-- Above index one, the large jumps have the finite mean α/(α−1). -/
def fullyCompensatedStable (α : ℝ) (hα : 0 < α) (ω : Sample) : ℝ :=
  unitCompensatedStable α hα ω - α/(α-1)

theorem measurable_fullyCompensatedStable (α : ℝ) (hα : 0 < α) :
    Measurable (fullyCompensatedStable α hα) :=
  (measurable_unitCompensatedStable α hα).sub_const _

theorem fullyCompensatedStable_characteristic {α : ℝ}
    (hα : 0 < α) (ha : 1 < α) (hb : α < 2) (t : ℝ) :
    (∫ ω, Complex.exp ((t*fullyCompensatedStable α hα ω : ℝ) * Complex.I) ∂powerLaw α hα) =
      Complex.exp (∫ y, compensatedExponent t (fun y => y.val.toReal) y ∂powerIntensity α) := by
  have he (ω : Sample) : Complex.exp ((t*fullyCompensatedStable α hα ω : ℝ) * Complex.I) =
      Complex.exp ((t*unitCompensatedStable α hα ω : ℝ) * Complex.I) *
        Complex.exp (-(t*(α/(α-1)) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [fullyCompensatedStable, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  simp_rw [he]
  rw [integral_mul_const, unitCompensatedStable_characteristic hα hb, ← Complex.exp_add]
  congr 1
  rw [fullStableExponent_split]
  simp only [Pi.sub_apply]
  have hi : Integrable (fun y => (t*largeMark y : ℝ) * Complex.I) (powerIntensity α) :=
    ((largeMark_integrable ha).const_mul t).ofReal.mul_const Complex.I
  rw [integral_sub (unitStableExponent_integrable hα hb t) hi, integral_mul_const,
    integral_complex_ofReal, integral_const_mul, largeMark_integral ha]
  ring

/-- The Lévy exponent for 1<α<2. -/
theorem fullyCompensatedStable_characteristic_real {α : ℝ}
    (hα : 0 < α) (ha : 1 < α) (hb : α < 2) (t : ℝ) :
    (∫ ω, Complex.exp ((t*fullyCompensatedStable α hα ω : ℝ) * Complex.I) ∂powerLaw α hα) =
      Complex.exp (∫ y in Ioi (0 : ℝ), (α*y^(-α-1) : ℝ) •
        (Complex.exp ((t*y : ℝ) * Complex.I) - 1 - (t*y : ℝ) * Complex.I)) := by
  rw [fullyCompensatedStable_characteristic hα ha hb,
    powerIntensity_integral_complex hα.le _ (by unfold compensatedExponent; fun_prop)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [compensatedExponent, extremeOfReal_val_of_pos hy, ENNReal.toReal_ofReal hy.le]

end AnnularPoissonClouds
end
end ConditionedStableLaws
