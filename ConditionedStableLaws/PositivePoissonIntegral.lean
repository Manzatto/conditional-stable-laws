import ConditionedStableLaws.PoissonCampbell
import ConditionedStableLaws.PowerIntensityMoments

/-!
Uncompensated Poisson integrals for tail indices below one.
-/

open MeasureTheory ProbabilityTheory Set Filter Classical
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

/-- A finite number of unit atoms integrates every finite nonnegative
function to a finite value; boundedness of the function is unnecessary. -/
theorem IsPointMeasure.setLIntegral_lt_top_of_finite_mass {μ : Measure ExtremeState}
    (hμ : IsPointMeasure μ) (A : Set ExtremeState) (hA : MeasurableSet A)
    (hfinite : μ A < ∞) (f : ExtremeState → ℝ≥0∞) (hf : Measurable f)
    (hft : ∀ x ∈ A, f x ≠ ∞) : (∫⁻ x in A, f x ∂μ) < ∞ := by
  obtain ⟨J, hJ, a, rfl⟩ := hμ
  have : Countable J := hJ
  let : MeasurableSpace J := ⊤
  have hm : MeasurableSet {j : J | a j ∈ A} := trivial
  have he : (Measure.sum (fun j => Measure.dirac (a j))) A =
      Measure.count {j : J | a j ∈ A} := by
    simp only [Measure.count, Measure.sum_apply_of_countable]
    apply tsum_congr
    intro j
    simp [Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hm, Set.indicator_apply]
  rw [he] at hfinite
  have hs := (Measure.count_apply_lt_top' hm).mp hfinite
  rw [← lintegral_indicator hA, lintegral_sum_measure]
  simp_rw [lintegral_dirac' _ (hf.indicator hA)]
  rw [tsum_eq_sum (s := hs.toFinset) (fun j hj =>
    Set.indicator_of_notMem (by simpa using hj) f)]
  apply ENNReal.sum_lt_top.mpr
  intro j hj
  have hjA : a j ∈ A := by simpa using hj
  rw [Set.indicator_of_mem hjA]
  exact (hft _ hjA).lt_top

/-- A finite real mark represented nonnegatively; it agrees with the extended mark away from
infinity. -/
def positiveMark (y : ExtremeState) : ℝ≥0∞ := ENNReal.ofReal y.val.toReal

theorem measurable_positiveMark : Measurable positiveMark := by unfold positiveMark; fun_prop

theorem positiveMark_ne_top (y : ExtremeState) : positiveMark y ≠ ∞ := ENNReal.ofReal_ne_top

theorem positiveMark_eq (y : ExtremeState) (hy : y.val ≠ ∞) : positiveMark y = y.val :=
  ENNReal.ofReal_toReal hy

namespace AnnularPoissonClouds

/-- The canonical probability law carrying the power-law Poisson measure. -/
def powerLaw (α : ℝ) (hα : 0 < α) : Measure Sample :=
  law (powerIntensity α) (powerIntensity_tail_lt_top hα)

instance powerLaw_probability (α : ℝ) (hα : 0 < α) : IsProbabilityMeasure (powerLaw α hα) := by
  unfold powerLaw
  infer_instance

/-- The expected small-jump mass, with its exact decay rate. -/
theorem small_jump_mean {α ε : ℝ} (hα : 0 < α) (ha : α < 1) (hε : 0 < ε) :
    (∫⁻ ω : Sample, ∫⁻ y in {y : ExtremeState | y.val ≤ ENNReal.ofReal ε},
      positiveMark y ∂(randomMeasure.toFun ω).toMeasure ∂powerLaw α hα) =
      ENNReal.ofReal (α / (1 - α) * ε ^ (1 - α)) := by
  have hm : MeasurableSet {y : ExtremeState | y.val ≤ ENNReal.ofReal ε} :=
    measurableSet_le measurable_subtype_coe measurable_const
  simp_rw [← lintegral_indicator hm]
  rw [show powerLaw α hα = law (powerIntensity α) (powerIntensity_tail_lt_top hα) from rfl,
    campbell _ _ _ (measurable_positiveMark.indicator hm), lintegral_indicator hm]
  simpa only [positiveMark, Real.rpow_one] using powerIntensity_small_moment hα ha hε

/-- For `0<α<1`, the total mark sum is finite almost surely. Small marks are
controlled by their expectation, and large marks by local finiteness. -/
theorem total_positiveMark_finite {α : ℝ} (hα : 0 < α) (ha : α < 1) :
    ∀ᵐ ω ∂powerLaw α hα,
      (∫⁻ y, positiveMark y ∂(randomMeasure.toFun ω).toMeasure) < ∞ := by
  let A : Set ExtremeState := {y | y.val ≤ 1}
  have hA : MeasurableSet A := measurableSet_le measurable_subtype_coe measurable_const
  have hm : AEMeasurable (fun ω : Sample => ∫⁻ y in A, positiveMark y
      ∂(randomMeasure.toFun ω).toMeasure) (powerLaw α hα) := by
    simp_rw [← lintegral_indicator hA]
    exact aemeasurable_lintegral _ _ _ (measurable_positiveMark.indicator hA)
  have hi : (∫⁻ ω : Sample, ∫⁻ y in A, positiveMark y
      ∂(randomMeasure.toFun ω).toMeasure ∂powerLaw α hα) ≠ ∞ := by
    have hh := small_jump_mean hα ha (show (0 : ℝ) < 1 by norm_num)
    simp only [ENNReal.ofReal_one] at hh
    exact hh.trans_ne ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' hm hi] with ω hω
  rw [← lintegral_add_compl positiveMark hA]
  apply ENNReal.add_lt_top.mpr
  refine ⟨hω, ?_⟩
  apply (randomMeasure.toFun ω).atomic.setLIntegral_lt_top_of_finite_mass Aᶜ hA.compl
    (lt_of_le_of_lt (measure_mono ?_) ((randomMeasure.toFun ω).finite_tail 1 (by norm_num)))
    positiveMark measurable_positiveMark (fun y _ => positiveMark_ne_top y)
  intro y hy
  change ¬ y.val ≤ 1 at hy
  exact (not_le.mp hy).le

/-- The power-law Poisson measure has no atom at the added infinity point. -/
theorem infinity_mass_zero_ae {α : ℝ} (hα : 0 < α) :
    ∀ᵐ ω ∂powerLaw α hα,
      (randomMeasure.toFun ω).toMeasure {y : ExtremeState | y.val = ∞} = 0 :=
  mass_zero_ae_of_intensity_zero _ _ _
    (measurableSet_eq_fun measurable_subtype_coe measurable_const) (powerIntensity_infinity α)

/-- The extended mark integral is the finite-mark integral almost surely; the infinity point is a
null set. -/
theorem mark_integral_eq_ae {α : ℝ} (hα : 0 < α) :
    (fun ω => ∫⁻ y : ExtremeState, y.val ∂(randomMeasure.toFun ω).toMeasure) =ᵐ[powerLaw α hα]
      (fun ω => ∫⁻ y, positiveMark y ∂(randomMeasure.toFun ω).toMeasure) := by
  filter_upwards [infinity_mass_zero_ae hα] with ω hω
  apply lintegral_congr_ae
  have hy : ∀ᵐ y ∂(randomMeasure.toFun ω).toMeasure, y.val ≠ ∞ := by
    rw [ae_iff]
    simpa only [not_not] using hω
  exact hy.mono (fun y hy => (positiveMark_eq y hy).symm)

/-- The positive Poisson integral in the stable-law statement is finite almost surely when `0<α<1`.
-/
theorem total_mark_finite {α : ℝ} (hα : 0 < α) (ha : α < 1) :
    ∀ᵐ ω ∂powerLaw α hα,
      (∫⁻ y : ExtremeState, y.val ∂(randomMeasure.toFun ω).toMeasure) < ∞ := by
  filter_upwards [mark_integral_eq_ae hα, total_positiveMark_finite hα ha] with ω he hf
  rwa [he]

/-- The real-valued limit is the uncompensated Poisson integral, which is finite almost surely. -/
def positiveIntegral (ω : Sample) : ℝ :=
  (∫⁻ y : ExtremeState, y.val ∂(randomMeasure.toFun ω).toMeasure).toReal

theorem positiveIntegral_aemeasurable {α : ℝ} (hα : 0 < α) :
    AEMeasurable positiveIntegral (powerLaw α hα) :=
  (aemeasurable_lintegral _ _ (fun y : ExtremeState => y.val) measurable_subtype_coe).ennreal_toReal

end AnnularPoissonClouds
end
end ConditionedStableLaws
