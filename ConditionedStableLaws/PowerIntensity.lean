import ConditionedStableLaws.PointMeasures
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The power-law Poisson intensity

The measure α y^(-α-1) dy on (0,∞] is constructed by transporting the
Lebesgue density on the positive real line. It has no atom at infinity and
finite mass on every positive tail.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ConditionedStableLaws

noncomputable section

/-- Embed positive reals in the extreme-value state space; the value outside
the positive line is immaterial to the restricted measure below. -/
def extremeOfReal (x : ℝ) : ExtremeState :=
  if hx : 0 < x then ⟨ENNReal.ofReal x, ENNReal.ofReal_pos.mpr hx⟩
  else ⟨1, by norm_num⟩

theorem measurable_extremeOfReal : Measurable extremeOfReal := by
  apply Measurable.subtype_mk
  change Measurable (fun x : ℝ => (extremeOfReal x).val)
  have heq : (fun x : ℝ => (extremeOfReal x).val) =
      (fun x : ℝ => if 0 < x then ENNReal.ofReal x else 1) := by
    funext x
    by_cases hx : 0 < x <;> simp [extremeOfReal, hx]
  rw [heq]
  exact Measurable.ite measurableSet_Ioi ENNReal.measurable_ofReal measurable_const

theorem extremeOfReal_val_of_pos {x : ℝ} (hx : 0 < x) :
    (extremeOfReal x).val = ENNReal.ofReal x := by simp [extremeOfReal, hx]

/-- The intensity measure, including the point at infinity in its codomain, with zero mass assigned
to that point. -/
def powerIntensity (α : ℝ) : Measure ExtremeState :=
  (((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun x => ENNReal.ofReal (α * x ^ (-α - 1)))).map extremeOfReal

theorem powerIntensity_apply (α : ℝ) (A : Set ExtremeState) (hA : MeasurableSet A) :
    powerIntensity α A =
      ∫⁻ x in extremeOfReal ⁻¹' A ∩ Ioi (0 : ℝ),
        ENNReal.ofReal (α * x ^ (-α - 1)) := by
  rw [powerIntensity, Measure.map_apply measurable_extremeOfReal hA,
    withDensity_apply _ (measurable_extremeOfReal hA),
    Measure.restrict_restrict (measurable_extremeOfReal hA)]

/-- Exact strict-tail mass of the intensity. -/
theorem powerIntensity_Ioi {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    powerIntensity α {y | ENNReal.ofReal t < y.val} = ENNReal.ofReal (t ^ (-α)) := by
  have hA : MeasurableSet {y : ExtremeState | ENNReal.ofReal t < y.val} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  rw [powerIntensity_apply α _ hA]
  have hpre : extremeOfReal ⁻¹' {y | ENNReal.ofReal t < y.val} ∩ Ioi (0 : ℝ) = Ioi t := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      change ENNReal.ofReal t < (extremeOfReal x).val at hx
      rw [extremeOfReal_val_of_pos hx0, ENNReal.ofReal_lt_ofReal_iff hx0] at hx
      exact hx
    · intro hx
      have hx0 := ht.trans hx
      refine ⟨?_, hx0⟩
      change ENNReal.ofReal t < (extremeOfReal x).val
      rw [extremeOfReal_val_of_pos hx0, ENNReal.ofReal_lt_ofReal_iff hx0]
      exact hx
  rw [hpre]
  have hi : IntegrableOn (fun x : ℝ => α * x ^ (-α - 1)) (Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) ht).const_mul α
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) ht]
    rw [show -α - 1 + 1 = -α by ring]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hα.le (Real.rpow_nonneg (ht.trans hx).le _)

/-- The intensity gives no mass to the included point at infinity. -/
theorem powerIntensity_infinity (α : ℝ) :
    powerIntensity α {y | y.val = ∞} = 0 := by
  rw [powerIntensity_apply α _ (measurableSet_eq_fun measurable_subtype_coe measurable_const)]
  have hpre : extremeOfReal ⁻¹' {y | y.val = ∞} ∩ Ioi (0 : ℝ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hx0⟩
    change (extremeOfReal x).val = ∞ at hx
    rw [extremeOfReal_val_of_pos hx0] at hx
    exact ENNReal.ofReal_ne_top hx
  rw [hpre]
  simp

/-- The intensity is atomless, including at every finite point. -/
theorem powerIntensity_singleton (α : ℝ) (z : ExtremeState) :
    powerIntensity α {z} = 0 := by
  rw [powerIntensity_apply α _ (measurableSet_singleton z)]
  have hsub : extremeOfReal ⁻¹' {z} ∩ Ioi (0 : ℝ) ⊆ {z.val.toReal} := by
    rintro x ⟨hx, hx0⟩
    have hv : (extremeOfReal x).val = z.val := congrArg Subtype.val hx
    have heq : z.val.toReal = x := by
      rw [← hv, extremeOfReal_val_of_pos hx0, ENNReal.toReal_ofReal hx0.le]
    exact heq.symm
  have hnull : (volume : Measure ℝ) (extremeOfReal ⁻¹' {z} ∩ Ioi (0 : ℝ)) = 0 :=
    measure_mono_null hsub (measure_singleton _)
  rw [Measure.restrict_eq_zero.mpr hnull]
  simp

/-- Finite half-open intervals have the difference of the power tails as
their exact intensity, matching the rare-event interval normalization. -/
theorem powerIntensity_interval {α a b : ℝ}
    (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) :
    powerIntensity α {y | ENNReal.ofReal a < y.val ∧ y.val ≤ ENNReal.ofReal b} =
      ENNReal.ofReal (a ^ (-α)) - ENNReal.ofReal (b ^ (-α)) := by
  have hb : 0 < b := ha.trans_le hab
  have hset : {y : ExtremeState | ENNReal.ofReal a < y.val ∧ y.val ≤ ENNReal.ofReal b} =
      {y | ENNReal.ofReal a < y.val} \ {y | ENNReal.ofReal b < y.val} := by
    ext y
    simp only [mem_ofPred_eq, mem_sdiff, not_lt]
  rw [hset, measure_sdiff]
  · rw [powerIntensity_Ioi hα ha, powerIntensity_Ioi hα hb]
  · intro y hy
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hab) hy
  · exact (measurableSet_lt measurable_const measurable_subtype_coe).nullMeasurableSet
  · rw [powerIntensity_Ioi hα hb]
    exact ENNReal.ofReal_ne_top

/-- Positive closed tails have finite intensity. -/
theorem powerIntensity_tail_lt_top {α : ℝ} (hα : 0 < α) (ε : ℝ≥0) (hε : 0 < ε) :
    powerIntensity α (extremeTail ε) < ∞ := by
  have hhalf : 0 < (ε : ℝ) / 2 := by exact half_pos (by exact_mod_cast hε)
  apply lt_of_le_of_lt (measure_mono ?_)
    (show powerIntensity α {y | ENNReal.ofReal ((ε : ℝ) / 2) < y.val} < ∞ by
      rw [powerIntensity_Ioi hα hhalf]; exact ENNReal.ofReal_lt_top)
  intro y hy
  change (ε : ℝ≥0∞) ≤ y.val at hy
  change ENNReal.ofReal ((ε : ℝ) / 2) < y.val
  apply lt_of_lt_of_le ?_ hy
  have hεreal : (0 : ℝ) < ε := by exact_mod_cast hε
  have hlt := (ENNReal.ofReal_lt_ofReal_iff hεreal).mpr (half_lt_self hεreal)
  simpa using hlt

instance powerIntensity_nullSingletonClass (α : ℝ) : NullSingletonClass (powerIntensity α) :=
  ⟨powerIntensity_singleton α⟩

/-- Finite positive tails give the ordinary topological local finiteness. -/
theorem powerIntensity_isLocallyFinite {α : ℝ} (hα : 0 < α) :
    IsLocallyFiniteMeasure (powerIntensity α) := by
  constructor
  intro y
  obtain ⟨ε, hε, hεy⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp y.property
  have hεpos : 0 < ε := by exact_mod_cast hε
  refine ⟨{z : ExtremeState | (ε : ℝ≥0∞) < z.val},
    (isOpen_lt continuous_const continuous_subtype_val).mem_nhds hεy, ?_⟩
  exact lt_of_le_of_lt
    (measure_mono (show {z : ExtremeState | (ε : ℝ≥0∞) < z.val} ⊆ extremeTail ε
      from fun z hz => show (ε : ℝ≥0∞) ≤ z.val from
        (show (ε : ℝ≥0∞) < z.val from hz).le))
    (powerIntensity_tail_lt_top hα ε hεpos)

end
end ConditionedStableLaws
