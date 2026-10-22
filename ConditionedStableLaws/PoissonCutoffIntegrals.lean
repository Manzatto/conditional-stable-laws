import ConditionedStableLaws.CompensatedStableLaw
import ConditionedStableLaws.CompensatedIntegralIdentities

/-!
Cutoff integrals of the same Poisson random measure.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

def bandMark (ε : ℝ) : ExtremeState → ℝ :=
  {y : ExtremeState | ENNReal.ofReal ε < y.val ∧ y.val ≤ 1}.indicator (fun y => y.val.toReal)

theorem measurable_bandMark (ε : ℝ) : Measurable (bandMark ε) :=
  (by fun_prop : Measurable (fun y : ExtremeState => y.val.toReal)).indicator
    ((measurableSet_lt measurable_const measurable_subtype_coe).inter
      (measurableSet_le measurable_subtype_coe measurable_const))

theorem bandMark_nonneg (ε : ℝ) (y : ExtremeState) : 0 ≤ bandMark ε y := by
  apply Set.indicator_nonneg
  exact fun _ _ => ENNReal.toReal_nonneg

theorem bandMark_le_smallMark (ε : ℝ) (y : ExtremeState) : bandMark ε y ≤ smallMark 1 y := by
  by_cases hy : ENNReal.ofReal ε < y.val ∧ y.val ≤ 1
  · simp [bandMark, smallMark, hy]
  · simpa [bandMark, hy] using smallMark_nonneg 1 y

theorem norm_bandMark_le (ε : ℝ) (y : ExtremeState) : ‖bandMark ε y‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (bandMark_nonneg ε y)]
  exact (bandMark_le_smallMark ε y).trans ((le_abs_self _).trans (norm_smallMark_le zero_le_one y))

theorem bandMark_eq_sub {ε : ℝ} (hε : ε ≤ 1) (y : ExtremeState) :
    bandMark ε y = smallMark 1 y-smallMark ε y := by
  have he : ENNReal.ofReal ε ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hε
  by_cases hy : y.val ≤ ENNReal.ofReal ε
  · simp [bandMark, smallMark, hy, hy.trans he, not_lt.mpr hy]
  · by_cases hy1 : y.val ≤ 1
    · simp [bandMark, smallMark, hy, hy1, not_le.mp hy]
    · simp [bandMark, smallMark, hy, hy1]

theorem bandMark_integrable {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    Integrable (bandMark ε) (powerIntensity α) := by
  let A : Set ExtremeState := {y | ENNReal.ofReal ε < y.val ∧ y.val ≤ 1}
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_subtype_coe).inter
    (measurableSet_le measurable_subtype_coe measurable_const)
  have : IsFiniteMeasure ((powerIntensity α).restrict A) := ⟨by
    rw [Measure.restrict_apply_univ]
    have ht : powerIntensity α {y : ExtremeState | ENNReal.ofReal ε < y.val} < ∞ := by
      rw [powerIntensity_Ioi hα hε]
      exact ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt (measure_mono (show A ⊆
      {y : ExtremeState | ENNReal.ofReal ε < y.val} from fun _ hy => hy.1)) ht⟩
  change Integrable (A.indicator (fun y => y.val.toReal)) (powerIntensity α)
  rw [integrable_indicator_iff hA]
  apply Integrable.of_bound (show AEStronglyMeasurable (fun y : ExtremeState => y.val.toReal)
    ((powerIntensity α).restrict A) from (show Measurable _ by fun_prop).aestronglyMeasurable) 1
  filter_upwards [ae_restrict_mem hA] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono (by simp) hy.2).trans_eq ENNReal.toReal_one

theorem bandMark_square_integrable {α ε : ℝ} (hα : 0 < α) (ha : α < 2) :
    Integrable (fun y => (bandMark ε y)^2) (powerIntensity α) := by
  apply (smallMark_square_integrable hα ha zero_lt_one).mono'
    ((measurable_bandMark ε).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (bandMark_nonneg ε y) (bandMark_le_smallMark ε y) 2)

def tailMark (ε : ℝ) : ExtremeState → ℝ :=
  {y : ExtremeState | ENNReal.ofReal ε < y.val}.indicator (fun y => y.val.toReal)

theorem measurable_tailMark (ε : ℝ) : Measurable (tailMark ε) :=
  (by fun_prop : Measurable (fun y : ExtremeState => y.val.toReal)).indicator
    (measurableSet_lt measurable_const measurable_subtype_coe)

theorem tailMark_nonneg (ε : ℝ) (y : ExtremeState) : 0 ≤ tailMark ε y := by
  apply Set.indicator_nonneg
  exact fun _ _ => ENNReal.toReal_nonneg

theorem tailMark_eq_large_add_band {ε : ℝ} (hε : ε ≤ 1) (y : ExtremeState) :
    tailMark ε y = largeMark y+bandMark ε y := by
  have he : ENNReal.ofReal ε ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hε
  by_cases hy : y.val ≤ 1
  · by_cases hye : ENNReal.ofReal ε < y.val <;>
      simp [tailMark, largeMark, bandMark, hy, not_lt.mpr hy, hye]
  · have hy1 := not_le.mp hy
    have hye := he.trans_lt hy1
    simp [tailMark, largeMark, bandMark, hy, hy1, hye]

theorem tailMark_lintegral_finite (ξ : LocallyFinitePointMeasure) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ y, ENNReal.ofReal (tailMark ε y) ∂ξ.toMeasure) < ∞ := by
  have hA : MeasurableSet {y : ExtremeState | ENNReal.ofReal ε < y.val} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  have he : (fun y => ENNReal.ofReal (tailMark ε y)) =
      {y : ExtremeState | ENNReal.ofReal ε < y.val}.indicator positiveMark := by
    funext y
    by_cases hy : ENNReal.ofReal ε < y.val <;> simp [tailMark, positiveMark, hy]
  rw [he, lintegral_indicator hA]
  let e : ℝ≥0 := ⟨ε, hε.le⟩
  have hee : (e : ℝ≥0∞) = ENNReal.ofReal ε :=
    (show ENNReal.ofReal (e : ℝ) = (e : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal).symm
  exact ξ.atomic.setLIntegral_lt_top_of_finite_mass _ hA
    (lt_of_le_of_lt (measure_mono (show {y : ExtremeState | ENNReal.ofReal ε < y.val} ⊆ extremeTail e from
      fun y hy => by change (e : ℝ≥0∞) ≤ y.val; rw [hee]; exact hy.le))
      (ξ.finite_tail e (by exact_mod_cast hε)))
    positiveMark measurable_positiveMark (fun y _ => positiveMark_ne_top y)

/-- The finite sum of marks strictly above a positive cutoff. -/
def jumpIntegral (ξ : LocallyFinitePointMeasure) (ε : ℝ) : ℝ :=
  (∫⁻ y, ENNReal.ofReal (tailMark ε y) ∂ξ.toMeasure).toReal

theorem jumpIntegral_eq_setIntegral (ξ : LocallyFinitePointMeasure) {ε : ℝ} (hε : 0 < ε) :
    jumpIntegral ξ ε = ∫ y in {y : ExtremeState | ENNReal.ofReal ε < y.val}, y.val.toReal ∂ξ.toMeasure := by
  have hi : Integrable (tailMark ε) ξ.toMeasure :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_tailMark ε).aestronglyMeasurable
      (ae_of_all _ (tailMark_nonneg ε))).mp (tailMark_lintegral_finite ξ hε).ne
  rw [jumpIntegral, ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (tailMark_nonneg ε)),
    ENNReal.toReal_ofReal (integral_nonneg (tailMark_nonneg ε)), tailMark,
    integral_indicator (measurableSet_lt measurable_const measurable_subtype_coe)]

theorem jumpIntegral_eq_large_add_band (ξ : LocallyFinitePointMeasure) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    jumpIntegral ξ ε = (∫⁻ y, ENNReal.ofReal (largeMark y) ∂ξ.toMeasure).toReal +
      (∫⁻ y, ENNReal.ofReal (bandMark ε y) ∂ξ.toMeasure).toReal := by
  have hb : (∫⁻ y, ENNReal.ofReal (bandMark ε y) ∂ξ.toMeasure) < ∞ :=
    lt_of_le_of_lt (lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (by
      rw [tailMark_eq_large_add_band hε1]
      exact le_add_of_nonneg_left (largeMark_nonneg y)))) (tailMark_lintegral_finite ξ hε)
  unfold jumpIntegral
  have hl : (∫⁻ y, ENNReal.ofReal (largeMark y) ∂ξ.toMeasure) < ∞ := by
    simpa only [tailMark, largeMark, ENNReal.ofReal_one] using
      tailMark_lintegral_finite ξ zero_lt_one
  simp_rw [tailMark_eq_large_add_band hε1, ENNReal.ofReal_add (largeMark_nonneg _) (bandMark_nonneg ε _)]
  rw [lintegral_add_left measurable_largeMark.ennreal_ofReal, ENNReal.toReal_add hl.ne hb.ne]

namespace AnnularPoissonClouds

theorem component_testIntegral_congr_ae
    (υ : Measure ExtremeState) (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)
    (n : ℕ) (f g : ExtremeState → ℝ) (he : ∀ y ∈ annulus n, f y = g y) :
    (fun ω : Sample => FinitePoissonCloud.testIntegral f (ω n)) =ᵐ[law υ hυ]
      (fun ω => FinitePoissonCloud.testIntegral g (ω n)) := by
  filter_upwards [supported_components_ae υ hυ] with ω hω
  have ha : ∀ᵐ y ∂((component n).toFun ω).toMeasure, y ∈ annulus n := by
    rw [ae_iff]
    exact hω n
  exact integral_congr_ae (ha.mono he)

theorem largeMark_lintegral_finite (ξ : LocallyFinitePointMeasure) :
    (∫⁻ y, ENNReal.ofReal (largeMark y) ∂ξ.toMeasure) < ∞ := by
  have hA : MeasurableSet {y : ExtremeState | 1 < y.val} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  have he : (fun y => ENNReal.ofReal (largeMark y)) =
      {y : ExtremeState | 1 < y.val}.indicator positiveMark := by
    funext y
    by_cases hy : 1 < y.val <;> simp [largeMark, positiveMark, hy]
  rw [he, lintegral_indicator hA]
  exact ξ.atomic.setLIntegral_lt_top_of_finite_mass _ hA
    (lt_of_le_of_lt (measure_mono (show {y : ExtremeState | 1 < y.val} ⊆ extremeTail 1 from
      fun y hy => by change (1 : ℝ≥0∞) ≤ y.val; exact hy.le)) (ξ.finite_tail 1 zero_lt_one))
    positiveMark measurable_positiveMark (fun y _ => positiveMark_ne_top y)

/-- The initial cloud is precisely the large-jump integral of the same
superposed random measure, almost surely. -/
theorem largeCloud_eq_integral_ae
    (υ : Measure ExtremeState) (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞) :
    (fun ω : Sample => FinitePoissonCloud.testIntegral (fun y => y.val.toReal) (ω 0)) =ᵐ[law υ hυ]
      (fun ω => (∫⁻ y, ENNReal.ofReal (largeMark y) ∂(randomMeasure.toFun ω).toMeasure).toReal) := by
  have ht := component_testIntegral_tendsto υ hυ largeMark measurable_largeMark largeMark_nonneg
    (ae_of_all _ (fun ω => largeMark_lintegral_finite (randomMeasure.toFun ω)))
  have hzero := component_testIntegral_congr_ae υ hυ 0 largeMark (fun y => y.val.toReal)
    (fun y hy => by
      rw [annulus_zero] at hy
      change 1 < y.val at hy
      simp [largeMark, hy])
  have hother (n : ℕ) : (fun ω : Sample => FinitePoissonCloud.testIntegral largeMark (ω (n+1))) =ᵐ[law υ hυ]
      (fun _ => 0) := by
    have he := component_testIntegral_congr_ae υ hυ (n+1) largeMark (fun _ => 0) (fun y hy => by
      rw [annulus_succ] at hy
      have hn : cutoff n ≤ 1 := by
        simp [cutoff]
      have hy1 : y.val ≤ 1 := hy.2.trans (by exact_mod_cast hn)
      simp [largeMark, not_lt.mpr hy1])
    simpa only [FinitePoissonCloud.testIntegral, integral_zero] using he
  filter_upwards [ht, hzero, ae_all_iff.mpr hother] with ω hω hω0 hωother
  have hp : Tendsto (fun n => ∑ i ∈ Finset.range n, FinitePoissonCloud.testIntegral largeMark (ω i))
      atTop (𝓝 (FinitePoissonCloud.testIntegral (fun y => y.val.toReal) (ω 0))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    symm
    rw [Finset.sum_eq_single 0]
    · exact hω0
    · intro i _ hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      exact hωother j
    · intro hi
      exact (hi (Finset.mem_range.mpr hn)).elim
  exact tendsto_nhds_unique hp hω

theorem smallJumps_sub_eq_band_ae {α ε : ℝ}
    (hα : 0 < α) (ha : α < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (fun ω => compensatedSmallJumps α 1 hα zero_le_one ω -
      compensatedSmallJumps α ε hα hε.le ω) =ᵐ[powerLaw α hα]
      (fun ω => (∫⁻ y, ENNReal.ofReal (bandMark ε y)
        ∂(randomMeasure.toFun ω).toMeasure).toReal - ∫ y, bandMark ε y ∂powerIntensity α) := by
  have hbε : ∀ y, ‖smallMark ε y‖ ≤ 1 := fun y => (norm_smallMark_le hε.le y).trans hε1
  have he := compensatedIntegral_sub_ae (powerIntensity α) (powerIntensity_tail_lt_top hα)
    (smallMark 1) (smallMark ε) (bandMark ε) (measurable_smallMark 1) (measurable_smallMark ε)
    (measurable_bandMark ε) zero_le_one (norm_smallMark_le zero_le_one) hbε (norm_bandMark_le ε)
    (smallMark_square_integrable hα ha zero_lt_one) (smallMark_square_integrable hα ha hε)
    (bandMark_square_integrable hα ha) (bandMark_eq_sub hε1)
  have he' := compensatedIntegral_eq_centered_integral_ae (powerIntensity α) (powerIntensity_tail_lt_top hα)
    (bandMark ε) (measurable_bandMark ε) (bandMark_nonneg ε) zero_le_one (norm_bandMark_le ε)
    (bandMark_integrable hα hε) (bandMark_square_integrable hα ha)
  exact he.symm.trans he'

/-- The exact cutoff expression with compensation only in (ε,1]. -/
def unitCutoff (α ε : ℝ) (ω : Sample) : ℝ :=
  jumpIntegral (randomMeasure.toFun ω) ε - ∫ y, bandMark ε y ∂powerIntensity α

theorem unitCutoff_eq_setIntegrals (α : ℝ) {ε : ℝ} (hε : 0 < ε) (ω : Sample) :
    unitCutoff α ε ω =
      (∫ y in {y : ExtremeState | ENNReal.ofReal ε < y.val}, y.val.toReal
        ∂(randomMeasure.toFun ω).toMeasure) -
      ∫ y in {y : ExtremeState | ENNReal.ofReal ε < y.val ∧ y.val ≤ 1}, y.val.toReal ∂powerIntensity α := by
  rw [unitCutoff, jumpIntegral_eq_setIntegral _ hε, bandMark]
  rw [integral_indicator (show MeasurableSet
    {y : ExtremeState | ENNReal.ofReal ε < y.val ∧ y.val ≤ 1} from
      (measurableSet_lt measurable_const measurable_subtype_coe).inter
        (measurableSet_le measurable_subtype_coe measurable_const))]

theorem unitCutoff_eq_ae {α ε : ℝ} (hα : 0 < α) (ha : α < 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    unitCutoff α ε =ᵐ[powerLaw α hα]
      (fun ω => unitCompensatedStable α hα ω-compensatedSmallJumps α ε hα hε.le ω) := by
  filter_upwards [largeCloud_eq_integral_ae (powerIntensity α) (powerIntensity_tail_lt_top hα),
    smallJumps_sub_eq_band_ae hα ha hε hε1] with ω hbig hsmall
  change jumpIntegral (randomMeasure.toFun ω) ε - _ = _
  rw [jumpIntegral_eq_large_add_band _ hε hε1, ← hbig]
  change _ = FinitePoissonCloud.testIntegral (fun y => y.val.toReal) (ω 0) +
    compensatedSmallJumps α 1 hα zero_le_one ω - compensatedSmallJumps α ε hα hε.le ω
  linarith

theorem unitCutoff_aemeasurable {α : ℝ} (hα : 0 < α) (ε : ℝ) :
    AEMeasurable (unitCutoff α ε) (powerLaw α hα) :=
  ((aemeasurable_lintegral (powerIntensity α) (powerIntensity_tail_lt_top hα) _
    (measurable_tailMark ε).ennreal_ofReal).ennreal_toReal).sub_const _

/-- The compensated cutoff integrals converge in probability as the cutoff tends to zero, on the
original Poisson probability space. -/
theorem unitCutoff_tendstoInMeasure {ι : Type*} {l : Filter ι} {α : ℝ}
    (hα : 0 < α) (ha : α < 2) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hε1 : ∀ i, ε i ≤ 1)
    (he : Tendsto ε l (𝓝 0)) :
    TendstoInMeasure (powerLaw α hα) (fun i => unitCutoff α (ε i)) l (unitCompensatedStable α hα) := by
  have hs := compensatedSmallJumps_tendstoInMeasure hα ha ε hε he
  have ht : TendstoInMeasure (powerLaw α hα)
      (fun i ω => unitCompensatedStable α hα ω-compensatedSmallJumps α (ε i) hα (hε i).le ω)
      l (unitCompensatedStable α hα) := by
    rw [tendstoInMeasure_iff_dist] at hs ⊢
    intro t ht
    simpa only [Real.dist_eq, sub_zero, sub_sub_cancel_left, abs_neg] using hs t ht
  exact TendstoInMeasure.congr (fun i => (unitCutoff_eq_ae hα ha (hε i) (hε1 i)).symm)
    EventuallyEq.rfl ht

theorem unitCutoff_tendstoInDistribution {α : ℝ}
    (hα : 0 < α) (ha : α < 2) (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hε1 : ∀ i, ε i ≤ 1)
    (he : Tendsto ε atTop (𝓝 0)) :
    TendstoInDistribution (fun i => unitCutoff α (ε i)) atTop (unitCompensatedStable α hα)
      (fun _ => powerLaw α hα) (powerLaw α hα) :=
  (unitCutoff_tendstoInMeasure hα ha ε hε hε1 he).tendstoInDistribution
    (fun i => unitCutoff_aemeasurable hα (ε i))

/-- The exact cutoff expression with compensation of every jump above ε. -/
def fullCutoff (α ε : ℝ) (ω : Sample) : ℝ :=
  jumpIntegral (randomMeasure.toFun ω) ε - ∫ y, tailMark ε y ∂powerIntensity α

theorem fullCutoff_eq_unitCutoff_sub {α ε : ℝ} (ha : 1 < α) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ω : Sample) : fullCutoff α ε ω = unitCutoff α ε ω - α/(α-1) := by
  have he : tailMark ε = fun y => largeMark y+bandMark ε y := funext (tailMark_eq_large_add_band hε1)
  rw [fullCutoff, unitCutoff, he, integral_add (largeMark_integrable ha)
    (bandMark_integrable (zero_lt_one.trans ha) hε), largeMark_integral ha]
  ring

theorem fullCutoff_eq_setIntegrals (α : ℝ) {ε : ℝ} (hε : 0 < ε) (ω : Sample) :
    fullCutoff α ε ω =
      (∫ y in {y : ExtremeState | ENNReal.ofReal ε < y.val}, y.val.toReal
        ∂(randomMeasure.toFun ω).toMeasure) -
      ∫ y in {y : ExtremeState | ENNReal.ofReal ε < y.val}, y.val.toReal ∂powerIntensity α := by
  rw [fullCutoff, jumpIntegral_eq_setIntegral _ hε, tailMark,
    integral_indicator (measurableSet_lt measurable_const measurable_subtype_coe)]

theorem fullCutoff_aemeasurable {α : ℝ} (hα : 0 < α) (ε : ℝ) :
    AEMeasurable (fullCutoff α ε) (powerLaw α hα) :=
  ((aemeasurable_lintegral (powerIntensity α) (powerIntensity_tail_lt_top hα) _
    (measurable_tailMark ε).ennreal_ofReal).ennreal_toReal).sub_const _

/-- The full-compensation cutoff limit for 1<α<2. -/
theorem fullCutoff_tendstoInMeasure {ι : Type*} {l : Filter ι} {α : ℝ}
    (hα : 0 < α) (ha : 1 < α) (hb : α < 2)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hε1 : ∀ i, ε i ≤ 1) (he : Tendsto ε l (𝓝 0)) :
    TendstoInMeasure (powerLaw α hα) (fun i => fullCutoff α (ε i)) l (fullyCompensatedStable α hα) := by
  have ht := unitCutoff_tendstoInMeasure hα hb ε hε hε1 he
  rw [tendstoInMeasure_iff_dist] at ht ⊢
  intro t ht0
  simpa only [fullCutoff_eq_unitCutoff_sub ha (hε _) (hε1 _), fullyCompensatedStable,
    dist_sub_right] using ht t ht0

theorem fullCutoff_tendstoInDistribution {α : ℝ}
    (hα : 0 < α) (ha : 1 < α) (hb : α < 2)
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hε1 : ∀ i, ε i ≤ 1) (he : Tendsto ε atTop (𝓝 0)) :
    TendstoInDistribution (fun i => fullCutoff α (ε i)) atTop (fullyCompensatedStable α hα)
      (fun _ => powerLaw α hα) (powerLaw α hα) :=
  (fullCutoff_tendstoInMeasure hα ha hb ε hε hε1 he).tendstoInDistribution
    (fun i => fullCutoff_aemeasurable hα (ε i))

end AnnularPoissonClouds
end
end ConditionedStableLaws
