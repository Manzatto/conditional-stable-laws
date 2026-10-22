import ConditionedStableLaws.StableLawCompensated
import ConditionedStableLaws.StableScaling

/-!
# The limits are stable laws

The limits `Z_α` (`0 < α < 1`), `Z₁` and `Z_α` (`1 < α < 2`) are `α`-stable: scaling the explicit
power-density characteristic exponents gives the independent-sum stability identity directly. For `0
< α < 1` the limit `∫ y N(dy)` is known through its Laplace transform; it is identified almost
surely with `unitCompensatedStable α + α/(1-α)`, by uniqueness of limits in probability of the
cutoff integrals.
-/

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.StableIdentification

noncomputable section

open AnnularPoissonClouds StableLawSmall CompensatedPoissonLimits

theorem charFun_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : AEMeasurable Z P) (t : ℝ) :
    charFun (P.map Z) t = ∫ ω, Complex.exp ((t * Z ω : ℝ) * Complex.I) ∂P := by
  rw [charFun_apply_real, integral_map hZ
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)).aestronglyMeasurable]
  congr 1; funext ω; push_cast; ring_nf

theorem unit_exponent_eq {α : ℝ} (t : ℝ) :
    (∫ y in Ioi (0 : ℝ), (α * y ^ (-α - 1) : ℝ) •
      (Complex.exp ((t * y : ℝ) * Complex.I) - 1 - (t * (if y ≤ 1 then y else 0) : ℝ) * Complex.I))
      = Cited.powerLevyExponent α t := by
  unfold Cited.powerLevyExponent
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  by_cases h1 : y ≤ 1
  · simp only [h1, ite_true, Set.indicator, Set.mem_Icc, hy0.le, true_and, Pi.one_apply,
      Complex.real_smul]
    push_cast; ring_nf
  · simp only [h1, ite_false, Set.indicator, Set.mem_Icc, hy0.le, true_and, Complex.real_smul]
    push_cast; ring_nf

/-- `Z₁` and, more generally, the unit-compensated limits are `α`-stable. -/
theorem unitCompensatedStable_isStable {α : ℝ} (hα : 0 < α) (ha : α < 2) :
    Cited.IsStableLaw α ((powerLaw α hα).map (unitCompensatedStable α hα)) := by
  have hm := (measurable_unitCompensatedStable α hα).aemeasurable (μ := powerLaw α hα)
  have : IsProbabilityMeasure ((powerLaw α hα).map (unitCompensatedStable α hα)) :=
    (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  refine StableScaling.isStableLaw_of_powerLevyExponent hα ha 0 _ fun t => ?_
  rw [charFun_map_eq hm, unitCompensatedStable_characteristic_real hα ha, unit_exponent_eq]
  simp

/-- The fully compensated limits `Z_α`, `1 < α < 2`, are `α`-stable. -/
theorem fullyCompensatedStable_isStable {α : ℝ} (hα : 0 < α) (ha : α < 2) :
    Cited.IsStableLaw α ((powerLaw α hα).map (fullyCompensatedStable α hα)) := by
  have hm := (measurable_fullyCompensatedStable α hα).aemeasurable (μ := powerLaw α hα)
  have : IsProbabilityMeasure ((powerLaw α hα).map (fullyCompensatedStable α hα)) :=
    (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  refine StableScaling.isStableLaw_of_powerLevyExponent hα ha (-(α / (α - 1))) _ fun t => ?_
  rw [charFun_map_eq hm]
  have hsplit : ∀ ω, Complex.exp ((t * fullyCompensatedStable α hα ω : ℝ) * Complex.I) =
      Complex.exp (Complex.I * ((-(α / (α - 1)) : ℝ) * t)) *
        Complex.exp ((t * unitCompensatedStable α hα ω : ℝ) * Complex.I) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    simp only [fullyCompensatedStable]
    push_cast; ring
  simp_rw [hsplit]
  rw [integral_const_mul, unitCompensatedStable_characteristic_real hα ha, unit_exponent_eq,
    ← Complex.exp_add]

/-- `∫_{(ε,1]} y υ_α(dy) = α (1 - ε^{1-α})/(1 - α)` for `α < 1`. -/
theorem bandMark_integral_lt_one {α ε : ℝ} (hα : 0 < α) (ha : α < 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ y, bandMark ε y ∂powerIntensity α = α * (1 - ε ^ (1 - α)) / (1 - α) := by
  rw [powerIntensity_integral_real hα.le _ (measurable_bandMark ε)]
  have heq : ∀ x ∈ Ioi (0 : ℝ), α * x ^ (-α - 1) * bandMark ε (extremeOfReal x) =
      (Ioc ε 1).indicator (fun x => α * x ^ (-α)) x := by
    intro x hx
    have hx : 0 < x := hx
    by_cases h : ε < x ∧ x ≤ 1
    · rw [indicator_of_mem (show x ∈ Ioc ε 1 from h)]
      have hb : bandMark ε (extremeOfReal x) = x := by
        simp [bandMark, Set.indicator, extremeOfReal_val_of_pos hx,
          ENNReal.ofReal_lt_ofReal_iff hx, ENNReal.toReal_ofReal hx.le, h.1, h.2]
      rw [hb, Real.rpow_sub_one hx.ne']
      field_simp
    · rw [indicator_of_notMem (show x ∉ Ioc ε 1 from h)]
      have hb : bandMark ε (extremeOfReal x) = 0 := by
        simp only [bandMark, Set.indicator, extremeOfReal_val_of_pos hx, Set.mem_ofPred_eq,
          ENNReal.ofReal_lt_ofReal_iff hx, ENNReal.ofReal_le_one]
        rw [ite_eq_right h]
      rw [hb, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 (show Ioc ε 1 ⊆ Ioi 0 from fun x hx => hε.trans hx.1),
    ← intervalIntegral.integral_of_le hε1, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le hε1]; exact fun h0 => absurd h0.1 (not_le.2 hε)⟩),
    show -α + 1 = 1 - α by ring, Real.one_rpow]
  have : 1 - α ≠ 0 := by linarith
  field_simp

/-- For `0 < α < 1`, `∫ y N(dy) = unitCompensatedStable α + α/(1-α)` almost surely. -/
theorem positiveIntegral_ae_eq {α : ℝ} (hα : 0 < α) (ha : α < 1) :
    positiveIntegral =ᵐ[powerLaw α hα] fun ω => unitCompensatedStable α hα ω + α / (1 - α) := by
  have hband : Tendsto (fun k : ℕ => ∫ y, bandMark (epsCut k) y ∂powerIntensity α) atTop
      (𝓝 (α / (1 - α))) := by
    have h1α : 0 < 1 - α := by linarith
    have hp : Tendsto (fun k : ℕ => (epsCut k : ℝ) ^ (1 - α)) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (1 - α) (Or.inr h1α.le)).tendsto.comp tendsto_epsCut
      rwa [Real.zero_rpow h1α.ne'] at this
    have := ((hp.const_sub 1).const_mul α).div_const (1 - α)
    rw [sub_zero, mul_one] at this
    refine this.congr fun k => ?_
    rw [bandMark_integral_lt_one hα ha (by exact_mod_cast epsCut_pos k) (epsCut_le_one k)]
  have hjump : ∀ᵐ ω ∂powerLaw α hα, Tendsto (fun k => jumpIntegral (randomMeasure.toFun ω)
      (epsCut k)) atTop (𝓝 (positiveIntegral ω)) := by
    filter_upwards [cutIntegral_tendsto hα ha] with ω hω
    have := hω.add (jumpIntegral_sub_cutIntegral_tendsto (randomMeasure.toFun ω))
    simpa using this
  have hcut1 : TendstoInMeasure (powerLaw α hα) (fun k => unitCutoff α (epsCut k)) atTop
      (fun ω => positiveIntegral ω - α / (1 - α)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun k => (unitCutoff_aemeasurable hα _).aestronglyMeasurable)
      ?_
    filter_upwards [hjump] with ω hω
    exact hω.sub hband
  have hcut2 := unitCutoff_tendstoInMeasure hα (by linarith) (fun k => (epsCut k : ℝ))
    (fun k => by exact_mod_cast epsCut_pos k) epsCut_le_one tendsto_epsCut
  have huniq := tendstoInMeasure_ae_unique hcut1 hcut2
  filter_upwards [huniq] with ω hω
  linarith

/-- The limit `Z_α = ∫ y N(dy)` of part (i) is `α`-stable. -/
theorem positiveIntegral_isStable {α : ℝ} (hα : 0 < α) (ha : α < 1) :
    Cited.IsStableLaw α ((powerLaw α hα).map positiveIntegral) := by
  have hm := positiveIntegral_aemeasurable hα
  have : IsProbabilityMeasure ((powerLaw α hα).map positiveIntegral) := (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  refine StableScaling.isStableLaw_of_powerLevyExponent hα (by linarith) (α / (1 - α)) _ fun t => ?_
  have hu := (measurable_unitCompensatedStable α hα).aemeasurable (μ := powerLaw α hα)
  rw [Measure.map_congr (positiveIntegral_ae_eq hα ha), charFun_map_eq (hu.add_const _)]
  have hsplit : ∀ ω, Complex.exp ((t * (unitCompensatedStable α hα ω + α / (1 - α)) : ℝ) *
      Complex.I) = Complex.exp (Complex.I * ((α / (1 - α) : ℝ) * t)) *
        Complex.exp ((t * unitCompensatedStable α hα ω : ℝ) * Complex.I) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  simp_rw [hsplit]
  rw [integral_const_mul, unitCompensatedStable_characteristic_real hα (by linarith),
    unit_exponent_eq, ← Complex.exp_add]

end

end ConditionedStableLaws.StableIdentification
