import ConditionedStableLaws.PoissonCutoffIntegrals
import ConditionedStableLaws.StableLawSmall

/-!
# Compensated jump integrals of the limiting Poisson random measure

For the Poisson random measure `N` with intensity `υ_α = α y^{-α-1} dy`:

* the centring constants `∫_{(ε,1]} y υ_1(dy) = log(1/ε)` and `∫_{(ε,∞]} y υ_α(dy) = α/(α-1)
  ε^{1-α}` (`α > 1`);
* the jumps above the upper cutoff `Rₖ` vanish for every point measure;
* the cut, compensated integrals `∫_{(εₖ,Rₖ]} y N(dy) - ∫ (compensator)` converge in distribution to
  `Z₁` (`α = 1`, unit compensation) and to `Z_α` (`1 < α < 2`, full compensation), the limits in the
  stable laws for `α = 1` and `1 < α < 2`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.CompensatedPoissonLimits

noncomputable section

open AnnularPoissonClouds StableLawSmall

theorem powerIntensity_integral_real {α : ℝ} (hα : 0 ≤ α) (f : ExtremeState → ℝ)
    (hf : Measurable f) :
    ∫ y, f y ∂powerIntensity α = ∫ x in Ioi (0 : ℝ), α * x ^ (-α - 1) * f (extremeOfReal x) := by
  rw [powerIntensity, integral_map measurable_extremeOfReal.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (mul_nonneg hα (Real.rpow_nonneg hx.le _)), smul_eq_mul]

/-- `∫_{(ε,1]} y υ_1(dy) = log(1/ε)`. -/
theorem bandMark_integral_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ y, bandMark ε y ∂powerIntensity 1 = Real.log (1 / ε) := by
  rw [powerIntensity_integral_real zero_le_one _ (measurable_bandMark ε)]
  have heq : ∀ x ∈ Ioi (0 : ℝ), 1 * x ^ (-1 - 1 : ℝ) * bandMark ε (extremeOfReal x) =
      (Ioc ε 1).indicator (fun x => x⁻¹) x := by
    intro x hx
    have hx : 0 < x := hx
    by_cases h : ε < x ∧ x ≤ 1
    · rw [indicator_of_mem (show x ∈ Ioc ε 1 from h)]
      have hb : bandMark ε (extremeOfReal x) = x := by
        simp [bandMark, Set.indicator, extremeOfReal_val_of_pos hx,
          ENNReal.ofReal_lt_ofReal_iff hx, ENNReal.toReal_ofReal hx.le, h.1, h.2]
      rw [hb, show (-1 - 1 : ℝ) = -2 by norm_num, Real.rpow_neg hx.le, Real.rpow_two]
      field_simp
    · rw [indicator_of_notMem (show x ∉ Ioc ε 1 from h)]
      have hb : bandMark ε (extremeOfReal x) = 0 := by
        simp only [bandMark, Set.indicator, extremeOfReal_val_of_pos hx, Set.mem_ofPred_eq,
          ENNReal.ofReal_lt_ofReal_iff hx, ENNReal.ofReal_le_one]
        rw [ite_eq_right h]
      rw [hb, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 (show Ioc ε 1 ⊆ Ioi 0 from fun x hx => hε.trans hx.1), ← intervalIntegral.integral_of_le hε1,
    integral_inv_of_pos hε one_pos]

/-- `∫_{(ε,∞]} y υ_α(dy) = α/(α-1) ε^{1-α}` for `α > 1`. -/
theorem tailMark_integral {α ε : ℝ} (hα1 : 1 < α) (hε : 0 < ε) :
    ∫ y, tailMark ε y ∂powerIntensity α = α / (α - 1) * ε ^ (1 - α) := by
  have hα : 0 < α := zero_lt_one.trans hα1
  rw [powerIntensity_integral_real hα.le _ (measurable_tailMark ε)]
  have heq : ∀ x ∈ Ioi (0 : ℝ), α * x ^ (-α - 1) * tailMark ε (extremeOfReal x) =
      (Ioi ε).indicator (fun x => α * x ^ (-α)) x := by
    intro x hx
    have hx : 0 < x := hx
    by_cases h : ε < x
    · rw [indicator_of_mem (show x ∈ Ioi ε from h)]
      have hb : tailMark ε (extremeOfReal x) = x := by
        simp [tailMark, Set.indicator, extremeOfReal_val_of_pos hx,
          ENNReal.ofReal_lt_ofReal_iff hx, ENNReal.toReal_ofReal hx.le, h]
      rw [hb, Real.rpow_sub_one hx.ne']
      field_simp
    · rw [indicator_of_notMem (show x ∉ Ioi ε from h)]
      have hb : tailMark ε (extremeOfReal x) = 0 := by
        simp only [tailMark, Set.indicator, extremeOfReal_val_of_pos hx, Set.mem_ofPred_eq,
          ENNReal.ofReal_lt_ofReal_iff hx]
        rw [ite_eq_right h]
      rw [hb, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.2 (show Ioi ε ⊆ Ioi 0 from fun x hx => hε.trans hx), integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) hε, show -α + 1 = 1 - α by ring]
  have : α - 1 ≠ 0 := by linarith
  have : 1 - α ≠ 0 := by linarith
  field_simp
  ring

/-! ### The cutoffs -/

theorem epsCut_le_one (k : ℕ) : (epsCut k : ℝ) ≤ 1 := by
  simp only [epsCut, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
  exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by positivity)

theorem tendsto_epsCut : Tendsto (fun k : ℕ => (epsCut k : ℝ)) atTop (𝓝 0) := by
  simp only [epsCut, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_RCut : Tendsto (fun k : ℕ => (RCut k : ℝ)) atTop atTop := by
  simp only [RCut, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem one_le_RCut (k : ℕ) : (1 : ℝ≥0) ≤ RCut k := by
  unfold RCut; exact le_add_self

/-- The jumps above the upper cutoff vanish: for every point measure,
`jumpIntegral ξ εₖ - ∫_{(εₖ,Rₖ]} y ξ(dy) → 0`. -/
theorem jumpIntegral_sub_cutIntegral_tendsto (ξ : LocallyFinitePointMeasure) :
    Tendsto (fun k => jumpIntegral ξ (epsCut k) - cutIntegral k ξ) atTop (𝓝 0) := by
  set μξ := ξ.toMeasure
  have hint (ε : ℝ) (hε : 0 < ε) : Integrable (tailMark ε) μξ :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_tailMark ε).aestronglyMeasurable
      (ae_of_all _ (tailMark_nonneg ε))).mp (tailMark_lintegral_finite ξ hε).ne
  have hjump (ε : ℝ) (hε : 0 < ε) : jumpIntegral ξ ε = ∫ y, tailMark ε y ∂μξ := by
    rw [jumpIntegral, ← ofReal_integral_eq_lintegral_ofReal (hint ε hε)
      (ae_of_all _ (tailMark_nonneg ε)), ENNReal.toReal_ofReal (integral_nonneg (tailMark_nonneg ε))]
  set I : ℕ → Set ExtremeState := fun k =>
    Ioc (TruncatedPointIntegrals.endpoint (epsCut k) (epsCut_pos k))
      (TruncatedPointIntegrals.endpoint (RCut k) ((epsCut_pos k).trans_le (epsCut_le_RCut k)))
  set g : ℕ → ExtremeState → ℝ := fun k =>
    {y : ExtremeState | ((RCut k : ℝ≥0) : ℝ≥0∞) < y.val}.indicator (fun y => y.val.toReal)
  have hgm (k : ℕ) : Measurable (g k) :=
    (by fun_prop : Measurable (fun y : ExtremeState => y.val.toReal)).indicator
      (measurableSet_lt measurable_const measurable_subtype_coe)
  have hsplit (k : ℕ) (y : ExtremeState) :
      tailMark (epsCut k : ℝ) y = (I k).indicator (fun y => y.val.toReal) y + g k y := by
    have hεR : ((epsCut k : ℝ≥0) : ℝ≥0∞) ≤ ((RCut k : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.coe_le_coe.2 (epsCut_le_RCut k)
    have hofr : ENNReal.ofReal (epsCut k : ℝ) = ((epsCut k : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.ofReal_coe_nnreal
    simp only [tailMark, g, I, Set.indicator, Set.mem_ofPred_eq, mem_Ioc,
      TruncatedPointIntegrals.endpoint, ← Subtype.coe_lt_coe, ← Subtype.coe_le_coe, hofr]
    by_cases h1 : ((epsCut k : ℝ≥0) : ℝ≥0∞) < y.val
    · by_cases h2 : y.val ≤ ((RCut k : ℝ≥0) : ℝ≥0∞)
      · simp [h1, h2, not_lt.2 h2]
      · simp [h1, h2, not_le.1 h2]
    · have h3 : ¬ ((RCut k : ℝ≥0) : ℝ≥0∞) < y.val := fun h => h1 (hεR.trans_lt h)
      simp [h1, h3]
  have hIint (k : ℕ) : Integrable ((I k).indicator (fun y : ExtremeState => y.val.toReal)) μξ := by
    refine (hint (epsCut k : ℝ) (by exact_mod_cast epsCut_pos k)).mono'
      ((by fun_prop : Measurable (fun y : ExtremeState => y.val.toReal)).indicator
        measurableSet_Ioc).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) y)]
    have := hsplit k y
    have : 0 ≤ g k y := indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) y
    linarith
  have hdiff (k : ℕ) : jumpIntegral ξ (epsCut k) - cutIntegral k ξ = ∫ y, g k y ∂μξ := by
    rw [hjump (epsCut k : ℝ) (by exact_mod_cast epsCut_pos k)]
    unfold cutIntegral TruncatedPointIntegrals.truncatedIntegral
    rw [← integral_indicator measurableSet_Ioc]
    have hgi : Integrable (g k) μξ := by
      have := (hint (epsCut k : ℝ) (by exact_mod_cast epsCut_pos k)).sub (hIint k)
      refine this.congr (ae_of_all _ fun y => ?_)
      rw [Pi.sub_apply]; linarith [hsplit k y]
    rw [show (fun y => tailMark (epsCut k : ℝ) y) = fun y =>
      (I k).indicator (fun y => y.val.toReal) y + g k y from funext (hsplit k),
      integral_add (hIint k) hgi]
    ring
  simp_rw [hdiff]
  rw [show (0 : ℝ) = ∫ _y, (0 : ℝ) ∂μξ by simp]
  refine tendsto_integral_filter_of_dominated_convergence (tailMark 1)
    (Eventually.of_forall fun k => (hgm k).aestronglyMeasurable)
    (Eventually.of_forall fun k => ae_of_all _ fun y => ?_) (hint 1 one_pos)
    (ae_of_all _ fun y => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) y)]
    by_cases h : ((RCut k : ℝ≥0) : ℝ≥0∞) < y.val
    · have h1 : 1 < y.val := lt_of_le_of_lt (by exact_mod_cast one_le_RCut k) h
      simp [tailMark, Set.indicator, h, h1, ENNReal.ofReal_one]
    · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_right h]
      exact tailMark_nonneg 1 y
  · by_cases htop : y.val = ⊤
    · refine tendsto_const_nhds.congr fun k => ?_
      simp [g, htop]
    · apply tendsto_const_nhds.congr'
      have hev := tendsto_RCut.eventually (eventually_ge_atTop y.val.toReal)
      filter_upwards [hev] with k hk
      have : ¬ ((RCut k : ℝ≥0) : ℝ≥0∞) < y.val := by
        rw [not_lt, ← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hk
      simp only [g, Set.indicator, Set.mem_ofPred_eq, ite_eq_right this]

/-- The cut, unit-compensated Poisson integrals converge in distribution to
`Z₁`-type limits: `∫_{(εₖ,Rₖ]} y N(dy) - ∫_{(εₖ,1]} y υ_α(dy) → unitCompensatedStable`. -/
theorem cut_unitCompensated_tendstoInDistribution {α : ℝ} (hα : 0 < α) (ha : α < 2) :
    TendstoInDistribution (fun k ω => cutIntegral k (randomMeasure.toFun ω) -
        ∫ y, bandMark (epsCut k) y ∂powerIntensity α) atTop (unitCompensatedStable α hα)
      (fun _ => powerLaw α hα) (powerLaw α hα) := by
  have hX := (unitCutoff_tendstoInMeasure hα ha (fun k => (epsCut k : ℝ))
    (fun k => by exact_mod_cast epsCut_pos k) epsCut_le_one tendsto_epsCut).tendstoInDistribution
    (fun k => unitCutoff_aemeasurable hα _)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_
    (fun k => ((measurable_cutIntegral k).comp randomMeasure.measurable).aemeasurable.sub_const _)
  refine tendstoInMeasure_of_tendsto_ae (fun k => ?_) (ae_of_all _ fun ω => ?_)
  · exact (((measurable_cutIntegral k).comp randomMeasure.measurable).aemeasurable.sub_const _
      |>.sub (unitCutoff_aemeasurable hα _)).aestronglyMeasurable
  · have := (jumpIntegral_sub_cutIntegral_tendsto (randomMeasure.toFun ω)).neg
    rw [neg_zero] at this
    refine this.congr fun k => ?_
    simp only [Pi.sub_apply, unitCutoff]
    ring

/-- The cut, fully compensated Poisson integrals converge in distribution to
`Z_α` for `1 < α < 2`: `∫_{(εₖ,Rₖ]} y N(dy) - ∫_{(εₖ,∞]} y υ_α(dy) → fullyCompensatedStable`. -/
theorem cut_fullyCompensated_tendstoInDistribution {α : ℝ} (hα : 0 < α) (ha : 1 < α)
    (hb : α < 2) :
    TendstoInDistribution (fun k ω => cutIntegral k (randomMeasure.toFun ω) -
        ∫ y, tailMark (epsCut k) y ∂powerIntensity α) atTop (fullyCompensatedStable α hα)
      (fun _ => powerLaw α hα) (powerLaw α hα) := by
  have hX := fullCutoff_tendstoInDistribution hα ha hb (fun k => (epsCut k : ℝ))
    (fun k => by exact_mod_cast epsCut_pos k) epsCut_le_one tendsto_epsCut
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_
    (fun k => ((measurable_cutIntegral k).comp randomMeasure.measurable).aemeasurable.sub_const _)
  refine tendstoInMeasure_of_tendsto_ae (fun k => ?_) (ae_of_all _ fun ω => ?_)
  · exact (((measurable_cutIntegral k).comp randomMeasure.measurable).aemeasurable.sub_const _
      |>.sub (fullCutoff_aemeasurable hα _)).aestronglyMeasurable
  · have := (jumpIntegral_sub_cutIntegral_tendsto (randomMeasure.toFun ω)).neg
    rw [neg_zero] at this
    refine this.congr fun k => ?_
    simp only [Pi.sub_apply, fullCutoff]
    ring

end

end ConditionedStableLaws.CompensatedPoissonLimits
