import ConditionedStableLaws.SmallJumpMoment

/-! Comparing truncated second moments in the quasi-stationary and quasi-ergodic laws. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
noncomputable section
namespace ConditionedStableLaws.ContinuousMultiplier
open StandingHypothesis SecondMoment SmallJumpMoment
variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {K : KilledKernel M}

omit [BorelSpace M] in
/-- A lower bound for η where f is large transfers truncated second moments from ν to μ.
The bounded region contributes only T², uniformly in the truncation level. -/
theorem trunc_second_moment_mu_le
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    {f : M → ℝ} (hfm : Measurable f) (hf : ∀ y, 0 ≤ f y)
    {T a : ℝ} (_hT : 0 ≤ T) (ha : 0 < a)
    (hlower : ∀ y, T < f y → a ≤ (d.weight y).toReal)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ y, trunc f t y ^ 2 ∂μ) ≤
      a⁻¹ * (∫ y, trunc f t y ^ 2 ∂μ.withDensity d.weight) + T ^ 2 := by
  have hb : ∀ y, |trunc f t y| ≤ t := fun y => by
    rw [abs_of_nonneg (trunc_nonneg hf t y)]
    exact trunc_le ht y
  have htm := measurable_trunc hfm t
  have hti : Integrable (fun y => trunc f t y ^ 2) μ :=
    integrable_of_bdd (htm.pow_const 2) (sq_bdd hb)
  obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound d hc
  have hw : Measurable fun y => (d.weight y).toReal := d.measurable_weight.ennreal_toReal
  have hwi : Integrable (fun y => trunc f t y ^ 2 * (d.weight y).toReal) μ :=
    hti.mul_bdd hw.aestronglyMeasurable (ae_of_all _ hBη)
  have heq : (∫ y, trunc f t y ^ 2 ∂μ.withDensity d.weight) =
      ∫ y, trunc f t y ^ 2 * (d.weight y).toReal ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (ae_of_all _ fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y))]
    congr 1
    funext y
    exact mul_comm _ _
  rw [heq]
  calc
    _ ≤ ∫ y, (a⁻¹ * (trunc f t y ^ 2 * (d.weight y).toReal) + T ^ 2) ∂μ := by
      apply integral_mono hti ((hwi.const_mul _).add (integrable_const _))
      intro y
      change trunc f t y ^ 2 ≤ a⁻¹ * (trunc f t y ^ 2 * (d.weight y).toReal) + T ^ 2
      have hp : 0 ≤ a⁻¹ * (trunc f t y ^ 2 * (d.weight y).toReal) := by positivity
      by_cases hy : T < f y
      · have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hlower y hy) (sq_nonneg (trunc f t y)))
          (inv_nonneg.mpr ha.le)
        have he : a⁻¹ * (trunc f t y ^ 2 * a) = trunc f t y ^ 2 := by field_simp
        rw [he] at hh
        exact hh.trans (le_add_of_nonneg_right (sq_nonneg T))
      · have hbT : trunc f t y ≤ T := (trunc_le_self hf t y).trans (le_of_not_gt hy)
        have hs := pow_le_pow_left₀ (trunc_nonneg hf t y) hbT 2
        linarith
    _ = _ := by
      rw [integral_add (hwi.const_mul _) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul]

end ConditionedStableLaws.ContinuousMultiplier
