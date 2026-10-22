import ConditionedStableLaws.ContinuousMultiplierTruncation

/-!
# Deterministic compensation for the continuous-multiplier residual
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open SmallJumpMoment NormalizationBridge SecondMoment

/-- A deterministic version of the small-relative-error argument. -/
theorem tendsto_zero_of_small_bounds {a b : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hb : Tendsto b atTop (𝓝 0))
    (ha : ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∀ᶠ n in atTop, |a n| ≤ η * L + K * b n) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := ha (ε / (2 * (L + 1))) (by positivity)
  have hsmall : ∀ᶠ n in atTop, K * b n < ε / 2 := by
    have hh : Tendsto (fun n => K * b n) atTop (𝓝 0) := by simpa using hb.const_mul K
    exact hh.eventually_lt_const (half_pos hε)
  filter_upwards [hK, hsmall] with n hn hnsmall
  rw [Real.dist_eq, sub_zero]
  have hcoef : ε / (2 * (L + 1)) * L < ε / 2 := by
    apply (mul_lt_mul_iff_of_pos_right (show 0 < 2 * (L + 1) by positivity)).mp
    field_simp
    nlinarith
  linarith

section Integrals
variable {M : Type*} [MeasurableSpace M] (μ : Measure M) [IsProbabilityMeasure μ]
  {f r : M → ℝ}

/-- Changing an upper cutoff affects only the intervening band. -/
theorem abs_integral_cut_sub_le (hfm : Measurable f) (hrm : Measurable r)
    {η K a b : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K) (ha : 0 ≤ a) (hab : a ≤ b)
    (hr : ∀ x, |r x| ≤ η * f x + K) :
    |(∫ x, cut f r b x ∂μ) - ∫ x, cut f r a x ∂μ| ≤
      (η * b + K) * μ.real {x | a < f x} := by
  have hb := ha.trans hab
  have hbi := integrable_of_bdd (ν := μ) (measurable_cut hfm hrm b) (abs_cut_le hη hK hb hr)
  have hai := integrable_of_bdd (ν := μ) (measurable_cut hfm hrm a) (abs_cut_le hη hK ha hr)
  have htail : MeasurableSet {x | a < f x} := measurableSet_lt measurable_const hfm
  have hpt (x : M) : |cut f r b x - cut f r a x| ≤
      {y | a < f y}.indicator (fun _ => η * b + K) x := by
    by_cases hxa : f x ≤ a
    · rw [cut, cut, indicator_of_mem (show x ∈ {x | f x ≤ b} from hxa.trans hab),
        indicator_of_mem (show x ∈ {x | f x ≤ a} from hxa), sub_self, abs_zero,
        indicator_of_notMem (show x ∉ {x | a < f x} from not_lt.mpr hxa)]
    · rw [cut, cut, indicator_of_notMem (show x ∉ {x | f x ≤ a} from hxa), sub_zero,
        indicator_of_mem (show x ∈ {x | a < f x} from lt_of_not_ge hxa)]
      exact abs_cut_le hη hK hb hr x
  rw [← integral_sub hbi hai]
  calc
    _ ≤ ∫ x, |cut f r b x - cut f r a x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => cut f r b x - cut f r a x) (μ := μ)
    _ ≤ ∫ x, {y | a < f y}.indicator (fun _ => η * b + K) x ∂μ :=
      integral_mono (hbi.sub hai).abs ((integrable_const _).indicator htail) hpt
    _ = _ := by rw [integral_indicator htail, integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, mul_comm]

/-- An integrable majorant makes the multiplier residual integrable. -/
theorem integrable_residual_of_bound (hfi : Integrable f μ) (hrm : Measurable r)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |r x| ≤ η * f x + K) :
    Integrable r μ := by
  obtain ⟨K, _, hK⟩ := hr 1 one_pos
  exact (hfi.add (integrable_const K)).mono' hrm.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, one_mul, Pi.add_apply] using hK x)

/-- Absolute residual tail means are bounded by those of the original observable. -/
theorem abs_integral_residual_tail_le (hfm : Measurable f) (hfi : Integrable f μ)
    (hri : Integrable r μ) {η K t : ℝ}
    (hr : ∀ x, |r x| ≤ η * f x + K) :
    |∫ x, {y | t < f y}.indicator r x ∂μ| ≤
      η * (∫ x, {y | t < f y}.indicator f x ∂μ) + K * μ.real {x | t < f x} := by
  have hs : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hfm
  have hbound (x : M) : |{y | t < f y}.indicator r x| ≤
      {y | t < f y}.indicator (fun y => η * f y + K) x := by
    by_cases hx : t < f x
    · simpa only [indicator_of_mem (show x ∈ {y | t < f y} from hx)] using hr x
    · simp only [indicator_of_notMem (show x ∉ {y | t < f y} from hx), abs_zero, le_refl]
  calc
    _ ≤ ∫ x, |{y | t < f y}.indicator r x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => {y | t < f y}.indicator r x) (μ := μ)
    _ ≤ ∫ x, {y | t < f y}.indicator (fun y => η * f y + K) x ∂μ :=
      integral_mono (hri.indicator hs).abs (((hfi.const_mul η).add (integrable_const K)).indicator hs)
        hbound
    _ = _ := by
      rw [integral_indicator hs, integral_add ((hfi.restrict).const_mul η) (integrable_const K),
        integral_const_mul, integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
        ← integral_indicator hs]
      ring

end Integrals
end
end ConditionedStableLaws.ContinuousMultiplier
