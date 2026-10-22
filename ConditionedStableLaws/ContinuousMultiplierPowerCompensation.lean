import ConditionedStableLaws.ContinuousMultiplierCompensation

/-! Compensation errors for residuals with arbitrarily small relative growth. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open SmallJumpMoment NormalizationBridge SecondMoment

variable {M : Type*} [MeasurableSpace M] (ν : Measure M) [IsProbabilityMeasure ν]
  {f r : M → ℝ}

omit [IsProbabilityMeasure ν] in
theorem integral_tail_eq_sub (hfm : Measurable f) (hri : Integrable r ν) (t : ℝ) :
    (∫ x, {y | t < f y}.indicator r x ∂ν) =
      (∫ x, r x ∂ν) - ∫ x, cut f r t x ∂ν := by
  have hs : MeasurableSet {y | f y ≤ t} := measurableSet_le hfm measurable_const
  have ht : MeasurableSet {y | t < f y} := measurableSet_lt measurable_const hfm
  have hid : r = fun x => cut f r t x + {y | t < f y}.indicator r x := by
    funext x
    by_cases hx : f x ≤ t
    · simp [cut, hx, not_lt.mpr hx]
    · simp [cut, hx, lt_of_not_ge hx]
  have he := integral_congr_ae (μ := ν) (ae_of_all _ fun x => congrFun hid x)
  have hci : Integrable (cut f r t) ν := hri.indicator hs
  rw [integral_add hci (hri.indicator ht)] at he
  linarith

/-- Two fixed multiples of the normalizer give asymptotically identical
residual compensation. This includes the index-one truncation convention. -/
theorem cut_band_center_tendsto_zero (hfm : Measurable f) (hrm : Measurable r)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |r x| ≤ η * f x + K)
    {Cc α : ℝ} (hC : 0 < Cc) (hα : 0 < α)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-α))) atTop (𝓝 1))
    {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (fun n : ℕ => (n : ℝ) / positivePowerScale Cc α n *
      ((∫ x, cut f r (R * positivePowerScale Cc α n) x ∂ν) -
        ∫ x, cut f r (positivePowerScale Cc α n) x ∂ν)) atTop (𝓝 0) := by
  let B := positivePowerScale Cc α
  have hB : ∀ n, 0 < B n := positivePowerScale_pos hC
  have hinv : Tendsto (fun n => (B n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (positivePowerScale_tendsto_atTop hC hα)
  have htailB : Tendsto (fun n : ℕ => (n : ℝ) * ν.real {x | B n < f x}) atTop (𝓝 1) := by
    simpa only [mul_one, Real.one_rpow] using CompensationAsymptotics.scaled_tail hC hα htail one_pos
  have hb : Tendsto (fun n : ℕ => (n : ℝ) * ν.real {x | B n < f x} / B n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using htailB.mul hinv
  apply tendsto_zero_of_small_bounds (L := 2 * R) (by linarith) hb
  intro η hη
  obtain ⟨K, hK, hbnd⟩ := hr η hη
  refine ⟨K, ?_⟩
  filter_upwards [htailB.eventually (ge_mem_nhds one_lt_two)] with n hn
  have hi := abs_integral_cut_sub_le ν hfm hrm (b := R * B n) hη.le hK (hB n).le
    (by nlinarith [hB n]) hbnd
  rw [abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (hB n).le)]
  have hh := mul_le_mul_of_nonneg_left hi (div_nonneg (Nat.cast_nonneg n) (hB n).le)
  have hh2 := mul_le_mul_of_nonneg_left hn (show 0 ≤ η * R by positivity)
  have he : (n : ℝ) / B n * ((η * (R * B n) + K) * ν.real {x | B n < f x}) =
      η * R * ((n : ℝ) * ν.real {x | B n < f x}) +
        K * ((n : ℝ) * ν.real {x | B n < f x} / B n) := by field_simp [(hB n).ne']
  rw [he] at hh
  linarith

/-- Above index one, full residual means and cutoff residual means differ by o(B/n). -/
theorem full_center_tendsto_zero (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hrm : Measurable r)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |r x| ≤ η * f x + K)
    {Cc α : ℝ} (hC : 0 < Cc) (hα1 : 1 < α)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-α))) atTop (𝓝 1))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n : ℕ => (n : ℝ) / positivePowerScale Cc α n *
      ((∫ x, r x ∂ν) - ∫ x, cut f r (R * positivePowerScale Cc α n) x ∂ν))
      atTop (𝓝 0) := by
  let B := positivePowerScale Cc α
  have hα : 0 < α := zero_lt_one.trans hα1
  have hB : ∀ n, 0 < B n := positivePowerScale_pos hC
  have hfi := integrable_of_power_tail_asymptotic ν f hfm hf Cc α hC hα1 htail
  have hri := integrable_residual_of_bound ν hfi hrm hr
  have hinv : Tendsto (fun n => (B n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (positivePowerScale_tendsto_atTop hC hα)
  have htailR : Tendsto (fun n : ℕ => (n : ℝ) * ν.real {x | R * B n < f x})
      atTop (𝓝 (R ^ (-α))) := by
    simpa only [B, mul_comm] using CompensationAsymptotics.scaled_tail hC hα htail hR
  have hb : Tendsto (fun n : ℕ => (n : ℝ) * ν.real {x | R * B n < f x} / B n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using htailR.mul hinv
  let L := α / (α - 1) * R ^ (1 - α) + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hmean : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / B n * (∫ x, {y | R * B n < f y}.indicator f x ∂ν) ≤ L := by
    have hm := CompensationAsymptotics.scaled_tail_mean hfm hf hC hα1 htail hR
    have he := hm.eventually (ge_mem_nhds (show α / (α - 1) * R ^ (1 - α) < L by dsimp [L]; linarith))
    simpa only [integral_tail_eq_sub ν hfm hfi, cut] using he
  apply tendsto_zero_of_small_bounds hL hb
  intro η hη
  obtain ⟨K, _, hbnd⟩ := hr η hη
  refine ⟨K, ?_⟩
  filter_upwards [hmean] with n hn
  rw [← integral_tail_eq_sub ν hfm hri, abs_mul,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (hB n).le)]
  have hi := abs_integral_residual_tail_le ν hfm hfi hri hbnd (t := R * B n)
  have hh := mul_le_mul_of_nonneg_left hi (div_nonneg (Nat.cast_nonneg n) (hB n).le)
  have hh2 := mul_le_mul_of_nonneg_left hn hη.le
  calc
    _ ≤ (n : ℝ) / B n * (η * (∫ x, {y | R * B n < f y}.indicator f x ∂ν) +
        K * ν.real {x | R * B n < f x}) := hh
    _ ≤ η * L + K * ((n : ℝ) * ν.real {x | R * B n < f x} / B n) := by
      simp only [div_eq_mul_inv] at hh2 ⊢
      nlinarith [hh2]

end
end ConditionedStableLaws.ContinuousMultiplier
