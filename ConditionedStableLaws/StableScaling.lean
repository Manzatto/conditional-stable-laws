import ConditionedStableLaws.Cited.StableClassification
import ConditionedStableLaws.CompensatedStableLaw
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Stability from scaling of the explicit characteristic exponent

To identify the fully compensated limit in the regime `1 < α < 2` as stable, it suffices to change
variables in its explicit power-density integral.
-/

open MeasureTheory Set Complex Filter
open scoped ENNReal
set_option backward.isDefEq.respectTransparency.types false

namespace ConditionedStableLaws.StableScaling
noncomputable section

/-- The fully compensated power-density exponent used for `1 < α < 2`. -/
def fullExponent (α t : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), (α * y ^ (-α - 1) : ℝ) •
    (exp ((t * y : ℝ) * I) - 1 - (t * y : ℝ) * I)

/-- Homogeneity follows directly from the substitution `y ↦ c*y`. -/
theorem fullExponent_scale (α t : ℝ) {c : ℝ} (hc : 0 < c) :
    fullExponent α (c * t) = (c ^ α : ℝ) • fullExponent α t := by
  let F := fun y : ℝ ↦ (α * y ^ (-α - 1) : ℝ) •
    (exp ((t * y : ℝ) * I) - 1 - (t * y : ℝ) * I)
  have hpow : c ^ (α + 1) * c ^ (-α - 1) = 1 := by
    rw [← Real.rpow_add hc, show α + 1 + (-α - 1) = 0 by ring, Real.rpow_zero]
  have hpoint : ∀ y ∈ Ioi (0 : ℝ),
      (α * y ^ (-α - 1) : ℝ) •
        (exp (((c * t) * y : ℝ) * I) - 1 - ((c * t) * y : ℝ) * I) =
      (c ^ (α + 1) : ℝ) • F (c * y) := by
    intro y hy
    change (α * y ^ (-α - 1) : ℝ) •
        (exp (((c * t) * y : ℝ) * I) - 1 - ((c * t) * y : ℝ) * I) =
      (c ^ (α + 1) : ℝ) • ((α * (c * y) ^ (-α - 1) : ℝ) •
        (exp ((t * (c * y) : ℝ) * I) - 1 - (t * (c * y) : ℝ) * I))
    rw [Real.mul_rpow hc.le hy.le, smul_smul]
    have hs : c ^ (α + 1) * (α * (c ^ (-α - 1) * y ^ (-α - 1))) =
        α * y ^ (-α - 1) := by
      calc
        _ = (α * y ^ (-α - 1)) * (c ^ (α + 1) * c ^ (-α - 1)) := by ring
        _ = _ := by rw [hpow, mul_one]
    rw [hs, show t * (c * y) = c * t * y by ring]
  unfold fullExponent
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_smul,
    integral_comp_mul_left_Ioi F 0 hc, mul_zero, smul_smul]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hc]
  congr 1
  ring

/-- A homogeneous characteristic exponent gives the exact independent-sum scaling law. -/
theorem isStableLaw_of_homogeneous_exponent {α : ℝ} (hα : 0 < α)
    (μ : Measure ℝ) (Ψ : ℝ → ℂ)
    (hchar : ∀ t, charFun μ t = exp (Ψ t))
    (hscale : ∀ c : ℝ, 0 < c → ∀ t, Ψ (c * t) = (c ^ α : ℝ) • Ψ t) :
    Cited.IsStableLaw α μ := by
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  let c := (n : ℝ) ^ (1 / α)
  have hc : 0 < c := Real.rpow_pos_of_pos hn0 _
  have hcn : c ^ α = n := by
    dsimp [c]
    rw [← Real.rpow_mul hn0.le, one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one]
  refine ⟨0, fun t ↦ ?_⟩
  rw [hchar, hchar, hscale c hc, hcn]
  simp only [zero_mul, ofReal_zero, mul_zero, exp_zero, mul_one]
  rw [← Complex.exp_nat_mul]
  simp [Complex.real_smul]

/-- The fully compensated characteristic function implies stability. -/
theorem isStableLaw_of_fullExponent {α : ℝ} (hα : 0 < α)
    (μ : Measure ℝ) (hchar : ∀ t, charFun μ t = exp (fullExponent α t)) :
    Cited.IsStableLaw α μ :=
  isStableLaw_of_homogeneous_exponent hα μ (fullExponent α) hchar
    (fun _c hc t ↦ fullExponent_scale α t hc)

/-- Compensation at an arbitrary positive cutoff, on the real positive half-line. -/
def cutoffIntegrand (α t R y : ℝ) : ℂ :=
  (α * y ^ (-α - 1) : ℝ) •
    (exp ((t * y : ℝ) * I) - 1 - (t * (if y ≤ R then y else 0) : ℝ) * I)

theorem cutoffIntegrand_one_integrable {α : ℝ} (hα : 0 < α) (ha : α < 2) (t : ℝ) :
    IntegrableOn (cutoffIntegrand α t 1) (Ioi (0 : ℝ)) := by
  have hi := unitStableExponent_integrable hα ha t
  rw [powerIntensity] at hi
  have hm := hi.comp_aemeasurable measurable_extremeOfReal.aemeasurable
  have hw := (integrable_withDensity_iff_integrable_smul'
    (by fun_prop : Measurable (fun y : ℝ ↦ ENNReal.ofReal (α * y ^ (-α - 1))))
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hm
  apply hw.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (mul_nonneg hα.le (Real.rpow_nonneg hy.le _))]
  simp only [Function.comp_apply, unitStableExponent, smallMark, Set.indicator_apply,
    extremeOfReal_val_of_pos hy, ENNReal.toReal_ofReal hy.le, Set.mem_ofPred_eq,
    ENNReal.ofReal_one, ENNReal.ofReal_le_one]
  rfl

theorem powerLevyExponent_eq_integral (α t : ℝ) :
    Cited.powerLevyExponent α t = ∫ y in Ioi (0 : ℝ), cutoffIntegrand α t 1 y := by
  unfold Cited.powerLevyExponent
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change 0 < y at hy
  by_cases h1 : y ≤ 1
  · simp [cutoffIntegrand, Set.indicator, hy.le, h1, Complex.real_smul]
    ring_nf
  · simp [cutoffIntegrand, Set.indicator, hy.le, h1, Complex.real_smul]
    ring_nf

/-- Moving the cutoff from one to `c` changes the exponent by a finite real drift integral. -/
theorem cutoff_integral_eq {α c : ℝ} (hα : 0 < α) (ha : α < 2) (hc : 1 ≤ c) (t : ℝ) :
    (∫ y in Ioi (0 : ℝ), cutoffIntegrand α t c y) =
      Cited.powerLevyExponent α t - (t * (∫ y in Ioc (1 : ℝ) c, α * y ^ (-α)) : ℝ) * I := by
  let J : ℝ → ℂ := (Ioc (1 : ℝ) c).indicator
    (fun y ↦ (t * (α * y ^ (-α)) : ℝ) * I)
  have hj : IntegrableOn (fun y : ℝ ↦ α * y ^ (-α)) (Ioc 1 c) := by
    apply Integrable.const_mul
    exact (intervalIntegral.intervalIntegrable_rpow (a := 1) (b := c)
      (Or.inr (by rw [Set.uIcc_of_le hc]; intro h; norm_num at h))).1
  have hJ : Integrable J volume := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (hj.const_mul t).ofReal.mul_const I
  have hsplit : ∀ y ∈ Ioi (0 : ℝ),
      cutoffIntegrand α t c y = cutoffIntegrand α t 1 y - J y := by
    intro y hy
    change 0 < y at hy
    by_cases h1 : y ≤ 1
    · have hcy : y ≤ c := h1.trans hc
      simp [cutoffIntegrand, J, h1, hcy]
    · by_cases hcy : y ≤ c
      · have hmem : y ∈ Ioc (1 : ℝ) c := ⟨lt_of_not_ge h1, hcy⟩
        simp only [cutoffIntegrand, J, h1, hcy, ite_false, ite_true,
          Set.indicator_of_mem hmem, Complex.real_smul]
        rw [Real.rpow_sub_one hy.ne']
        push_cast
        field_simp [show (y : ℂ) ≠ 0 by exact_mod_cast hy.ne']
        ring
      · simp [cutoffIntegrand, J, h1, hcy]
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_sub (cutoffIntegrand_one_integrable hα ha t) hJ.restrict,
    ← powerLevyExponent_eq_integral]
  congr 1
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (1 : ℝ) c ⊆ Ioi 0 from fun _ h ↦ zero_lt_one.trans h.1)]
  rw [integral_mul_const, integral_complex_ofReal, integral_const_mul]

/-- Positive scaling of the unit-cutoff exponent, with its explicit finite drift correction. -/
theorem powerLevyExponent_scale {α : ℝ} (hα : 0 < α) (ha : α < 2)
    {c : ℝ} (hc : 1 ≤ c) (t : ℝ) :
    Cited.powerLevyExponent α (c * t) = (c ^ α : ℝ) •
      (Cited.powerLevyExponent α t -
        (t * (∫ y in Ioc (1 : ℝ) c, α * y ^ (-α)) : ℝ) * I) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hpow : c ^ (α + 1) * c ^ (-α - 1) = 1 := by
    rw [← Real.rpow_add hc0, show α + 1 + (-α - 1) = 0 by ring, Real.rpow_zero]
  have hpoint : ∀ y ∈ Ioi (0 : ℝ), cutoffIntegrand α (c * t) 1 y =
      (c ^ (α + 1) : ℝ) • cutoffIntegrand α t c (c * y) := by
    intro y hy
    change 0 < y at hy
    have hcut : c * y ≤ c ↔ y ≤ 1 := by
      constructor
      · intro h
        nlinarith
      · intro h
        simpa using mul_le_mul_of_nonneg_left h hc0.le
    unfold cutoffIntegrand
    rw [Real.mul_rpow hc0.le hy.le, smul_smul]
    have hw : c ^ (α + 1) * (α * (c ^ (-α - 1) * y ^ (-α - 1))) =
        α * y ^ (-α - 1) := by
      calc
        _ = (α * y ^ (-α - 1)) * (c ^ (α + 1) * c ^ (-α - 1)) := by ring
        _ = _ := by rw [hpow, mul_one]
    rw [hw]
    simp only [hcut]
    by_cases h1 : y ≤ 1 <;> simp only [h1, ite_true, ite_false]
    all_goals (congr 1; push_cast; ring_nf)
  rw [powerLevyExponent_eq_integral,
    setIntegral_congr_fun measurableSet_Ioi hpoint, integral_smul,
    integral_comp_mul_left_Ioi (cutoffIntegrand α t c) 0 hc0, mul_zero, smul_smul]
  have he : c ^ (α + 1) * c⁻¹ = c ^ α := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]
    congr 1
    ring
  rw [he, cutoff_integral_eq hα ha hc t]

/-- Stability of the compensated limits, from exponent scaling. -/
theorem isStableLaw_of_powerLevyExponent {α : ℝ} (hα : 0 < α) (ha : α < 2)
    (γ : ℝ) (μ : Measure ℝ)
    (hchar : ∀ t, charFun μ t = exp (I * (γ * t) + Cited.powerLevyExponent α t)) :
    Cited.IsStableLaw α μ := by
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  let c := (n : ℝ) ^ (1 / α)
  have hc : 1 ≤ c := by
    dsimp [c]
    exact Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  have hcn : c ^ α = n := by
    dsimp [c]
    rw [← Real.rpow_mul hn0.le, one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one]
  let J := ∫ y in Ioc (1 : ℝ) c, α * y ^ (-α)
  refine ⟨((n : ℝ) - c) * γ + n * J, fun t ↦ ?_⟩
  rw [hchar, hchar, powerLevyExponent_scale hα ha hc, hcn,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [Complex.real_smul]
  dsimp [J, c]
  push_cast
  ring

end
end ConditionedStableLaws.StableScaling
