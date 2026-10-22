import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic

/-!
# Comparing the quasi-stationary and quasi-ergodic Lp spaces

Bounded weights give the forward inclusion for every exponent, including
infinity. A positive lower bound gives the reverse inclusion and quantitative
norm comparisons. An explicit vanishing-weight example shows why a lower
bound cannot be omitted, even for finite measures and continuous weights.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace ConditionedStableLaws
noncomputable section

variable {M E : Type*} [MeasurableSpace M] [NormedAddCommGroup E]
  {μ : Measure M} {η : M → ℝ≥0∞} {C a p : ℝ≥0∞}

theorem weightedMeasure_le_of_weight_le (hη : ∀ᵐ x ∂μ, η x ≤ C) :
    μ.withDensity η ≤ C • μ := by
  simpa only [withDensity_const] using withDensity_mono hη

theorem measure_le_weighted_of_weight_ge (ha : a ≠ 0) (hat : a ≠ ∞)
    (hη : ∀ᵐ x ∂μ, a ≤ η x) : μ ≤ a⁻¹ • μ.withDensity η := by
  have hl : a • μ ≤ μ.withDensity η := by
    simpa only [withDensity_const] using withDensity_mono hη
  calc
    μ = a⁻¹ • (a • μ) := by rw [smul_smul, ENNReal.inv_mul_cancel ha hat, one_smul]
    _ ≤ a⁻¹ • μ.withDensity η := by
      apply Measure.le_iff.mpr
      intro A hA
      exact mul_le_mul' le_rfl (Measure.le_iff.mp hl A hA)

/-- The continuous bounded eigenfunction gives `Lp(μ) ⊆ Lp(η μ)`. -/
theorem memLp_weighted_of_memLp {f : M → E} (hC : C ≠ ∞)
    (hη : ∀ᵐ x ∂μ, η x ≤ C) (hf : MemLp f p μ) :
    MemLp f p (μ.withDensity η) :=
  hf.of_measure_le_smul hC (weightedMeasure_le_of_weight_le hη)

theorem eLpNorm_weighted_le {f : M → E} (hη : ∀ᵐ x ∂μ, η x ≤ C) :
    eLpNorm f p (μ.withDensity η) ≤ C ^ (1 / p).toReal * eLpNorm f p μ :=
  eLpNorm_le_of_measure_le_smul (weightedMeasure_le_of_weight_le hη)

theorem eLpNorm_le_weighted {f : M → E} (ha : a ≠ 0) (hat : a ≠ ∞)
    (hη : ∀ᵐ x ∂μ, a ≤ η x) :
    eLpNorm f p μ ≤ (a⁻¹) ^ (1 / p).toReal * eLpNorm f p (μ.withDensity η) :=
  eLpNorm_le_of_measure_le_smul (measure_le_weighted_of_weight_ge ha hat hη)

/-- A weight bounded above and away from zero gives identical Lp membership,
with the two norm comparisons stated above. -/
theorem memLp_weighted_iff {f : M → E} (hC : C ≠ ∞)
    (ha : a ≠ 0) (hat : a ≠ ∞)
    (hlo : ∀ᵐ x ∂μ, a ≤ η x) (hhi : ∀ᵐ x ∂μ, η x ≤ C) :
    MemLp f p (μ.withDensity η) ↔ MemLp f p μ := by
  constructor
  · intro hf
    exact hf.of_measure_le_smul (by simpa using ha)
      (measure_le_weighted_of_weight_ge ha hat hlo)
  · exact memLp_weighted_of_memLp hC hhi

/-- The forward integrability inclusion used in the conditional LLN. -/
theorem integrable_weighted_of_integrable {f : M → E} (hC : C ≠ ∞)
    (hη : ∀ᵐ x ∂μ, η x ≤ C) (hf : Integrable f μ) :
    Integrable f (μ.withDensity η) := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact memLp_weighted_of_memLp hC hη hf

/-- The reverse inclusion can fail for a continuous weight tending to zero:
`1/x` is integrable against `x dx` on `(0,1)` but not against `dx`. -/
theorem integrability_reverse_inclusion_fails :
    let μ : Measure ℝ := volume.restrict (Ioo 0 1)
    Integrable (fun x : ℝ => x⁻¹) (μ.withDensity (fun x => ENNReal.ofReal x)) ∧
      ¬ Integrable (fun x : ℝ => x⁻¹) μ := by
  dsimp only
  constructor
  · rw [integrable_withDensity_iff (by fun_prop)
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    have hi : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo 0 1)) :=
      integrable_const 1
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [ENNReal.toReal_ofReal hx.1.le, inv_mul_cancel₀ hx.1.ne']
  · intro hi
    have hr : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo 0 1) := by
      simpa only [Real.rpow_neg_one, IntegrableOn] using hi
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mp hr
    norm_num at this

end
end ConditionedStableLaws
