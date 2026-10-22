import ConditionedStableLaws.CompensatedPoissonIntegral
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-! Characteristic functions of the constructed compensated Poisson integrals. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

/-- A global quadratic bound for the compensated exponential. -/
theorem norm_compensated_exp_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ ≤ 3 * x^2 := by
  by_cases hx : ‖(x : ℂ) * Complex.I‖ ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le hx
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      sq_abs] at h
    nlinarith [sq_nonneg x]
  · have ha : 1 < |x| := by simpa using (not_le.mp hx)
    calc
      _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ + ‖(x : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
          ‖(x : ℂ) * Complex.I‖ := by gcongr; exact norm_sub_le _ _
      _ = 2 + |x| := by simp; norm_num
      _ ≤ 3*x^2 := by nlinarith [sq_abs x, sq_nonneg (|x|-1)]

def compensatedExponent (t : ℝ) (f : ExtremeState → ℝ) (y : ExtremeState) : ℂ :=
  Complex.exp ((t*f y : ℝ) * Complex.I) - 1 - (t*f y : ℝ) * Complex.I

theorem compensatedExponent_integrable (υ : Measure ExtremeState) (t : ℝ)
    (f : ExtremeState → ℝ) (hf : Measurable f)
    (hi : Integrable (fun y => (f y)^2) υ) : Integrable (compensatedExponent t f) υ := by
  apply (hi.const_mul (3*t^2)).mono'
    (show AEStronglyMeasurable (compensatedExponent t f) υ by
      apply Measurable.aestronglyMeasurable
      unfold compensatedExponent
      fun_prop)
  exact ae_of_all _ (fun y => (norm_compensated_exp_le (t*f y)).trans_eq (by ring))

namespace FinitePoissonCloud

theorem testIntegral_const_mul (t : ℝ) (f : ExtremeState → ℝ) (ω : Sample) :
    testIntegral (fun y => t*f y) ω = t * testIntegral f ω := by
  simp only [testIntegral_eq_sum, Finset.mul_sum]

end FinitePoissonCloud

namespace AnnularPoissonClouds

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)

theorem component_characteristic (n : ℕ) (t : ℝ) (f : ExtremeState → ℝ)
    (hf : Measurable f) :
    (∫ ω : FinitePoissonCloud.Sample,
      Complex.exp ((t * FinitePoissonCloud.testIntegral f ω : ℝ) * Complex.I)
      ∂componentLaw υ hυ n) =
      Complex.exp (∫ y, Complex.exp ((t*f y : ℝ) * Complex.I) - 1 ∂υ.restrict (annulus n)) := by
  let v := componentIntensity υ hυ n
  have hfun : Integrable (fun y => Complex.exp ((t*f y : ℝ) * Complex.I))
      (v.normalize : Measure ExtremeState) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun y => by rw [Complex.norm_exp]; simp)
  have he : (v.mass : ℝ≥0∞) • (v.normalize : Measure ExtremeState) = υ.restrict (annulus n) := by
    have : Nonempty ExtremeState := ⟨⟨1, by simp⟩⟩
    exact congrArg (fun w : FiniteMeasure ExtremeState => (w : Measure ExtremeState))
      v.self_eq_mass_smul_normalize.symm
  simp_rw [← FinitePoissonCloud.testIntegral_const_mul]
  change (∫ ω, Complex.exp ((∫ y, t*f y ∂(FinitePoissonCloud.pointMeasure ω).toMeasure) * Complex.I)
    ∂FinitePoissonCloud.law v.mass v.normalize) = _
  rw [FinitePoissonCloud.characteristic_functional _ _ _ (hf.const_mul t), ← he,
    integral_smul_measure, integral_sub hfun (integrable_const 1)]
  simp only [integral_const, probReal_univ, one_smul, ENNReal.coe_toReal, Complex.real_smul]

theorem centered_component_characteristic (n : ℕ) (t : ℝ) (f : ExtremeState → ℝ)
    (hf : Measurable f) {B : ℝ} (_hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B) :
    (∫ ω : Sample, Complex.exp ((t * centeredComponent υ f n ω : ℝ) * Complex.I)
      ∂law υ hυ) =
      Complex.exp (∫ y, compensatedExponent t f y ∂υ.restrict (annulus n)) := by
  have : IsFiniteMeasure (υ.restrict (annulus n)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact annulus_measure_lt_top υ hυ n⟩
  have hfi : Integrable f (υ.restrict (annulus n)) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hb)
  have hei : Integrable (fun y => Complex.exp ((t*f y : ℝ) * Complex.I) - 1)
      (υ.restrict (annulus n)) := by
    apply (Integrable.of_bound (by fun_prop) 1 ?_).sub (integrable_const 1)
    exact ae_of_all _ (fun y => by rw [Complex.norm_exp]; simp)
  have hl : HasLaw (fun ω : Sample => ω n) (componentLaw υ hυ n) (law υ hυ) :=
    ⟨(measurable_pi_apply n).aemeasurable, Measure.infinitePi_map_eval (componentLaw υ hυ) n⟩
  have he (ω : Sample) : Complex.exp ((t * centeredComponent υ f n ω : ℝ) * Complex.I) =
      Complex.exp ((t * FinitePoissonCloud.testIntegral f (ω n) : ℝ) * Complex.I) *
      Complex.exp (-(t * ∫ y, f y ∂υ.restrict (annulus n) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [centeredComponent, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hc : (∫ ω : Sample,
      Complex.exp ((t * FinitePoissonCloud.testIntegral f (ω n) : ℝ) * Complex.I) ∂law υ hυ) =
      ∫ ω : FinitePoissonCloud.Sample,
      Complex.exp ((t * FinitePoissonCloud.testIntegral f ω : ℝ) * Complex.I) ∂componentLaw υ hυ n :=
    hl.integral_comp (show AEStronglyMeasurable
      (fun ω : FinitePoissonCloud.Sample =>
        Complex.exp ((t * FinitePoissonCloud.testIntegral f ω : ℝ) * Complex.I))
      (componentLaw υ hυ n) by
      have := FinitePoissonCloud.measurable_testIntegral f hf
      fun_prop)
  rw [hc, component_characteristic υ hυ n t f hf, ← Complex.exp_add]
  congr 1
  unfold compensatedExponent
  have hlin : Integrable (fun y => (t*f y : ℝ) * Complex.I) (υ.restrict (annulus n)) :=
    (hfi.const_mul t).ofReal.mul_const Complex.I
  rw [integral_sub hei hlin,
    integral_mul_const, integral_complex_ofReal, integral_const_mul]
  ring

theorem centered_partialSum_characteristic (n : ℕ) (t : ℝ) (f : ExtremeState → ℝ)
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B) :
    (∫ ω : Sample, Complex.exp
      ((t * CompensatedSeries.partialSum (centeredComponent υ f) n ω : ℝ) * Complex.I)
      ∂law υ hυ) =
      Complex.exp (∑ i ∈ Finset.range n,
        ∫ y, compensatedExponent t f y ∂υ.restrict (annulus i)) := by
  have hm (i : ℕ) : Measurable (fun ω : Sample =>
      Complex.exp ((t * centeredComponent υ f i ω : ℝ) * Complex.I)) := by
    have := measurable_centeredComponent υ f hf i
    fun_prop
  have hi : iIndepFun (fun i : Fin n => fun ω : Sample =>
      Complex.exp ((t * centeredComponent υ f i ω : ℝ) * Complex.I)) (law υ hυ) :=
    ((independent_centeredComponents υ hυ f hf).comp
      (fun _ => fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I))
      (fun _ => by fun_prop)).precomp Fin.val_injective
  have he (ω : Sample) : Complex.exp
      ((t * CompensatedSeries.partialSum (centeredComponent υ f) n ω : ℝ) * Complex.I) =
      ∏ i : Fin n, Complex.exp ((t * centeredComponent υ f i ω : ℝ) * Complex.I) := by
    rw [CompensatedSeries.partialSum, ← Fin.sum_univ_eq_sum_range,
      Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [he]
  rw [hi.integral_fun_prod_eq_prod_integral (fun i => (hm i).aestronglyMeasurable)]
  simp_rw [centered_component_characteristic υ hυ _ t f hf hB hb]
  rw [← Complex.exp_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun i => ∫ y, compensatedExponent t f y ∂υ.restrict (annulus i)) n

theorem compensatedIntegral_characteristic (t : ℝ) (f : ExtremeState → ℝ)
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B)
    (hfi : Integrable (fun y => (f y)^2) υ) :
    (∫ ω : Sample, Complex.exp
      ((t * compensatedIntegral υ hυ f hf hB hb ω : ℝ) * Complex.I) ∂law υ hυ) =
      Complex.exp (∫ y, compensatedExponent t f y ∂υ) := by
  have hchar (X : Sample → ℝ) (hX : Measurable X) :
      charFun ((law υ hυ).map X) t =
        ∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) ∂law υ hυ := by
    rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  have hp (n : ℕ) : Measurable (CompensatedSeries.partialSum (centeredComponent υ f) n) :=
    Finset.measurable_sum _ (fun i _ => measurable_centeredComponent υ f hf i)
  have ht := (centered_partialSum_tendstoInDistribution υ hυ f hf hB hb hfi).tendsto_charFun t
  simp_rw [hchar _ (hp _), hchar _ (measurable_compensatedIntegral υ hυ f hf hB hb),
    centered_partialSum_characteristic υ hυ _ t f hf hB hb] at ht
  have hgi : Integrable (compensatedExponent t f)
      (Measure.sum (fun n => υ.restrict (annulus n))) := by
    rw [sum_restrict_annulus]
    exact compensatedExponent_integrable υ t f hf hfi
  have hs := (hasSum_integral_measure hgi).tendsto_sum_nat
  rw [sum_restrict_annulus] at hs
  exact tendsto_nhds_unique ht (Complex.continuous_exp.tendsto _ |>.comp hs)

end AnnularPoissonClouds
end
end ConditionedStableLaws
