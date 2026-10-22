import ConditionedStableLaws.PoissonSecondMoments
import ConditionedStableLaws.PowerIntensityMoments

/-! Centered independent annular Poisson integrals and their exact variances. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.AnnularPoissonClouds
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)

theorem component_testIntegral_mean (n : ℕ) (f : ExtremeState → ℝ)
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B) :
    (∫ ω : FinitePoissonCloud.Sample, FinitePoissonCloud.testIntegral f ω ∂componentLaw υ hυ n) =
      ∫ x, f x ∂υ.restrict (annulus n) := by
  let v := componentIntensity υ hυ n
  have : Nonempty ExtremeState := ⟨⟨1, by simp⟩⟩
  have he : (v.mass : ℝ≥0∞) • (v.normalize : Measure ExtremeState) = υ.restrict (annulus n) :=
    congrArg (fun w : FiniteMeasure ExtremeState => (w : Measure ExtremeState))
      v.self_eq_mass_smul_normalize.symm
  change (∫ ω, FinitePoissonCloud.testIntegral f ω ∂FinitePoissonCloud.law v.mass v.normalize) = _
  rw [FinitePoissonCloud.testIntegral_mean _ _ f hf hB hb, ← he, integral_smul_measure]
  rfl

theorem component_testIntegral_variance (n : ℕ) (f : ExtremeState → ℝ)
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B) :
    Var[FinitePoissonCloud.testIntegral f; componentLaw υ hυ n] =
      ∫ x, (f x)^2 ∂υ.restrict (annulus n) := by
  let v := componentIntensity υ hυ n
  have : Nonempty ExtremeState := ⟨⟨1, by simp⟩⟩
  have he : (v.mass : ℝ≥0∞) • (v.normalize : Measure ExtremeState) = υ.restrict (annulus n) :=
    congrArg (fun w : FiniteMeasure ExtremeState => (w : Measure ExtremeState))
      v.self_eq_mass_smul_normalize.symm
  change Var[FinitePoissonCloud.testIntegral f; FinitePoissonCloud.law v.mass v.normalize] = _
  rw [FinitePoissonCloud.testIntegral_variance _ _ f hf hB hb, ← he, integral_smul_measure]
  rfl

/-- A centered integral of the n-th Poisson cloud on the common countable product probability space.
-/
def centeredComponent (f : ExtremeState → ℝ) (n : ℕ) (ω : Sample) : ℝ :=
  FinitePoissonCloud.testIntegral f (ω n) - ∫ x, f x ∂υ.restrict (annulus n)

theorem measurable_centeredComponent (f : ExtremeState → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (centeredComponent υ f n) :=
  ((FinitePoissonCloud.measurable_testIntegral f hf).comp (measurable_pi_apply n)).sub_const _

theorem independent_centeredComponents (f : ExtremeState → ℝ) (hf : Measurable f) :
    iIndepFun (centeredComponent υ f) (law υ hυ) :=
  iIndepFun_infinitePi (fun n => (FinitePoissonCloud.measurable_testIntegral f hf).sub_const
    (∫ x, f x ∂υ.restrict (annulus n)))

theorem centeredComponent_memLp (f : ExtremeState → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B) (n : ℕ) :
    MemLp (centeredComponent υ f n) 2 (law υ hυ) := by
  have hm : MemLp (FinitePoissonCloud.testIntegral f) 2 (componentLaw υ hυ n) :=
    (memLp_two_iff_integrable_sq (FinitePoissonCloud.measurable_testIntegral f hf).aestronglyMeasurable).mpr
      (FinitePoissonCloud.integrable_testIntegral_sq _ _ f hf hB hb)
  exact (hm.sub (memLp_const _)).comp_measurePreserving
    (measurePreserving_eval_infinitePi (componentLaw υ hυ) n)

theorem centeredComponent_mean (f : ExtremeState → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B) (n : ℕ) :
    (∫ ω, centeredComponent υ f n ω ∂law υ hυ) = 0 := by
  have hl : HasLaw (fun ω : Sample => ω n) (componentLaw υ hυ n) (law υ hυ) :=
    ⟨(measurable_pi_apply n).aemeasurable, Measure.infinitePi_map_eval (componentLaw υ hυ) n⟩
  have hm := ((FinitePoissonCloud.measurable_testIntegral f hf).sub_const
    (∫ x, f x ∂υ.restrict (annulus n))).aestronglyMeasurable (μ := componentLaw υ hυ n)
  calc
    _ = ∫ ω : FinitePoissonCloud.Sample,
        FinitePoissonCloud.testIntegral f ω - ∫ x, f x ∂υ.restrict (annulus n)
        ∂componentLaw υ hυ n := hl.integral_comp hm
    _ = 0 := by
      have hi : Integrable (FinitePoissonCloud.testIntegral f) (componentLaw υ hυ n) :=
        FinitePoissonCloud.integrable_testIntegral _ _ f hf hB hb
      rw [integral_sub hi (integrable_const _),
        component_testIntegral_mean υ hυ n f hf hB hb]
      simp

/-- The exact mean square of the centered component is its intensity square
integral, including every numerical normalization factor. -/
theorem centeredComponent_second_moment (f : ExtremeState → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B) (n : ℕ) :
    (∫ ω, (centeredComponent υ f n ω)^2 ∂law υ hυ) =
      ∫ x, (f x)^2 ∂υ.restrict (annulus n) := by
  have hl : HasLaw (fun ω : Sample => ω n) (componentLaw υ hυ n) (law υ hυ) :=
    ⟨(measurable_pi_apply n).aemeasurable, Measure.infinitePi_map_eval (componentLaw υ hυ) n⟩
  calc
    _ = ∫ ω : FinitePoissonCloud.Sample,
        (FinitePoissonCloud.testIntegral f ω - ∫ x, f x ∂υ.restrict (annulus n))^2
        ∂componentLaw υ hυ n :=
      hl.integral_comp (((FinitePoissonCloud.measurable_testIntegral f hf).sub_const
        (∫ x, f x ∂υ.restrict (annulus n))).pow_const 2).aestronglyMeasurable
    _ = Var[FinitePoissonCloud.testIntegral f; componentLaw υ hυ n] := by
      rw [variance_eq_integral (FinitePoissonCloud.measurable_testIntegral f hf).aemeasurable,
        component_testIntegral_mean υ hυ n f hf hB hb]
    _ = _ := component_testIntegral_variance υ hυ n f hf hB hb

theorem centeredComponent_second_moments_hasSum (f : ExtremeState → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B) (hfi : Integrable (fun x => (f x)^2) υ) :
    HasSum (fun n => ∫ ω, (centeredComponent υ f n ω)^2 ∂law υ hυ)
      (∫ x, (f x)^2 ∂υ) := by
  simp_rw [centeredComponent_second_moment υ hυ f hf hB hb]
  have hi : Integrable (fun x => (f x)^2) (Measure.sum (fun n => υ.restrict (annulus n))) := by
    rwa [sum_restrict_annulus]
  simpa only [sum_restrict_annulus] using hasSum_integral_measure hi

end
end ConditionedStableLaws.AnnularPoissonClouds
