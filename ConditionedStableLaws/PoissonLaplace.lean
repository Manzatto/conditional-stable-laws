import ConditionedStableLaws.PoissonCampbell
import Mathlib.Probability.Independence.Integration

/-!
Laplace functionals for the countable Poisson construction.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem tendsto_sum_of_ofReal_tsum (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {s : ℝ≥0∞} (hs : s ≠ ∞) (he : ∑' n, ENNReal.ofReal (a n) = s) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 s.toReal) := by
  have h := (ENNReal.summable.hasSum (f := fun n => ENNReal.ofReal (a n))).tendsto_sum_nat
  rw [he] at h
  have hh := (ENNReal.continuousAt_toReal hs).tendsto.comp h
  convert hh using 1
  funext n
  simp only [Function.comp_def]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (ha _)]

namespace FinitePoissonCloud

def testIntegral (f : ExtremeState → ℝ) (ω : Sample) : ℝ :=
  ∫ x, f x ∂(pointMeasure ω).toMeasure

theorem testIntegral_eq_sum (f : ExtremeState → ℝ) (ω : Sample) :
    testIntegral f ω = ∑ i : Fin ω.1, f (ω.2 i) :=
  LocallyFinitePointMeasure.integral_empirical ω.2 f

theorem measurable_testIntegral (f : ExtremeState → ℝ) (hf : Measurable f) :
    Measurable (testIntegral f) := by
  apply measurable_of_sigma
  intro n
  simp only [testIntegral_eq_sum]
  change Measurable (fun a : Fin n → ExtremeState => ∑ i : Fin n, f (a i))
  exact Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))

theorem testIntegral_nonneg (f : ExtremeState → ℝ) (hf : ∀ x, 0 ≤ f x) (ω : Sample) :
    0 ≤ testIntegral f ω := by
  rw [testIntegral_eq_sum]
  exact Finset.sum_nonneg (fun i _ => hf _)

theorem lintegral_eq_ofReal_testIntegral (f : ExtremeState → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (ω : Sample) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂(pointMeasure ω).toMeasure) =
      ENNReal.ofReal (testIntegral f ω) := by
  rw [testIntegral_eq_sum]
  simp only [pointMeasure, LocallyFinitePointMeasure.empirical, lintegral_sum_measure,
    lintegral_dirac' _ hf.ennreal_ofReal, tsum_fintype]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => hf0 _)).symm

end FinitePoissonCloud

namespace AnnularPoissonClouds

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)

/-- The finite-cloud exponential formula in terms of its annular intensity, allowing tests which are
not integrable against that intensity. -/
theorem component_laplace (n : ℕ) (f : ExtremeState → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ ω : FinitePoissonCloud.Sample, Real.exp (-FinitePoissonCloud.testIntegral f ω)
      ∂componentLaw υ hυ n) =
      Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂υ.restrict (annulus n))) := by
  let v := componentIntensity υ hυ n
  have hfun : Integrable (fun x => Real.exp (-f x)) (v.normalize : Measure ExtremeState) := by
    apply Integrable.of_bound hf.neg.exp.aestronglyMeasurable 1
    apply ae_of_all
    intro x
    change ‖Real.exp (-f x)‖ ≤ 1
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x))
  have he : (v.mass : ℝ≥0∞) • (v.normalize : Measure ExtremeState) = υ.restrict (annulus n) := by
    have : Nonempty ExtremeState := ⟨⟨1, by simp⟩⟩
    exact congrArg (fun w : FiniteMeasure ExtremeState => (w : Measure ExtremeState))
      v.self_eq_mass_smul_normalize.symm
  change (∫ ω, Real.exp (-(∫ x, f x ∂(FinitePoissonCloud.pointMeasure ω).toMeasure))
    ∂FinitePoissonCloud.law v.mass v.normalize) = _
  rw [FinitePoissonCloud.laplace_functional _ _ f hf hf0, ← he,
    integral_smul_measure, integral_sub (integrable_const 1) hfun]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, ENNReal.coe_toReal]
  congr 1
  ring

theorem finite_components_laplace (n : ℕ) (f : ExtremeState → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ ω : Sample, Real.exp (-(∑ i ∈ Finset.range n,
      FinitePoissonCloud.testIntegral f (ω i))) ∂law υ hυ) =
      Real.exp (-(∑ i ∈ Finset.range n, ∫ x, 1 - Real.exp (-f x) ∂υ.restrict (annulus i))) := by
  have hm : Measurable (fun ω : FinitePoissonCloud.Sample =>
      Real.exp (-FinitePoissonCloud.testIntegral f ω)) :=
    (FinitePoissonCloud.measurable_testIntegral f hf).neg.exp
  have hi : iIndepFun (fun i : Fin n => fun ω : Sample =>
      Real.exp (-FinitePoissonCloud.testIntegral f (ω i))) (law υ hυ) :=
    (iIndepFun_infinitePi (P := componentLaw υ hυ) (fun _ => hm)).precomp Fin.val_injective
  have hex (ω : Sample) : Real.exp (-(∑ i ∈ Finset.range n,
      FinitePoissonCloud.testIntegral f (ω i))) =
      ∏ i : Fin n, Real.exp (-FinitePoissonCloud.testIntegral f (ω i)) := by
    rw [← Fin.sum_univ_eq_sum_range, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [hex]
  rw [hi.integral_fun_prod_eq_prod_integral (fun i => (hm.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)]
  have hc (i : Fin n) :
      (∫ ω : Sample, Real.exp (-FinitePoissonCloud.testIntegral f (ω i)) ∂law υ hυ) =
      Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂υ.restrict (annulus i))) := by
    calc
      _ = ∫ ω : FinitePoissonCloud.Sample, Real.exp (-FinitePoissonCloud.testIntegral f ω)
          ∂componentLaw υ hυ i :=
        (show HasLaw (fun ω : Sample => ω i) (componentLaw υ hυ i) (law υ hυ) from
          ⟨(measurable_pi_apply (i : ℕ)).aemeasurable,
            Measure.infinitePi_map_eval (componentLaw υ hυ) i⟩).integral_comp hm.aestronglyMeasurable
      _ = _ := component_laplace υ hυ i f hf hf0
  simp_rw [hc]
  rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => -(∫ x, 1 - Real.exp (-f x) ∂υ.restrict (annulus i))) n

/-- Finite sums of the component integrals converge to the random measure integral wherever that
integral is finite. -/
theorem component_testIntegral_tendsto (f : ExtremeState → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfinite : ∀ᵐ ω ∂law υ hυ,
      (∫⁻ x, ENNReal.ofReal (f x) ∂(randomMeasure.toFun ω).toMeasure) < ∞) :
    ∀ᵐ ω ∂law υ hυ, Tendsto
      (fun n => ∑ i ∈ Finset.range n, FinitePoissonCloud.testIntegral f (ω i)) atTop
      (𝓝 ((∫⁻ x, ENNReal.ofReal (f x) ∂(randomMeasure.toFun ω).toMeasure).toReal)) := by
  filter_upwards [randomMeasure_toMeasure_ae υ hυ, hfinite] with ω hω hωf
  apply tendsto_sum_of_ofReal_tsum _
    (fun i => FinitePoissonCloud.testIntegral_nonneg f hf0 (ω i)) hωf.ne
  rw [hω, lintegral_sum_measure]
  apply tsum_congr
  intro i
  exact (FinitePoissonCloud.lintegral_eq_ofReal_testIntegral f hf hf0 (ω i)).symm

/-- The Laplace functional of the countable construction, proved by
independence of finite annular sums and dominated convergence. -/
theorem laplace_functional (f : ExtremeState → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hgi : Integrable (fun x => 1 - Real.exp (-f x)) υ)
    (hfinite : ∀ᵐ ω ∂law υ hυ,
      (∫⁻ x, ENNReal.ofReal (f x) ∂(randomMeasure.toFun ω).toMeasure) < ∞) :
    (∫ ω : Sample, Real.exp
      (-((∫⁻ x, ENNReal.ofReal (f x) ∂(randomMeasure.toFun ω).toMeasure).toReal)) ∂law υ hυ) =
      Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂υ)) := by
  let S (n : ℕ) (ω : Sample) := ∑ i ∈ Finset.range n, FinitePoissonCloud.testIntegral f (ω i)
  have hm (n : ℕ) : Measurable (fun ω => Real.exp (-S n ω)) :=
    (Finset.measurable_sum _ (fun i _ =>
      (FinitePoissonCloud.measurable_testIntegral f hf).comp (measurable_pi_apply i))).neg.exp
  have hb (n : ℕ) : ∀ᵐ ω ∂law υ hυ, ‖Real.exp (-S n ω)‖ ≤ (1 : ℝ) := by
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Finset.sum_nonneg (fun i _ =>
      FinitePoissonCloud.testIntegral_nonneg f hf0 (ω i)))
  have ht : ∀ᵐ ω ∂law υ hυ, Tendsto (fun n => Real.exp (-S n ω)) atTop
      (𝓝 (Real.exp (-((∫⁻ x, ENNReal.ofReal (f x) ∂(randomMeasure.toFun ω).toMeasure).toReal)))) := by
    filter_upwards [component_testIntegral_tendsto υ hυ f hf hf0 hfinite] with ω hω
    simpa only [S, ← Real.exp_eq_exp_ℝ] using hω.neg.exp
  have hD := tendsto_integral_of_dominated_convergence (fun _ : Sample => (1 : ℝ))
    (fun n => (hm n).aestronglyMeasurable) (integrable_const 1) hb ht
  have hg : Integrable (fun x => 1 - Real.exp (-f x))
      (Measure.sum (fun n => υ.restrict (annulus n))) := by
    rwa [sum_restrict_annulus]
  have hsum := (hasSum_integral_measure hg).tendsto_sum_nat.neg.exp
  rw [sum_restrict_annulus] at hsum
  have hE : Tendsto (fun n => ∫ ω : Sample, Real.exp (-S n ω) ∂law υ hυ) atTop
      (𝓝 (Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂υ)))) := by
    simp only [S, finite_components_laplace υ hυ _ f hf hf0]
    simpa only [← Real.exp_eq_exp_ℝ] using hsum
  exact tendsto_nhds_unique hD hE

end AnnularPoissonClouds
end
end ConditionedStableLaws
