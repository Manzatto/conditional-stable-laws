import ConditionedStableLaws.PoissonExistence

/-!
First moments of finite and countable Poisson clouds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem poisson_mean_series (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial * n)
      (r : ℝ) := by
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have he (n : ℕ) : Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) /
      (n + 1).factorial * (n + 1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hh : HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) /
      (n + 1).factorial * (n + 1)) (r : ℝ) := by
    simpa only [he, mul_one] using hs
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_zero,
    mul_zero, sub_zero, Nat.cast_add, Nat.cast_one] using hh

theorem poisson_mean_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_natCast] using (poisson_mean_series r).summable

theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_mean_series r).tsum_eq

theorem poisson_lintegral_mean (r : ℝ≥0) :
    (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r) = r := by
  have he := ofReal_integral_eq_lintegral_ofReal (poisson_mean_integrable r)
    (ae_of_all _ (fun n => Nat.cast_nonneg n))
  simpa only [poisson_mean, ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal] using he.symm

namespace FinitePoissonCloud

/-- Integrating a nonnegative test over the cloud is a measurable random variable. -/
theorem measurable_lintegral (f : ExtremeState → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω : Sample => ∫⁻ x, f x ∂(pointMeasure ω).toMeasure) := by
  apply measurable_of_sigma
  intro n
  simp only [pointMeasure, tag, LocallyFinitePointMeasure.empirical]
  simp_rw [lintegral_sum_measure, lintegral_dirac' _ hf]
  exact Measurable.tsum (fun i => hf.comp (measurable_pi_apply i))

/-- Campbell's first-moment identity for the concrete marked cloud, with no
integrability restriction on the nonnegative test. -/
theorem campbell (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω : Sample, ∫⁻ x, f x ∂(pointMeasure ω).toMeasure ∂law r ν) =
      (r : ℝ≥0∞) * ∫⁻ x, f x ∂(ν : Measure ExtremeState) := by
  rw [lintegral_law r ν _ (measurable_lintegral f hf)]
  have he (n : ℕ) :
      (∫⁻ a : Fin n → ExtremeState, ∫⁻ x, f x ∂(pointMeasure ⟨n,a⟩).toMeasure
        ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))) =
      (n : ℝ≥0∞) * ∫⁻ x, f x ∂(ν : Measure ExtremeState) := by
    simp only [pointMeasure, LocallyFinitePointMeasure.empirical]
    simp_rw [lintegral_sum_measure, lintegral_dirac' _ hf]
    rw [lintegral_tsum (f := fun i : Fin n => fun a : Fin n → ExtremeState => f (a i))
      (fun i => (hf.comp (measurable_pi_apply i)).aemeasurable)]
    have hi (i : Fin n) :
        (∫⁻ a : Fin n → ExtremeState, f (a i)
          ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))) =
        ∫⁻ x, f x ∂(ν : Measure ExtremeState) :=
      (measurePreserving_eval (fun _ : Fin n => (ν : Measure ExtremeState)) i).lintegral_comp hf
    simp_rw [hi]
    simp
  simp_rw [he]
  rw [lintegral_mul_const _ (by fun_prop), poisson_lintegral_mean]

end FinitePoissonCloud

namespace AnnularPoissonClouds

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)

/-- The construction's almost-sure measure identity, useful for arbitrary
test integrals rather than just region counts. -/
theorem randomMeasure_toMeasure_ae :
    ∀ᵐ ω ∂law υ hυ, (randomMeasure.toFun ω).toMeasure =
      Measure.sum (fun n => ((component n).toFun ω).toMeasure) := by
  filter_upwards [randomMeasure_apply_ae υ hυ] with ω hω
  ext A hA
  rw [hω A, Measure.sum_apply _ hA]

theorem aemeasurable_lintegral (f : ExtremeState → ℝ≥0∞) (hf : Measurable f) :
    AEMeasurable (fun ω : Sample => ∫⁻ x, f x ∂(randomMeasure.toFun ω).toMeasure) (law υ hυ) := by
  have hm : Measurable (fun ω : Sample => ∑' n,
      ∫⁻ x, f x ∂(FinitePoissonCloud.pointMeasure (ω n)).toMeasure) :=
    Measurable.tsum (fun n => (FinitePoissonCloud.measurable_lintegral f hf).comp
      (measurable_pi_apply n))
  apply hm.aemeasurable.congr
  filter_upwards [randomMeasure_toMeasure_ae υ hυ] with ω hω
  rw [hω, lintegral_sum_measure]
  rfl

/-- Campbell's formula for the locally finite Poisson random measure. Both sides may be infinite. -/
theorem campbell (f : ExtremeState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω : Sample, ∫⁻ x, f x ∂(randomMeasure.toFun ω).toMeasure ∂law υ hυ) =
      ∫⁻ x, f x ∂υ := by
  have he : (fun ω : Sample => ∫⁻ x, f x ∂(randomMeasure.toFun ω).toMeasure) =ᵐ[law υ hυ]
      (fun ω => ∑' n, ∫⁻ x, f x ∂((component n).toFun ω).toMeasure) := by
    filter_upwards [randomMeasure_toMeasure_ae υ hυ] with ω hω
    rw [hω, lintegral_sum_measure]
  rw [lintegral_congr_ae he, lintegral_tsum]
  · have hc (n : ℕ) :
        (∫⁻ ω : Sample, ∫⁻ x, f x ∂((component n).toFun ω).toMeasure ∂law υ hυ) =
        ∫⁻ x, f x ∂υ.restrict (annulus n) := by
      have h := (measurePreserving_eval_infinitePi (componentLaw υ hυ) n).lintegral_comp
        (FinitePoissonCloud.measurable_lintegral f hf)
      change (∫⁻ ω : Sample, ∫⁻ x, f x ∂(FinitePoissonCloud.pointMeasure (ω n)).toMeasure
        ∂law υ hυ) = _
      calc
        _ = ∫⁻ ω : FinitePoissonCloud.Sample, ∫⁻ x, f x ∂(FinitePoissonCloud.pointMeasure ω).toMeasure
            ∂componentLaw υ hυ n := h
        _ = _ := ?_
      change (∫⁻ ω : FinitePoissonCloud.Sample, ∫⁻ x, f x ∂(FinitePoissonCloud.pointMeasure ω).toMeasure
        ∂FinitePoissonCloud.law (componentIntensity υ hυ n).mass
          (componentIntensity υ hυ n).normalize) = _
      rw [FinitePoissonCloud.campbell _ _ f hf]
      have : Nonempty ExtremeState := ⟨⟨1, by simp⟩⟩
      have hm : ((componentIntensity υ hυ n).mass : ℝ≥0∞) •
          ((componentIntensity υ hυ n).normalize : Measure ExtremeState) =
          υ.restrict (annulus n) :=
        congrArg (fun w : FiniteMeasure ExtremeState => (w : Measure ExtremeState))
          (componentIntensity υ hυ n).self_eq_mass_smul_normalize.symm
      rw [← hm, lintegral_smul_measure]
      rfl
    simp_rw [hc]
    rw [← lintegral_sum_measure, sum_restrict_annulus]
  · intro n
    exact ((FinitePoissonCloud.measurable_lintegral f hf).comp
      (measurable_pi_apply n)).aemeasurable

/-- Integrable intensity tests give finite random Poisson integrals almost surely. -/
theorem lintegral_lt_top_ae (f : ExtremeState → ℝ≥0∞) (hf : Measurable f)
    (hfi : (∫⁻ x, f x ∂υ) < ∞) :
    ∀ᵐ ω ∂law υ hυ, (∫⁻ x, f x ∂(randomMeasure.toFun ω).toMeasure) < ∞ := by
  apply ae_lt_top' (aemeasurable_lintegral υ hυ f hf)
  rw [campbell υ hυ f hf]
  exact hfi.ne

/-- A zero-intensity measurable set contains no atoms almost surely. -/
theorem mass_zero_ae_of_intensity_zero (A : Set ExtremeState) (hA : MeasurableSet A)
    (hz : υ A = 0) :
    ∀ᵐ ω ∂law υ hυ, (randomMeasure.toFun ω).toMeasure A = 0 := by
  have hm := aemeasurable_lintegral υ hυ (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  have hi := campbell υ hυ (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  simp only [lintegral_indicator hA, lintegral_one, Measure.restrict_apply_univ] at hm hi
  exact (lintegral_eq_zero_iff' hm).mp (hi.trans hz)

end AnnularPoissonClouds
end
end ConditionedStableLaws
