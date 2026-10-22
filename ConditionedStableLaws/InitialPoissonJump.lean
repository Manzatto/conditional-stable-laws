import ConditionedStableLaws.CompensatedCharacteristic
import Mathlib.Probability.Independence.CharacteristicFunction

/-! Adding the finite large-jump cloud to the compensated small-jump limit. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.AnnularPoissonClouds
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)

theorem centeredComponent_zero_ae (f : ExtremeState → ℝ)
    (hz : ∀ y ∈ annulus 0, f y = 0) :
    centeredComponent υ f 0 =ᵐ[law υ hυ] (fun _ => 0) := by
  have hm : (∫ y, f y ∂υ.restrict (annulus 0)) = 0 :=
    integral_eq_zero_of_ae ((ae_restrict_mem (measurableSet_annulus 0)).mono hz)
  filter_upwards [supported_components_ae υ hυ] with ω hω
  have ha : ∀ᵐ y ∂((component 0).toFun ω).toMeasure, y ∈ annulus 0 := by
    rw [ae_iff]
    exact hω 0
  change (∫ y, f y ∂((component 0).toFun ω).toMeasure) - _ = 0
  rw [integral_eq_zero_of_ae (ha.mono hz), hm, sub_self]

/-- Independence of the initial cloud from every small-jump partial sum. The zero contribution on
its own shell follows from support. -/
theorem initial_independent_centered_partialSum
    (f g : ExtremeState → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hz : ∀ y ∈ annulus 0, f y = 0) (n : ℕ) :
    IndepFun (fun ω : Sample => FinitePoissonCloud.testIntegral g (ω 0))
      (CompensatedSeries.partialSum (centeredComponent υ f) n) (law υ hυ) := by
  classical
  let Y : ℕ → Sample → ℝ := fun i ω => if i = 0 then
    FinitePoissonCloud.testIntegral g (ω i) else centeredComponent υ f i ω
  have hm (i : ℕ) : Measurable (Y i) := by
    by_cases hi : i = 0
    · simpa [Y, hi, Function.comp_def] using
        (FinitePoissonCloud.measurable_testIntegral g hg).comp (measurable_pi_apply 0)
    · simpa [Y, hi] using measurable_centeredComponent υ f hf i
  have hi : iIndepFun Y (law υ hυ) := by
    apply iIndepFun_infinitePi (X := fun i ω => if i = 0 then
      FinitePoissonCloud.testIntegral g ω else
      FinitePoissonCloud.testIntegral f ω - ∫ y, f y ∂υ.restrict (annulus i))
    intro i
    by_cases hi : i = 0
    · simpa [hi] using FinitePoissonCloud.measurable_testIntegral g hg
    · simpa only [ite_eq_right hi] using (FinitePoissonCloud.measurable_testIntegral f hf).sub_const _
  have hind := (hi.indepFun_finsetSum_of_notMem hm
    (s := (Finset.range n).erase 0) (i := 0) (by simp)).symm
  apply hind.congr (ae_of_all _ (fun ω => by simp [Y]))
  filter_upwards [centeredComponent_zero_ae υ hυ f hz] with ω hω
  simp only [Finset.sum_apply, CompensatedSeries.partialSum]
  calc
    _ = ∑ i ∈ (Finset.range n).erase 0, centeredComponent υ f i ω := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_right (Finset.mem_erase.mp hi).1
    _ = ∑ i ∈ Finset.range n, centeredComponent υ f i ω := by
      by_cases hn : 0 ∈ Finset.range n
      · simpa only [hω, add_zero] using
          Finset.sum_erase_add (s := Finset.range n) (f := fun i => centeredComponent υ f i ω) hn
      · rw [Finset.erase_eq_of_notMem hn]

theorem initial_add_partialSum_characteristic (n : ℕ) (t : ℝ)
    (f g : ExtremeState → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B)
    (hz : ∀ y ∈ annulus 0, f y = 0) :
    (∫ ω : Sample, Complex.exp ((t * (FinitePoissonCloud.testIntegral g (ω 0) +
      CompensatedSeries.partialSum (centeredComponent υ f) n ω) : ℝ) * Complex.I) ∂law υ hυ) =
    Complex.exp (∫ y, Complex.exp ((t*g y : ℝ) * Complex.I) - 1 ∂υ.restrict (annulus 0)) *
      Complex.exp (∑ i ∈ Finset.range n,
        ∫ y, compensatedExponent t f y ∂υ.restrict (annulus i)) := by
  have hm : Measurable (fun ω : Sample => FinitePoissonCloud.testIntegral g (ω 0)) :=
    (FinitePoissonCloud.measurable_testIntegral g hg).comp (measurable_pi_apply 0)
  have hp : Measurable (CompensatedSeries.partialSum (centeredComponent υ f) n) :=
    Finset.measurable_sum _ (fun i _ => measurable_centeredComponent υ f hf i)
  have hi := (initial_independent_centered_partialSum υ hυ f g hf hg hz n).comp
    (show Measurable (fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I)) by fun_prop)
    (show Measurable (fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I)) by fun_prop)
  have he (a b : ℝ) : Complex.exp ((t*(a+b) : ℝ) * Complex.I) =
      Complex.exp ((t*a : ℝ) * Complex.I) * Complex.exp ((t*b : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  have hexp : Measurable (fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I)) := by fun_prop
  have hfactor := hi.integral_fun_mul_eq_mul_integral
    (hexp.comp hm).aestronglyMeasurable (hexp.comp hp).aestronglyMeasurable
  simp only [Function.comp_def] at hfactor
  rw [hfactor,
    centered_partialSum_characteristic υ hυ n t f hf hB hb]
  congr 1
  have hl : HasLaw (fun ω : Sample => ω 0) (componentLaw υ hυ 0) (law υ hυ) :=
    ⟨(measurable_pi_apply 0).aemeasurable, Measure.infinitePi_map_eval (componentLaw υ hυ) 0⟩
  calc
    _ = ∫ ω : FinitePoissonCloud.Sample,
        Complex.exp ((t * FinitePoissonCloud.testIntegral g ω : ℝ) * Complex.I)
        ∂componentLaw υ hυ 0 :=
      hl.integral_comp (show AEStronglyMeasurable
        (fun ω : FinitePoissonCloud.Sample =>
          Complex.exp ((t * FinitePoissonCloud.testIntegral g ω : ℝ) * Complex.I))
        (componentLaw υ hυ 0) by
        have := FinitePoissonCloud.measurable_testIntegral g hg
        fun_prop)
    _ = _ := component_characteristic υ hυ 0 t g hg

/-- Adding the initial finite cloud preserves the convergence in probability of the compensated
annular sums, even when its marks have no first or second moment. -/
theorem initial_add_partialSum_tendstoInMeasure
    (f g : ExtremeState → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B)
    (hfi : Integrable (fun y => (f y)^2) υ) :
    TendstoInMeasure (law υ hυ)
      (fun n ω => FinitePoissonCloud.testIntegral g (ω 0) +
        CompensatedSeries.partialSum (centeredComponent υ f) n ω) atTop
      (fun ω => FinitePoissonCloud.testIntegral g (ω 0) +
        compensatedIntegral υ hυ f hf hB hb ω) := by
  have ht := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (centered_partialSum_tendsto_eLpNorm υ hυ f hf hB hb hfi)
  rw [tendstoInMeasure_iff_dist] at ht ⊢
  intro ε hε
  simpa only [Real.dist_eq, add_sub_add_left_eq_sub] using ht ε hε

/-- The full large-plus-compensated-small characteristic formula on the
same canonical Poisson-cloud space. -/
theorem initial_add_compensated_characteristic (t : ℝ)
    (f g : ExtremeState → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B)
    (hfi : Integrable (fun y => (f y)^2) υ)
    (hz : ∀ y ∈ annulus 0, f y = 0) :
    (∫ ω : Sample, Complex.exp ((t * (FinitePoissonCloud.testIntegral g (ω 0) +
      compensatedIntegral υ hυ f hf hB hb ω) : ℝ) * Complex.I) ∂law υ hυ) =
      Complex.exp ((∫ y, Complex.exp ((t*g y : ℝ) * Complex.I) - 1
        ∂υ.restrict (annulus 0)) + ∫ y, compensatedExponent t f y ∂υ) := by
  have hm : Measurable (fun ω : Sample => FinitePoissonCloud.testIntegral g (ω 0)) :=
    (FinitePoissonCloud.measurable_testIntegral g hg).comp (measurable_pi_apply 0)
  have hp (n : ℕ) : Measurable (CompensatedSeries.partialSum (centeredComponent υ f) n) :=
    Finset.measurable_sum _ (fun i _ => measurable_centeredComponent υ f hf i)
  have hchar (X : Sample → ℝ) (hX : Measurable X) :
      charFun ((law υ hυ).map X) t =
        ∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) ∂law υ hυ := by
    rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  have ht := ((initial_add_partialSum_tendstoInMeasure υ hυ f g hf hB hb hfi).tendstoInDistribution
    (fun n => (hm.add (hp n)).aemeasurable)).tendsto_charFun t
  have he (n : ℕ) : charFun ((law υ hυ).map (fun ω =>
      FinitePoissonCloud.testIntegral g (ω 0) +
      CompensatedSeries.partialSum (centeredComponent υ f) n ω)) t =
      Complex.exp (∫ y, Complex.exp ((t*g y : ℝ) * Complex.I) - 1 ∂υ.restrict (annulus 0)) *
        Complex.exp (∑ i ∈ Finset.range n,
          ∫ y, compensatedExponent t f y ∂υ.restrict (annulus i)) := by
    rw [hchar (fun ω => FinitePoissonCloud.testIntegral g (ω 0) +
      CompensatedSeries.partialSum (centeredComponent υ f) n ω) (hm.add (hp n))]
    exact initial_add_partialSum_characteristic υ hυ n t f g hf hg hB hb hz
  simp_rw [he] at ht
  rw [hchar (fun ω => FinitePoissonCloud.testIntegral g (ω 0) +
    compensatedIntegral υ hυ f hf hB hb ω)
    (hm.add (measurable_compensatedIntegral υ hυ f hf hB hb))] at ht
  have hgi : Integrable (compensatedExponent t f)
      (Measure.sum (fun n => υ.restrict (annulus n))) := by
    rw [sum_restrict_annulus]
    exact compensatedExponent_integrable υ t f hf hfi
  have hs := (hasSum_integral_measure hgi).tendsto_sum_nat
  rw [sum_restrict_annulus] at hs
  rw [Complex.exp_add]
  exact tendsto_nhds_unique ht ((Complex.continuous_exp.tendsto _ |>.comp hs).const_mul _)

end
end ConditionedStableLaws.AnnularPoissonClouds
