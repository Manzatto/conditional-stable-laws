import ConditionedStableLaws.PoissonRandomMeasure
import ConditionedStableLaws.VagueEvaluation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# A finite cloud with a Poisson number of independent marks

The sample space records the finite number of marks and all their locations. The law first chooses a
Poisson count, then a finite product of the mark law. The resulting point measure is measurable for
the vague topology.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.FinitePoissonCloud
noncomputable section

abbrev Sample := Sigma (fun n : ℕ => Fin n → ExtremeState)

def tag (n : ℕ) (a : Fin n → ExtremeState) : Sample := ⟨n,a⟩

theorem measurable_sigmaMk (n : ℕ) : Measurable (tag n : (Fin n → ExtremeState) → Sample) :=
  Measurable.of_le_map (iInf_le _ n)

theorem measurable_of_sigma {Y : Type*} [MeasurableSpace Y] {f : Sample → Y}
    (hf : ∀ n, Measurable (fun a => f (tag n a))) : Measurable f := by
  rw [measurable_iff_le_map]
  change _ ≤ (⨅ n : ℕ, (inferInstance : MeasurableSpace (Fin n → ExtremeState)).map (tag n)).map f
  rw [MeasurableSpace.map_iInf]
  apply le_iInf
  intro n
  rw [MeasurableSpace.map_comp]
  exact (hf n).le_map

theorem measurable_size : Measurable (Sigma.fst : Sample → ℕ) :=
  measurable_of_sigma (fun _ => measurable_const)

/-- A finite cloud as a point measure, allowing repeated marks. -/
def pointMeasure : Sample → LocallyFinitePointMeasure :=
  fun ω => LocallyFinitePointMeasure.empirical ω.2

theorem measurable_pointMeasure : Measurable pointMeasure := by
  apply measurable_of_sigma
  intro n
  exact LocallyFinitePointMeasure.measurable_empirical n

def randomPointMeasure : RandomPointMeasure Sample := ⟨pointMeasure, measurable_pointMeasure⟩

/-- Given its size, every mark has law `ν`, independently of the other marks. -/
def markKernel (ν : ProbabilityMeasure ExtremeState) : Kernel ℕ Sample where
  toFun n := (Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))).map (tag n)
  measurable' := measurable_of_countable _

instance markKernel_isMarkov (ν : ProbabilityMeasure ExtremeState) : IsMarkovKernel (markKernel ν) := by
  constructor
  intro n
  change IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))).map (tag n))
  exact (Measure.isProbabilityMeasure_map_iff (measurable_sigmaMk n).aemeasurable).mpr inferInstance

/-- The probability law of the random cloud. -/
def law (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState) : Measure Sample :=
  markKernel ν ∘ₘ poissonMeasure r

instance law_isProbability (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState) :
    IsProbabilityMeasure (law r ν) := by unfold law; infer_instance

theorem lintegral_law (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : Sample → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ω ∂law r ν) =
      ∫⁻ n, ∫⁻ a : Fin n → ExtremeState, f ⟨n,a⟩
        ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState)) ∂poissonMeasure r := by
  rw [law, Measure.lintegral_bind (markKernel ν).aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro n
  change (∫⁻ ω, f ω ∂(Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))).map (tag n)) = _
  exact lintegral_map hf (measurable_sigmaMk n)

/-- The number recorded by a sample is its total point mass. -/
theorem pointMeasure_mass (ω : Sample) : (pointMeasure ω).toMeasure univ = ω.1 := by
  exact LocallyFinitePointMeasure.empirical_univ ω.2

/-- Choosing the marks does not alter the Poisson law of the cloud size. -/
theorem size_hasLaw (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState) :
    HasLaw (fun ω : Sample => ω.1) (poissonMeasure r) (law r ν) := by
  refine ⟨measurable_size.aemeasurable, ?_⟩
  ext A hA
  rw [Measure.map_apply measurable_size hA]
  change (markKernel ν ∘ₘ poissonMeasure r) (Sigma.fst ⁻¹' A) = _
  rw [Measure.bind_apply (measurable_size hA) (markKernel ν).aemeasurable]
  have heq (n : ℕ) : markKernel ν n (Sigma.fst ⁻¹' A) = A.indicator (fun _ => 1) n := by
    change (Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))).map (tag n)
      (Sigma.fst ⁻¹' A) = _
    rw [Measure.map_apply (measurable_sigmaMk n) (measurable_size hA)]
    by_cases hn : n ∈ A
    · simp [Set.preimage, tag, hn]
    · simp [Set.preimage, tag, hn]
  simp_rw [heq]
  simp [lintegral_indicator hA]

/-- In particular the total mass has exactly the Poisson count law. -/
theorem total_mass_hasLaw (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState) :
    HasLaw (fun ω => (pointMeasure ω).toMeasure univ) (poissonCountLaw r) (law r ν) := by
  have hh := (hasLaw_map (P := poissonMeasure r)
    (show AEMeasurable (fun n : ℕ => (n : ℝ≥0∞)) (poissonMeasure r) by fun_prop)).comp
    (size_hasLaw r ν)
  simpa only [Function.comp_def, pointMeasure_mass, poissonCountLaw, ENNReal.toNNReal_coe] using hh

/-- Integrate by first fixing the cloud size and then all its marks. -/
theorem integral_law {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : Sample → E) (hf : Measurable f) (hfi : Integrable f (law r ν)) :
    (∫ ω, f ω ∂law r ν) =
      ∫ n, ∫ a : Fin n → ExtremeState, f ⟨n,a⟩
        ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState)) ∂poissonMeasure r := by
  change Integrable f (markKernel ν ∘ₘ poissonMeasure r) at hfi
  change (∫ ω, f ω ∂(markKernel ν ∘ₘ poissonMeasure r)) = _
  rw [Measure.comp_eq_comp_const_apply] at hfi ⊢
  rw [Kernel.integral_comp hfi]
  apply integral_congr_ae
  filter_upwards [] with n
  change (∫ ω, f ω ∂(Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))).map (tag n)) = _
  exact integral_map (measurable_sigmaMk n).aemeasurable hf.aestronglyMeasurable

/-- The Poisson probability generating function, including arbitrary real
arguments; the exponential series establishes convergence. -/
theorem integral_pow_poisson (r : ℝ≥0) (z : ℝ) :
    (∫ n : ℕ, z ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (z - 1)) := by
  rw [integral_poissonMeasure]
  have hs := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * z)).mul_left
    (Real.exp (-(r : ℝ)))
  have he : Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * z) =
      Real.exp ((r : ℝ) * (z - 1)) := by rw [← Real.exp_add]; congr 1; ring
  rw [← he]
  convert hs.tsum_eq using 1
  · congr 1
    ext n
    simp only [smul_eq_mul, mul_pow]
    ring
  · simp only [← Real.exp_eq_exp_ℝ]

/-- A bounded multiplicative test of the cloud has the usual Poisson exponential functional. This is
derived from the marked-cloud law. -/
theorem integral_product (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (∫ ω : Sample, ∏ i : Fin ω.1, f (ω.2 i) ∂law r ν) =
      Real.exp ((r : ℝ) * ((∫ x, f x ∂(ν : Measure ExtremeState)) - 1)) := by
  have hm : Measurable (fun ω : Sample => ∏ i : Fin ω.1, f (ω.2 i)) := by
    apply measurable_of_sigma
    intro n
    change Measurable (fun a : Fin n → ExtremeState => ∏ i, f (a i))
    exact Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
  have hi : Integrable (fun ω : Sample => ∏ i : Fin ω.1, f (ω.2 i)) (law r ν) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ => hf0 _))]
    calc
      ∏ i : Fin ω.1, f (ω.2 i) ≤ ∏ _i : Fin ω.1, (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => hf0 _) (fun i _ => hf1 _)
      _ = 1 := by simp
  rw [integral_law r ν _ hm hi]
  simp_rw [integral_fintype_prod_eq_pow, Fintype.card_fin]
  exact integral_pow_poisson r _

/-- The Laplace functional for a nonnegative test function on a finite cloud. -/
theorem laplace_functional (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ ω : Sample, Real.exp (-(∫ x, f x ∂(pointMeasure ω).toMeasure)) ∂law r ν) =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-f x) ∂(ν : Measure ExtremeState)) - 1)) := by
  have heq (ω : Sample) : Real.exp (-(∫ x, f x ∂(pointMeasure ω).toMeasure)) =
      ∏ i : Fin ω.1, Real.exp (-f (ω.2 i)) := by
    rw [pointMeasure, LocallyFinitePointMeasure.integral_empirical, ← Finset.sum_neg_distrib,
      Real.exp_sum]
  simp_rw [heq]
  exact integral_product r ν (fun x => Real.exp (-f x)) hf.neg.exp
    (fun _ => (Real.exp_pos _).le) (fun x => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x)))

/-- Complex generating function of a Poisson count, proved by its exponential
series. This includes the unit-circle characteristic function. -/
theorem integral_pow_poisson_complex (r : ℝ≥0) (z : ℂ) :
    (∫ n : ℕ, z ^ n ∂poissonMeasure r) = Complex.exp ((r : ℂ) * (z - 1)) := by
  rw [integral_poissonMeasure]
  have hs := (NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * z)).mul_left
    (Complex.exp (-(r : ℂ)))
  have he : Complex.exp (-(r : ℂ)) * Complex.exp ((r : ℂ) * z) =
      Complex.exp ((r : ℂ) * (z - 1)) := by rw [← Complex.exp_add]; congr 1; ring
  rw [← he]
  convert hs.tsum_eq using 1
  · congr 1
    ext n
    simp only [Complex.real_smul, ← Complex.ofReal_exp, ← Complex.ofReal_neg]
    push_cast
    simp only [mul_pow]
    ring
  · simp only [← Complex.exp_eq_exp_ℂ]

/-- The characteristic-functional calculation for bounded complex marks. -/
theorem integral_product_complex (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℂ) (hf : Measurable f) (hf1 : ∀ x, ‖f x‖ ≤ 1) :
    (∫ ω : Sample, ∏ i : Fin ω.1, f (ω.2 i) ∂law r ν) =
      Complex.exp ((r : ℂ) * ((∫ x, f x ∂(ν : Measure ExtremeState)) - 1)) := by
  have hm : Measurable (fun ω : Sample => ∏ i : Fin ω.1, f (ω.2 i)) := by
    apply measurable_of_sigma
    intro n
    change Measurable (fun a : Fin n → ExtremeState => ∏ i, f (a i))
    exact Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
  have hi : Integrable (fun ω : Sample => ∏ i : Fin ω.1, f (ω.2 i)) (law r ν) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    apply ae_of_all
    intro ω
    rw [norm_prod]
    calc
      ∏ i : Fin ω.1, ‖f (ω.2 i)‖ ≤ ∏ _i : Fin ω.1, (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hf1 _)
      _ = 1 := by simp
  rw [integral_law r ν _ hm hi]
  simp_rw [integral_fintype_prod_eq_pow, Fintype.card_fin]
  exact integral_pow_poisson_complex r _

/-- Characteristic functional of the finite cloud. -/
theorem characteristic_functional (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) :
    (∫ ω : Sample, Complex.exp ((∫ x, f x ∂(pointMeasure ω).toMeasure) * Complex.I)
      ∂law r ν) =
      Complex.exp ((r : ℂ) * ((∫ x, Complex.exp (f x * Complex.I)
        ∂(ν : Measure ExtremeState)) - 1)) := by
  have heq (ω : Sample) :
      Complex.exp ((∫ x, f x ∂(pointMeasure ω).toMeasure) * Complex.I) =
        ∏ i : Fin ω.1, Complex.exp (f (ω.2 i) * Complex.I) := by
    rw [pointMeasure, LocallyFinitePointMeasure.integral_empirical, Complex.ofReal_sum,
      Finset.sum_mul, Complex.exp_sum]
  simp_rw [heq]
  apply integral_product_complex r ν _ (hf.complex_ofReal.mul_const Complex.I).cexp
  intro x
  simp

end
end ConditionedStableLaws.FinitePoissonCloud
