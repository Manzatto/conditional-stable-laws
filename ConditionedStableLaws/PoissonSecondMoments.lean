import ConditionedStableLaws.PoissonLaplace
import Mathlib.Probability.Moments.Variance

/-! Second moments and variance of finite Poisson clouds. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem poisson_second_factorial_series (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial *
      ((n : ℝ) * (n - 1))) ((r : ℝ) ^ 2) := by
  have hs := (hasSum_one_poissonMeasure r).mul_left ((r : ℝ) ^ 2)
  have he (n : ℕ) : Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 2) /
      (n + 2).factorial * ((n + 2 : ℝ) * (n + 1)) =
      (r : ℝ)^2 * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rw [pow_succ, pow_succ]
    field_simp
    ring
  apply (hasSum_nat_add_iff' 2).mp
  have he' (n : ℕ) : (n + 2 : ℝ) - 1 = n + 1 := by ring
  simpa only [Nat.cast_add, Nat.cast_ofNat, he', Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_self,
    add_zero, sub_zero, he, mul_one] using hs

theorem poisson_second_moment_series (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial * (n : ℝ)^2)
      ((r : ℝ)^2 + r) := by
  convert (poisson_second_factorial_series r).add (poisson_mean_series r) using 1
  funext n
  ring

theorem poisson_second_moment_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [norm_pow, Real.norm_natCast] using
    (poisson_second_moment_series r).summable

theorem poisson_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2 + r := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_second_moment_series r).tsum_eq

theorem poisson_second_factorial_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) * (n - 1)) (poissonMeasure r) := by
  convert (poisson_second_moment_integrable r).sub (poisson_mean_integrable r) using 1
  funext n
  simp only [Pi.sub_apply]
  ring

theorem poisson_second_factorial_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) * (n - 1) ∂poissonMeasure r) = (r : ℝ)^2 := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_second_factorial_series r).tsum_eq

namespace FinitePoissonCloud

theorem norm_testIntegral_le (f : ExtremeState → ℝ) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B) (ω : Sample) : ‖testIntegral f ω‖ ≤ (ω.1 : ℝ) * B := by
  rw [testIntegral_eq_sum]
  exact (norm_sum_le _ _).trans (by
    calc
      ∑ i : Fin ω.1, ‖f (ω.2 i)‖ ≤ ∑ _i : Fin ω.1, B :=
        Finset.sum_le_sum (fun i _ => hb _)
      _ = _ := by simp)

theorem integrable_testIntegral (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) {B : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ x, ‖f x‖ ≤ B) : Integrable (testIntegral f) (law r ν) := by
  have hi : Integrable (fun ω : Sample => (ω.1 : ℝ) * B) (law r ν) :=
    ((size_hasLaw r ν).integrable_comp (poisson_mean_integrable r)).mul_const B
  apply hi.mono' (measurable_testIntegral f hf).aestronglyMeasurable
  exact ae_of_all _ (norm_testIntegral_le f hb)

theorem integrable_testIntegral_sq (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) {B : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ x, ‖f x‖ ≤ B) : Integrable (fun ω => (testIntegral f ω)^2) (law r ν) := by
  have hi : Integrable (fun ω : Sample => (ω.1 : ℝ)^2 * B^2) (law r ν) :=
    ((size_hasLaw r ν).integrable_comp (poisson_second_moment_integrable r)).mul_const (B^2)
  apply hi.mono' ((measurable_testIntegral f hf).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [norm_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_testIntegral_le f hb ω) 2

theorem testIntegral_mean (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖f x‖ ≤ B) :
    (∫ ω, testIntegral f ω ∂law r ν) = (r : ℝ) * ∫ x, f x ∂(ν : Measure ExtremeState) := by
  have hfi : Integrable f (ν : Measure ExtremeState) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hb)
  rw [integral_law r ν _ (measurable_testIntegral f hf) (integrable_testIntegral r ν f hf hB hb)]
  have he (n : ℕ) : (∫ a : Fin n → ExtremeState, testIntegral f ⟨n,a⟩
      ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))) =
      (n : ℝ) * ∫ x, f x ∂(ν : Measure ExtremeState) := by
    simp_rw [testIntegral_eq_sum]
    change (∫ a : Fin n → ExtremeState, ∑ i : Fin n, f (a i)
      ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))) = _
    rw [integral_finsetSum (f := fun i : Fin n => fun a : Fin n → ExtremeState => f (a i)) Finset.univ
      (fun i _ => (measurePreserving_eval (fun _ : Fin n => (ν : Measure ExtremeState)) i).integrable_comp_of_integrable hfi)]
    simp_rw [integral_comp_eval (μ := fun _ : Fin n => (ν : Measure ExtremeState)) hf.aestronglyMeasurable]
    simp
  simp_rw [he]
  rw [integral_mul_const, poisson_mean]

/-- The second moment of a fixed number of iid marks. -/
theorem fixed_size_second_moment (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) (n : ℕ) :
    (∫ a : Fin n → ExtremeState, (∑ i : Fin n, f (a i))^2
      ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))) =
      (n : ℝ) * ∫ x, (f x)^2 ∂(ν : Measure ExtremeState) +
        ((n : ℝ) * (n - 1)) * (∫ x, f x ∂(ν : Measure ExtremeState))^2 := by
  have hf2 : MemLp f 2 (ν : Measure ExtremeState) :=
    MemLp.of_bound hf.aestronglyMeasurable B (ae_of_all _ hb)
  have hX (i : Fin n) : MemLp (fun a : Fin n → ExtremeState => f (a i)) 2
      (Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))) :=
    hf2.comp_measurePreserving (measurePreserving_eval _ i)
  have hS := memLp_finsetSum (s := Finset.univ) (fun i _ => hX i)
  have hvar := variance_sum_pi (μ := fun _ : Fin n => (ν : Measure ExtremeState)) (fun _ => hf2)
  have he : (∑ i : Fin n, (fun a : Fin n → ExtremeState => f (a i))) =
      (fun a => ∑ i : Fin n, f (a i)) := by
    funext a
    exact Finset.sum_apply a _ _
  rw [he, variance_eq_sub hS, variance_eq_sub hf2] at hvar
  have hmean : (∫ a : Fin n → ExtremeState, ∑ i : Fin n, f (a i)
      ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))) =
      (n : ℝ) * ∫ x, f x ∂(ν : Measure ExtremeState) := by
    rw [integral_finsetSum (f := fun i : Fin n => fun a : Fin n → ExtremeState => f (a i)) _
      (fun i _ => (hX i).integrable (by norm_num))]
    simp_rw [integral_comp_eval (μ := fun _ : Fin n => (ν : Measure ExtremeState)) hf.aestronglyMeasurable]
    simp
  change (∫ a : Fin n → ExtremeState, (∑ i, f (a i))^2 ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState))) -
      (∫ a : Fin n → ExtremeState, ∑ i, f (a i) ∂Measure.pi (fun _ : Fin n => (ν : Measure ExtremeState)))^2 = _ at hvar
  rw [hmean] at hvar
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Pi.pow_apply] at hvar
  nlinarith

/-- Campbell's second-moment formula for a bounded real test. -/
theorem testIntegral_second_moment (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖f x‖ ≤ B) :
    (∫ ω, (testIntegral f ω)^2 ∂law r ν) =
      (r : ℝ) * ∫ x, (f x)^2 ∂(ν : Measure ExtremeState) +
        (r : ℝ)^2 * (∫ x, f x ∂(ν : Measure ExtremeState))^2 := by
  rw [integral_law r ν _ ((measurable_testIntegral f hf).pow_const 2)
    (integrable_testIntegral_sq r ν f hf hB hb)]
  simp_rw [testIntegral_eq_sum, fixed_size_second_moment ν f hf hb]
  rw [integral_add ((poisson_mean_integrable r).mul_const _)
      ((poisson_second_factorial_integrable r).mul_const _),
    integral_mul_const, integral_mul_const, poisson_mean, poisson_second_factorial_moment]

/-- The centered variance is exactly the intensity integral of the squared test. -/
theorem testIntegral_variance (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (f : ExtremeState → ℝ) (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖f x‖ ≤ B) :
    Var[testIntegral f; law r ν] = (r : ℝ) * ∫ x, (f x)^2 ∂(ν : Measure ExtremeState) := by
  have hL : MemLp (testIntegral f) 2 (law r ν) :=
    (memLp_two_iff_integrable_sq (measurable_testIntegral f hf).aestronglyMeasurable).mpr
      (integrable_testIntegral_sq r ν f hf hB hb)
  rw [variance_eq_sub hL]
  change (∫ ω, (testIntegral f ω)^2 ∂law r ν) - (∫ ω, testIntegral f ω ∂law r ν)^2 = _
  rw [testIntegral_second_moment r ν f hf hB hb, testIntegral_mean r ν f hf hB hb]
  ring

end FinitePoissonCloud

end
end ConditionedStableLaws
