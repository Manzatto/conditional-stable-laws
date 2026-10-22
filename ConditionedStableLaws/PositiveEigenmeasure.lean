import ConditionedStableLaws.PositiveEigenpair
import ConditionedStableLaws.PositiveFunctionalMeasure

/-!
# A positive left probability eigenmeasure

Normalized evaluations of the positive Neumann resolvent are represented by probability measures.
Compactness of probability measures and the resolvent equation give a left eigenmeasure at the
positive norm-growth rate.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace ConditionedStableLaws.PositiveEigenmeasure
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
theorem exists_eq_norm_of_nonneg [Nonempty M] (f : M →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∃ x : M, f x = ‖f‖ := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn univ_nonempty f.continuous.continuousOn
  refine ⟨x, le_antisymm (f.apply_le_norm x) ?_⟩
  apply (BoundedContinuousFunction.norm_le (hf x)).mpr
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg (hf y)]
  exact hx (mem_univ y)

/-- Existence of a probability measure satisfying the left eigenrelation on every bounded continuous
test function. -/
theorem exists_probability_eigenmeasure [Nonempty M]
    (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) (hcompact : IsCompactOperator T)
    (hT : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x)
    {r : ℝ} (hr : 0 < r) (hlower : ∀ n : ℕ, r^n ≤ ‖T^n‖)
    (hupper : ∀ q : ℝ, r < q → ∀ᶠ n : ℕ in atTop, ‖T^n‖ ≤ q^n) :
    ∃ μ : ProbabilityMeasure M, ∀ g : M →ᵇ ℝ,
      (∫ x, T g x ∂(μ : Measure M)) = r * ∫ x, g x ∂(μ : Measure M) := by
  let a : ℕ → ℝ := fun n => r + 1 / ((n : ℝ)+1)
  have hagt (n : ℕ) : r < a n := lt_add_of_pos_right r (by positivity)
  have hapos (n : ℕ) : 0 < a n := hr.trans (hagt n)
  have ha : Tendsto a atTop (𝓝 r) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := r)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hanti : Antitone a := by intro i j hij; dsimp [a]; gcongr
  have hs (n : ℕ) := PositiveResolvent.scaled_powers_summable T hr.le (hagt n) hupper
  let f : ℕ → M →ᵇ ℝ := fun n => PositiveResolvent.vector T (a n)
  have hf (n : ℕ) (x : M) : 1 ≤ f n x :=
    PositiveResolvent.vector_ge_one T hT (hapos n) (hs n) x
  have hnpos (n : ℕ) : 0 < ‖f n‖ := by
    obtain ⟨x⟩ := ‹Nonempty M›
    exact zero_lt_one.trans_le ((hf n x).trans ((f n).apply_le_norm x))
  choose x hx using (fun n => exists_eq_norm_of_nonneg (f n) (fun y => zero_le_one.trans (hf n y)))
  let L : ℕ → (M →ᵇ ℝ) →L[ℝ] ℝ := fun n =>
    ‖f n‖⁻¹ • (BoundedContinuousFunction.evalCLM ℝ (x n)).comp (PositiveResolvent.operatorSum T (a n))
  have hL (n : ℕ) (g : M →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y) : 0 ≤ L n g := by
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (PositiveResolvent.operatorSum_nonneg T hT (hapos n) (hs n) g hg (x n))
  have hLone (n : ℕ) : L n 1 = 1 := by
    change ‖f n‖⁻¹ * PositiveResolvent.operatorSum T (a n) 1 (x n) = 1
    rw [PositiveResolvent.operatorSum_one T (hs n), hx n]
    exact inv_mul_cancel₀ (hnpos n).ne'
  let μs : ℕ → ProbabilityMeasure M := fun n => PositiveFunctionalMeasure.probabilityMeasure (L n) (hL n) (hLone n)
  have hint (n : ℕ) (g : M →ᵇ ℝ) : (∫ y, g y ∂(μs n : Measure M)) = L n g :=
    PositiveFunctionalMeasure.integral_probabilityMeasure (L n) (hL n) (hLone n) g
  have hLeq (n : ℕ) (g : M →ᵇ ℝ) :
      L n (T g) = a n * L n g - (a n * ‖f n‖⁻¹) * g (x n) := by
    change ‖f n‖⁻¹ * PositiveResolvent.operatorSum T (a n) (T g) (x n) = _
    rw [PositiveResolvent.operatorSum_right_equation T (hapos n).ne' (hs n)]
    change ‖f n‖⁻¹ * (a n * (PositiveResolvent.operatorSum T (a n) g (x n) - g (x n))) =
      a n * (‖f n‖⁻¹ * PositiveResolvent.operatorSum T (a n) g (x n)) - (a n * ‖f n‖⁻¹) * g (x n)
    ring
  have hnorm := PositiveEigenpair.resolvent_norm_tendsto_atTop T hcompact hT hr hlower hupper a ha hagt hanti
  have hinv : Tendsto (fun n => ‖f n‖⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hnorm
  have hcoeff : Tendsto (fun n => a n * ‖f n‖⁻¹) atTop (𝓝 (0 : ℝ)) := by simpa only [mul_zero] using ha.mul hinv
  obtain ⟨μ, φ, hφ, hμ⟩ := CompactSpace.tendsto_subseq μs
  refine ⟨μ, fun g => ?_⟩
  have herror : Tendsto (fun n => (a n * ‖f n‖⁻¹) * g (x n)) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (g.norm_coe_le_norm (x n)) (norm_nonneg _)))
    simpa only [norm_zero, zero_mul] using hcoeff.norm.mul_const ‖g‖
  have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) g
  have hTg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) (T g)
  have hrhs := ((ha.comp hφ.tendsto_atTop).mul hg).sub (herror.comp hφ.tendsto_atTop)
  apply tendsto_nhds_unique hTg
  have hevent : (fun n => a (φ n) * (∫ y, g y ∂(μs (φ n) : Measure M)) -
      (a (φ n) * ‖f (φ n)‖⁻¹) * g (x (φ n))) =
      (fun n => ∫ y, T g y ∂(μs (φ n) : Measure M)) := by
    funext n
    rw [hint, hint, hLeq]
  simpa only [sub_zero, Function.comp_def, hevent] using hrhs

end
end ConditionedStableLaws.PositiveEigenmeasure

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Continuous test identities determine the left kernel eigenmeasure. -/
theorem HypothesisH.left_eigenmeasure_of_continuous_test (h : HypothesisH ρ K)
    (μ : Measure M) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r)
    (htest : ∀ g : M →ᵇ ℝ, (∫ x, h.continuousKernelOperator g x ∂μ) = r * ∫ x, g x ∂μ) :
    K.kernel ∘ₘ μ = ENNReal.ofReal r • μ := by
  have : IsFiniteMeasure (ENNReal.ofReal r • μ) := μ.smul_finite ENNReal.ofReal_ne_top
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  have hint : (∫ y, g y ∂(K.kernel ∘ₘ μ)) = ∫ x, ∫ y, g y ∂K.kernel x ∂μ := by
    rw [Measure.comp_eq_comp_const_apply]
    exact Kernel.integral_comp (g.integrable _)
  rw [hint, integral_smul_measure, ENNReal.toReal_ofReal hr, smul_eq_mul]
  simpa only [h.continuousKernelOperator_apply] using htest g

/-- H alone yields a right continuous eigenfunction and a left probability eigenmeasure at the same
strictly positive rate. -/
theorem HypothesisH.exists_positive_eigenpair_and_eigenmeasure (h : HypothesisH ρ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ η : M →ᵇ ℝ,
      (∀ x, 0 ≤ η x) ∧ ‖η‖ = 1 ∧ h.continuousKernelOperator η = r • η ∧
      ∃ μ : ProbabilityMeasure M, K.kernel ∘ₘ (μ : Measure M) = ENNReal.ofReal r • (μ : Measure M) := by
  have : Nonempty M := (nonempty_of_measure_ne_zero h.surviving_mass_pos.ne').to_subtype.map Subtype.val
  obtain ⟨r, hr, hrone, _, hlower, hupper⟩ := h.exists_positive_operator_growth_rate
  obtain ⟨η, hη, hnorm, heq⟩ := PositiveEigenpair.exists_positive_eigenfunction
    h.continuousKernelOperator h.continuousKernelOperator_isCompact
    h.continuousKernelOperator_nonneg hr hlower hupper
  obtain ⟨μ, hμ⟩ := PositiveEigenmeasure.exists_probability_eigenmeasure
    h.continuousKernelOperator h.continuousKernelOperator_isCompact
    h.continuousKernelOperator_nonneg hr hlower hupper
  exact ⟨r, hr, hrone, η, hη, hnorm, heq, μ,
    h.left_eigenmeasure_of_continuous_test μ hr.le hμ⟩

/-- Complete right Doob eigen-data and a left probability eigenmeasure, both constructed from H and
sharing their eigenvalue. -/
theorem HypothesisH.exists_eigenData_and_eigenmeasure (h : HypothesisH ρ K) :
    ∃ d : DoobTransform.EigenData K.kernel, d.rate ≤ 1 ∧ Continuous d.weight ∧
      (∃ x, d.weight x ≠ 0) ∧ d.liveSet = survivingSet K.kernel ∧
      ∃ μ : ProbabilityMeasure M, K.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) := by
  obtain ⟨r, hr, hrone, η, hη, hnorm, heq, μ, hμ⟩ := h.exists_positive_eigenpair_and_eigenmeasure
  have happrox : Tendsto (fun _n : ℕ => h.continuousKernelOperator η - r • η) atTop (𝓝 0) := by
    simpa only [heq, sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : M →ᵇ ℝ)) atTop (𝓝 0))
  obtain ⟨d, hdr, hcont, hnonzero, hlive⟩ := h.exists_eigenData_of_approximate r hr
    (fun _ => η) (fun _ => hnorm) (fun _ => hη) happrox
  refine ⟨d, ?_, hcont, hnonzero, hlive, μ, ?_⟩
  · rw [hdr]
    exact (ENNReal.ofReal_le_ofReal hrone).trans_eq (by simp)
  · rwa [hdr]

end
end ConditionedStableLaws.StandingHypothesis
