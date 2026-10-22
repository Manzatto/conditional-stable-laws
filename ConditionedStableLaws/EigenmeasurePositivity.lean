import ConditionedStableLaws.PositiveEigenpair
import ConditionedStableLaws.EigenmeasureDensity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# A left eigenmeasure gives positive mass to the surviving region

The escaping region can have positive eigenmeasure mass. The assertion needed
for normalization is instead that the surviving region has positive mass.
We use Fredholm's alternative for the compact operator killed outside the
escaping region: it has no nonzero eigenvalue because every point there dies
in finite time.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Apply the killed kernel after setting the test function to zero off `S`. -/
def HypothesisH.restrictedOperator (h : HypothesisH ρ K) (S : Set M)
    (hS : MeasurableSet S) : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ) := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  exact (h.smoothedOperator 1).comp
    ((ConditionalMixing.lpMultiplication ρ
      (indicatorConstLp ∞ hS (measure_ne_top ρ S) (1 : ℝ))).comp
      (BoundedContinuousFunction.toLp ∞ ρ ℝ))

theorem HypothesisH.restrictedOperator_apply (h : HypothesisH ρ K)
    (S : Set M) (hS : MeasurableSet S) (f : M →ᵇ ℝ) (x : M) :
    h.restrictedOperator S hS f x = ∫ y in S, f y ∂K.kernel x := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  change h.smoothedOperator 1 _ x = _
  rw [h.smoothedOperator_apply, h.stepEvaluation_apply, one_mul, ← integral_indicator hS]
  apply integral_congr_ae
  apply (h.absolutelyContinuous x).ae_eq
  filter_upwards [ConditionalMixing.lpMultiplication_ae ρ
    (indicatorConstLp ∞ hS (measure_ne_top ρ S) (1 : ℝ))
    (BoundedContinuousFunction.toLp ∞ ρ ℝ f),
    indicatorConstLp_coeFn (p := ∞) (hs := hS) (hμs := measure_ne_top ρ S) (c := (1 : ℝ)),
    BoundedContinuousFunction.coeFn_toLp ∞ ρ ℝ f] with y hm hi hf
  change ConditionalMixing.lpMultiplication ρ _ (BoundedContinuousFunction.toLp ∞ ρ ℝ f) y = _
  rw [hm, hi, hf]
  by_cases hy : y ∈ S <;> simp [hy]

theorem HypothesisH.restrictedOperator_isCompact (h : HypothesisH ρ K)
    (S : Set M) (hS : MeasurableSet S) : IsCompactOperator (h.restrictedOperator S hS) := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  exact ((transitionIntegralOperator_isCompact ρ ⟨h.density, h.continuous_density⟩).smul
    (1 : ℝ)).comp_clm _

/-- Restriction does not change iteration when started in a forward invariant set. -/
theorem HypothesisH.restrictedOperator_pow_apply_of_invariant (h : HypothesisH ρ K)
    (S : Set M) (hS : MeasurableSet S) (hclosed : ∀ x ∈ S, K.kernel x Sᶜ = 0)
    (n : ℕ) (f : M →ᵇ ℝ) {x : M} (hx : x ∈ S) :
    (h.restrictedOperator S hS ^ n) f x = (h.continuousKernelOperator ^ n) f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change h.restrictedOperator S hS ((h.restrictedOperator S hS ^ n) f) x =
        h.continuousKernelOperator ((h.continuousKernelOperator ^ n) f) x
      rw [h.restrictedOperator_apply, h.continuousKernelOperator_apply,
        ← integral_indicator hS]
      have hae : ∀ᵐ y ∂K.kernel x, y ∈ S := hclosed x hx
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      rw [indicator_of_mem hy]
      exact ih hy

/-- Killing outside the escaping set leaves no nonzero real eigenvalue. -/
theorem HypothesisH.restricted_escaping_no_eigenvalue (h : HypothesisH ρ K)
    {r : ℝ} (hr : r ≠ 0) :
    ¬ Module.End.HasEigenvalue
      (h.restrictedOperator (escapingSet K.kernel) (measurableSet_escapingSet K.kernel) :
        Module.End ℝ (M →ᵇ ℝ)) r := by
  intro he
  obtain ⟨f, hf⟩ := he.exists_hasEigenvector
  have heq : h.restrictedOperator (escapingSet K.kernel)
      (measurableSet_escapingSet K.kernel) f = r • f := hf.apply_eq_smul
  have hpow (n : ℕ) :
      (h.restrictedOperator (escapingSet K.kernel) (measurableSet_escapingSet K.kernel)^n) f =
        r^n • f := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, heq,
        smul_smul, pow_succ]
  have hz (x : M) (hx : x ∈ escapingSet K.kernel) : f x = 0 := by
    obtain ⟨n, hn, hmass⟩ := hx
    have hval := congrArg (fun g : M →ᵇ ℝ => g x) (hpow n)
    rw [h.restrictedOperator_pow_apply_of_invariant _ _
      (fun y hy => escaping_no_jump_to_surviving K.kernel hy) n f ⟨n, hn, hmass⟩,
      h.continuousKernelOperator_pow_apply] at hval
    have hm : (K.kernel^n) x = 0 := Measure.measure_univ_eq_zero.mp hmass
    rw [hm, integral_zero_measure] at hval
    exact (mul_eq_zero.mp hval.symm).resolve_left (pow_ne_zero n hr)
  have hzero : h.restrictedOperator (escapingSet K.kernel)
      (measurableSet_escapingSet K.kernel) f = 0 := by
    ext x
    rw [h.restrictedOperator_apply]
    exact setIntegral_eq_zero_of_forall_eq_zero hz
  have hrf : r • f = 0 := heq.symm.trans hzero
  exact hf.2 ((smul_eq_zero.mp hrf).resolve_left hr)

/-- Integral action of the restricted operator on a left eigenmeasure
concentrated on the restriction set. -/
theorem HypothesisH.integral_restrictedOperator (h : HypothesisH ρ K)
    (μ : Measure M) [IsFiniteMeasure μ] (S : Set M) (hS : MeasurableSet S)
    (hμS : μ Sᶜ = 0) (r : ℝ≥0∞) (hleft : K.kernel ∘ₘ μ = r • μ)
    (f : M →ᵇ ℝ) :
    (∫ x, h.restrictedOperator S hS f x ∂μ) = r.toReal * ∫ x, f x ∂μ := by
  have hfi : Integrable (S.indicator (f : M → ℝ)) (K.kernel ∘ₘ μ) :=
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)).indicator hS
  have hint : (∫ y, S.indicator (f : M → ℝ) y ∂(K.kernel ∘ₘ μ)) =
      ∫ x, ∫ y, S.indicator (f : M → ℝ) y ∂K.kernel x ∂μ := by
    rw [Measure.comp_eq_comp_const_apply] at hfi ⊢
    exact Kernel.integral_comp (a := ()) hfi
  simp_rw [h.restrictedOperator_apply, ← integral_indicator hS]
  rw [← hint, hleft, integral_smul_measure, integral_indicator hS,
    Measure.restrict_eq_self_of_ae_mem hμS]
  rfl

/-- Every positive-rate left probability eigenmeasure charges the surviving
region. It need not give zero mass to the escaping region. -/
theorem HypothesisH.eigenmeasure_surviving_mass_pos (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] (r : ℝ≥0∞)
    (hr0 : r ≠ 0) (hrt : r ≠ ∞) (hleft : K.kernel ∘ₘ μ = r • μ) :
    0 < μ (survivingSet K.kernel) := by
  by_contra hn
  have hz : μ (escapingSet K.kernel)ᶜ = 0 := le_antisymm (le_of_not_gt hn) bot_le
  let T := h.restrictedOperator (escapingSet K.kernel) (measurableSet_escapingSet K.kernel)
  have hr : r.toReal ≠ 0 := (ENNReal.toReal_pos hr0 hrt).ne'
  have hres := (h.restrictedOperator_isCompact (escapingSet K.kernel)
    (measurableSet_escapingSet K.kernel)).hasEigenvalue_or_mem_resolventSet hr
  have hunit := spectrum.mem_resolventSet_iff.mp
    (hres.resolve_left (h.restricted_escaping_no_eigenvalue hr))
  have hsurj := (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2
  obtain ⟨f, hf⟩ := hsurj (1 : M →ᵇ ℝ)
  have heq : r.toReal • f - T f = 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one, sub_apply,
      smul_apply, one_apply_eq_self] using hf
  have hi := congrArg (fun g : M →ᵇ ℝ => ∫ x, g x ∂μ) heq
  have hfi : Integrable (f : M → ℝ) μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hTi : Integrable (T f : M → ℝ) μ :=
    (T f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace (T f))
  simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul] at hi
  rw [integral_sub (hfi.const_mul _) hTi, integral_const_mul,
    h.integral_restrictedOperator μ _ (measurableSet_escapingSet K.kernel) hz r hleft f] at hi
  simp at hi

/-- The pairing used to normalize the right eigenfunction is strictly positive. -/
theorem HypothesisH.eigenfunction_integral_pos (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (hne : ∃ x, d.weight x ≠ 0) (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) :
    0 < ∫⁻ x, d.weight x ∂μ := by
  apply (lintegral_pos_iff_support d.measurable_weight).mpr
  change 0 < μ d.liveSet
  rw [h.eigenfunction_liveSet_eq d hc hne]
  exact h.eigenmeasure_surviving_mass_pos μ d.rate d.rate_ne_zero d.rate_ne_top hleft

end
end ConditionedStableLaws.StandingHypothesis
