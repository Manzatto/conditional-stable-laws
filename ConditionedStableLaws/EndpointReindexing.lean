import ConditionedStableLaws.QProcessEndpoint
import ConditionedStableLaws.PoissonTargetStart
import ConditionedStableLaws.ConvergingTogether

/-!
# Endpoint reindexing of conditioned Birkhoff sums

Both bounded-average errors under reindexing. For finite-valued measurable observables, Hypothesis H
implies that the terminal observation divided by any diverging positive normalization tends to zero
in conditioned probability.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators
noncomputable section
namespace ConditionedStableLaws

/-- A bounded finite average has the same bound. -/
theorem abs_birkhoffAverage_le (u : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ i, |u i| ≤ B) (n : ℕ) : |birkhoffAverage u n| ≤ B := by
  by_cases hn : n = 0
  · simp [hn, birkhoffAverage, hB]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [birkhoffAverage, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
  calc |birkhoffSum u n| ≤ ∑ i ∈ Finset.range n, |u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, B := Finset.sum_le_sum fun i _ => hu i
    _ = B * n := by simp [mul_comm]

/-- The bounded-average reindexing bound with the denominator `n+1`. -/
theorem bounded_average_succ_difference (u : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ i, |u i| ≤ B) {n : ℕ} (hn : 0 < n) :
    |birkhoffAverage u (n + 1) - birkhoffAverage u n| ≤ 2 * B / (n + 1 : ℕ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have heq : birkhoffAverage u (n + 1) - birkhoffAverage u n =
      (u n - birkhoffAverage u n) / (n + 1 : ℕ) := by
    unfold birkhoffAverage
    rw [birkhoffSum_succ]
    push_cast
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hn1]
  apply div_le_div_of_nonneg_right _ hn1.le
  exact (abs_sub _ _).trans (by linarith [hu n, abs_birkhoffAverage_le u hB hu n])

namespace CanonicalChain
open StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Under H, terminal conditioned laws send every sequence of μ-small measurable sets to zero, by
the spectral estimate. -/
theorem conditioned_endpoint_small_sets_of_H
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (hsmall : Tendsto (fun n => μ.real (U n)) atTop (𝓝 0)) :
    Tendsto (fun n => (C.conditionedMeasure x.val n).real
      {ω | ω n ∈ Option.some '' U n}) atTop (𝓝 0) := by
  obtain ⟨A, θ, _hA, hθ0, hθ1, hdec⟩ := h.exists_pointwise_decay d hc μ hleft hnorm
  set r : ℝ := d.rate.toReal
  have hr : r ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨d.rate_ne_zero, d.rate_ne_top⟩
  set p : ℕ → ℝ := fun n => μ.real (U n)
  set a : ℕ → ℝ := fun n => r⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ
  have ha : Tendsto a atTop (𝓝 (d.weight x.val).toReal) := by
    have ht := QProcessEndpoint.normalized_integral_tendsto h d hc μ hleft hnorm
      measurable_const (f := fun _ => (1 : ℝ)) (B := 1) (fun _ => by norm_num) x.val
    simpa only [integral_const, smul_eq_mul, mul_one, probReal_univ,
      toKilledKernel_kernel] using ht
  have hx : (d.weight x.val).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨x.property, d.weight_ne_top _⟩
  let F : ℕ → M → ℝ := fun n y => (U n).indicator (fun _ => (1 : ℝ)) y - p n
  have hFmeas (n : ℕ) : Measurable (F n) := (measurable_const.indicator (hU n)).sub_const _
  have hFbound (n : ℕ) (y : M) : |F n y| ≤ 2 := by
    have hp0 : 0 ≤ p n := measureReal_nonneg
    have hp1 : p n ≤ 1 := measureReal_le_one
    dsimp [F]
    by_cases hy : y ∈ U n
    · rw [indicator_of_mem hy, abs_le]
      constructor <;> linarith
    · rw [indicator_of_notMem hy, abs_le]
      constructor <;> linarith
  have hFzero (n : ℕ) : ∫ y, F n y ∂μ = 0 := by
    rw [show F n = (fun y => (U n).indicator (fun _ => (1 : ℝ)) y - p n) from rfl,
      integral_sub ((integrable_const _).indicator (hU n)) (integrable_const _),
      integral_indicator_const _ (hU n)]
    simp [p]
  have hcenter : Tendsto (fun k : ℕ => r⁻¹ ^ (k + 1) *
      ∫ y, F (k + 1) y ∂(C.killedTransition ^ (k + 1)) x.val) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_)
      (show Tendsto (fun k : ℕ => A * θ ^ k * 2) atTop (𝓝 0) from by
        simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul A).mul_const 2)
    simpa only [Real.norm_eq_abs, toKilledKernel_kernel] using hdec (F (k + 1)) (hFmeas _) 2
      (hFbound _) (hFzero _) k x.val
  have hap : Tendsto (fun k : ℕ => p (k + 1) * a (k + 1)) atTop (𝓝 0) := by
    simpa using (hsmall.comp (tendsto_add_atTop_nat 1)).mul
      (ha.comp (tendsto_add_atTop_nat 1))
  have hnum : Tendsto (fun k : ℕ => r⁻¹ ^ (k + 1) *
      ((C.killedTransition ^ (k + 1)) x.val).real (U (k + 1))) atTop (𝓝 0) := by
    have ht := hcenter.add hap
    simp only [add_zero] at ht
    apply ht.congr
    intro k
    have : IsFiniteMeasure ((C.killedTransition ^ (k + 1)) x.val) :=
      (killedKernel_power_isFinite C.toKilledKernel (k + 1)).isFiniteMeasure _
    dsimp [F, a]
    rw [integral_sub ((integrable_const _).indicator (hU _)) (integrable_const _),
      integral_indicator_const _ (hU _), integral_const, smul_eq_mul, smul_eq_mul]
    ring
  apply (tendsto_add_atTop_iff_nat 1).1
  have ht := hnum.div (ha.comp (tendsto_add_atTop_nat 1)) hx
  simp only [zero_div] at ht
  apply ht.congr
  intro k
  rw [Measure.real, C.conditionedMeasure_endpoint x.val (k + 1) (U _) (hU _),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  dsimp [a]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero hr))]
  rw [div_eq_mul_inv, mul_comm]
  rfl

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Finite-valued measurable functions have vanishing tails, without a moment assumption. -/
theorem finite_observable_tail_tendsto_zero (μ : Measure M) [IsFiniteMeasure μ]
    {f : M → ℝ} (hf : Measurable f) :
    Tendsto (fun t : ℝ => μ.real {y | t < |f y|}) atTop (𝓝 0) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ) (s := fun t : ℝ => {y | t < |f y|})
    (fun _ => (measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using hf.norm)).nullMeasurableSet)
    (fun s t hst y hy => lt_of_le_of_lt hst hy) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ t : ℝ, {y | t < |f y|}) = ∅ := by
    ext y
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨|f y|, le_rfl⟩
  rw [he, measure_empty] at ht
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

/-- **Negligible terminal value.** Every finite-valued measurable observable has a negligible
terminal value on every diverging positive scale, under H. This includes all stable, Gaussian and
LLN scales. -/
theorem normalized_endpoint_probability_of_H
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {f : M → ℝ} (hf : Measurable f)
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (C.conditionedMeasure x.val n).real
      {ω | ε < |zeroExtension f (ω n) / a n|}) atTop (𝓝 0) := by
  have hs := (finite_observable_tail_tendsto_zero μ hf).comp (ha.const_mul_atTop hε)
  have ht := C.conditioned_endpoint_small_sets_of_H h d hc μ hleft hnorm x
    (fun n => {y | ε * a n < |f y|}) (fun _ => measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using hf.norm)) hs
  apply ht.congr'
  filter_upwards [ha.eventually_gt_atTop 0] with n han
  congr 1
  ext ω
  cases hω : ω n with
  | none => simp [hω, zeroExtension, hε.le]
  | some y =>
    simp only [hω, Set.mem_ofPred_eq, Set.mem_image, Option.some.injEq,
      exists_eq_right, zeroExtension_some, abs_div, abs_of_pos han]
    exact (lt_div_iff₀ han).symm


/-- The shifted sum contains times 1 through n. -/
def pathShiftedBirkhoffSum (f : M → ℝ) (n : ℕ) (ω : Path M) : ℝ :=
  birkhoffSum (fun i => zeroExtension f (ω (i + 1))) n

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
@[fun_prop]
theorem measurable_pathShiftedBirkhoffSum {f : M → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (pathShiftedBirkhoffSum f n) := by
  unfold pathShiftedBirkhoffSum birkhoffSum
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_zeroExtension hf).comp (measurable_pi_apply (i + 1))

/-- The entire reindexing error vanishes in conditioned probability, under H. -/
theorem normalized_reindexing_probability_of_H
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {f : M → ℝ} (hf : Measurable f)
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (C.conditionedMeasure x.val n).real
      {ω | ε < |pathBirkhoffSum f n ω / a n - pathShiftedBirkhoffSum f n ω / a n|})
      atTop (𝓝 0) := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val
      (d.liveSet_subset_survivingSet x.property) n
  have hend := C.normalized_endpoint_probability_of_H h d hc μ hleft hnorm x hf a ha
    (ε / 2) (half_pos hε)
  have hstart := (constant_div_tendsto_zero (f x.val) ha).abs
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hend
  filter_upwards [hstart.eventually_lt_const
    (show |(0 : ℝ)| < ε / 2 by simpa only [abs_zero] using half_pos hε)] with n hn
  have heq : {ω | ε < |pathBirkhoffSum f n ω / a n - pathShiftedBirkhoffSum f n ω / a n|}
      =ᵐ[C.conditionedMeasure x.val n]
      {ω | ε < |f x.val / a n - zeroExtension f (ω n) / a n|} := by
    filter_upwards [C.ae_initial_conditionedMeasure x.val n] with ω hω
    apply propext
    rw [← sub_div]
    change (ε < |(birkhoffSum (fun i => zeroExtension f (ω i)) n -
      birkhoffSum (fun i => zeroExtension f (ω (i + 1))) n) / a n|) ↔ _
    rw [birkhoffSum_endpoint_difference, hω, zeroExtension_some, sub_div]
  rw [measureReal_congr heq]
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  change ε < |f x.val / a n - zeroExtension f (ω n) / a n| at hω
  change ε / 2 < |zeroExtension f (ω n) / a n|
  have hb := abs_sub (f x.val / a n) (zeroExtension f (ω n) / a n)
  linarith

/-- Every centered limit on a diverging scale survives the change from 0,...,n−1 to 1,...,n. -/
theorem shifted_limit_of_H
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {f : M → ℝ} (hf : Measurable f)
    (a center : ℕ → ℝ) (ha : Tendsto a atTop atTop) (Z : Ω' → ℝ)
    (hlim : TendstoInDistribution
      (fun n ω => (pathBirkhoffSum f n ω - center n) / a n) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q) :
    TendstoInDistribution
      (fun n ω => (pathShiftedBirkhoffSum f n ω - center n) / a n) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val
      (d.liveSet_subset_survivingSet x.property) n
  apply tendstoInDistribution_of_varying_probability_approximation
    (fun n => C.conditionedMeasure x.val n) Q _ _ Z
    (fun n => ((measurable_pathShiftedBirkhoffSum hf n).sub_const _).div_const _)
    (fun n => ((measurable_pathBirkhoffSum hf n).sub_const _).div_const _) hlim
  intro ε hε
  have ht := C.normalized_reindexing_probability_of_H h d hc μ hleft hnorm x hf a ha ε hε
  apply ht.congr
  intro n
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  have heq : (pathShiftedBirkhoffSum f n ω - center n) / a n -
      (pathBirkhoffSum f n ω - center n) / a n =
      -(pathBirkhoffSum f n ω / a n - pathShiftedBirkhoffSum f n ω / a n) := by ring
  rw [heq, abs_neg]

/-- Adding the final observation also preserves every centered limit on a diverging scale. -/
theorem inclusive_sum_limit_of_H
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {f : M → ℝ} (hf : Measurable f)
    (a center : ℕ → ℝ) (ha : Tendsto a atTop atTop) (Z : Ω' → ℝ)
    (hlim : TendstoInDistribution
      (fun n ω => (pathBirkhoffSum f n ω - center n) / a n) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q) :
    TendstoInDistribution
      (fun n ω => (pathBirkhoffSum f (n + 1) ω - center n) / a n) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val
      (d.liveSet_subset_survivingSet x.property) n
  apply tendstoInDistribution_of_varying_probability_approximation
    (fun n => C.conditionedMeasure x.val n) Q _ _ Z
    (fun n => ((measurable_pathBirkhoffSum hf (n + 1)).sub_const _).div_const _)
    (fun n => ((measurable_pathBirkhoffSum hf n).sub_const _).div_const _) hlim
  intro ε hε
  have ht := C.normalized_endpoint_probability_of_H h d hc μ hleft hnorm x hf a ha ε hε
  apply ht.congr
  intro n
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, pathBirkhoffSum_succ]
  have heq : (pathBirkhoffSum f n ω + zeroExtension f (ω n) - center n) / a n -
      (pathBirkhoffSum f n ω - center n) / a n = zeroExtension f (ω n) / a n := by ring
  rw [heq]


omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- **Reindexing bounds for bounded observables.** The two bounds for the conditioned expectations,
with denominators n and n+1 respectively. -/
theorem bounded_conditioned_indexing
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State)
    {f : M → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, |f y| ≤ B)
    {n : ℕ} (hn : 0 < n) :
    |(∫ ω, pathShiftedBirkhoffSum f n ω / n ∂C.conditionedMeasure x.val n) -
      ∫ ω, pathBirkhoffSum f n ω / n ∂C.conditionedMeasure x.val n| ≤ 2 * B / n ∧
    |(∫ ω, pathBirkhoffSum f (n + 1) ω / (n + 1 : ℕ) ∂C.conditionedMeasure x.val n) -
      ∫ ω, pathBirkhoffSum f n ω / n ∂C.conditionedMeasure x.val n| ≤ 2 * B / (n + 1 : ℕ) := by
  have : IsProbabilityMeasure (C.conditionedMeasure x.val n) :=
    C.conditionedMeasure_isProbability_of_surviving x.val
      (d.liveSet_subset_survivingSet x.property) n
  have hu (ω : Path M) (i : ℕ) : |zeroExtension f (ω i)| ≤ B := by
    cases ω i with
    | none => simpa only [zeroExtension_none, abs_zero] using hB
    | some y => exact hb y
  have hi (k : ℕ) : Integrable (fun ω => pathBirkhoffSum f k ω / k)
      (C.conditionedMeasure x.val n) := by
    apply Integrable.of_bound ((measurable_pathBirkhoffSum hf k).div_const _).aestronglyMeasurable B
    apply ae_of_all
    intro ω
    simpa only [Real.norm_eq_abs, birkhoffAverage, pathBirkhoffSum] using abs_birkhoffAverage_le
      (fun i => zeroExtension f (ω i)) hB (hu ω) k
  have his : Integrable (fun ω => pathShiftedBirkhoffSum f n ω / n)
      (C.conditionedMeasure x.val n) := by
    apply Integrable.of_bound ((measurable_pathShiftedBirkhoffSum hf n).div_const _).aestronglyMeasurable B
    apply ae_of_all
    intro ω
    simpa only [Real.norm_eq_abs, birkhoffAverage, pathShiftedBirkhoffSum] using abs_birkhoffAverage_le
      (fun i => zeroExtension f (ω (i + 1))) hB (fun i => hu ω (i + 1)) n
  have hbound (X Y : Path M → ℝ) (hX : Integrable X (C.conditionedMeasure x.val n))
      (hY : Integrable Y (C.conditionedMeasure x.val n)) (K : ℝ)
      (hK : ∀ ω, |X ω - Y ω| ≤ K) :
      |(∫ ω, X ω ∂C.conditionedMeasure x.val n) - ∫ ω, Y ω ∂C.conditionedMeasure x.val n| ≤ K := by
    rw [← integral_sub hX hY]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := C.conditionedMeasure x.val n)
        (f := fun ω => X ω - Y ω) (C := K)
        (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hK ω))
  constructor
  · apply hbound _ _ his (hi n) _
    intro ω
    rw [abs_sub_comm]
    exact normalized_endpoint_bound (fun i => zeroExtension f (ω i)) n B n
      (by exact_mod_cast hn) (hu ω)
  · apply hbound _ _ (hi (n + 1)) (hi n) _
    intro ω
    exact bounded_average_succ_difference (fun i => zeroExtension f (ω i)) hB (hu ω) hn

end CanonicalChain
end ConditionedStableLaws
