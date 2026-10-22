import ConditionedStableLaws.SeparatedChainBounds
import ConditionedStableLaws.HypothesisSpectralGap
import ConditionedStableLaws.SuperlogCutoff

/-!
# Chain-derived mixed configuration estimates

The concrete superlogarithmic cutoff is independent of the moment order. Both separated-event and
excluded-configuration estimates are proved for the trimmed canonical coordinates. The spectral
package is derived from H.
-/
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 800000
namespace ConditionedStableLaws

/-- Repeated labels contribute the appropriate powers in a mixed moment. -/
theorem factorialSlots_product {J : Type*} [Fintype J] (r : J → ℕ) (p : J → ℝ) :
    (∏ i : Fin (∑ j, r j), p ((factorialSlotsEquiv r).symm i).1) = ∏ j, p j ^ r j := by
  rw [Equiv.prod_comp (factorialSlotsEquiv r).symm (fun a : Σ j, Fin (r j) => p a.1),
    Fintype.prod_sigma]
  simp

/-- Changing targets at finitely many horizons does not alter the configuration bounds or their
asymptotic consequences. -/
def RareConfigurationEstimates.congr_targets_eventually
    {Ω A J : Type*} [MeasurableSpace Ω] [Fintype J]
    {P : ℕ → Measure Ω} {X : ∀ n : ℕ, Fin n → Ω → A}
    {U V : ℕ → J → Set A} {p : J → ℕ → ℝ} {r : J → ℕ}
    (e : RareConfigurationEstimates P X U p r)
    (hUV : ∀ᶠ n in atTop, U n = V n) : RareConfigurationEstimates P X V p r where
  cutoff := e.cutoff
  error := e.error
  excludedBound := e.excludedBound
  cutoff_sublinear := e.cutoff_sublinear
  error_nonneg := e.error_nonneg
  scaled_error_tendsto := e.scaled_error_tendsto
  excluded_tendsto := e.excluded_tendsto
  separated_error := by
    filter_upwards [e.separated_error, hUV] with n hn heq
    rwa [← heq]
  excluded_error := by
    filter_upwards [e.excluded_error, hUV] with n hn heq
    rwa [← heq]

namespace CanonicalChain
open StandingHypothesis EndpointTrimming SeparatedChainBounds
variable {M J : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  [Fintype J] {ρ : Measure M} (C : CanonicalChain M)

/-- All factorial-moment configuration hypotheses, from the spectral gap and one-step small-target
estimates. The excluded bound is a sum whose limit follows from the cluster argument. -/
def spectral_trimmed_configuration_estimates
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (μ : Measure M) (hμρ : μ ≪ ρ)
    (hmean : ∀ v, s.mean v = ∫ y, v y ∂μ)
    (hleft : ∀ v, s.mean (((d.rate.toReal)⁻¹ • h.transitionOperator) v) = s.mean v)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, a ≤ (d.weight y).toReal)
    (δ : ℕ → ℝ) (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hsmall : ∀ᶠ n in atTop, ∀ y, (C.killedTransition y).real (U n) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (rate : ℝ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n)) atTop (𝓝 rate))
    (targets : ℕ → J → Set M) (hTargets : ∀ n j, MeasurableSet (targets n j))
    (hTargetsU : ∀ n j, targets n j ⊆ U n)
    (r : J → ℕ) (hr : 0 < ∑ j, r j) :
    RareConfigurationEstimates (fun n => C.conditionedMeasure x.val n)
      (fun n => trimmedObservations (superlogCutoff n) (fun i : Fin n => fun ω : Path M => ω i.val))
      (fun n => liftedTargets (fun j => Option.some '' targets n j))
      (fun j n => (μ.withDensity d.weight).real (targets n j)) r := by
  let k := ∑ j, r j
  let A : ℕ → Fin k → Set M := fun n i => targets n ((factorialSlotsEquiv r).symm i).1
  let D := mixingConstant h d s x.val k
  have hD : 0 ≤ D := mixingConstant_nonneg h d s x.val k
  have hθ := scaled_geometric_superlogCutoff_sub_one_tendsto_zero_of_nonneg
    s.decay_nonneg s.decay_lt_one (show (0 : ℝ) ≤ 1 by norm_num) 1
  have he : Tendsto (fun n : ℕ => (n : ℝ)*s.decay^(superlogCutoff n-1)*δ n) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, zero_mul] using hθ.mul hδ
  have hsum := C.conditioned_excluded_sum_tendsto_zero h d s μ hμρ hmean hleft x U hU a ha
    hlower δ hδ0 hsmall hδ superlogCutoff rate (Eventually.of_forall superlogCutoff_pos)
    superlogCutoff_div_tendsto_zero hp he k hr A (fun n i => hTargets n _) (fun n i => hTargetsU n _)
  refine {
    cutoff := superlogCutoff
    error := fun n => D*s.decay^(superlogCutoff n-1)
    excludedBound := fun n => ∑ t ∈ excludedConfigurations n k (superlogCutoff n),
      C.trimmedTargetWeight x.val n (superlogCutoff n) k (A n) t
    cutoff_sublinear := superlogCutoff_div_tendsto_zero
    error_nonneg := Eventually.of_forall (fun n => mul_nonneg hD (pow_nonneg s.decay_nonneg _))
    scaled_error_tendsto := scaled_geometric_superlogCutoff_sub_one_tendsto_zero_of_nonneg
      s.decay_nonneg s.decay_lt_one hD k
    excluded_tendsto := hsum
    separated_error := ?_
    excluded_error := ?_ }
  · have hpow : Tendsto (fun n => s.decay^(superlogCutoff n-1)) atTop (𝓝 0) := by
      simpa only [pow_zero, one_mul] using
        scaled_geometric_superlogCutoff_sub_one_tendsto_zero_of_nonneg
          s.decay_nonneg s.decay_lt_one (show (0 : ℝ) ≤ 1 by norm_num) 0
    have hlim : Tendsto (fun n => ‖h.stepEvaluation (d.rate.toReal)⁻¹ x.val‖*s.constant*
        s.decay^(superlogCutoff n-1)*‖s.one‖) atTop (𝓝 0) := by
      simpa using (hpow.const_mul (‖h.stepEvaluation (d.rate.toReal)⁻¹ x.val‖*s.constant)).mul_const ‖s.one‖
    have hx : 0 < (d.weight x.val).toReal / 2 :=
      half_pos (ENNReal.toReal_pos x.property (d.weight_ne_top _))
    filter_upwards [superlogCutoff_sub_one_eventually_pos, (tendsto_order.mp hlim).2 _ hx]
      with n hqn hsmalln t ht
    rw [← C.trimmedTargetWeight_eq_mixed x.val n (superlogCutoff n) (targets n) r t,
      ← factorialSlots_product r (fun j => (μ.withDensity d.weight).real (targets n j))]
    exact C.conditioned_separated_trimmedWeight_mixing h d s μ hμρ hmean x n (superlogCutoff n)
      k (by omega) hr t ht hsmalln.le (A n) (fun i => hTargets n _)
  · exact Eventually.of_forall (fun n => by
      rw [C.sum_excluded_trimmed_mixed_eq]
      rw [abs_of_nonneg (sum_nonneg (fun t _ => C.trimmedTargetWeight_nonneg
        x.val n (superlogCutoff n) k (A n) t))])

/-- The chain configuration criterion under H, with the spectral package supplied by H. -/
theorem nonempty_trimmed_configuration_estimates_of_H
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, a ≤ (d.weight y).toReal)
    (δ : ℕ → ℝ) (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hsmall : ∀ᶠ n in atTop, ∀ y, (C.killedTransition y).real (U n) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (rate : ℝ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n)) atTop (𝓝 rate))
    (targets : ℕ → J → Set M) (hTargets : ∀ n j, MeasurableSet (targets n j))
    (hTargetsU : ∀ n j, targets n j ⊆ U n)
    (r : J → ℕ) (hr : 0 < ∑ j, r j) :
    Nonempty (RareConfigurationEstimates (fun n => C.conditionedMeasure x.val n)
      (fun n => trimmedObservations (superlogCutoff n) (fun i : Fin n => fun ω : Path M => ω i.val))
      (fun n => liftedTargets (fun j => Option.some '' targets n j))
      (fun j n => (μ.withDensity d.weight).real (targets n j)) r) := by
  obtain ⟨s, hsmean, hsleft⟩ := h.exists_survivalGapData_with_mean_invariant d hc μ hleft hnorm
  exact ⟨C.spectral_trimmed_configuration_estimates h d s μ
    (h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft) hsmean hsleft
    x U hU a ha hlower δ hδ0 hsmall hδ rate hp targets hTargets hTargetsU r hr⟩

/-- Independent Poisson limits for the original, untrimmed canonical counts.
Endpoint restoration uses only the first-order boundary-hit probability. -/
theorem independent_poisson_counts_of_H
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, a ≤ (d.weight y).toReal)
    (hxU : ∀ᶠ n in atTop, x.val ∉ U n)
    (δ : ℕ → ℝ) (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hsmall : ∀ᶠ n in atTop, ∀ y, (C.killedTransition y).real (U n) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (totalRate : ℝ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n)) atTop (𝓝 totalRate))
    (targets : ℕ → J → Set M) (hTargets : ∀ n j, MeasurableSet (targets n j))
    (hTargetsU : ∀ n j, targets n j ⊆ U n)
    (hdis : ∀ n, Pairwise fun i j => Disjoint (targets n i) (targets n j))
    (rates : J → ℝ≥0)
    (hRates : ∀ j, Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (targets n j))
      atTop (𝓝 (rates j : ℝ))) :
    Tendsto (fun n => ProbabilityMeasure.map (C.liveConditionedProbabilityMeasure d x n)
      (visitCountVector (fun i : Fin n => fun ω : Path M => ω i.val)
        (fun j => Option.some '' targets n j))) atTop
      (𝓝 (independentPoissonProbabilityMeasure rates)) := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val (d.liveSet_subset_survivingSet x.property) n
  obtain ⟨s, hsmean, hsleft⟩ := h.exists_survivalGapData_with_mean_invariant d hc μ hleft hnorm
  have hμρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  have hsum := C.conditioned_endpoint_sum_tendsto_zero h d s μ hμρ hsmean hsleft x U hU a ha
    hlower hxU δ hδ0 hsmall hδ superlogCutoff totalRate superlogCutoff_div_tendsto_zero hp
  have hboundary := boundaryHit_tendsto_zero_of_common_target_sum
    (fun n => C.conditionedMeasure x.val n) (fun n (i : Fin n) (ω : Path M) => ω i.val)
    (fun n j => Option.some '' targets n j) (fun n => Option.some '' U n)
    (fun n j => Set.image_mono (hTargetsU n j)) superlogCutoff hsum
  exact independent_poisson_of_trimmed_configuration_estimates
    (fun n => C.conditionedMeasure x.val n) (fun n (i : Fin n) (ω : Path M) => ω i.val)
    (fun _ _ => measurable_pi_apply _) (fun n j => Option.some '' targets n j)
    (fun n j => measurableEmbedding_some_state.measurableSet_image' (hTargets n j))
    (fun n => liftedTargets_disjoint (targets n) (hdis n)) superlogCutoff hboundary
    (fun j n => (μ.withDensity d.weight).real (targets n j)) rates hRates
    (fun r hr => C.spectral_trimmed_configuration_estimates h d s μ hμρ hsmean hsleft
      x U hU a ha hlower δ hδ0 hsmall hδ totalRate hp targets hTargets hTargetsU r hr)

end CanonicalChain
end ConditionedStableLaws
