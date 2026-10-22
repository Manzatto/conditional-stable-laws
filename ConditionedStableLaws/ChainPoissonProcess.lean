import ConditionedStableLaws.SingularChainTargets
import ConditionedStableLaws.PoissonProcessConvergence
import ConditionedStableLaws.NormalizationBridge

/-!
Conditioned-chain interval estimates for the vague Poisson point-process criterion.
-/
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace ConditionedStableLaws

/-- A finite family of strictly positive real thresholds has a common
strictly positive lower bound; the empty family is also covered. -/
theorem exists_positive_common_lower_bound {J : Type*} [Fintype J]
    (f : J → ℝ) (hf : ∀ j, 0 < f j) : ∃ a : ℝ, 0 < a ∧ ∀ j, a ≤ f j := by
  classical
  have hh (s : Finset J) : ∃ a : ℝ, 0 < a ∧ ∀ j ∈ s, a ≤ f j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert j s hj ih =>
        obtain ⟨a,ha,has⟩ := ih
        refine ⟨min a (f j), lt_min ha (hf j), ?_⟩
        intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (has i hi)
  obtain ⟨a,ha,has⟩ := hh univ
  exact ⟨a,ha,fun j => has j (mem_univ _)⟩

namespace CanonicalChain
open StandingHypothesis EndpointTrimming
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The interval criterion for normalized canonical observations, with all chain probability
estimates derived from H. Eventual equality with live targets handles the cemetery normalization
convention. -/
theorem nonempty_trimmed_interval_estimates_of_H
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (ηlower : ℝ) (ha : 0 < ηlower)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, ηlower ≤ (d.weight y).toReal)
    (hxU : ∀ᶠ n in atTop, x.val ∉ U n)
    (δ : ℕ → ℝ) (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hsmall : ∀ᶠ n in atTop, ∀ y, (C.killedTransition y).real (U n) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (totalRate : ℝ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n)) atTop (𝓝 totalRate))
    (k : ℕ) (a b : Fin k → ExtremeState) (υ : Measure ExtremeState)
    (g : ℕ → Option M → ExtremeState)
    (targets : ℕ → Fin k → Set M) (hTargets : ∀ n j, MeasurableSet (targets n j))
    (hTargetsU : ∀ n j, targets n j ⊆ U n)
    (hTargetsEq : ∀ᶠ n in atTop, ∀ j, (g n) ⁻¹' Ioc (a j) (b j) = Option.some '' targets n j)
    (hRates : ∀ j, Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (targets n j))
      atTop (𝓝 (υ (Ioc (a j) (b j))).toReal)) :
    Nonempty (TrimmedIntervalConfigurationEstimates (fun n => C.conditionedMeasure x.val n)
      (fun n (i : Fin n) (ω : Path M) => ω i.val) g υ a b) := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val (d.liveSet_subset_survivingSet x.property) n
  obtain ⟨s, hsmean, hsleft⟩ := h.exists_survivalGapData_with_mean_invariant d hc μ hleft hnorm
  have hμρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  have hsum := C.conditioned_endpoint_sum_tendsto_zero h d s μ hμρ hsmean hsleft x U hU ηlower ha
    hlower hxU δ hδ0 hsmall hδ superlogCutoff totalRate superlogCutoff_div_tendsto_zero hp
  have hboundary := boundaryHit_tendsto_zero_of_common_target_sum
    (fun n => C.conditionedMeasure x.val n) (fun n (i : Fin n) (ω : Path M) => ω i.val)
    (fun n j => Option.some '' targets n j) (fun n => Option.some '' U n)
    (fun n j => Set.image_mono (hTargetsU n j)) superlogCutoff hsum
  refine ⟨{
    probability := fun j n => (μ.withDensity d.weight).real (targets n j)
    trimWidth := superlogCutoff
    rate_limit := hRates
    boundary_tendsto := ?_
    configurations := ?_ }⟩
  · apply hboundary.congr'
    filter_upwards [hTargetsEq] with n hn
    simp_rw [hn]
  · intro r hr
    let e := C.spectral_trimmed_configuration_estimates h d s μ hμρ hsmean hsleft
      x U hU ηlower ha hlower δ hδ0 hsmall hδ totalRate hp targets hTargets hTargetsU r hr
    apply e.congr_targets_eventually
    filter_upwards [hTargetsEq] with n hn
    funext j
    simp only [liftedTargets, hn]

open NormalizationBridge in
/-- Every finite positive interval family has trimmed configuration estimates, including an infinite
upper endpoint. -/
theorem nonempty_singular_interval_estimates_of_H_tail
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {x₀ : M} (hx₀ : d.weight x₀ ≠ 0) {β C₀ α : ℝ}
    (hβ : 0 < β) (hC : 0 < C₀) (hα : 0 < α)
    (htail : Tendsto (fun t : ℝ => (μ.withDensity d.weight).real
      {z | t < singularObservable x₀ β z} / (C₀*t^(-α))) atTop (𝓝 1))
    (k : ℕ) (a b : Fin k → ExtremeState) (hab : ∀ j, a j < b j) :
    Nonempty (TrimmedIntervalConfigurationEstimates (fun n => C.conditionedMeasure x.val n)
      (fun n (i : Fin n) (ω : Path M) => ω i.val)
      (pathNormalization (singularObservable x₀ β) (singularObservable_pos x₀ β)
        (positivePowerScale C₀ α) (positivePowerScale_pos hC)) (powerIntensity α) a b) := by
  have : IsProbabilityMeasure (μ.withDensity d.weight) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  obtain ⟨level,hl,hlevel⟩ := exists_positive_common_lower_bound
    (fun j => (a j).val.toReal) (fun j => lower_toReal_pos (hab j))
  obtain ⟨ηlower,δ,hηlower,hδ0,hlower,hsmall,hδ,hxU⟩ := C.singular_target_chain_inputs
    h d hc μ hleft hnorm x hx₀ hβ hC hα hl htail
  let U : ℕ → Set M := fun n => {z | level*powerScale C₀ α n < singularObservable x₀ β z}
  let targets : ℕ → Fin k → Set M := fun n j => normalizedTarget (singularObservable x₀ β)
    (singularObservable_pos x₀ β) (positivePowerScale C₀ α) (positivePowerScale_pos hC) n (a j) (b j)
  apply C.nonempty_trimmed_interval_estimates_of_H h d hc μ hleft hnorm x U
    (fun _ => measurableSet_lt measurable_const (measurable_singularObservable x₀ β))
    ηlower hηlower hlower hxU δ (Eventually.of_forall hδ0) (Eventually.of_forall hsmall) hδ
    (level^(-α)) (normalized_tail_limit hC hα htail hl) k a b (powerIntensity α)
    (pathNormalization (singularObservable x₀ β) (singularObservable_pos x₀ β)
      (positivePowerScale C₀ α) (positivePowerScale_pos hC)) targets
  · intro n j
    exact measurableSet_normalizedTarget _ (measurable_singularObservable x₀ β) _ _ _ n (a j) (b j)
  · intro n j
    exact normalizedTarget_subset_powerTail hC hα _ (singularObservable_pos x₀ β)
      (a j) (b j) (hab j) (hlevel j) n
  · have hh := fun j => pathNormalization_preimage_eventually (singularObservable x₀ β)
      (singularObservable_pos x₀ β) hC hα (a j) (b j) (hab j)
    exact Filter.eventually_all.mpr hh
  · intro j
    exact normalizedTarget_rate (μ.withDensity d.weight) _ (measurable_singularObservable x₀ β)
      (singularObservable_pos x₀ β) hC hα htail (a j) (b j) (hab j)

open NormalizationBridge in
/-- The vague Poisson point-process limit under survival conditioning. All multitime estimates and
endpoint removal are consequences of H; the remaining scalar tail hypothesis is supplied by
admissibility below. -/
theorem singular_poisson_process_of_H_tail
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {x₀ : M} (hx₀ : d.weight x₀ ≠ 0) {β C₀ α : ℝ}
    (hβ : 0 < β) (hC : 0 < C₀) (hα : 0 < α)
    (htail : Tendsto (fun t : ℝ => (μ.withDensity d.weight).real
      {z | t < singularObservable x₀ β z} / (C₀*t^(-α))) atTop (𝓝 1)) :
    TendstoInDistribution (fun n => (pathEmpirical (singularObservable x₀ β)
      (measurable_singularObservable x₀ β) (singularObservable_pos x₀ β)
      n (positivePowerScale C₀ α n) (positivePowerScale_pos hC n)).toFun) atTop
      AnnularPoissonClouds.randomMeasure.toFun
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (AnnularPoissonClouds.law (powerIntensity α) (powerIntensity_tail_lt_top hα)) := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val (d.liveSet_subset_survivingSet x.property) n
  have : IsProbabilityMeasure (μ.withDensity d.weight) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  apply path_empirical_poisson_process_convergence_of_trimmed_estimates
    (fun n => C.conditionedMeasure x.val n) (powerIntensity α) (powerIntensity_tail_lt_top hα)
    (singularObservable x₀ β) (measurable_singularObservable x₀ β) (singularObservable_pos x₀ β)
    (positivePowerScale C₀ α) (positivePowerScale_pos hC)
  intro k a b hab _hdis
  exact Classical.choice (C.nonempty_singular_interval_estimates_of_H_tail h d hc μ hleft hnorm
    x hx₀ hβ hC hα htail k a b hab)

open NormalizationBridge in
/-- The Poisson point-process limit from H and admissibility, for the normalized singular observable
under the survival-conditioned law. The index-zero normalization is set to one; at every positive
index it is exactly `(C n)^(1/α)` with `C=volumeConstant*η(x₀)*m(x₀)` and `α=dimension/β`. -/
theorem poisson_point_process_of_admissibility
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) :
    TendstoInDistribution (fun n => (pathEmpirical (singularObservable x₀ β)
      (measurable_singularObservable x₀ β) (singularObservable_pos x₀ β) n
      (positivePowerScale (volumeConstant*(d.weight x₀).toReal*m x₀) (dimension/β) n)
      (positivePowerScale_pos (mul_pos (mul_pos hadm.1.2.1
        (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1) n)).toFun) atTop
      AnnularPoissonClouds.randomMeasure.toFun
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (AnnularPoissonClouds.law (powerIntensity (dimension/β))
        (powerIntensity_tail_lt_top (div_pos hadm.1.1 hβ))) := by
  exact C.singular_poisson_process_of_H_tail h d hc μ hleft hnorm x hx₀ hβ
    (mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1)
    (div_pos hadm.1.1 hβ) (C.admissible_weighted_tail h d hc μ m hm hm0 hμ hadm hx₀ hβ)

open NormalizationBridge in
/-- Every finite disjoint interval family has joint count convergence to the counts of the Poisson
random measure. -/
theorem poisson_interval_counts_of_admissibility
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β)
    (k : ℕ) (a b : Fin k → ExtremeState) (hab : ∀ j, a j < b j)
    (hdis : Pairwise fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) :
    TendstoInDistribution (fun n ω j => ((pathEmpirical (singularObservable x₀ β)
      (measurable_singularObservable x₀ β) (singularObservable_pos x₀ β) n
      (positivePowerScale (volumeConstant*(d.weight x₀).toReal*m x₀) (dimension/β) n)
      (positivePowerScale_pos (mul_pos (mul_pos hadm.1.2.1
        (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1) n)).toFun ω).countOn
        (Ioc (a j) (b j))) atTop
      (fun ω j => (AnnularPoissonClouds.randomMeasure.toFun ω).countOn (Ioc (a j) (b j)))
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (AnnularPoissonClouds.law (powerIntensity (dimension/β))
        (powerIntensity_tail_lt_top (div_pos hadm.1.1 hβ))) := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val (d.liveSet_subset_survivingSet x.property) n
  have hC := mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  have hα := div_pos hadm.1.1 hβ
  have htail := C.admissible_weighted_tail h d hc μ m hm hm0 hμ hadm hx₀ hβ
  exact poisson_interval_counts_of_trimmed_estimates (fun n => C.conditionedMeasure x.val n)
    (AnnularPoissonClouds.law (powerIntensity (dimension/β)) (powerIntensity_tail_lt_top hα))
    AnnularPoissonClouds.randomMeasure (powerIntensity (dimension/β))
    (AnnularPoissonClouds.isPoissonRandomMeasure _ _)
    (fun n (i : Fin n) (ω : Path M) => ω i.val) (fun _ i => measurable_pi_apply i.val)
    (pathNormalization (singularObservable x₀ β) (singularObservable_pos x₀ β)
      (positivePowerScale _ _) (positivePowerScale_pos hC))
    (measurable_pathNormalization _ (measurable_singularObservable x₀ β) _ _ _) k a b hdis
    (Classical.choice (C.nonempty_singular_interval_estimates_of_H_tail h d hc μ hleft hnorm
      x hx₀ hβ hC hα htail k a b hab))

end CanonicalChain
/-- The limiting random measure in the PPP theorem has Poisson counts and
independent counts on disjoint measurable finite-intensity sets. -/
theorem power_poisson_limit_isPoissonRandomMeasure {α : ℝ} (hα : 0 < α) :
    IsPoissonRandomMeasure AnnularPoissonClouds.randomMeasure
      (AnnularPoissonClouds.law (powerIntensity α) (powerIntensity_tail_lt_top hα))
      (powerIntensity α) :=
  AnnularPoissonClouds.isPoissonRandomMeasure _ _

end ConditionedStableLaws
