import ConditionedStableLaws.ShrinkingTargetPoisson

/-! Poisson limits for visits after the deterministic initial observation. -/
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace ConditionedStableLaws.CanonicalChain
open StandingHypothesis EndpointTrimming ConditionalMixing
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The first-order boundary estimate after deleting time zero requires no
assumption excluding the initial state from the targets. -/
theorem conditioned_positive_endpoint_sum_tendsto_zero
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
    (hδ : Tendsto δ atTop (𝓝 0)) (L : ℕ → ℕ) (rate : ℝ)
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (μ.withDensity d.weight).real (U n))
      atTop (𝓝 rate)) :
    Tendsto (fun n => ∑ i ∈ boundaryTimes n (L n),
      (if i.val = 0 then 0 else
        (C.conditionedMeasure x.val n).real {ω | ω i.val ∈ Option.some '' U n})) atTop (𝓝 0) := by
  obtain ⟨R, _hR0, hRt, hR⟩ := h.weight_bounded d s.eigenvector s.eigenvector_ae
  have hweight : ∀ y, (d.weight y).toReal ≤ R.toReal := fun y => ENNReal.toReal_mono hRt (hR y)
  have hx : 0 < (d.weight x.val).toReal := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  let D := 2 * s.survivalBound / a
  let Cx := max s.constant ‖1 - rankOne s.mean s.eigenvector‖ *
    (d.rate.toReal)⁻¹ * R.toReal / (d.weight x.val).toReal
  have hD : 0 ≤ D := by dsimp [D]; exact div_nonneg (by nlinarith [s.survivalBound_nonneg]) ha.le
  have hCx : 0 ≤ Cx := by dsimp [Cx]; positivity
  have hden : ∀ᶠ n in atTop, (d.weight x.val).toReal / 2 ≤
      (d.rate.toReal)⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ := by
    have hh := (tendsto_order.mp (s.normalized_survival_tendstoUniformly.tendsto_at x.val)).1
      _ (half_lt_self hx)
    filter_upwards [hh] with n hn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, Measure.real, toKilledKernel_kernel] using hn.le
  have hlim := boundary_marginal_bound_tendsto_zero L
    (fun n => (μ.withDensity d.weight).real (U n)) δ D Cx s.decay rate hL hp hδ
  apply squeeze_zero' (Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => by split <;> positivity))) _ hlim
  filter_upwards [hlower, hδ0, hsmall, hden] with n hlow hδn hsmalln hdenn
  apply sum_boundary_marginals_le n (L n) _ _ D Cx s.decay (δ n)
    measureReal_nonneg hD hCx s.decay_nonneg s.decay_lt_one hδn
  · intro i hi
    simp [hi]
  · intro i hi
    simp only [ite_eq_right (Nat.ne_of_gt hi)]
    have hit : i.val + (n - i.val) = n := Nat.add_sub_of_le i.isLt.le
    have hupper (y : M) : (d.rate.toReal)⁻¹ ^ (n - i.val) *
        ((C.killedTransition ^ (n - i.val)) y).real univ ≤ s.survivalBound := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, Measure.real, toKilledKernel_kernel] using s.normalized_survival_real_le (n - i.val) y
    have hdom := C.conditioned_target_le_doob d x i.val (n - i.val) (U n) (hU n)
      s.survivalBound a s.survivalBound_nonneg ha hlow hupper (by simpa only [hit] using hdenn)
    rw [hit] at hdom
    have hret := h.doob_short_return d μ hμρ s.mean hmean s.eigenvector s.eigenvector_ae
      (U n) (hU n) (weightedTargetVector s.eigenvector (U n) (hU n))
      (weightedTargetVector_ae s.eigenvector (U n) (hU n) _ s.eigenvector_ae) (hleft _)
      R.toReal (δ n) (d.weight x.val).toReal s.constant s.decay ENNReal.toReal_nonneg hδn hx
      s.constant_nonneg s.decay_nonneg hweight hsmalln s.gap (i.val - 1) x le_rfl
    rw [Nat.sub_add_cancel hi] at hret
    exact hdom.trans (mul_le_mul_of_nonneg_left hret hD)

/-- Replace only time zero by the cemetery state. -/
def afterInitial {n : ℕ} (i : Fin n) (ω : Path M) : Option M :=
  if i.val = 0 then none else ω i.val

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
@[fun_prop]
theorem measurable_afterInitial {n : ℕ} (i : Fin n) : Measurable (afterInitial i : Path M → _) := by
  unfold afterInitial
  split <;> fun_prop

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Deleting time zero before trimming has no further effect: the initial
strip already contains time zero. -/
theorem trimmed_afterInitial (n : ℕ) :
    trimmedObservations (superlogCutoff n) (afterInitial (M := M)) =
      trimmedObservations (superlogCutoff n) (fun i : Fin n => fun ω : Path M => ω i.val) := by
  funext i ω
  by_cases hi : i ∈ boundaryTimes n (superlogCutoff n)
  · simp [trimmedObservations, hi]
  · have hi0 : i.val ≠ 0 := by
      intro hzero
      apply hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Or.inl ?_⟩
      rw [hzero]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one (superlogCutoff_pos n)
    simp [trimmedObservations, hi, afterInitial, hi0]

/-- Independent Poisson limits for visits at times 1,...,n-1. Unlike the
original-count theorem, this allows the starting state to belong to the target. -/
theorem independent_poisson_after_initial_of_H
    {J : Type*} [Fintype J]
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, a ≤ (d.weight y).toReal)
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
      (visitCountVector (afterInitial (n := n)) (fun j => Option.some '' targets n j))) atTop
      (𝓝 (independentPoissonProbabilityMeasure rates)) := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val (d.liveSet_subset_survivingSet x.property) n
  obtain ⟨s, hsmean, hsleft⟩ := h.exists_survivalGapData_with_mean_invariant d hc μ hleft hnorm
  have hμρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  have hsum := C.conditioned_positive_endpoint_sum_tendsto_zero h d s μ hμρ hsmean hsleft x U hU a ha
    hlower δ hδ0 hsmall hδ superlogCutoff totalRate superlogCutoff_div_tendsto_zero hp
  have hsum' : Tendsto (fun n => ∑ i ∈ boundaryTimes n (superlogCutoff n),
      (C.conditionedMeasure x.val n).real {ω | afterInitial i ω ∈ Option.some '' U n})
      atTop (𝓝 0) := by
    apply hsum.congr
    intro n
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val = 0
    · simp [afterInitial, hi]
    · simp [afterInitial, hi]
  have hboundary := boundaryHit_tendsto_zero_of_common_target_sum
    (fun n => C.conditionedMeasure x.val n) (fun _ => afterInitial (M := M))
    (fun n j => Option.some '' targets n j) (fun n => Option.some '' U n)
    (fun n j => Set.image_mono (hTargetsU n j)) superlogCutoff hsum'
  apply independent_poisson_of_trimmed_configuration_estimates
    (fun n => C.conditionedMeasure x.val n) (fun _ => afterInitial (M := M))
    (fun _ => measurable_afterInitial) (fun n j => Option.some '' targets n j)
    (fun n j => measurableEmbedding_some_state.measurableSet_image' (hTargets n j))
    (fun n => liftedTargets_disjoint (targets n) (hdis n)) superlogCutoff hboundary
    (fun j n => (μ.withDensity d.weight).real (targets n j)) rates hRates
  intro r hr
  simpa only [trimmed_afterInitial] using
    C.spectral_trimmed_configuration_estimates h d s μ hμρ hsmean hsleft
      x U hU a ha hlower δ hδ0 hsmall hδ totalRate hp targets hTargets hTargetsU r hr

/-- Survival conditioning preserves the prescribed initial observation. -/
theorem ae_initial_conditionedMeasure (x : M) (n : ℕ) :
    ∀ᵐ ω ∂C.conditionedMeasure x n, ω 0 = some x := by
  have hsingle : MeasurableSet ({some x} : Set (Option M)) := by
    change MeasurableSet (Option.some ⁻¹' ({some x} : Set (Option M)))
    have he : Option.some ⁻¹' ({some x} : Set (Option M)) = ({x} : Set M) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.some.injEq]
    rw [he]
    exact measurableSet_singleton x
  have hz : ∀ᵐ ω ∂C.pathMeasure x, ω 0 = some x := by
    apply ae_iff.mpr
    change C.pathMeasure x ((fun ω => ω 0) ⁻¹' ({some x} : Set (Option M))ᶜ) = 0
    rw [← Measure.map_apply (measurable_pi_apply 0) hsingle.compl,
      C.pathMeasure_initial, Measure.dirac_apply' _ hsingle.compl]
    simp
  exact ProbabilityTheory.cond_absolutelyContinuous.ae_le hz

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The deterministic contribution of time zero is exactly one when the path starts in U. -/
theorem visitTimes_eq_one_add_afterInitial {n : ℕ} (hn : 0 < n) (ω : Path M)
    (U : Set M) (hzero : ω 0 ∈ Option.some '' U) :
    (visitTimes (fun i : Fin n => ω i.val) (Option.some '' U)).card =
      1 + (visitTimes (fun i : Fin n => afterInitial i ω) (Option.some '' U)).card := by
  classical
  let z : Fin n := ⟨0, hn⟩
  have hz : z ∈ visitTimes (fun i : Fin n => ω i.val) (Option.some '' U) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
  have heq : visitTimes (fun i : Fin n => afterInitial i ω) (Option.some '' U) =
      (visitTimes (fun i : Fin n => ω i.val) (Option.some '' U)).erase z := by
    ext i
    by_cases hi : i.val = 0
    · have hiz : i = z := Fin.ext hi
      subst i
      simp [visitTimes, afterInitial, z]
    · have hiz : i ≠ z := fun h => hi (congrArg Fin.val h)
      simp [visitTimes, afterInitial, hi, hiz]
  rw [heq]
  have hcard := Finset.card_erase_add_one hz
  omega

/-- The Poisson law for visits at strictly positive times, including a start at the center. -/
theorem conditional_poisson_after_initial_shrinking_targets
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {x₁ : M} (hx₁ : d.weight x₁ ≠ 0)
    (U : ℕ → Set M) (hU : ShrinkingNeighborhoods U x₁) (rate : ℝ≥0)
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n))
      atTop (𝓝 (rate : ℝ))) :
    Tendsto (fun n => ProbabilityMeasure.map (C.liveConditionedProbabilityMeasure d x n)
      (fun ω : Path M => (visitTimes (fun i : Fin n => afterInitial i ω)
        (Option.some '' U n)).card)) atTop (𝓝 (poissonProbabilityMeasure rate)) := by
  have : IsProbabilityMeasure (μ.withDensity d.weight) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  have hη : Continuous (fun y => (d.weight y).toReal) := continuous_iff_continuousAt.mpr
    (fun y => (ENNReal.continuousAt_toReal (d.weight_ne_top y)).comp hc.continuousAt)
  have hpos : 0 < (d.weight x₁).toReal := ENNReal.toReal_pos hx₁ (d.weight_ne_top _)
  have hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, (d.weight x₁).toReal/2 ≤ (d.weight y).toReal := by
    filter_upwards [hU.eventually_lower_bound hη hpos] with n hn y hy
    exact (hn y hy).le
  have hUS : ∀ᶠ n in atTop, U n ⊆ survivingSet C.killedTransition := by
    filter_upwards [hU.eventually_subset_positive hη hpos] with n hn y hy
    apply d.liveSet_subset_survivingSet
    exact (ENNReal.toReal_pos_iff.mp (hn hy)).1.ne'
  have hsmall := h.uniform_small_targets_of_eigenData d hc μ hleft hnorm U hU.measurableSet hUS
    (target_measure_tendsto_zero _ hscale)
  obtain ⟨δ, hδ0, hδbound, hδ⟩ := C.exists_small_target_envelope x.val U hsmall
  have hv := C.independent_poisson_after_initial_of_H h d hc μ hleft hnorm x U hU.measurableSet
    ((d.weight x₁).toReal/2) (half_pos hpos) hlower
    δ (Eventually.of_forall hδ0) (Eventually.of_forall hδbound) hδ (rate : ℝ) hscale
    (fun n (_ : Unit) => U n) (fun n _ => hU.measurableSet n) (fun _ _ => subset_rfl)
    (fun _ i j hij => (hij (Subsingleton.elim i j)).elim) (fun _ => rate) (fun _ => hscale)
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hv (continuous_apply ())
  have hlim : (independentPoissonProbabilityMeasure (fun _ : Unit => rate)).map
      (fun v : Unit → ℕ => v ()) = poissonProbabilityMeasure rate := by
    apply Subtype.ext
    exact (independentPoissonProbabilityMeasure_coordinate_hasLaw (fun _ : Unit => rate) ()).map_eq
  rw [hlim] at hm
  apply hm.congr
  intro n
  apply Subtype.ext
  change ((C.conditionedMeasure x.val n).map
      (visitCountVector afterInitial (fun _ : Unit => Option.some '' U n))).map (fun v => v ()) = _
  have hvmeas : Measurable (visitCountVector
      (afterInitial (M := M) (n := n)) (fun _ : Unit => Option.some '' U n)) :=
    measurable_visitCountVector _ measurable_afterInitial _
      (fun _ => measurableEmbedding_some_state.measurableSet_image' (hU.measurableSet n))
  rw [Measure.map_map (measurable_pi_apply ()) hvmeas]
  rfl

/-- **Starting at the target.** Starting at the target center gives the shifted law `1 +
Poisson(rate)` under the conditioned path law. -/
theorem conditional_poisson_target_start
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x₁ : d.State) (U : ℕ → Set M) (hU : ShrinkingNeighborhoods U x₁.val) (rate : ℝ≥0)
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n))
      atTop (𝓝 (rate : ℝ))) :
    Tendsto (fun n => ProbabilityMeasure.map (C.liveConditionedProbabilityMeasure d x₁ n)
      (fun ω : Path M => (visitTimes (fun i : Fin n => ω i.val) (Option.some '' U n)).card))
      atTop (𝓝 ((poissonProbabilityMeasure rate).map (fun k : ℕ => 1 + k))) := by
  have ht := C.conditional_poisson_after_initial_shrinking_targets h d hc μ hleft hnorm
    x₁ x₁.property U hU rate hscale
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ ht
    (continuous_const.add continuous_id : Continuous (fun k : ℕ => 1 + k))
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  apply Subtype.ext
  change ((C.conditionedMeasure x₁.val n).map
    (fun ω => (visitTimes (fun i : Fin n => afterInitial i ω) (Option.some '' U n)).card)).map
      (fun k : ℕ => 1 + k) = _
  have hmeas : Measurable (fun ω : Path M =>
      (visitTimes (fun i : Fin n => afterInitial i ω) (Option.some '' U n)).card) := by
    exact (measurable_pi_apply ()).comp (measurable_visitCountVector
      (afterInitial (M := M) (n := n)) measurable_afterInitial
      (fun _ : Unit => Option.some '' U n)
      (fun _ => measurableEmbedding_some_state.measurableSet_image' (hU.measurableSet n)))
  rw [Measure.map_map (show Measurable (fun k : ℕ => 1 + k) from measurable_const.add measurable_id) hmeas]
  apply Measure.map_congr
  filter_upwards [C.ae_initial_conditionedMeasure x₁.val n] with ω hω
  exact (visitTimes_eq_one_add_afterInitial hn ω (U n)
    (by rw [hω]; exact Set.mem_image_of_mem _ (hU.center_mem n))).symm

end ConditionedStableLaws.CanonicalChain
