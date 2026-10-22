import ConditionedStableLaws.ChainPoissonProcess

/-!
# Conditional Poisson law for shrinking neighborhoods

The scalar Poisson limit is derived from the chain configuration estimates and first-order endpoint
removal. The starting point is distinct from the target center.
-/
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace ConditionedStableLaws.CanonicalChain
open StandingHypothesis
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Conditional Poisson law for the number of visits at times 0,...,n−1 under the
survival-conditioned law. -/
theorem conditional_poisson_shrinking_targets
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {x₁ : M} (hx₁ : d.weight x₁ ≠ 0) (hxx₁ : x.val ≠ x₁)
    (U : ℕ → Set M) (hU : ShrinkingNeighborhoods U x₁) (rate : ℝ≥0)
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n))
      atTop (𝓝 (rate : ℝ))) :
    Tendsto (fun n => ProbabilityMeasure.map (C.liveConditionedProbabilityMeasure d x n)
      (fun ω : Path M => (visitTimes (fun i : Fin n => ω i.val) (Option.some '' U n)).card))
      atTop (𝓝 (poissonProbabilityMeasure rate)) := by
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
  obtain ⟨δ,hδ0,hδbound,hδ⟩ := C.exists_small_target_envelope x.val U hsmall
  have hv := C.independent_poisson_counts_of_H h d hc μ hleft hnorm x U hU.measurableSet
    ((d.weight x₁).toReal/2) (half_pos hpos) hlower (hU.eventually_not_mem hxx₁)
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
      (visitCountVector (fun i : Fin n => fun ω : Path M => ω i.val)
        (fun _ : Unit => Option.some '' U n))).map (fun v => v ()) = _
  have hvmeas : Measurable (visitCountVector
      (fun i : Fin n => fun ω : Path M => ω i.val) (fun _ : Unit => Option.some '' U n)) :=
    measurable_visitCountVector (fun i : Fin n => fun ω : Path M => ω i.val)
      (fun i => measurable_pi_apply i.val) (fun _ : Unit => Option.some '' U n)
      (fun _ => measurableEmbedding_some_state.measurableSet_image' (hU.measurableSet n))
  rw [Measure.map_map (measurable_pi_apply ()) hvmeas]
  rfl

end ConditionedStableLaws.CanonicalChain
