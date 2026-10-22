import ConditionedStableLaws.RareEventPoisson
import ConditionedStableLaws.CemeteryBridge

/-!
# Removing endpoint strips in probability

Observations in the boundary strips are replaced by a new cemetery value.
Every boundary factorial configuration then has exactly zero weight. Original
and trimmed count vectors coincide unless a target is hit in a removed strip;
weak convergence transfers under vanishing probability of that event. No
higher boundary factorial-moment estimate is required.
-/

open MeasureTheory Filter Set Classical
open scoped Topology BigOperators NNReal
noncomputable section
namespace ConditionedStableLaws.EndpointTrimming
variable {Ω A J : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype J]

/-- Delete both endpoint strips without shifting the remaining time labels. -/
def trimmedObservations {n : ℕ} (L : ℕ) (X : Fin n → Ω → A) : Fin n → Ω → Option A :=
  fun t ω => if t ∈ boundaryTimes n L then none else some (X t ω)

/-- Targets avoid the new cemetery point. -/
def liftedTargets (U : J → Set A) : J → Set (Option A) := fun j => Option.some '' U j

theorem measurable_trimmedObservations {n : ℕ} (L : ℕ) (X : Fin n → Ω → A)
    (hX : ∀ t, Measurable (X t)) (t : Fin n) : Measurable (trimmedObservations L X t) := by
  change Measurable (fun ω => if t ∈ boundaryTimes n L then (none : Option A) else some (X t ω))
  by_cases ht : t ∈ boundaryTimes n L
  · simp only [ht, ↓reduceIte]
    exact measurable_const
  · simp only [ht, ↓reduceIte]
    exact measurable_some_state.comp (hX t)

omit [Fintype J] in
theorem measurableSet_liftedTargets (U : J → Set A) (hU : ∀ j, MeasurableSet (U j)) (j : J) :
    MeasurableSet (liftedTargets U j) :=
  measurableEmbedding_some_state.measurableSet_image' (hU j)

omit [MeasurableSpace Ω] [MeasurableSpace A] [Fintype J] in
theorem liftedTargets_disjoint (U : J → Set A) (hU : Pairwise fun i j => Disjoint (U i) (U j)) :
    Pairwise fun i j => Disjoint (liftedTargets U i) (liftedTargets U j) := by
  intro i j hij
  exact Set.disjoint_image_of_injective (Option.some_injective A) (hU hij)

/-- At least one target is visited in a deleted time strip. -/
def boundaryHit {n : ℕ} (L : ℕ) (X : Fin n → Ω → A) (U : J → Set A) : Set Ω :=
  {ω | ∃ t ∈ boundaryTimes n L, ∃ j, X t ω ∈ U j}

theorem measurableSet_boundaryHit {n : ℕ} (L : ℕ) (X : Fin n → Ω → A)
    (hX : ∀ t, Measurable (X t)) (U : J → Set A) (hU : ∀ j, MeasurableSet (U j)) :
    MeasurableSet (boundaryHit L X U) := by
  have he : boundaryHit L X U = ⋃ t ∈ boundaryTimes n L, ⋃ j, (X t) ⁻¹' U j := by
    ext ω
    simp [boundaryHit]
  rw [he]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun t _ =>
    MeasurableSet.iUnion fun j => (hU j).preimage (hX t)

omit [MeasurableSpace Ω] [MeasurableSpace A] [Fintype J] in
/-- The original and trimmed count vectors agree outside the boundary-hit event. -/
theorem visitCountVector_eq_of_not_boundaryHit {n : ℕ} (L : ℕ)
    (X : Fin n → Ω → A) (U : J → Set A) (ω : Ω) (hω : ω ∉ boundaryHit L X U) :
    visitCountVector X U ω = visitCountVector (trimmedObservations L X) (liftedTargets U) ω := by
  funext j
  change (visitTimes (fun t => X t ω) (U j)).card =
    (visitTimes (fun t => trimmedObservations L X t ω) (liftedTargets U j)).card
  apply congrArg Finset.card
  apply Finset.ext
  intro t
  by_cases ht : t ∈ boundaryTimes n L
  · have hnot : X t ω ∉ U j := fun h => hω ⟨t, ht, j, h⟩
    simp [visitTimes, trimmedObservations, liftedTargets, ht, hnot]
  · simp [visitTimes, trimmedObservations, liftedTargets, ht]

omit [MeasurableSpace A] in
/-- Boundary configurations contribute exactly zero after trimming, at every
mixed order, regardless of how many other observations they contain. -/
theorem mixedWeight_eq_zero_of_boundary {n : ℕ} (P : Measure Ω) (L : ℕ)
    (X : Fin n → Ω → A) (U : J → Set A) (r : J → ℕ)
    (t : Fin (∑ j, r j) → Fin n) (ht : t ∈ boundaryConfigurations n (∑ j, r j) L) :
    mixedFactorialEventWeight P (trimmedObservations L X) (liftedTargets U) r t = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, t i ∈ boundaryTimes n L := by
    simpa [boundaryConfigurations] using ht
  have he : mixedJointVisitEvent (trimmedObservations L X) (liftedTargets U) r t = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have ha := hω ((factorialSlotsEquiv r).symm i)
    simp [trimmedObservations, liftedTargets, hi] at ha
  simp [mixedFactorialEventWeight, he, Measure.real]

omit [MeasurableSpace A] in
/-- Away from the removed strips, all mixed joint-event weights are unchanged. -/
theorem mixedWeight_eq_of_not_boundary {n : ℕ} (P : Measure Ω) (L : ℕ)
    (X : Fin n → Ω → A) (U : J → Set A) (r : J → ℕ)
    (t : Fin (∑ j, r j) → Fin n) (ht : t ∉ boundaryConfigurations n (∑ j, r j) L) :
    mixedFactorialEventWeight P (trimmedObservations L X) (liftedTargets U) r t =
      mixedFactorialEventWeight P X U r t := by
  have hnot : ∀ i, t i ∉ boundaryTimes n L := by simpa [boundaryConfigurations] using ht
  have he : mixedJointVisitEvent (trimmedObservations L X) (liftedTargets U) r t =
      mixedJointVisitEvent X U r t := by
    ext ω
    simp [mixedJointVisitEvent, trimmedObservations, liftedTargets, hnot]
  simp only [mixedFactorialEventWeight, he]

omit [MeasurableSpace A] in
/-- Thus only close configurations need an aggregate bound for the trimmed process; all additional
endpoint terms are zero. -/
theorem sum_excluded_trimmed_eq_sum_close {n : ℕ} (P : Measure Ω) (L : ℕ)
    (X : Fin n → Ω → A) (U : J → Set A) (r : J → ℕ) :
    (∑ t ∈ excludedConfigurations n (∑ j, r j) L,
      mixedFactorialEventWeight P (trimmedObservations L X) (liftedTargets U) r t) =
    ∑ t ∈ badConfigurations n (∑ j, r j) L,
      mixedFactorialEventWeight P (trimmedObservations L X) (liftedTargets U) r t := by
  symm
  apply Finset.sum_subset (Finset.subset_union_left)
  intro t ht hnot
  have hbd : t ∈ boundaryConfigurations n (∑ j, r j) L :=
    (Finset.mem_union.mp ht).resolve_left hnot
  exact mixedWeight_eq_zero_of_boundary P L X U r t hbd

omit [MeasurableSpace A] in
/-- The boundary-hit probability is controlled by the sum of one-time hit probabilities; no moments
of the boundary counts enter. -/
theorem boundaryHit_probability_le {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (L : ℕ) (X : Fin n → Ω → A) (U : J → Set A) :
    P.real (boundaryHit L X U) ≤
      ∑ t ∈ boundaryTimes n L, ∑ j, P.real {ω | X t ω ∈ U j} := by
  have he : boundaryHit L X U = ⋃ t ∈ boundaryTimes n L, ⋃ j, {ω | X t ω ∈ U j} := by
    ext ω
    simp [boundaryHit]
  rw [he]
  exact (measureReal_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum (fun t _ => measureReal_iUnion_fintype_le _))


omit [MeasurableSpace A] [Fintype J] in
/-- Coupled observations can change any event probability only on the event
where the observations may differ. -/
theorem abs_event_probability_sub_le (P : Measure Ω) [IsFiniteMeasure P]
    (X Y : Ω → A) (bad : Set Ω) (heq : ∀ ω ∉ bad, X ω = Y ω) (S : Set A) :
    |P.real (X ⁻¹' S) - P.real (Y ⁻¹' S)| ≤ P.real bad := by
  have hxy : X ⁻¹' S ⊆ (Y ⁻¹' S) ∪ bad := by
    intro ω hω
    by_cases hb : ω ∈ bad
    · exact Or.inr hb
    · exact Or.inl (by simpa [heq ω hb] using hω)
  have hyx : Y ⁻¹' S ⊆ (X ⁻¹' S) ∪ bad := by
    intro ω hω
    by_cases hb : ω ∈ bad
    · exact Or.inr hb
    · exact Or.inl (by simpa [heq ω hb] using hω)
  have hx := (measureReal_mono (μ := P) hxy).trans (measureReal_union_le _ _)
  have hy := (measureReal_mono (μ := P) hyx).trans (measureReal_union_le _ _)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [MeasurableSpace A] in
/-- Equality with high probability transfers weak convergence of finite count-vector laws, even when
the underlying law varies with `n`. -/
theorem natVector_law_transfer
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ℕ → Ω → J → ℕ) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (bad : ℕ → Set Ω) (heq : ∀ n ω, ω ∉ bad n → X n ω = Y n ω)
    (hbad : Tendsto (fun n => (P n).real (bad n)) atTop (𝓝 0))
    (ν : ProbabilityMeasure (J → ℕ))
    (hYlim : Tendsto (fun n => natVectorProbabilityLaw (P n) (Y n)) atTop (𝓝 ν)) :
    Tendsto (fun n => natVectorProbabilityLaw (P n) (X n)) atTop (𝓝 ν) := by
  apply probabilityMeasure_natVector_tendsto_of_atoms
  intro k
  have hYa := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hYlim
    (show IsClopen ({k} : Set (J → ℕ)) from ⟨isClosed_discrete _, isOpen_discrete _⟩)
  have hYr : Tendsto (fun n => (natVectorProbabilityLaw (P n) (Y n) : Measure (J → ℕ)).real {k})
      atTop (𝓝 ((ν : Measure (J → ℕ)).real {k})) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using NNReal.tendsto_coe.mpr hYa
  have hmapX (n : ℕ) : (natVectorProbabilityLaw (P n) (X n) : Measure (J → ℕ)).real {k} =
      (P n).real ((X n) ⁻¹' {k}) := by
    change ((P n).map (X n)).real {k} = _
    rw [Measure.real, Measure.map_apply (hX n) (measurableSet_singleton k)]
    rfl
  have hmapY (n : ℕ) : (natVectorProbabilityLaw (P n) (Y n) : Measure (J → ℕ)).real {k} =
      (P n).real ((Y n) ⁻¹' {k}) := by
    change ((P n).map (Y n)).real {k} = _
    rw [Measure.real, Measure.map_apply (hY n) (measurableSet_singleton k)]
    rfl
  have hd : Tendsto (fun n => (P n).real ((X n) ⁻¹' {k}) - (P n).real ((Y n) ⁻¹' {k}))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hbad
    simpa only [Real.norm_eq_abs] using abs_event_probability_sub_le
      (P n) (X n) (Y n) (bad n) (heq n) {k}
  simp only [hmapY] at hYr
  simpa only [hmapX, sub_add_cancel, zero_add] using hd.add hYr

/-- Restore the untrimmed count vector after proving the trimmed count limit. The sole endpoint
hypothesis is a first-order boundary-hit probability. -/
theorem count_law_transfer_of_boundaryHit
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (U : ℕ → J → Set A) (hU : ∀ n j, MeasurableSet (U n j)) (L : ℕ → ℕ)
    (hboundary : Tendsto (fun n => (P n).real (boundaryHit (L n) (X n) (U n))) atTop (𝓝 0))
    (ν : ProbabilityMeasure (J → ℕ))
    (htrim : Tendsto (fun n => natVectorProbabilityLaw (P n)
      (visitCountVector (trimmedObservations (L n) (X n)) (liftedTargets (U n)))) atTop (𝓝 ν)) :
    Tendsto (fun n => natVectorProbabilityLaw (P n) (visitCountVector (X n) (U n))) atTop (𝓝 ν) := by
  apply natVector_law_transfer P (fun n => visitCountVector (X n) (U n))
    (fun n => visitCountVector (trimmedObservations (L n) (X n)) (liftedTargets (U n)))
    (fun n => measurable_visitCountVector (X n) (hX n) (U n) (hU n))
    (fun n => measurable_visitCountVector _ (measurable_trimmedObservations (L n) (X n) (hX n))
      _ (measurableSet_liftedTargets (U n) (hU n)))
    (fun n => boundaryHit (L n) (X n) (U n))
    (fun n ω hω => visitCountVector_eq_of_not_boundaryHit (L n) (X n) (U n) ω hω)
    hboundary ν htrim

omit [MeasurableSpace A] in
/-- One-time endpoint estimates are enough to verify the boundary-hit
hypothesis used in the count-law transfer. -/
theorem boundaryHit_tendsto_zero_of_sum
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n : ℕ, Fin n → Ω → A) (U : ℕ → J → Set A) (L : ℕ → ℕ)
    (hsum : Tendsto (fun n => ∑ t ∈ boundaryTimes n (L n),
      ∑ j, (P n).real {ω | X n t ω ∈ U n j}) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).real (boundaryHit (L n) (X n) (U n))) atTop (𝓝 0) :=
  squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => boundaryHit_probability_le (P n) (L n) (X n) (U n)) hsum

/-- The rare-configuration criterion can be applied to the trimmed process
and then transferred to the original process without endpoint moment bounds. -/
theorem independent_poisson_of_trimmed_configuration_estimates
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (U : ℕ → J → Set A) (hU : ∀ n j, MeasurableSet (U n j))
    (hdis : ∀ n, Pairwise fun i j => Disjoint (U n i) (U n j))
    (L : ℕ → ℕ)
    (hboundary : Tendsto (fun n => (P n).real (boundaryHit (L n) (X n) (U n))) atTop (𝓝 0))
    (p : J → ℕ → ℝ) (rate : J → ℝ≥0)
    (hp : ∀ j, Tendsto (fun n : ℕ => (n : ℝ) * p j n) atTop (𝓝 (rate j : ℝ)))
    (estimates : ∀ r : J → ℕ, 0 < ∑ j, r j → RareConfigurationEstimates P
      (fun n => trimmedObservations (L n) (X n)) (fun n => liftedTargets (U n)) p r) :
    Tendsto (fun n => natVectorProbabilityLaw (P n) (visitCountVector (X n) (U n)))
      atTop (𝓝 (independentPoissonProbabilityMeasure rate)) := by
  apply count_law_transfer_of_boundaryHit P X hX U hU L hboundary
    (independentPoissonProbabilityMeasure rate)
  exact independent_poisson_visit_counts_of_configuration_estimates P
    (fun n => trimmedObservations (L n) (X n))
    (fun n => measurable_trimmedObservations (L n) (X n) (hX n))
    (fun n => liftedTargets (U n)) (fun n => measurableSet_liftedTargets (U n) (hU n))
    (fun n => liftedTargets_disjoint (U n) (hdis n)) p rate hp estimates


omit [MeasurableSpace A] [Fintype J] in
/-- Labels contained in one rare target can all be controlled by a single
boundary union, without paying a factor for the number of labels. -/
theorem boundaryHit_probability_le_commonTarget {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (L : ℕ) (X : Fin n → Ω → A)
    (U : J → Set A) (V : Set A) (hUV : ∀ j, U j ⊆ V) :
    P.real (boundaryHit L X U) ≤
      ∑ t ∈ boundaryTimes n L, P.real {ω | X t ω ∈ V} := by
  have hs : boundaryHit L X U ⊆ ⋃ t ∈ boundaryTimes n L, {ω | X t ω ∈ V} := by
    rintro ω ⟨t, ht, j, hj⟩
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hUV j hj⟩⟩
  exact (measureReal_mono hs (measure_ne_top P _)).trans (measureReal_biUnion_finset_le _ _)

omit [MeasurableSpace A] [Fintype J] in
theorem boundaryHit_tendsto_zero_of_common_target_sum
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n : ℕ, Fin n → Ω → A) (U : ℕ → J → Set A) (V : ℕ → Set A)
    (hUV : ∀ n j, U n j ⊆ V n) (L : ℕ → ℕ)
    (hsum : Tendsto (fun n => ∑ t ∈ boundaryTimes n (L n),
      (P n).real {ω | X n t ω ∈ V n}) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).real (boundaryHit (L n) (X n) (U n))) atTop (𝓝 0) :=
  squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => boundaryHit_probability_le_commonTarget (P n) (L n) (X n) (U n) (V n) (hUV n)) hsum

end ConditionedStableLaws.EndpointTrimming
