import ConditionedStableLaws.RemarkConsequences
import ConditionedStableLaws.PoissonTargetStart

/-!
# Finite-count independence: the deterministic exception and a dependence criterion

Functions of the initial observation are independent, since it is deterministic even after survival
conditioning. At two observations, disjoint targets avoiding the initial state give an obstruction
to independence whenever both time-one hits have positive probability under the conditioned law.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
noncomputable section
namespace ConditionedStableLaws.CanonicalChain

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  (C : CanonicalChain M)

/-- Any two functions of the initial state are independent under the conditioned path law, because
that state is prescribed deterministically. -/
theorem initial_functions_independent
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State) (n : ℕ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : Option M → A) (G : Option M → B) :
    IndepFun (fun ω : Path M => F (ω 0)) (fun ω : Path M => G (ω 0))
      (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) := by
  have hconst : IndepFun (fun _ : Path M => F (some x.val)) (fun _ : Path M => G (some x.val))
      (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) :=
    indepFun_const_left _ _
  apply hconst.congr
  · filter_upwards [C.ae_initial_conditionedMeasure x.val n] with ω hω
    exact congrArg F hω.symm
  · filter_upwards [C.ae_initial_conditionedMeasure x.val n] with ω hω
    exact congrArg G hω.symm

/-- In particular, the empirical counts for n=1 are independent for every pair of targets, even
under survival conditioning. -/
theorem initial_visit_counts_independent
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State) (n : ℕ)
    (U V : Set M) :
    IndepFun
      (fun ω : Path M => (visitTimes (fun i : Fin 1 => ω i.val) (Option.some '' U)).card)
      (fun ω : Path M => (visitTimes (fun i : Fin 1 => ω i.val) (Option.some '' V)).card)
      (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) := by
  have he : ∀ ω : Path M, (fun i : Fin 1 => ω i.val) = fun _ : Fin 1 => ω 0 := by
    intro ω
    funext i
    rw [Fin.eq_zero i]
    rfl
  simpa only [he] using C.initial_functions_independent d x n
    (fun z => (visitTimes (fun _ : Fin 1 => z) (Option.some '' U)).card)
    (fun z => (visitTimes (fun _ : Fin 1 => z) (Option.some '' V)).card)

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- With time zero outside the target, its two-observation count equals the
single-observation count at time one. -/
theorem visitTimes_two_eq_time_one (ω : Path M) (U : Set (Option M))
    (hzero : ω 0 ∉ U) :
    (visitTimes (fun i : Fin 2 => ω i.val) U).card =
      (visitTimes (fun _ : Fin 1 => ω 1) U).card := by
  classical
  unfold visitTimes
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_two, Fin.sum_univ_one]
  simp [hzero]

/-- The two-observation empirical counts are dependent whenever the initial point avoids two
disjoint targets and both targets have positive hitting probability at time one under the specified
conditioned path law. -/
theorem two_visit_counts_not_independent
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State) (n : ℕ)
    {U V : Set M} (hd : Disjoint U V) (hxU : x.val ∉ U) (hxV : x.val ∉ V)
    (hU : (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))
      {ω | ω 1 ∈ Option.some '' U} ≠ 0)
    (hV : (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))
      {ω | ω 1 ∈ Option.some '' V} ≠ 0) :
    ¬ IndepFun
      (fun ω : Path M => (visitTimes (fun i : Fin 2 => ω i.val) (Option.some '' U)).card)
      (fun ω : Path M => (visitTimes (fun i : Fin 2 => ω i.val) (Option.some '' V)).card)
      (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) := by
  have hnot := not_independent_single_observation_counts (fun ω : Path M => ω 1)
    (Set.disjoint_image_of_injective (Option.some_injective M) hd) hU hV
  intro hi
  apply hnot
  apply hi.congr
  · filter_upwards [C.ae_initial_conditionedMeasure x.val n] with ω hω
    apply visitTimes_two_eq_time_one
    simpa only [hω, Set.mem_image, Option.some.injEq, exists_eq_right] using hxU
  · filter_upwards [C.ae_initial_conditionedMeasure x.val n] with ω hω
    apply visitTimes_two_eq_time_one
    simpa only [hω, Set.mem_image, Option.some.injEq, exists_eq_right] using hxV

end ConditionedStableLaws.CanonicalChain
