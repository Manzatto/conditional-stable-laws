import ConditionedStableLaws.FiniteCountExample
/-!
# A finite-state example with dependent finite counts

The uniform three-state refresh chain satisfies H. Starting from state zero, the counts of states
one and two among times zero and one are dependent under the conditioned canonical path law.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ConditionedStableLaws.FiniteCountExample
noncomputable section
/-- The three states carry the metric inherited from their natural labels. -/
abbrev threeStateMetric : MetricSpace (Fin 3) :=
  MetricSpace.induced Fin.val Fin.val_injective inferInstance
attribute [local instance] threeStateMetric
def threeLaw : Measure (Fin 3) := Measure.uniformOfFinset Finset.univ
instance : IsProbabilityMeasure threeLaw :=
  ⟨by rw [threeLaw, Measure.uniformOfFinset_apply]; simp [ENNReal.div_self]⟩
theorem threeLaw_singleton (x : Fin 3) : threeLaw {x} = (3 : ℝ≥0∞)⁻¹ := by
  rw [threeLaw, Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ x)]
  simp
instance threeLaw_fullSupport [t : TopologicalSpace (Fin 3)] :
    @Measure.IsOpenPosMeasure (Fin 3) t inferInstance threeLaw where
  open_pos U _ hU := by
    obtain ⟨x, hx⟩ := hU
    have hpos : 0 < threeLaw {x} := by rw [threeLaw_singleton]; norm_num
    exact (hpos.trans_le (measure_mono (singleton_subset_iff.mpr hx))).ne'
/-- The concrete uniform refresh chain satisfies every clause of H. -/
def threeStateHypothesisH : StandingHypothesis.HypothesisH threeLaw
    (refreshChain threeLaw).toKilledKernel := refreshChain_hypothesisH threeLaw

/-- An explicit example where finite empirical counts are not independent under the conditioned path
law of a chain satisfying H. -/
theorem threeState_counts_dependent :
    ¬ IndepFun
      (fun ω : CanonicalChain.Path (Fin 3) =>
        (visitTimes (fun i : Fin 2 => ω i.val) (Option.some '' {(1 : Fin 3)})).card)
      (fun ω : CanonicalChain.Path (Fin 3) =>
        (visitTimes (fun i : Fin 2 => ω i.val) (Option.some '' {(2 : Fin 3)})).card)
      ((refreshChain threeLaw).liveConditionedProbabilityMeasure (refreshEigenData threeLaw)
        (refreshState threeLaw 0) 2 : Measure (CanonicalChain.Path (Fin 3))) := by
  apply refresh_two_counts_dependent threeLaw (0 : Fin 3)
    (measurableSet_singleton _) (measurableSet_singleton _)
  · norm_num
  · norm_num
  · norm_num
  · rw [threeLaw_singleton]
    norm_num
  · rw [threeLaw_singleton]
    norm_num
end
end ConditionedStableLaws.FiniteCountExample
