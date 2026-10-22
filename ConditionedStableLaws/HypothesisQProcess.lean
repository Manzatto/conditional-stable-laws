import ConditionedStableLaws.HypothesisSpectralGap

/-! The canonical Q-process finite-history limit from H alone. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.CanonicalChain
noncomputable section
open StandingHypothesis QProcessLimit
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Under H, the Q-process exists and all survival-conditioned finite-history events converge. -/
theorem exists_conditioned_cylinder_limit (h : HypothesisH ρ C.toKilledKernel) :
    ∃ d : DoobTransform.EigenData C.killedTransition,
      d.rate ≤ 1 ∧ Continuous d.weight ∧ d.liveSet = survivingSet C.killedTransition ∧
      ∀ (x : d.State) (n : ℕ) (A : Set (History (Option M) n)), MeasurableSet A →
        Tendsto (fun N : ℕ =>
          C.conditionedMeasure x.val N {ω | Preorder.frestrictLe n ω ∈ A}) atTop
          (𝓝 (C.doobPathMeasure d x {ω | coeHistory (C.cemeteryEigenData d) n
            (Preorder.frestrictLe n ω) ∈ A})) := by
  obtain ⟨d, hdr, hc, hlive, _μ, _hleft, _hnorm, ⟨s⟩⟩ := h.exists_eigenData_survivalGap
  exact ⟨d, hdr, hc, hlive, fun x n A hA =>
    C.conditioned_cylinder_tendsto_doob_of_operator_gap h d s x n A hA⟩

end
end ConditionedStableLaws.CanonicalChain
