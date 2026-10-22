import ConditionedStableLaws.PointMeasures
import Mathlib.MeasureTheory.Measure.Count

/-!
# Integer counts of point measures

A countable unit-Dirac representation forces every finite Borel evaluation to be a natural number,
including repeated atoms with their multiplicities.
-/

open MeasureTheory Set Classical
open scoped ENNReal NNReal

namespace ConditionedStableLaws
noncomputable section

/-- Finite evaluations of a countable unit-Dirac measure are integer counts. -/
theorem IsPointMeasure.exists_nat_of_apply_lt_top {μ : Measure ExtremeState}
    (hμ : IsPointMeasure μ) (A : Set ExtremeState) (hA : MeasurableSet A)
    (hfinite : μ A < ∞) : ∃ n : ℕ, μ A = n := by
  obtain ⟨J, hJ, a, rfl⟩ := hμ
  have : Countable J := hJ
  let : MeasurableSpace J := ⊤
  have hJA : MeasurableSet {j : J | a j ∈ A} := trivial
  have heq : (Measure.sum (fun j => Measure.dirac (a j))) A =
      Measure.count {j : J | a j ∈ A} := by
    simp only [Measure.count, Measure.sum_apply_of_countable]
    apply tsum_congr
    intro j
    simp [Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hJA, Set.indicator_apply]
  rw [heq] at hfinite ⊢
  have hs := (Measure.count_apply_lt_top' hJA).mp hfinite
  exact ⟨hs.toFinset.card, Measure.count_apply_finite' hs hJA⟩

namespace LocallyFinitePointMeasure

theorem exists_nat_tail (ξ : LocallyFinitePointMeasure) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ n : ℕ, ξ.toMeasure (extremeTail ε) = n :=
  ξ.atomic.exists_nat_of_apply_lt_top (extremeTail ε)
    (measurableSet_le measurable_const measurable_subtype_coe) (ξ.finite_tail ε hε)

theorem exists_nat_singleton (ξ : LocallyFinitePointMeasure) (y : ExtremeState) :
    ∃ n : ℕ, ξ.toMeasure {y} = n :=
  ξ.atomic.exists_nat_of_apply_lt_top {y} (measurableSet_singleton y)
    (isCompact_singleton.measure_lt_top)

end LocallyFinitePointMeasure
end
end ConditionedStableLaws
