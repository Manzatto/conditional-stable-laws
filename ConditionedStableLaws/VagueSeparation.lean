import ConditionedStableLaws.PointMeasures
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Metrizable.Real

/-!
# Separation of the vague point-measure topology

Compactly supported test integrals determine the locally finite measure, so the induced vague
topology is Hausdorff. This verifies that the topology used for random point measures distinguishes
their measures.
-/

open MeasureTheory
open scoped CompactlySupported ENNReal

namespace ConditionedStableLaws
noncomputable section

instance extremeState_locallyCompact : LocallyCompactSpace ExtremeState :=
  (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ≥0∞))).locallyCompactSpace

instance extremeState_metrizable : TopologicalSpace.MetrizableSpace ExtremeState :=
  Topology.IsEmbedding.subtypeVal.metrizableSpace

namespace LocallyFinitePointMeasure

theorem testIntegrals_injective : Function.Injective testIntegrals := by
  intro ξ ζ heq
  apply ext
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact congrFun heq f

theorem isEmbedding_testIntegrals : Topology.IsEmbedding testIntegrals :=
  ⟨⟨rfl⟩, testIntegrals_injective⟩

instance : T2Space LocallyFinitePointMeasure := isEmbedding_testIntegrals.t2Space

end LocallyFinitePointMeasure
end
end ConditionedStableLaws
