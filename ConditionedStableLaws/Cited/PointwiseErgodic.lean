import ConditionedStableLaws.QProcessLimit
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Path shift
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace ConditionedStableLaws.Cited

/-- The left shift on one-sided trajectories. -/
def pathShift {X : Type*} (ω : ℕ → X) : ℕ → X := fun n => ω (n + 1)

end ConditionedStableLaws.Cited
