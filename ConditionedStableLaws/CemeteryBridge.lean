import ConditionedStableLaws.CanonicalChain
import ConditionedStableLaws.StandingHypothesis

/-!
# From a canonical cemetery-state chain to its killed kernel

Restricting the source of the transition kernel to live states, and pulling its target measure back
along `Option.some`, gives the killed kernel on `M`: the one-step transition formula, the
subprobability bound, and the split between survival and cemetery mass.
-/

open MeasureTheory ProbabilityTheory Set

namespace ConditionedStableLaws

noncomputable section

variable {M : Type*} [MeasurableSpace M]

/-- The inclusion of live states is a measurable embedding for the chosen
coproduct sigma algebra on `Option M`. -/
theorem measurableEmbedding_some_state :
    MeasurableEmbedding (Option.some : M → Option M) where
  injective := fun _ _ h => Option.some.inj h
  measurable := measurable_some_state
  measurableSet_image' := by
    intro A hA
    change MeasurableSet (Option.some ⁻¹' (Option.some '' A))
    have heq : Option.some ⁻¹' (Option.some '' A) = A := by
      ext x
      simp
    rwa [heq]

namespace CanonicalChain

variable (C : CanonicalChain M)

/-- The transition kernel before absorption, defined from the cemetery-state transition kernel. -/
def killedTransition : Kernel M M :=
  (C.transition.comap Option.some measurable_some_state).comapRight
    measurableEmbedding_some_state

/-- The killed one-step law is exactly the live-state part of the original
transition law. -/
theorem killedTransition_apply (x : M) (A : Set M) (hA : MeasurableSet A) :
    C.killedTransition x A = C.transition (some x) (Option.some '' A) := by
  rw [killedTransition, Kernel.comapRight_apply' _ _ _ hA]
  rfl

theorem killedTransition_mass_le_one (x : M) : C.killedTransition x univ ≤ 1 := by
  rw [C.killedTransition_apply x univ MeasurableSet.univ]
  exact prob_le_one

/-- The killed kernel of the canonical chain. -/
def toKilledKernel : StandingHypothesis.KilledKernel M where
  kernel := C.killedTransition
  mass_le_one := C.killedTransition_mass_le_one

@[simp]
theorem toKilledKernel_kernel : C.toKilledKernel.kernel = C.killedTransition := rfl

omit [MeasurableSpace M] in
/-- The live-state range is the complement of the cemetery singleton. -/
theorem live_states_eq_cemetery_compl :
    Set.range (Option.some : M → Option M) = ({none} : Set (Option M))ᶜ := by
  ext y
  cases y <;> simp

/-- Total killed mass is the original one-step probability of a live state. -/
theorem killedTransition_univ (x : M) :
    C.killedTransition x univ = C.transition (some x) ({none} : Set (Option M))ᶜ := by
  rw [C.killedTransition_apply x univ MeasurableSet.univ, Set.image_univ,
    live_states_eq_cemetery_compl]

/-- The mass removed by killing is precisely the one-step cemetery mass. -/
theorem killedTransition_mass_add_cemetery (x : M) :
    C.killedTransition x univ + C.transition (some x) {none} = 1 := by
  rw [killedTransition_univ]
  simpa only [compl_compl, measure_univ] using
    measure_add_measure_compl (μ := C.transition (some x)) measurableSet_cemetery.compl

end CanonicalChain

end

end ConditionedStableLaws
