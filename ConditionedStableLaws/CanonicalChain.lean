import ConditionedStableLaws.Birkhoff
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ConditionalProbability

/-!
# Canonical absorbing Markov chains

The state space is `Option M`, with `none` the cemetery state. A subset is measurable precisely when
its intersection with the live states is measurable in `M`. Path laws are constructed from a Markov
transition kernel by the Ionescu–Tulcea theorem. Conditioning is restriction and normalization of
the path law on a measurable finite-time survival event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ConditionedStableLaws

noncomputable section

variable {M : Type*} [MeasurableSpace M]

/-- The coproduct sigma algebra on the live states and one cemetery point. -/
instance optionStateMeasurableSpace : MeasurableSpace (Option M) :=
  (inferInstance : MeasurableSpace M).map Option.some

@[fun_prop]
theorem measurable_some_state : Measurable (Option.some : M → Option M) :=
  Measurable.of_le_map le_rfl

@[measurability]
theorem measurableSet_cemetery : MeasurableSet ({none} : Set (Option M)) := by
  change MeasurableSet (Option.some ⁻¹' ({none} : Set (Option M)))
  have h : (Option.some ⁻¹' ({none} : Set (Option M))) = (∅ : Set M) := by
    ext x
    change (some x = none ↔ False)
    constructor
    · intro hx
      cases hx
    · exact False.elim
  rw [h]
  exact MeasurableSet.empty

/-- A probability transition kernel with an absorbing cemetery. -/
structure CanonicalChain (M : Type*) [MeasurableSpace M] where
  transition : Kernel (Option M) (Option M)
  markov : IsMarkovKernel transition
  absorbing : transition none = Measure.dirac none

attribute [instance] CanonicalChain.markov

namespace CanonicalChain

/-- Canonical coordinate paths, equipped with the product sigma algebra. -/
abbrev Path (M : Type*) := ℕ → Option M

variable (C : CanonicalChain M)

/-- The next-step kernel reads the most recent coordinate of a finite history. -/
def historyKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Option M) (Option M) :=
  C.transition.comap (fun ω => ω ⟨n, by simp⟩) (measurable_pi_apply _)

instance historyKernel_isMarkov (n : ℕ) : IsMarkovKernel (C.historyKernel n) := by
  unfold historyKernel
  infer_instance

@[simp]
theorem historyKernel_apply (n : ℕ) (ω : (i : Finset.Iic n) → Option M) :
    C.historyKernel n ω = C.transition (ω ⟨n, by simp⟩) := rfl

/-- A history ending in the cemetery has a deterministic cemetery next step. -/
theorem historyKernel_of_last_none (n : ℕ)
    (ω : (i : Finset.Iic n) → Option M) (hω : ω ⟨n, by simp⟩ = none) :
    C.historyKernel n ω = Measure.dirac none := by
  rw [historyKernel_apply, hω, C.absorbing]

/-- Path law obtained by starting at the live state `x` and iterating `transition`. -/
def pathMeasure (x : M) : Measure (Path M) :=
  Kernel.trajMeasure (Measure.dirac (some x)) C.historyKernel

instance pathMeasure_isProbability (x : M) : IsProbabilityMeasure (C.pathMeasure x) := by
  unfold pathMeasure
  infer_instance

/-- The zeroth coordinate of the constructed path law has the prescribed Dirac distribution. -/
theorem pathMeasure_initial (x : M) :
    (C.pathMeasure x).map (fun ω => ω 0) = Measure.dirac (some x) := by
  let e : ((i : Finset.Iic 0) → Option M) → Option M := fun ω => ω ⟨0, by simp⟩
  have he : Measurable e := measurable_pi_apply _
  have hcoord : (fun ω : Path M => ω 0) = e ∘ Preorder.frestrictLe 0 := rfl
  rw [hcoord, ← Measure.map_map he (Preorder.measurable_frestrictLe 0)]
  unfold pathMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_map he (MeasurableEquiv.measurable _)]
  rw [Measure.map_dirac' (he.comp (MeasurableEquiv.measurable _))]
  rfl

variable {C}

/-- Survival through time `n`, including time zero. -/
def survival (n : ℕ) : Set (Path M) :=
  {ω | ∀ k : ℕ, k ≤ n → ω k ≠ none}

omit [MeasurableSpace M] in
@[simp]
theorem mem_survival (n : ℕ) (ω : Path M) :
    ω ∈ survival n ↔ ∀ k : ℕ, k ≤ n → ω k ≠ none := Iff.rfl

@[measurability]
theorem measurableSet_survival (n : ℕ) : MeasurableSet (survival (M := M) n) := by
  simp only [survival, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    (measurableSet_cemetery.preimage (measurable_pi_apply k)).compl

omit [MeasurableSpace M] in
/-- Surviving longer implies surviving every earlier time. -/
theorem survival_antitone : Antitone (survival (M := M)) := by
  intro m n hmn ω hω k hkm
  exact hω k (hkm.trans hmn)

omit [MeasurableSpace M] in
@[simp]
theorem survival_zero : survival (M := M) 0 = {ω | ω 0 ≠ none} := by
  ext ω
  simp [survival]

omit [MeasurableSpace M] in
theorem survival_succ (n : ℕ) :
    survival (M := M) (n + 1) = survival n ∩ {ω | ω (n + 1) ≠ none} := by
  ext ω
  constructor
  · intro h
    exact ⟨survival_antitone (Nat.le_succ n) h, h (n + 1) le_rfl⟩
  · rintro ⟨h, hlast⟩ k hk
    rcases Nat.eq_or_lt_of_le hk with heq | hlt
    · subst k
      exact hlast
    · exact h k (Nat.lt_succ_iff.mp hlt)

variable (C)

/-- Starting from a live state gives survival through time zero with probability one. -/
theorem pathMeasure_survival_zero (x : M) : C.pathMeasure x (survival 0) = 1 := by
  rw [survival_zero]
  change C.pathMeasure x ((fun ω : Path M => ω 0) ⁻¹' ({none} : Set (Option M))ᶜ) = 1
  have h0 : Measurable (fun ω : Path M => ω 0) := measurable_pi_apply 0
  have hnone : MeasurableSet ({none} : Set (Option M))ᶜ := measurableSet_cemetery.compl
  rw [← Measure.map_apply h0 hnone, pathMeasure_initial, Measure.dirac_apply' _ hnone]
  simp

/-- The survival-conditioned canonical path law. At a null survival event it is the zero measure; it
is a probability measure when survival has positive probability. -/
def conditionedMeasure (x : M) (n : ℕ) : Measure (Path M) :=
  ProbabilityTheory.cond (C.pathMeasure x) (survival n)

theorem conditionedMeasure_isProbability (x : M) (n : ℕ)
    (h : C.pathMeasure x (survival n) ≠ 0) :
    IsProbabilityMeasure (C.conditionedMeasure x n) :=
  ProbabilityTheory.cond_isProbabilityMeasure h

/-- The defining conditional-probability formula with the path law. -/
theorem conditionedMeasure_apply (x : M) (n : ℕ) (A : Set (Path M)) :
    C.conditionedMeasure x n A =
      (C.pathMeasure x (survival n))⁻¹ * C.pathMeasure x (survival n ∩ A) :=
  ProbabilityTheory.cond_apply (measurableSet_survival n) (C.pathMeasure x) A

theorem conditionedMeasure_survival (x : M) (n : ℕ)
    (h : C.pathMeasure x (survival n) ≠ 0) :
    C.conditionedMeasure x n (survival n) = 1 :=
  ProbabilityTheory.cond_apply_self h (measure_ne_top _ _)

theorem ae_survival_conditionedMeasure (x : M) (n : ℕ) :
    ∀ᵐ ω ∂C.conditionedMeasure x n, ω ∈ survival n :=
  ProbabilityTheory.ae_cond_mem (measurableSet_survival n)

theorem survival_probability_antitone (x : M) :
    Antitone (fun n => C.pathMeasure x (survival n)) := by
  intro m n hmn
  exact measure_mono (survival_antitone hmn)

end CanonicalChain

/-- Extend an observable by zero at the cemetery. -/
def zeroExtension (f : M → ℝ) : Option M → ℝ
  | none => 0
  | some x => f x

omit [MeasurableSpace M] in
@[simp]
theorem zeroExtension_none (f : M → ℝ) : zeroExtension f none = 0 := rfl

omit [MeasurableSpace M] in
@[simp]
theorem zeroExtension_some (f : M → ℝ) (x : M) : zeroExtension f (some x) = f x := rfl

@[fun_prop]
theorem measurable_zeroExtension {f : M → ℝ} (hf : Measurable f) :
    Measurable (zeroExtension f) := by
  intro A hA
  change MeasurableSet (Option.some ⁻¹' (zeroExtension f ⁻¹' A))
  exact hf hA

/-- The Birkhoff sum as a measurable function on canonical paths. -/
def pathBirkhoffSum (f : M → ℝ) (n : ℕ) (ω : CanonicalChain.Path M) : ℝ :=
  birkhoffSum (fun k => zeroExtension f (ω k)) n

@[fun_prop]
theorem measurable_pathBirkhoffSum {f : M → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (pathBirkhoffSum f n) := by
  unfold pathBirkhoffSum birkhoffSum
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_zeroExtension hf).comp (measurable_pi_apply k)

omit [MeasurableSpace M] in
theorem pathBirkhoffSum_succ (f : M → ℝ) (n : ℕ) (ω : CanonicalChain.Path M) :
    pathBirkhoffSum f (n + 1) ω =
      pathBirkhoffSum f n ω + zeroExtension f (ω n) :=
  birkhoffSum_succ _ n

end

end ConditionedStableLaws
