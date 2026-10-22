import ConditionedStableLaws.RandomMeasureConvergence

/-!
# Countable superposition with eventually empty positive tails

The resulting object is the sum of the component measures. Its atomic representation uses a
countable sigma type of atoms. The domain condition is measurable and suffices for local finiteness;
it holds in particular for annular components whose supports tend to zero.
-/

open Filter MeasureTheory Set Classical
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace ConditionedStableLaws

namespace LocallyFinitePointMeasure

/-- Measurability of countably many interval coordinates already implies measurability into the
vague Borel sigma algebra. -/
theorem measurable_of_interval_counts {Ω : Type*} [MeasurableSpace Ω]
    (N : Ω → LocallyFinitePointMeasure)
    (hN : ∀ a b : ExtremeState, Measurable (fun ω => (N ω).countOn (Ioc a b))) :
    Measurable N := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ExtremeState
  let d : ℕ → ExtremeState := fun n => if n = 0 then ⊤ else e (n - 1)
  have hd : DenseRange d := by
    apply he.mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i + 1, by simp [d]⟩
  have htop : ⊤ ∈ range d := ⟨0, by simp [d]⟩
  have hm : Measurable (fun ω => CountTopologyPointMeasure.ofVague d (N ω)) := by
    change Measurable[_, @borel _ (TopologicalSpace.induced
      (CountTopologyPointMeasure.coordinates d) _)] _
    rw [borel_comap, measurable_comap_iff]
    change @Measurable Ω (ℕ × ℕ → ℕ) _ (borel (ℕ × ℕ → ℕ))
      (fun ω => intervalCountCoordinates d (N ω))
    rw [← @BorelSpace.measurable_eq (ℕ × ℕ → ℕ) _ _ _]
    exact Measurable.of_eval (fun i => hN (d i.1) (d i.2))
  exact (CountTopologyPointMeasure.continuous_toVague d hd htop).measurable.comp hm

end LocallyFinitePointMeasure

namespace CountableSuperposition

/-- Only finitely many components charge each positive compact tail. -/
def EventuallyZeroOnTails (ξ : ℕ → LocallyFinitePointMeasure) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → (ξ n).toMeasure (extremeTail ε) = 0

/-- The test condition has a countable form using reciprocal tails. -/
theorem eventuallyZeroOnTails_iff (ξ : ℕ → LocallyFinitePointMeasure) :
    EventuallyZeroOnTails ξ ↔ ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n →
      (ξ n).toMeasure (extremeTail (1 / (k + 1))) = 0 := by
  constructor
  · intro h k
    exact h _ (by positivity)
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, fun n hn => ?_⟩
    apply measure_mono_null _ (hN n hn)
    intro x hx
    exact (show ((1 / (k + 1) : ℝ≥0) : ℝ≥0∞) ≤ (ε : ℝ≥0∞) by
      exact_mod_cast hk.le).trans hx

/-- The local finiteness condition is a measurable subset of the sequence space. -/
theorem measurableSet_eventuallyZeroOnTails :
    MeasurableSet {ξ : ℕ → LocallyFinitePointMeasure | EventuallyZeroOnTails ξ} := by
  have heq : {ξ : ℕ → LocallyFinitePointMeasure | EventuallyZeroOnTails ξ} =
      ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ _h : N ≤ n,
        {ξ | (ξ n).toMeasure (extremeTail (1 / (k + 1))) = 0} := by
    ext ξ
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, eventuallyZeroOnTails_iff]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro hn
  exact measurableSet_eq_fun
    ((LocallyFinitePointMeasure.measurable_measure_tail _ (by positivity)).comp
      (measurable_pi_apply n)) measurable_const

/-- The measurable subtype on which the sum is locally finite. -/
def GoodSequence := {ξ : ℕ → LocallyFinitePointMeasure // EventuallyZeroOnTails ξ}

instance : MeasurableSpace GoodSequence := inferInstanceAs
  (MeasurableSpace {ξ : ℕ → LocallyFinitePointMeasure // EventuallyZeroOnTails ξ})

/-- Countable sums preserve a countable unit-Dirac representation. -/
theorem isPointMeasure_sum (ξ : ℕ → LocallyFinitePointMeasure) :
    IsPointMeasure (Measure.sum (fun n => (ξ n).toMeasure)) := by
  choose J hJ a ha using fun n => (ξ n).atomic
  let (n : ℕ) : Countable (J n) := hJ n
  refine ⟨Σ n, J n, inferInstance, (fun z => a z.1 z.2), ?_⟩
  ext A hA
  simp_rw [Measure.sum_apply _ hA, ha, Measure.sum_apply _ hA]
  exact (ENNReal.tsum_sigma _).symm

/-- The superposed measure, with local finiteness proved from the finite number of nonzero component
masses on each positive tail. -/
def superpose (ξ : GoodSequence) : LocallyFinitePointMeasure where
  toMeasure := Measure.sum (fun n => (ξ.val n).toMeasure)
  atomic := isPointMeasure_sum ξ.val
  finite_tail := by
    intro ε hε
    obtain ⟨N, hN⟩ := ξ.property ε hε
    rw [Measure.sum_apply_of_countable]
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => hN n (by simpa using hn))]
    exact ENNReal.sum_lt_top.mpr (fun n _ => (ξ.val n).finite_tail ε hε)

/-- Evaluation of the constructed point measure is precisely the sum of
component evaluations, for every set. -/
theorem superpose_apply (ξ : GoodSequence) (A : Set ExtremeState) :
    (superpose ξ).toMeasure A = ∑' n, (ξ.val n).toMeasure A :=
  Measure.sum_apply_of_countable _ _

/-- The countable superposition is measurable for the vague Borel topology. -/
theorem measurable_superpose : Measurable superpose := by
  apply LocallyFinitePointMeasure.measurable_of_interval_counts
  intro a b
  have hm : Measurable (fun ξ : GoodSequence => (superpose ξ).toMeasure (Ioc a b)) := by
    simp_rw [superpose_apply]
    apply Measurable.tsum
    intro n
    exact (LocallyFinitePointMeasure.measurable_measure_interval a.val b.val a.property).comp
      ((measurable_pi_apply n).comp measurable_subtype_coe)
  exact hm.ennreal_toReal.nat_floor

/-- An empty point measure supplies a harmless total extension off the
measurable domain where the countable sum is locally finite. -/
def emptyPointMeasure : LocallyFinitePointMeasure :=
  LocallyFinitePointMeasure.empirical (fun i : Fin 0 => Fin.elim0 i)

@[simp] theorem emptyPointMeasure_apply (A : Set ExtremeState) :
    emptyPointMeasure.toMeasure A = 0 := by
  simp [emptyPointMeasure, LocallyFinitePointMeasure.empirical_apply]

/-- A total measurable construction, equal to the sum on good sequences. -/
def superposeOrEmpty (ξ : ℕ → LocallyFinitePointMeasure) : LocallyFinitePointMeasure :=
  if h : EventuallyZeroOnTails ξ then superpose ⟨ξ, h⟩ else emptyPointMeasure

theorem measurable_superposeOrEmpty : Measurable superposeOrEmpty :=
  measurable_superpose.dite measurable_const measurableSet_eventuallyZeroOnTails

/-- The total version retains the exact sum identity at every good sequence. -/
theorem superposeOrEmpty_apply (ξ : ℕ → LocallyFinitePointMeasure)
    (hξ : EventuallyZeroOnTails ξ) (A : Set ExtremeState) :
    (superposeOrEmpty ξ).toMeasure A = ∑' n, (ξ n).toMeasure A := by
  rw [superposeOrEmpty, dite_eq_left hξ]
  exact superpose_apply ⟨ξ, hξ⟩ A

/-- Annular supports tending to zero imply the local finiteness condition. -/
theorem good_of_supported (A : ℕ → Set ExtremeState)
    (hA : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → Disjoint (A n) (extremeTail ε))
    (ξ : ℕ → LocallyFinitePointMeasure) (hξ : ∀ n, (ξ n).toMeasure (A n)ᶜ = 0) :
    EventuallyZeroOnTails ξ := by
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε hε
  refine ⟨N, fun n hn => measure_mono_null ?_ (hξ n)⟩
  intro x hx hxA
  exact Set.disjoint_left.mp (hN n hn) hxA hx

/-- An eventual deterministic upper bound on the component supports is
another convenient criterion, directly suited to shrinking annuli. -/
theorem good_of_upper_bounds (ξ : ℕ → LocallyFinitePointMeasure) (b : ℕ → ℝ≥0)
    (hb : Tendsto b atTop (𝓝 0))
    (hξ : ∀ᶠ n in atTop, (ξ n).toMeasure {x : ExtremeState | (b n : ℝ≥0∞) < x.val} = 0) :
    EventuallyZeroOnTails ξ := by
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, b n < ε := hb.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := (hsmall.and hξ).exists_forall_of_atTop
  refine ⟨N, fun n hn => measure_mono_null ?_ (hN n hn).2⟩
  intro x hx
  exact (show (b n : ℝ≥0∞) < (ε : ℝ≥0∞) by exact_mod_cast (hN n hn).1).trans_le hx

/-- Random point measures may be superposed on a common probability space. The definition is total,
and the equality with the sum holds wherever the components satisfy the local finiteness condition.
-/
def randomSuperposition {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ → RandomPointMeasure Ω) : RandomPointMeasure Ω where
  toFun ω := superposeOrEmpty (fun n => (N n).toFun ω)
  measurable := measurable_superposeOrEmpty.comp (Measurable.of_eval (fun n => (N n).measurable))

theorem randomSuperposition_apply_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → RandomPointMeasure Ω)
    (hN : ∀ᵐ ω ∂P, EventuallyZeroOnTails (fun n => (N n).toFun ω)) :
    ∀ᵐ ω ∂P, ∀ A : Set ExtremeState,
      ((randomSuperposition N).toFun ω).toMeasure A = ∑' n, ((N n).toFun ω).toMeasure A := by
  filter_upwards [hN] with ω hω A
  exact superposeOrEmpty_apply _ hω A

end CountableSuperposition
end ConditionedStableLaws
