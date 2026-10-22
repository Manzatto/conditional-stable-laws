import ConditionedStableLaws.VagueConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Weak convergence from finite-dimensional interval counts

A countable family of dense interval endpoints induces a finer, second countable topology on the
same point measures. Its finite count cylinders form a pi-system. Deterministic interval-count
convergence proves that the identity into the vague topology is continuous.
-/

open Filter MeasureTheory Set Classical
open scoped Topology ENNReal NNReal

namespace ConditionedStableLaws
noncomputable section

/-- Natural interval counts indexed by two endpoint indices. -/
def intervalCountCoordinates (d : ℕ → ExtremeState) (ξ : LocallyFinitePointMeasure)
    (i : ℕ × ℕ) : ℕ := ξ.countOn (Ioc (d i.1) (d i.2))

theorem intervalCountCoordinates_eq_measureReal (d : ℕ → ExtremeState)
    (ξ : LocallyFinitePointMeasure) (i : ℕ × ℕ) :
    (intervalCountCoordinates d ξ i : ℝ) = ξ.toMeasure.real (Ioc (d i.1) (d i.2)) := by
  have h := ξ.countOn_interval_eq_measure (d i.1).val (d i.2).val (d i.1).property
  have h' := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_natCast] at h'
  convert h' using 1 <;> rfl

theorem measurable_intervalCountCoordinates (d : ℕ → ExtremeState) :
    Measurable (intervalCountCoordinates d) := by
  apply Measurable.of_eval
  intro i
  exact LocallyFinitePointMeasure.measurable_countOn_interval
    (d i.1).val (d i.2).val (d i.1).property

/-- The same point measures, equipped below with the topology of coordinatewise convergence of a
selected countable family of interval counts. -/
def CountTopologyPointMeasure (_d : ℕ → ExtremeState) := LocallyFinitePointMeasure

namespace CountTopologyPointMeasure

variable (d : ℕ → ExtremeState)

def toVague : CountTopologyPointMeasure d → LocallyFinitePointMeasure := id

def ofVague : LocallyFinitePointMeasure → CountTopologyPointMeasure d := id

def coordinates (ξ : CountTopologyPointMeasure d) : ℕ × ℕ → ℕ :=
  intervalCountCoordinates d (toVague d ξ)

instance : TopologicalSpace (CountTopologyPointMeasure d) :=
  TopologicalSpace.induced (coordinates d) inferInstance

instance : MeasurableSpace (CountTopologyPointMeasure d) := borel (CountTopologyPointMeasure d)

instance : BorelSpace (CountTopologyPointMeasure d) := ⟨rfl⟩

instance : SecondCountableTopology (CountTopologyPointMeasure d) :=
  TopologicalSpace.secondCountableTopology_induced _ _ (coordinates d)

instance : FirstCountableTopology (CountTopologyPointMeasure d) :=
  TopologicalSpace.firstCountableTopology_induced _ _ (coordinates d)

theorem continuous_coordinates : Continuous (coordinates d) := continuous_induced_dom

theorem measurable_ofVague : Measurable (ofVague d) := by
  change Measurable[_, @borel _ (TopologicalSpace.induced (coordinates d) _)] (ofVague d)
  rw [borel_comap, measurable_comap_iff]
  change @Measurable LocallyFinitePointMeasure (ℕ × ℕ → ℕ) _
    (borel (ℕ × ℕ → ℕ)) (intervalCountCoordinates d)
  rw [← @BorelSpace.measurable_eq (ℕ × ℕ → ℕ) _ _ _]
  exact measurable_intervalCountCoordinates d

/-- Passing from count convergence to vague convergence is continuous, by the deterministic interval
criterion. -/
theorem continuous_toVague (hd : DenseRange d) (htop : ⊤ ∈ range d) :
    Continuous (toVague d) := by
  apply SeqContinuous.continuous
  intro ξ ζ hξ
  apply LocallyFinitePointMeasure.tendsto_vague_of_interval_counts hd htop
  rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
  have ht := ((continuous_apply (i, j)).comp (continuous_coordinates d)).tendsto ζ |>.comp hξ
  have ht' := ((continuous_of_discreteTopology : Continuous (fun k : ℕ => (k : ℝ))).tendsto
    (coordinates d ζ (i, j))).comp ht
  simpa only [Function.comp_def, coordinates, intervalCountCoordinates_eq_measureReal] using ht'

/-- Finite exact-count cylinders. -/
def cylinder (F : Finset (ℕ × ℕ)) (k : ℕ × ℕ → ℕ) : Set (CountTopologyPointMeasure d) :=
  {ξ | ∀ i ∈ F, coordinates d ξ i = k i}

def cylinders : Set (Set (CountTopologyPointMeasure d)) :=
  {s | ∃ F k, s = cylinder d F k}

theorem isOpen_cylinder (F : Finset (ℕ × ℕ)) (k : ℕ × ℕ → ℕ) :
    IsOpen (cylinder d F k) := by
  have heq : cylinder d F k = ⋂ i ∈ F,
      (fun ξ : CountTopologyPointMeasure d => coordinates d ξ i) ⁻¹' {k i} := by
    ext ξ
    simp [cylinder]
  rw [heq]
  exact isOpen_biInter_finset fun i _ =>
    (isOpen_discrete {k i}).preimage ((continuous_apply i).comp (continuous_coordinates d))

theorem cylinders_isPiSystem : IsPiSystem (cylinders d) := by
  rintro s ⟨F, k, rfl⟩ t ⟨G, l, rfl⟩ ⟨ζ, hζF, hζG⟩
  refine ⟨F ∪ G, coordinates d ζ, ?_⟩
  ext ξ
  constructor
  · rintro ⟨hξF, hξG⟩ i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (hξF i hi).trans (hζF i hi).symm
    · exact (hξG i hi).trans (hζG i hi).symm
  · intro hξ
    exact ⟨fun i hi => (hξ i (Finset.mem_union_left _ hi)).trans (hζF i hi),
      fun i hi => (hξ i (Finset.mem_union_right _ hi)).trans (hζG i hi)⟩

theorem cylinders_nhds : ∀ u : Set (CountTopologyPointMeasure d), IsOpen u →
    ∀ ξ ∈ u, ∃ s ∈ cylinders d, s ∈ 𝓝 ξ ∧ s ⊆ u := by
  intro u hu ξ hξ
  have hmem := hu.mem_nhds hξ
  change u ∈ @nhds _ (TopologicalSpace.induced (coordinates d) _) ξ at hmem
  rw [nhds_induced] at hmem
  obtain ⟨V, hV, hVU⟩ := mem_comap.mp hmem
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨F, t, ht, hsub⟩ := hV
  refine ⟨cylinder d F (coordinates d ξ), ⟨F, coordinates d ξ, rfl⟩,
    (isOpen_cylinder d F _).mem_nhds (fun i _ => rfl), ?_⟩
  intro ζ hζ
  apply hVU
  apply hsub
  intro i hi
  rw [hζ i hi]
  exact mem_of_mem_nhds (ht i)

/-- Convergence of the masses of all finite exact-count cylinders gives weak
convergence for the count topology. -/
theorem probability_tendsto_of_cylinders
    {μ : ℕ → ProbabilityMeasure (CountTopologyPointMeasure d)}
    {ν : ProbabilityMeasure (CountTopologyPointMeasure d)}
    (h : ∀ F k, Tendsto (fun n => μ n (cylinder d F k)) atTop
      (𝓝 (ν (cylinder d F k)))) : Tendsto μ atTop (𝓝 ν) := by
  apply (cylinders_isPiSystem d).tendsto_probabilityMeasure_of_tendsto_of_mem
    (fun s hs => ?_) (cylinders_nhds d)
  · rintro s ⟨F, k, rfl⟩
    exact h F k
  · rcases hs with ⟨F, k, rfl⟩
    exact (isOpen_cylinder d F k).measurableSet

private theorem law_cylinder_eq_vector_atom
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : RandomPointMeasure Ω) (F : Finset (ℕ × ℕ)) (k : ℕ × ℕ → ℕ) :
    (P.map (fun ω => ofVague d (N.toFun ω)) (cylinder d F k)).toNNReal =
      (P.map (fun ω => F.restrict (intervalCountCoordinates d (N.toFun ω)))
        {F.restrict k}).toNNReal := by
  have hNm : Measurable (fun ω => ofVague d (N.toFun ω)) :=
    (measurable_ofVague d).comp N.measurable
  have hVm : Measurable (fun ω => F.restrict (intervalCountCoordinates d (N.toFun ω))) :=
    (Finset.measurable_restrict F).comp ((measurable_intervalCountCoordinates d).comp N.measurable)
  rw [Measure.map_apply hNm (isOpen_cylinder d F k).measurableSet,
    Measure.map_apply hVm (measurableSet_singleton _)]
  congr 2
  ext ω
  simp only [cylinder, coordinates, ofVague, toVague, id_eq, mem_preimage, mem_singleton_iff,
    funext_iff, Finset.restrict_def, Subtype.forall]
  rfl

end CountTopologyPointMeasure

/-- Finite-dimensional interval-count law convergence gives weak convergence of random point
measures for the vague topology. This version uses one countable dense family of endpoints and
permits overlapping intervals. -/
theorem randomPointMeasure_tendsto_of_joint_counts
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (N : (n : ℕ) → RandomPointMeasure (Ω n)) (Nlimit : RandomPointMeasure Ω')
    (d : ℕ → ExtremeState) (hd : DenseRange d) (htop : ⊤ ∈ range d)
    (hcounts : ∀ F : Finset (ℕ × ℕ),
      TendstoInDistribution
        (fun n ω => F.restrict (intervalCountCoordinates d ((N n).toFun ω))) atTop
        (fun ω => F.restrict (intervalCountCoordinates d (Nlimit.toFun ω))) P Q) :
    TendstoInDistribution (fun n => (N n).toFun) atTop Nlimit.toFun P Q := by
  have hc : TendstoInDistribution
      (fun n ω => CountTopologyPointMeasure.ofVague d ((N n).toFun ω)) atTop
      (fun ω => CountTopologyPointMeasure.ofVague d (Nlimit.toFun ω)) P Q := by
    refine ⟨fun n => ((CountTopologyPointMeasure.measurable_ofVague d).comp
      (N n).measurable).aemeasurable,
      ((CountTopologyPointMeasure.measurable_ofVague d).comp Nlimit.measurable).aemeasurable, ?_⟩
    apply CountTopologyPointMeasure.probability_tendsto_of_cylinders d
    intro F k
    have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
      (hcounts F).tendsto (isClopen_discrete {F.restrict k})
    change Tendsto (fun n => ((P n).map
      (fun ω => CountTopologyPointMeasure.ofVague d ((N n).toFun ω))
      (CountTopologyPointMeasure.cylinder d F k)).toNNReal) atTop
      (𝓝 ((Q.map (fun ω => CountTopologyPointMeasure.ofVague d (Nlimit.toFun ω))
        (CountTopologyPointMeasure.cylinder d F k)).toNNReal))
    simp only [CountTopologyPointMeasure.law_cylinder_eq_vector_atom]
    convert ht using 1 <;> rfl
  exact hc.continuous_comp (CountTopologyPointMeasure.continuous_toVague d hd htop)

/-- The interval-count criterion with arbitrary finite interval families.
The intervals may overlap or be empty. -/
theorem randomPointMeasure_tendsto_of_all_joint_intervals
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (N : (n : ℕ) → RandomPointMeasure (Ω n)) (Nlimit : RandomPointMeasure Ω')
    (hcounts : ∀ (k : ℕ) (a b : Fin k → ExtremeState),
      TendstoInDistribution
        (fun n ω => fun j => ((N n).toFun ω).countOn (Ioc (a j) (b j))) atTop
        (fun ω => fun j => (Nlimit.toFun ω).countOn (Ioc (a j) (b j))) P Q) :
    TendstoInDistribution (fun n => (N n).toFun) atTop Nlimit.toFun P Q := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ExtremeState
  let d : ℕ → ExtremeState := fun n => if n = 0 then ⊤ else e (n - 1)
  have hd : DenseRange d := by
    apply he.mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i + 1, by simp [d]⟩
  have htop : ⊤ ∈ range d := ⟨0, by simp [d]⟩
  apply randomPointMeasure_tendsto_of_joint_counts P Q N Nlimit d hd htop
  intro F
  let equiv : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
  have ht := hcounts (Fintype.card F)
    (fun i => d (equiv.symm i).val.1) (fun i => d (equiv.symm i).val.2)
  have ht' := ht.continuous_comp
    (g := fun v : Fin (Fintype.card F) → ℕ => fun i : F => v (equiv i))
    (by fun_prop)
  simpa only [Function.comp_def, Equiv.symm_apply_apply, intervalCountCoordinates,
    Finset.restrict_def] using ht'

end
end ConditionedStableLaws
