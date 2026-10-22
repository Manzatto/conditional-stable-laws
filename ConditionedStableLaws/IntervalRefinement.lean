import ConditionedStableLaws.VagueConvergence
import ConditionedStableLaws.RandomMeasureConvergence
import Mathlib.Data.Finset.Max

/-! Finite disjoint interval refinement and additivity of point counts. -/

open Set MeasureTheory
open scoped ENNReal

namespace ConditionedStableLaws.IntervalRefinement
noncomputable section
variable {X : Type*} [LinearOrder X]

/-- Strict adjacent endpoint pairs in a finite set. -/
def cells (S : Finset X) : Finset (X × X) :=
  (S.product S).filter (fun p => p.1 < p.2 ∧ ∀ c ∈ S, ¬ (p.1 < c ∧ c < p.2))

theorem mem_cells {S : Finset X} {p : X × X} : p ∈ cells S ↔
    p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ ∀ c ∈ S, ¬ (p.1 < c ∧ c < p.2) := by
  constructor
  · intro hp
    obtain ⟨hp, hlt, hadj⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2, hlt, hadj⟩
  · rintro ⟨ha, hb, hlt, hadj⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hlt, hadj⟩

theorem cells_disjoint (S : Finset X) :
    Pairwise (fun i j : cells S => Disjoint (Ioc i.val.1 i.val.2) (Ioc j.val.1 j.val.2)) := by
  intro i j hij
  rcases mem_cells.mp i.property with ⟨hi1, hi2, hi, hia⟩
  rcases mem_cells.mp j.property with ⟨hj1, hj2, hj, hja⟩
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hlow : i.val.1 = j.val.1 := by
    rcases lt_trichotomy i.val.1 j.val.1 with h | h | h
    · exact False.elim (hia _ hj1 ⟨h, hxj.1.trans_le hxi.2⟩)
    · exact h
    · exact False.elim (hja _ hi1 ⟨h, hxi.1.trans_le hxj.2⟩)
  have hupp : i.val.2 = j.val.2 := by
    rcases lt_trichotomy i.val.2 j.val.2 with h | h | h
    · exact False.elim (hja _ hi2 ⟨by rw [← hlow]; exact hi, h⟩)
    · exact h
    · exact False.elim (hia _ hj2 ⟨by rw [hlow]; exact hj, h⟩)
  exact hij (Subtype.ext (Prod.ext hlow hupp))

/-- Every point between two endpoints belongs to a unique adjacent cell,
and that cell is contained between the same two endpoints. -/
theorem exists_cell {S : Finset X} {a b x : X} (ha : a ∈ S) (hb : b ∈ S)
    (hx : x ∈ Ioc a b) :
    ∃ p ∈ cells S, a ≤ p.1 ∧ p.2 ≤ b ∧ x ∈ Ioc p.1 p.2 := by
  let L := S.filter (fun c => c < x)
  let U := S.filter (fun c => x ≤ c)
  have hL : L.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hx.1⟩⟩
  have hU : U.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hx.2⟩⟩
  let l := L.max' hL
  let u := U.min' hU
  have hlmem := Finset.mem_filter.mp (Finset.max'_mem L hL)
  have humem := Finset.mem_filter.mp (Finset.min'_mem U hU)
  have hax : a ≤ l := Finset.le_max' L a (Finset.mem_filter.mpr ⟨ha, hx.1⟩)
  have hxb : u ≤ b := Finset.min'_le U b (Finset.mem_filter.mpr ⟨hb, hx.2⟩)
  refine ⟨(l,u), mem_cells.mpr ⟨hlmem.1, humem.1, hlmem.2.trans_le humem.2, ?_⟩,
    hax, hxb, hlmem.2, humem.2⟩
  intro c hc hbetween
  by_cases hcx : c < x
  · exact (not_lt_of_ge (Finset.le_max' L c (Finset.mem_filter.mpr ⟨hc, hcx⟩))) hbetween.1
  · exact (not_lt_of_ge (Finset.min'_le U c
      (Finset.mem_filter.mpr ⟨hc, le_of_not_gt hcx⟩))) hbetween.2

def row (S : Finset X) (a b : X) : Finset (cells S) :=
  Finset.univ.filter (fun p => a ≤ p.val.1 ∧ p.val.2 ≤ b)

theorem interval_eq_union {S : Finset X} {a b : X} (ha : a ∈ S) (hb : b ∈ S) :
    Ioc a b = ⋃ p ∈ row S a b, Ioc p.val.1 p.val.2 := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hap, hpb, hxp⟩ := exists_cell ha hb hx
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hap, hpb⟩, hxp⟩⟩
  · intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    obtain ⟨hp, hxp⟩ := mem_iUnion.mp hp
    have hbounds := (Finset.mem_filter.mp hp).2
    exact ⟨hbounds.1.trans_lt hxp.1, hxp.2.trans hbounds.2⟩

/-- Natural point counts add over the disjoint adjacent cells. -/
theorem countOn_interval_eq_sum (ξ : LocallyFinitePointMeasure)
    {S : Finset ExtremeState} {a b : ExtremeState} (ha : a ∈ S) (hb : b ∈ S) :
    ξ.countOn (Ioc a b) = ∑ p ∈ row S a b, ξ.countOn (Ioc p.val.1 p.val.2) := by
  have hcast (u v : ExtremeState) : (ξ.countOn (Ioc u v) : ℝ≥0∞) = ξ.toMeasure (Ioc u v) :=
    ξ.countOn_interval_eq_measure u.val v.val u.property
  apply Nat.cast_injective (R := ℝ≥0∞)
  push_cast
  rw [hcast]
  simp_rw [hcast]
  rw [interval_eq_union ha hb]
  exact measure_biUnion_finset (fun i _ j _ hij => cells_disjoint S hij)
    (fun _ _ => measurableSet_Ioc)

/-- Every finite family of intervals has a common finite strict disjoint
refinement, with an exact row-sum formula for every point measure. -/
theorem exists_count_refinement {J : Type*} [Fintype J] (a b : J → ExtremeState) :
    ∃ k : ℕ, ∃ l u : Fin k → ExtremeState, ∃ R : J → Finset (Fin k),
      (∀ i, l i < u i) ∧
      Pairwise (fun i j => Disjoint (Ioc (l i) (u i)) (Ioc (l j) (u j))) ∧
      ∀ (ξ : LocallyFinitePointMeasure) j,
        ξ.countOn (Ioc (a j) (b j)) = ∑ i ∈ R j, ξ.countOn (Ioc (l i) (u i)) := by
  let S : Finset ExtremeState := Finset.univ.image a ∪ Finset.univ.image b
  let e : cells S ≃ Fin (Fintype.card (cells S)) := Fintype.equivFin (cells S)
  let l : Fin (Fintype.card (cells S)) → ExtremeState := fun i => (e.symm i).val.1
  let u : Fin (Fintype.card (cells S)) → ExtremeState := fun i => (e.symm i).val.2
  let R : J → Finset (Fin (Fintype.card (cells S))) :=
    fun j => (row S (a j) (b j)).map e.toEmbedding
  refine ⟨_, l, u, R, fun i => (mem_cells.mp (e.symm i).property).2.2.1, ?_, ?_⟩
  · intro i j hij
    exact cells_disjoint S (fun he => hij (e.symm.injective he))
  · intro ξ j
    have haj : a j ∈ S := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    have hbj : b j ∈ S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    rw [countOn_interval_eq_sum ξ haj hbj]
    simp only [R, Finset.sum_map, l, u, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

end
end ConditionedStableLaws.IntervalRefinement

namespace ConditionedStableLaws
open Filter
open scoped Topology

/-- Random point-measure criterion: joint convergence on every finite disjoint family of strict
positive half-open intervals implies weak convergence for the vague topology. No boundary
atomlessness condition is needed. -/
theorem kallenberg_random_point_measures
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (N : (n : ℕ) → RandomPointMeasure (Ω n)) (Nlimit : RandomPointMeasure Ω')
    (hcounts : ∀ (k : ℕ) (a b : Fin k → ExtremeState),
      (∀ i, a i < b i) →
      Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      TendstoInDistribution
        (fun n ω => fun j => ((N n).toFun ω).countOn (Ioc (a j) (b j))) atTop
        (fun ω => fun j => (Nlimit.toFun ω).countOn (Ioc (a j) (b j))) P Q) :
    TendstoInDistribution (fun n => (N n).toFun) atTop Nlimit.toFun P Q := by
  apply randomPointMeasure_tendsto_of_all_joint_intervals P Q N Nlimit
  intro k a b
  obtain ⟨m, l, u, R, hstrict, hdisjoint, hsum⟩ := IntervalRefinement.exists_count_refinement a b
  have ht := (hcounts m l u hstrict hdisjoint).continuous_comp
    (g := fun v : Fin m → ℕ => fun j : Fin k => ∑ i ∈ R j, v i) (by fun_prop)
  simpa only [Function.comp_def, ← hsum] using ht

end ConditionedStableLaws
