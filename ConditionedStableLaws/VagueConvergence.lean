import ConditionedStableLaws.VagueEvaluation
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Interval-count criteria for deterministic vague convergence

The proof restricts locally finite measures to a positive tail, proves weak
convergence of these finite restrictions by a pi-system criterion, and tests
against continuous compactly supported functions.
-/

open Filter MeasureTheory Set Classical
open scoped Topology NNReal ENNReal CompactlySupported

namespace ConditionedStableLaws
noncomputable section

/-- A finite-measure version of the pi-system weak-convergence criterion.
The total masses are allowed to converge to zero. -/
theorem finiteMeasure_tendsto_of_piSystem
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [SecondCountableTopology E]
    [OpensMeasurableSpace E] [Nonempty E]
    {S : Set (Set E)} (hS : IsPiSystem S)
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (hbasis : ∀ u : Set E, IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hmass : Tendsto (fun n => (μ n).mass) atTop (𝓝 ν.mass))
    (hsets : ∀ s ∈ S, Tendsto (fun n => (μ n) s) atTop (𝓝 (ν s))) :
    Tendsto μ atTop (𝓝 ν) := by
  by_cases hν : ν = 0
  · subst ν
    exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass (by simpa using hmass)
  apply (FiniteMeasure.tendsto_normalize_iff_tendsto hν).mp
  refine ⟨hS.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hbasis ?_, hmass⟩
  intro s hs
  have hmass0 : ν.mass ≠ 0 := (ν.mass_nonzero_iff).mpr hν
  have hevent : ∀ᶠ n in atTop, (μ n).mass ≠ 0 :=
    hmass.eventually_ne hmass0
  have ht := (hmass.inv₀ hmass0).mul (hsets s hs)
  rw [← ν.normalize_eq_of_nonzero hν s] at ht
  apply ht.congr'
  filter_upwards [hevent] with n hn
  exact ((μ n).normalize_eq_of_nonzero (((μ n).mass_nonzero_iff).mp hn) s).symm

instance extremeState_orderTopology : OrderTopology ExtremeState :=
  inferInstanceAs (OrderTopology (Set.Ioi (0 : ℝ≥0∞)))

instance extremeState_noMin : NoMinOrder ExtremeState :=
  inferInstanceAs (NoMinOrder (Set.Ioi (0 : ℝ≥0∞)))

instance extremeState_denselyOrdered : DenselyOrdered ExtremeState :=
  inferInstanceAs (DenselyOrdered (Set.Ioi (0 : ℝ≥0∞)))

instance extremeState_orderTop : OrderTop ExtremeState where
  top := ⟨∞, by simp⟩
  le_top x := le_top (a := x.val)

/-- Half-open intervals with endpoints in a prescribed set. -/
def extremeIntervals (D : Set ExtremeState) : Set (Set ExtremeState) :=
  {s | ∃ a ∈ D, ∃ b ∈ D, s = Ioc a b}

theorem extremeIntervals_isPiSystem (D : Set ExtremeState) : IsPiSystem (extremeIntervals D) := by
  rintro s ⟨a, ha, b, hb, rfl⟩ t ⟨c, hc, d, hd, rfl⟩ _
  refine ⟨max a c, ?_, min b d, ?_, Ioc_inter_Ioc⟩
  · exact (max_choice a c).elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hc)
  · exact (min_choice b d).elim (fun h => h.symm ▸ hb) (fun h => h.symm ▸ hd)

theorem extremeIntervals_measurable (D : Set ExtremeState) :
    ∀ s ∈ extremeIntervals D, MeasurableSet s := by
  rintro s ⟨a, _, b, _, rfl⟩
  exact measurableSet_Ioc

/-- The full family of half-open intervals on `(0, ∞]`, including the empty interval through equal
endpoints. -/
def dissectingExtremeIntervals : Set (Set ExtremeState) :=
  {s | ∃ a b : ExtremeState, a ≤ b ∧ s = Ioc a b}

/-- Half-open intervals form a semiring of sets. -/
theorem dissectingExtremeIntervals_isSetSemiring :
    IsSetSemiring dissectingExtremeIntervals :=
  IsSetSemiring.Ioc

/-- Every set in the interval semiring is measurable. -/
theorem dissectingExtremeIntervals_measurable :
    ∀ s ∈ dissectingExtremeIntervals, MeasurableSet s := by
  rintro s ⟨a, b, _, rfl⟩
  exact measurableSet_Ioc

/-- Dense endpoints, including infinity, give arbitrarily small interval
neighborhoods of every point of `(0,∞]`. -/
theorem extremeIntervals_nhds {D : Set ExtremeState} (hD : Dense D) (htop : ⊤ ∈ D) :
    ∀ u : Set ExtremeState, IsOpen u → ∀ x ∈ u,
      ∃ s ∈ extremeIntervals D, s ∈ 𝓝 x ∧ s ⊆ u := by
  intro u hu x hxu
  obtain ⟨l, hlx, hlu⟩ := exists_Ioc_subset_of_mem_nhds (hu.mem_nhds hxu) (exists_lt x)
  obtain ⟨a, haD, hla, hax⟩ := hD.exists_between hlx
  by_cases hx : x = ⊤
  · subst x
    refine ⟨Ioc a ⊤, ⟨a, haD, ⊤, htop, rfl⟩, ?_, ?_⟩
    · simpa only [Ioc_top] using Ioi_mem_nhds hax
    · exact (Ioc_subset_Ioc_left hla.le).trans hlu
  · obtain ⟨r, hxr, hru⟩ := exists_Ico_subset_of_mem_nhds (hu.mem_nhds hxu)
      ⟨⊤, lt_top_iff_ne_top.mpr hx⟩
    obtain ⟨b, hbD, hxb, hbr⟩ := hD.exists_between hxr
    refine ⟨Ioc a b, ⟨a, haD, b, hbD, rfl⟩, Ioc_mem_nhds hax hxb, ?_⟩
    intro y hy
    by_cases hyx : y ≤ x
    · exact hlu ⟨hla.trans hy.1, hyx⟩
    · exact hru ⟨(lt_of_not_ge hyx).le, hy.2.trans_lt hbr⟩

/-- The interval semiring dissects the topology: every open neighborhood
contains a member of the semiring that is still a neighborhood of the point. -/
theorem dissectingExtremeIntervals_nhds :
    ∀ u : Set ExtremeState, IsOpen u → ∀ x ∈ u,
      ∃ s ∈ dissectingExtremeIntervals, s ∈ 𝓝 x ∧ s ⊆ u := by
  intro u hu x hx
  obtain ⟨s, ⟨a, _, b, _, rfl⟩, hs, hsu⟩ :=
    extremeIntervals_nhds (D := (Set.univ : Set ExtremeState)) dense_univ (mem_univ ⊤)
      u hu x hx
  have hxab : x ∈ Ioc a b := mem_of_mem_nhds hs
  exact ⟨Ioc a b, ⟨a, b, (le_of_lt hxab.1).trans hxab.2, rfl⟩, hs, hsu⟩

namespace LocallyFinitePointMeasure

/-- Restriction to a positive open tail is a finite measure. -/
def tailRestriction (ξ : LocallyFinitePointMeasure) (a : ExtremeState) :
    FiniteMeasure ExtremeState :=
  ⟨ξ.toMeasure.restrict (Ioi a), ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    change ξ.toMeasure {x : ExtremeState | a.val < x.val} < ∞
    simpa only [and_true, le_top] using
      ξ.measure_interval_lt_top a.val ∞ a.property⟩⟩

@[simp]
theorem tailRestriction_mass (ξ : LocallyFinitePointMeasure) (a : ExtremeState) :
    ((ξ.tailRestriction a).mass : ℝ) = ξ.toMeasure.real (Ioi a) := by
  rw [FiniteMeasure.mass, ← FiniteMeasure.measureReal_eq_coe_coeFn]
  change (ξ.toMeasure.restrict (Ioi a)).real univ = _
  exact measureReal_restrict_apply_univ _

theorem tailRestriction_apply (ξ : LocallyFinitePointMeasure) (a : ExtremeState)
    {A : Set ExtremeState} (hA : MeasurableSet A) :
    ((ξ.tailRestriction a) A : ℝ) = ξ.toMeasure.real (A ∩ Ioi a) := by
  rw [← FiniteMeasure.measureReal_eq_coe_coeFn]
  change (ξ.toMeasure.restrict (Ioi a)).real A = _
  exact measureReal_restrict_apply hA

/-- Convergence on a dense family of interval endpoints gives weak convergence
of the finite restrictions to any selected positive tail. -/
theorem tailRestriction_tendsto_of_intervals
    {ξ : ℕ → LocallyFinitePointMeasure} {ζ : LocallyFinitePointMeasure}
    {D : Set ExtremeState} (hD : Dense D) (htop : ⊤ ∈ D)
    (hcounts : ∀ a ∈ D, ∀ b ∈ D,
      Tendsto (fun n => (ξ n).toMeasure.real (Ioc a b)) atTop
        (𝓝 (ζ.toMeasure.real (Ioc a b))))
    {a : ExtremeState} (ha : a ∈ D) :
    Tendsto (fun n => (ξ n).tailRestriction a) atTop (𝓝 (ζ.tailRestriction a)) := by
  apply finiteMeasure_tendsto_of_piSystem (extremeIntervals_isPiSystem D)
    (extremeIntervals_measurable D) (extremeIntervals_nhds hD htop)
  · apply NNReal.tendsto_coe.mp
    simpa only [tailRestriction_mass, Ioc_top] using hcounts a ha ⊤ htop
  · rintro A ⟨c, hc, b, hb, rfl⟩
    apply NNReal.tendsto_coe.mp
    simp only [tailRestriction_apply _ _ measurableSet_Ioc]
    have hinter : Ioc c b ∩ Ioi a = Ioc (max a c) b := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
      tauto
    rw [hinter]
    apply hcounts (max a c) _ b hb
    exact (max_choice a c).elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hc)

/-- A compactly supported test function vanishes below some endpoint from any
dense set. This also covers the identically zero function. -/
theorem exists_tail_containing_tsupport (f : C_c(ExtremeState, ℝ))
    {D : Set ExtremeState} (hD : Dense D) :
    ∃ a ∈ D, tsupport f ⊆ Ioi a := by
  by_cases hs : (tsupport f).Nonempty
  · obtain ⟨x, hx⟩ := f.hasCompactSupport.exists_isLeast hs
    obtain ⟨a, ha, hax⟩ := hD.exists_lt x
    exact ⟨a, ha, fun y hy => hax.trans_le (hx.2 hy)⟩
  · obtain ⟨a, ha⟩ := hD.nonempty
    exact ⟨a, ha, (not_nonempty_iff_eq_empty.mp hs) ▸ empty_subset _⟩

/-- Deterministic vague convergence follows from convergence of interval counts
on any dense set of endpoints containing infinity. The endpoint set can be
chosen to avoid the atoms of the limiting measure. -/
theorem tendsto_vague_of_interval_counts
    {ξ : ℕ → LocallyFinitePointMeasure} {ζ : LocallyFinitePointMeasure}
    {D : Set ExtremeState} (hD : Dense D) (htop : ⊤ ∈ D)
    (hcounts : ∀ a ∈ D, ∀ b ∈ D,
      Tendsto (fun n => (ξ n).toMeasure.real (Ioc a b)) atTop
        (𝓝 (ζ.toMeasure.real (Ioc a b)))) :
    Tendsto ξ atTop (𝓝 ζ) := by
  rw [tendsto_iff_test_integrals]
  intro f
  obtain ⟨a, ha, hsupport⟩ := exists_tail_containing_tsupport f hD
  have ht := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tailRestriction_tendsto_of_intervals hD htop hcounts ha) f.toBoundedContinuousFunction
  have heq (ρ : LocallyFinitePointMeasure) :
      (∫ x, f x ∂(ρ.tailRestriction a : Measure ExtremeState)) = ∫ x, f x ∂ρ.toMeasure := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsupport hx'))
  change Tendsto (fun n => ∫ x, f x ∂( (ξ n).tailRestriction a : Measure ExtremeState)) atTop
    (𝓝 (∫ x, f x ∂(ζ.tailRestriction a : Measure ExtremeState))) at ht
  simpa only [heq] using ht

/-- The points that are not atoms of a locally finite point measure form a
dense subset of `(0,∞]`. -/
theorem dense_nonatoms (ζ : LocallyFinitePointMeasure) :
    Dense {x : ExtremeState | ζ.toMeasure {x} = 0} := by
  have hcount : Set.Countable {x : ExtremeState | ζ.toMeasure {x} ≠ 0} := by
    simpa only [id_eq, Set.ofPred_eq_eq_singleton, pos_iff_ne_zero] using
      (Measure.countable_meas_level_set_pos (μ := ζ.toMeasure) measurable_id)
  have hsingle (x : ExtremeState) : Dense ({x}ᶜ : Set ExtremeState) := by
    have : NeBot (𝓝[≠] x) := (nhdsLT_neBot x).mono (nhdsLT_le_nhdsNE x)
    exact dense_compl_singleton x
  have h := dense_biInter_of_isOpen (S := {x : ExtremeState | ζ.toMeasure {x} ≠ 0})
    (f := fun x => ({x}ᶜ : Set ExtremeState)) (fun x _ => isOpen_compl_singleton)
    hcount (fun x _ => hsingle x)
  convert h using 1
  ext x
  simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, mem_singleton_iff]
  constructor
  · intro hx y hy hxy
    subst y
    exact hy hx
  · intro hx
    by_contra hx'
    exact hx x hx' rfl

/-- It suffices to check intervals whose finite endpoints avoid the atoms of
the limit. Infinity is allowed as an upper endpoint even when it is an atom. -/
theorem tendsto_vague_of_nonatom_interval_counts
    {ξ : ℕ → LocallyFinitePointMeasure} {ζ : LocallyFinitePointMeasure}
    (hcounts : ∀ a b : ExtremeState, a < b → ζ.toMeasure {a} = 0 →
      (b = ⊤ ∨ ζ.toMeasure {b} = 0) →
      Tendsto (fun n => (ξ n).toMeasure.real (Ioc a b)) atTop
        (𝓝 (ζ.toMeasure.real (Ioc a b)))) :
    Tendsto ξ atTop (𝓝 ζ) := by
  let D : Set ExtremeState := {x | ζ.toMeasure {x} = 0} ∪ {⊤}
  apply tendsto_vague_of_interval_counts
    ((ζ.dense_nonatoms).mono (show {x | ζ.toMeasure {x} = 0} ⊆ D from subset_union_left))
    (show ⊤ ∈ D from Or.inr rfl)
  intro a ha b hb
  by_cases hab : a < b
  · have ha0 : ζ.toMeasure {a} = 0 := by
      rcases ha with ha | ha
      · exact ha
      · have ha' : a = ⊤ := ha
        exact False.elim ((not_lt_of_ge le_top) (ha' ▸ hab))
    exact hcounts a b hab ha0 (hb.elim Or.inr (fun hb => Or.inl hb))
  · have hempty : Ioc a b = ∅ := Ioc_eq_empty_of_le (le_of_not_gt hab)
    simp only [hempty, measureReal_empty]
    exact tendsto_const_nhds

end LocallyFinitePointMeasure
end
end ConditionedStableLaws
