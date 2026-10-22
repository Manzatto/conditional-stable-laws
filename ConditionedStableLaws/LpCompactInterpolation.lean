import ConditionedStableLaws.LpMidpointInterpolation
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Compact interpolation at the L1/L-infinity midpoint

A special case of the Bennett–Sharpley compact interpolation theorem. On a finite measure space,
compatible bounded operators on `L1`, `L2`, and `L∞` have compact `L2` realization whenever their
`L∞` realization is compact. The proof uses finite conditional expectations. A finite family of
simple functions determines a finite sigma-algebra; conditional expectation onto it has
finite-dimensional range on `L2`. The compact image of the `L∞` unit ball is uniformly approximated
by such simple functions, and the midpoint interpolation estimate controls the remaining `L2`
operator norm.
-/

open scoped ENNReal Topology

open Filter Set

namespace ConditionedStableLaws
namespace LpCompactInterpolation

open MeasureTheory
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Type u} [m0 : MeasurableSpace X] {μ : Measure X}

/-! ## Uniform approximation by simple functions -/

/-- A measurable function whose range is contained in a compact set admits a uniform simple-function
approximation.  This elementary lemma is useful at the `L∞` endpoint. -/
theorem exists_simpleFunc_uniform_approx {f : X → ℝ} (hf : Measurable f) {K : Set ℝ}
    (hK : IsCompact K) (h_range : range f ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : SimpleFunc X ℝ, ∀ x, dist (s x) (f x) < ε := by
  have H : ∀ L : Set ℝ, IsCompact L →
      ∃ (s : SimpleFunc X ℝ) (U : Set ℝ), MeasurableSet U ∧ L ⊆ U ∧
        ∀ x, f x ∈ U → dist (s x) (f x) < ε := by
    intro L hL
    refine IsCompact.induction_on (p := fun A ↦
      ∃ (s : SimpleFunc X ℝ) (U : Set ℝ), MeasurableSet U ∧ A ⊆ U ∧
        ∀ x, f x ∈ U → dist (s x) (f x) < ε) hL ?_ ?_ ?_ ?_
    · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
    · intro A B hAB
      rintro ⟨s, U, hU, hAU, hs⟩
      exact ⟨s, U, hU, hAB.trans hAU, hs⟩
    · rintro A B ⟨s, U, hU, hAU, hs⟩ ⟨t, V, hV, hBV, ht⟩
      let W : Set X := f ⁻¹' U
      refine ⟨s.piecewise W (hf hU) t, U ∪ V, hU.union hV,
        union_subset_union hAU hBV, ?_⟩
      intro x hx
      by_cases hxf : f x ∈ U
      · simpa [W, SimpleFunc.piecewise_apply, hxf] using hs x hxf
      · have hxV : f x ∈ V := (mem_union _ _ _).1 hx |>.resolve_left hxf
        simpa [W, SimpleFunc.piecewise_apply, hxf] using ht x hxV
    · intro y hy
      refine ⟨Metric.ball y ε, ?_, SimpleFunc.const X y, Metric.ball y ε,
        Metric.isOpen_ball.measurableSet, Subset.rfl, ?_⟩
      · exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds y hε)
      · intro x hx
        simpa [SimpleFunc.const_apply, dist_comm] using hx
  obtain ⟨s, U, hU, hKU, hs⟩ := H K hK
  exact ⟨s, fun x ↦ hs x (hKU (h_range ⟨x, rfl⟩))⟩

/-! ## A common simple-function refinement -/

/-- Combine a finite family of simple functions into one vector-valued simple function. -/
noncomputable def SimpleFunc.pi {ι : Type*} [Fintype ι]
    (s : ι → SimpleFunc X ℝ) : SimpleFunc X (ι → ℝ) where
  toFun x i := s i x
  finite_range' := by
    refine (Set.Finite.pi (fun i ↦ (s i).finite_range)).subset ?_
    rintro _ ⟨x, rfl⟩ i -
    exact ⟨x, rfl⟩
  measurableSet_fiber' y := by
    have hset : {x | (fun i ↦ s i x) = y} = ⋂ i, s i ⁻¹' {y i} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_singleton_iff]
      exact funext_iff
    change MeasurableSet {x | (fun i ↦ s i x) = y}
    rw [hset]
    exact MeasurableSet.iInter fun i ↦ (s i).measurableSet_fiber _

@[simp]
theorem SimpleFunc.pi_apply {ι : Type*} [Fintype ι] (s : ι → SimpleFunc X ℝ)
    (x : X) (i : ι) : SimpleFunc.pi s x i = s i x := rfl

/-! ## Conditional expectation on `Lp` -/

/-- The value of conditional expectation in `Lp`. -/
noncomputable def condExpLpValue (subm : MeasurableSpace X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [IsFiniteMeasure μ] (f : Lp ℝ p μ) : Lp ℝ p μ :=
  ((Lp.memLp f).condExp (Fact.out : 1 ≤ p)).toLp μ[(f : X → ℝ) | subm]

theorem condExpLpValue_coe_ae (subm : MeasurableSpace X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [IsFiniteMeasure μ] (f : Lp ℝ p μ) :
    ((condExpLpValue (m0 := m0) (μ := μ) subm p f : Lp ℝ p μ) : X → ℝ) =ᵐ[μ]
      μ[(f : X → ℝ) | subm] :=
  MemLp.coeFn_toLp _

/-- Conditional expectation as a contraction of `Lp`, simultaneously for all `1 ≤ p` on a
finite measure space.  Defining all exponents from the same raw conditional expectation makes
compatibility automatic. -/
noncomputable def condExpLp (subm : MeasurableSpace X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [IsFiniteMeasure μ] : Lp ℝ p μ →L[ℝ] Lp ℝ p μ :=
  LinearMap.mkContinuous
    { toFun := condExpLpValue (m0 := m0) (μ := μ) subm p
      map_add' := by
        intro f g
        apply Lp.ext
        refine (condExpLpValue_coe_ae (m0 := m0) subm p (f + g)).trans ?_
        refine (condExp_congr_ae (Lp.coeFn_add f g)).trans ?_
        refine (condExp_add ((Lp.memLp f).integrable Fact.out)
          ((Lp.memLp g).integrable Fact.out) subm).trans ?_
        exact (((condExpLpValue_coe_ae (m0 := m0) subm p f).add
          (condExpLpValue_coe_ae (m0 := m0) subm p g)).symm).trans
            (Lp.coeFn_add _ _).symm
      map_smul' := by
        intro c f
        apply Lp.ext
        refine (condExpLpValue_coe_ae (m0 := m0) subm p (c • f)).trans ?_
        refine (condExp_congr_ae (Lp.coeFn_smul c f)).trans ?_
        refine (condExp_smul c (f : X → ℝ) subm).trans ?_
        exact (((condExpLpValue_coe_ae (m0 := m0) subm p f).const_smul c).symm).trans
          (Lp.coeFn_smul c _).symm }
    1 (by
      intro f
      change ‖condExpLpValue (m0 := m0) (μ := μ) subm p f‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_def, Lp.norm_def,
        eLpNorm_congr_ae (condExpLpValue_coe_ae (m0 := m0) subm p f)]
      simpa [lpNorm] using
        (Lp.memLp f).lpNorm_condExp_le_lpNorm (m := subm) (Fact.out : 1 ≤ p))

theorem condExpLp_coe_ae (subm : MeasurableSpace X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [IsFiniteMeasure μ] (f : Lp ℝ p μ) :
    ((condExpLp (m0 := m0) (μ := μ) subm p f : Lp ℝ p μ) : X → ℝ) =ᵐ[μ]
      μ[(f : X → ℝ) | subm] :=
  condExpLpValue_coe_ae (m0 := m0) subm p f

theorem norm_condExpLp_le_one (subm : MeasurableSpace X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [IsFiniteMeasure μ] : ‖condExpLp (m0 := m0) (μ := μ) subm p‖ ≤ 1 :=
  by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖condExpLpValue (m0 := m0) (μ := μ) subm p f‖ ≤ 1 * ‖f‖
    rw [one_mul, Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (condExpLpValue_coe_ae (m0 := m0) subm p f)]
    simpa [lpNorm] using
      (Lp.memLp f).lpNorm_condExp_le_lpNorm (m := subm) (Fact.out : 1 ≤ p)

/-- Conditional expectations defined above are compatible at any two exponents. -/
theorem condExpLp_compatible (subm : MeasurableSpace X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [IsFiniteMeasure μ] :
    @Cited.LpCompatible X X m0 m0 p p q q μ μ inferInstance inferInstance
      inferInstance inferInstance (condExpLp (m0 := m0) (μ := μ) subm p)
        (condExpLp (m0 := m0) (μ := μ) subm q) := by
  intro f g hfg
  exact (condExpLp_coe_ae (m0 := m0) subm p f).trans <|
    (condExp_congr_ae hfg).trans (condExpLp_coe_ae (m0 := m0) subm q g).symm

/-! ## Finite-dimensional conditional expectations -/

private noncomputable def simpleAtomLp {β : Type*} [IsFiniteMeasure μ]
    (s : SimpleFunc X β) (a : β) :
    Lp ℝ 2 μ :=
  indicatorConstLp 2 (s.measurableSet_fiber a) (measure_ne_top μ _) 1

private theorem simpleAtomLp_coe_ae {β : Type*} [IsFiniteMeasure μ]
    (s : SimpleFunc X β) (a : β) :
    ((simpleAtomLp (μ := μ) s a : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
      (s ⁻¹' {a}).indicator (fun _ ↦ 1) :=
  indicatorConstLp_coeFn

/-- The `L2` functions measurable with respect to the sigma-algebra generated by a simple
function form a finite-dimensional space. -/
theorem finiteDimensional_lpMeas_comap_simpleFunc {β : Type*} (s : SimpleFunc X β)
    [IsFiniteMeasure μ] :
    FiniteDimensional ℝ (lpMeas ℝ ℝ (MeasurableSpace.comap s ⊤) 2 μ) := by
  classical
  let : MeasurableSpace β := ⊤
  let atoms : Finset (Lp ℝ 2 μ) := s.range.image (simpleAtomLp (μ := μ) s)
  let V : Submodule ℝ (Lp ℝ 2 μ) := Submodule.span ℝ (atoms : Set (Lp ℝ 2 μ))
  have hV : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ atoms.finite_toSet
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  intro f hf
  have hmeas : AEStronglyMeasurable[MeasurableSpace.comap s ⊤]
      (f : X → ℝ) μ := mem_lpMeas_iff_aestronglyMeasurable.mp hf
  let g : X → ℝ := hmeas.mk f
  have hg : StronglyMeasurable[MeasurableSpace.comap s ⊤] g :=
    hmeas.stronglyMeasurable_mk
  obtain ⟨c, hc⟩ := (Function.factorsThrough_iff g).mp hg.factorsThrough
  have hfg : (f : X → ℝ) =ᵐ[μ] c ∘ s := hmeas.ae_eq_mk.trans <|
    Eventually.of_forall fun x ↦ congrFun hc x
  have hmem : MemLp (c ∘ s) 2 μ := (Lp.memLp f).ae_eq hfg
  have heq : f = ∑ a ∈ s.range, c a • simpleAtomLp (μ := μ) s a := by
    apply Lp.ext
    refine hfg.trans ?_
    have hatoms : ∀ᵐ x ∂μ, ∀ a ∈ s.range,
        (simpleAtomLp (μ := μ) s a : X → ℝ) x =
          (s ⁻¹' {a}).indicator (fun _ ↦ 1) x := by
      exact s.range.eventually_all.mpr fun a _ ↦ simpleAtomLp_coe_ae s a
    have hsum := Lp.coeFn_finsetSum s.range
      (fun a ↦ c a • simpleAtomLp (μ := μ) s a)
    have hsmuls : ∀ᵐ x ∂μ, ∀ a ∈ s.range,
        ((c a • simpleAtomLp (μ := μ) s a : Lp ℝ 2 μ) : X → ℝ) x =
          c a • (simpleAtomLp (μ := μ) s a : X → ℝ) x := by
      exact s.range.eventually_all.mpr fun a _ ↦ Lp.coeFn_smul _ _
    filter_upwards [hatoms, hsum, hsmuls] with x hx hsumx hsmulx
    rw [hsumx]
    simp only [Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun a ha ↦ hsmulx a ha)]
    rw [Finset.sum_congr rfl (fun a ha ↦ congrArg (c a • ·) (hx a ha))]
    simp only [smul_eq_mul, Set.indicator_apply, mem_preimage, mem_singleton_iff]
    rw [Finset.sum_eq_single (s x)]
    · simp [Function.comp_apply]
    · intro b hb hne
      rw [ite_eq_right_iff.mpr (fun h ↦ (hne h.symm).elim), mul_zero]
    · exact fun hnot ↦ (hnot (s.mem_range_self x)).elim
  rw [heq]
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- Conditional expectation onto the sigma-algebra generated by a simple function is compact on
`L2`: its range lies in the finite-dimensional measurable subspace above. -/
theorem isCompactOperator_condExpLp_two {β : Type*} (s : SimpleFunc X β)
    [IsFiniteMeasure μ] :
    IsCompactOperator (condExpLp (m0 := m0) (μ := μ)
      (MeasurableSpace.comap s ⊤) 2) := by
  classical
  let : MeasurableSpace β := ⊤
  let W : Submodule ℝ (Lp ℝ 2 μ) :=
    lpMeas ℝ ℝ (MeasurableSpace.comap s ⊤) 2 μ
  have hmem : ∀ f, condExpLp (m0 := m0) (μ := μ)
      (MeasurableSpace.comap s ⊤) 2 f ∈ W := by
    intro f
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    exact stronglyMeasurable_condExp.aestronglyMeasurable.congr
      (condExpLp_coe_ae (m0 := m0) (MeasurableSpace.comap s ⊤) 2 f).symm
  let QW : Lp ℝ 2 μ →L[ℝ] W :=
    (condExpLp (m0 := m0) (μ := μ) (MeasurableSpace.comap s ⊤) 2).codRestrict W hmem
  let : FiniteDimensional ℝ W := finiteDimensional_lpMeas_comap_simpleFunc s
  have hQW : IsCompactOperator QW := isCompactOperator_of_locallyCompactSpace_dom QW
  have hcomp := hQW.clm_comp W.subtypeL
  simpa [QW, W, Function.comp_def] using hcomp

/-! ## Uniform simple approximation in `L∞` -/

/-- Every real `L∞` function has a simple representative arbitrarily close in the `L∞` norm. -/
theorem exists_simpleFunc_toLp_top_norm_sub_lt [IsFiniteMeasure μ]
    (f : Lp ℝ ∞ μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : SimpleFunc X ℝ),
      ‖f - (s.memLp_top μ).toLp s‖ < ε := by
  let hfmeas : AEStronglyMeasurable (f : X → ℝ) μ := Lp.aestronglyMeasurable f
  let f' : X → ℝ := hfmeas.mk f
  let A : Set X := {x | ‖f' x‖ ≤ ‖f‖}
  have hf'_meas : Measurable f' := hfmeas.stronglyMeasurable_mk.measurable
  have hA : MeasurableSet A := measurableSet_le hf'_meas.norm measurable_const
  let g : X → ℝ := A.piecewise f' 0
  have hg_meas : Measurable g := Measurable.piecewise hA hf'_meas measurable_const
  have hnorm : lpNorm (f : X → ℝ) ∞ μ = ‖f‖ := by
    simp only [lpNorm, Lp.norm_def]
  have hA_ae : ∀ᵐ x ∂μ, x ∈ A := by
    filter_upwards [hfmeas.ae_eq_mk,
      ae_le_lpNorm_exponent_top (Lp.memLp f)] with x hfx hx
    change ‖f' x‖ ≤ ‖f‖
    have hfx' : (f : X → ℝ) x = f' x := by simpa [f'] using hfx
    rw [← hfx', ← hnorm]
    exact hx
  have hfg : (f : X → ℝ) =ᵐ[μ] g := by
    filter_upwards [hfmeas.ae_eq_mk, hA_ae] with x hfx hx
    simpa [g, f', hx] using hfx
  have hg_bound : ∀ x, ‖g x‖ ≤ ‖f‖ := by
    intro x
    by_cases hx : x ∈ A
    · change ‖f' x‖ ≤ ‖f‖ at hx
      change ‖A.piecewise f' 0 x‖ ≤ ‖f‖
      rw [Set.piecewise_eq_of_mem A f' 0 hx]
      exact hx
    · change ‖A.piecewise f' 0 x‖ ≤ ‖f‖
      rw [Set.piecewise_eq_of_notMem A f' 0 hx]
      simp
  have hg_range : range g ⊆ Metric.closedBall 0 ‖f‖ := by
    rintro _ ⟨x, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hg_bound x
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨s, hs⟩ := exists_simpleFunc_uniform_approx hg_meas
    (isCompact_closedBall 0 ‖f‖) hg_range hε2
  refine ⟨s, ?_⟩
  have hs_coe := MemLp.coeFn_toLp (s.memLp_top μ)
  have hsub := Lp.coeFn_sub f ((s.memLp_top μ).toLp s)
  have hpoint : ∀ᵐ x ∂μ,
      ‖((f - (s.memLp_top μ).toLp s : Lp ℝ ∞ μ) : X → ℝ) x‖ ≤ ε / 2 := by
    filter_upwards [hsub, hfg, hs_coe] with x hsubx hfgx hsx
    rw [hsubx]
    simp only [Pi.sub_apply]
    rw [hfgx, hsx]
    simpa only [dist_eq_norm, norm_sub_rev] using (hs x).le
  have hnormle : ‖f - (s.memLp_top μ).toLp s‖ ≤ ε / 2 := by
    simpa using Lp.norm_le_of_ae_bound hε2.le hpoint
  exact hnormle.trans_lt (half_lt_self hε)

/-- Conditional expectation fixes a simple function which is measurable for the smaller
sigma-algebra. -/
theorem condExpLp_toLp_simpleFunc_eq (subm : MeasurableSpace X) (hsubm : subm ≤ m0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] [IsFiniteMeasure μ] (s : @SimpleFunc X m0 ℝ)
    (hs : StronglyMeasurable[subm] s) :
    condExpLp (m0 := m0) (μ := μ) subm p
        (((@SimpleFunc.memLp_top X ℝ m0 _ s μ).mono_exponent le_top).toLp s) =
      ((@SimpleFunc.memLp_top X ℝ m0 _ s μ).mono_exponent le_top).toLp s := by
  let hsp : MemLp s p μ :=
    (@SimpleFunc.memLp_top X ℝ m0 _ s μ).mono_exponent le_top
  apply Lp.ext
  refine (condExpLp_coe_ae (m0 := m0) subm p (hsp.toLp s)).trans ?_
  have hcond : μ[(s : X → ℝ) | subm] = (s : X → ℝ) :=
    condExp_of_stronglyMeasurable hsubm hs (hsp.integrable Fact.out)
  refine (condExp_congr_ae (MemLp.coeFn_toLp hsp)).trans ?_
  rw [hcond]
  exact (MemLp.coeFn_toLp hsp).symm

/-! ## Finite conditional expectations approximate compact sets -/

set_option maxHeartbeats 800000 in
/-- A single finite sigma-algebra approximates the identity uniformly on a compact subset of
real `L∞`. The same conditional expectation has finite-dimensional range on `L²`. -/
theorem exists_condExpLp_uniform_approx [IsFiniteMeasure μ]
    {K : Set (Lp ℝ ∞ μ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (β : Type u) (S : SimpleFunc X β),
      ∀ y ∈ K, ‖y - condExpLp (m0 := m0) (μ := μ)
        (MeasurableSpace.comap S ⊤) ∞ y‖ < ε := by
  classical
  have hr : 0 < ε / 8 := by positivity
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun y : K ↦ Metric.ball (y : Lp ℝ ∞ μ) (ε / 8))
    (fun _ ↦ Metric.isOpen_ball) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self hr⟩)
  have hs : ∀ i : t, ∃ s : SimpleFunc X ℝ,
      ‖(i.val : Lp ℝ ∞ μ) - (s.memLp_top μ).toLp s‖ < ε / 8 :=
    fun i ↦ exists_simpleFunc_toLp_top_norm_sub_lt (i.val : Lp ℝ ∞ μ) hr
  choose s hs using hs
  let E := Lp ℝ ∞ μ
  let S := SimpleFunc.pi s
  have hSmeas : @Measurable X (t → ℝ) m0 ⊤ S := by
    let : MeasurableSpace (t → ℝ) := ⊤
    exact S.measurable
  let subm := MeasurableSpace.comap S ⊤
  let Q := condExpLp (m0 := m0) (μ := μ) subm ∞
  have hsubm : subm ≤ m0 := hSmeas.comap_le
  have hfix (i : t) : Q ((@SimpleFunc.memLp_top X ℝ m0 _ (s i) μ).toLp (s i)) =
      (@SimpleFunc.memLp_top X ℝ m0 _ (s i) μ).toLp (s i) := by
    have hm : StronglyMeasurable[subm] (s i) := by
      let : MeasurableSpace (t → ℝ) := ⊤
      have hS : @Measurable X (t → ℝ) subm ⊤ S := Measurable.of_comap_le le_rfl
      have hi : @Measurable (t → ℝ) ℝ ⊤ inferInstance (fun v ↦ v i) :=
        measurable_from_top
      exact (hi.comp hS).stronglyMeasurable
    exact condExpLp_toLp_simpleFunc_eq (m0 := m0) (μ := μ) subm hsubm ∞ (s i) hm
  have hQ (z : E) : ‖Q z‖ ≤ ‖z‖ := by
    exact (Q.le_opNorm z).trans (mul_le_of_le_one_left (norm_nonneg z)
      (norm_condExpLp_le_one (m0 := m0) (μ := μ) subm ∞))
  refine ⟨t → ℝ, S, ?_⟩
  intro y hy
  obtain ⟨i, hi, hiy⟩ := mem_iUnion₂.mp (ht hy)
  let j : t := ⟨i, hi⟩
  let z := (@SimpleFunc.memLp_top X ℝ m0 _ (s j) μ).toLp (s j)
  have hyi : ‖y - (i : E)‖ < ε / 8 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hiy
  have hiz : ‖(i : E) - z‖ < ε / 8 := hs j
  have hyz : ‖y - z‖ < ε / 4 := by
    have hb : ‖y - z‖ ≤ ‖y - (i : E)‖ + ‖(i : E) - z‖ := by
      simpa only [dist_eq_norm] using dist_triangle y (i : E) z
    linarith
  change ‖y - Q y‖ < ε
  have hQz : Q z = z := hfix j
  have hb : ‖y - Q y‖ ≤ 2 * ‖y - z‖ := by
    calc
      _ ≤ ‖y - z‖ + ‖z - Q y‖ := by
        simpa only [dist_eq_norm] using dist_triangle y z (Q y)
      _ = ‖y - z‖ + ‖Q (z - y)‖ := by rw [map_sub, hQz]
      _ ≤ ‖y - z‖ + ‖z - y‖ := add_le_add le_rfl (hQ (z - y))
      _ = _ := by rw [norm_sub_rev]; ring
  linarith

/-! ## Approximation and compact interpolation of operators -/

/-- A compact operator on real `L∞` is approximated in operator norm by postcomposition with
conditional expectation onto a finite sigma-algebra. -/
theorem exists_condExpLp_comp_approx [IsFiniteMeasure μ]
    (T : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ) (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (β : Type u) (S : SimpleFunc X β),
      ‖T - (condExpLp (m0 := m0) (μ := μ) (MeasurableSpace.comap S ⊤) ∞).comp T‖ < ε := by
  obtain ⟨β, S, hS⟩ := exists_condExpLp_uniform_approx
    (hT.isCompact_closure_image_closedBall 1) (half_pos hε)
  refine ⟨β, S, ?_⟩
  apply lt_of_le_of_lt (b := ε / 2) ?_ (half_lt_self hε)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
  intro f hf
  have hmem : T f ∈ closure (T '' Metric.closedBall 0 1) :=
    subset_closure ⟨f, by simpa only [Metric.mem_closedBall, dist_zero_right, hf]
      using (le_rfl : (1 : ℝ) ≤ 1), rfl⟩
  exact (hS (T f) hmem).le

/-- On a finite measure space, compatible bounded realizations on real `L¹`, `L²`, and `L∞` have
compact `L²` realization whenever their `L∞` realization is compact. It follows from finite
conditional expectations and the midpoint norm estimate. -/
theorem midpoint_compact_interpolation [IsFiniteMeasure μ]
    (T1 : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (T2 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ttop : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ)
    (hcompat21 : Cited.LpCompatible T2 T1)
    (hcompat1top : Cited.LpCompatible T1 Ttop)
    (hTtop : IsCompactOperator Ttop) : IsCompactOperator T2 := by
  have hc : T2 ∈ closure {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ | IsCompactOperator A} := by
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    let M0 := 2 * ‖T1‖
    have hM0 : 0 ≤ M0 := by positivity
    let ε := δ ^ 2 / (16 * (M0 + 1))
    have hε : 0 < ε := by positivity
    obtain ⟨β, S, hS⟩ := exists_condExpLp_comp_approx Ttop hTtop hε
    let Q1 := condExpLp (m0 := m0) (μ := μ) (MeasurableSpace.comap S ⊤) 1
    let Q2 := condExpLp (m0 := m0) (μ := μ) (MeasurableSpace.comap S ⊤) 2
    let Qtop := condExpLp (m0 := m0) (μ := μ) (MeasurableSpace.comap S ⊤) ∞
    let E1 := T1 - Q1.comp T1
    let E2 := T2 - Q2.comp T2
    let Etop := Ttop - Qtop.comp Ttop
    have hE21 : Cited.LpCompatible E2 E1 := LpCompatibility.sub hcompat21
      (LpCompatibility.comp (condExpLp_compatible (m0 := m0) _ 2 1) hcompat21)
    have hE1top : Cited.LpCompatible E1 Etop := LpCompatibility.sub hcompat1top
      (LpCompatibility.comp (condExpLp_compatible (m0 := m0) _ 1 ∞) hcompat1top)
    have hE1 : ‖E1‖ ≤ M0 := by
      calc
        _ ≤ ‖T1‖ + ‖Q1.comp T1‖ := norm_sub_le _ _
        _ ≤ ‖T1‖ + ‖Q1‖ * ‖T1‖ := add_le_add le_rfl (Q1.opNorm_comp_le T1)
        _ ≤ ‖T1‖ + 1 * ‖T1‖ := add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (norm_condExpLp_le_one (m0 := m0) (μ := μ) (MeasurableSpace.comap S ⊤) 1)
            (norm_nonneg T1))
        _ = M0 := by dsimp [M0]; ring
    let C := Real.sqrt (4 * M0) * Real.sqrt (4 * ε)
    have hC : 0 ≤ C := by positivity
    have hb : ‖E2‖ ≤ C := by
      apply ContinuousLinearMap.opNorm_le_bound _ hC
      exact LpMidpointInterpolation.midpoint_interpolation_norm E1 E2 Etop hE21 hE1top
        hM0 hε.le
        (fun f ↦ (E1.le_opNorm f).trans (mul_le_mul_of_nonneg_right hE1 (norm_nonneg f)))
        (fun f ↦ (Etop.le_opNorm f).trans
          (mul_le_mul_of_nonneg_right hS.le (norm_nonneg f)))
    have hCδ : C < δ := by
      have he : 16 * (M0 + 1) * ε = δ ^ 2 := by
        dsimp [ε]
        field_simp
      have hsq : C ^ 2 = 16 * M0 * ε := by
        dsimp [C]
        rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        ring
      nlinarith
    refine ⟨Q2.comp T2, (isCompactOperator_condExpLp_two S).comp_clm T2, ?_⟩
    rw [dist_eq_norm]
    change ‖E2‖ < δ
    exact hb.trans_lt hCδ
  rwa [isClosed_setOfPred_isCompactOperator.closure_eq] at hc

end LpCompactInterpolation
end ConditionedStableLaws
