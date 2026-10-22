import ConditionedStableLaws.RiemannianRegularityCharts

/-!
# Canonical normalized coordinates without changing the atlas

Postcomposing a chart with the inverse tangent trivialization at its centre
places its coordinates in the tangent space carrying the Riemannian norm.
This normalization is constructed at every point, for an arbitrary atlas.
-/

open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

namespace ConditionedStableLaws

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsManifold 𝓘(ℝ, E) 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The derivative of the preferred chart at its centre, as a continuous
linear equivalence. Its inverse constructs normalized tangent coordinates. -/
def tangentCoordinateEquiv (x : M) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)

/-- Normalized coordinates valued in the Riemannian tangent space. -/
def tangentCoordinates (x : M) (y : M) : TangentSpace 𝓘(ℝ, E) x :=
  (tangentCoordinateEquiv (E := E) x).symm (extChartAt 𝓘(ℝ, E) x y)

set_option backward.isDefEq.respectTransparency false in
/-- Every preferred chart, postcomposed with its inverse tangent coordinate
map, has asymptotically unit distortion in the forward distance bound. -/
theorem eventually_riemannianEDist_le_tangentCoordinates (x : M)
    {c : ℝ≥0} (hc : 1 < c) :
    ∀ᶠ y in 𝓝 x,
      riemannianEDist 𝓘(ℝ, E) x y ≤ c * edist (tangentCoordinates (E := E) x x) (tangentCoordinates (E := E) x y) := by
  let A := tangentCoordinateEquiv (E := E) x
  let e := extChartAt 𝓘(ℝ, E) x
  have hC : ∀ᶠ y in 𝓝 x,
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e y)) ∘L A.toContinuousLinearMap‖ₑ < c := by
    filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt
      E (TangentSpace 𝓘(ℝ, E)) x (show (1 : ℝ) < c from hc), chart_source_mem_nhds E x]
      with y hy h'y
    rw [TangentBundle.symmL_trivializationAt h'y] at hy
    have hxy : e.symm (e y) = y := e.left_inv (by simpa [e] using h'y)
    have hA : A.toContinuousLinearMap =
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearMapAt ℝ x := by
      exact Trivialization.coe_continuousLinearEquivAt_eq' _ _
    rw [← hA] at hy
    simp only [modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] at hy
    have hy' : ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e y)) ∘L A.toContinuousLinearMap‖ < (c : ℝ) := by
      convert! hy using 3 <;> congr
    simp only [enorm, nnnorm]
    exact_mod_cast hy'
  have hC' : ∀ᶠ z in 𝓝 (e x),
      z ∈ e.target ∧ ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z) ∘L A.toContinuousLinearMap‖ₑ < c := by
    have hcont : ContinuousAt e.symm (e x) := continuousAt_extChartAt_symm x
    have hCbase : {y | ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e y)) ∘L A.toContinuousLinearMap‖ₑ < c} ∈ 𝓝 (e.symm (e x)) := by
      rw [show e.symm (e x) = x from extChartAt_to_inv x]
      exact hC
    have hcpre := hcont.preimage_mem_nhds hCbase
    have htarget : e.target ∈ 𝓝 (e x) := by
      simpa only [modelWithCornersSelf_coe, Set.range_id, nhdsWithin_univ] using
        (extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) x)
    filter_upwards [hcpre, htarget] with z hz hzt
    refine ⟨hzt, ?_⟩
    change ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (e.symm z))) ∘L A.toContinuousLinearMap‖ₑ < c at hz
    rwa [e.right_inv hzt] at hz
  obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp hC'
  have hn : e ⁻¹' ball (e x) r ∈ 𝓝 x :=
    (continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds _ hrpos)
  filter_upwards [hn, chart_source_mem_nhds E x] with y hy h'y
  let ζ := ContinuousAffineMap.lineMap (R := ℝ) (tangentCoordinates (E := E) x x) (tangentCoordinates (E := E) x y)
  let η := A ∘ ζ
  have hηeq : η = ContinuousAffineMap.lineMap (R := ℝ) (e x) (e y) := by
    ext t
    simp [η, ζ, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply,
      tangentCoordinates, A, e]
  let γ := e.symm ∘ η
  have hη : Icc (0 : ℝ) 1 ⊆ η ⁻¹' {z | z ∈ e.target ∧
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z) ∘L A.toContinuousLinearMap‖ₑ < c} := by
    rw [hηeq]
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact ((convex_ball _ _).segment_subset (by simp [hrpos]) hy).trans hr
  have hηsmooth : CMDiff 1 η := by
    rw [hηeq, contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hζsmooth : ContDiff ℝ 1 ζ := ContinuousAffineMap.contDiff _
  have hdist : riemannianEDist 𝓘(ℝ, E) x y ≤ pathELength 𝓘(ℝ, E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp hηsmooth.contMDiffOn (fun t ht => (hη ht).1)
    · simp [γ, hηeq, e, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, hηeq, e, ContinuousAffineMap.coe_lineMap_eq, h'y]
  apply hdist.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hderη : mfderiv[Icc 0 1] η t = A.toContinuousLinearMap ∘L fderivWithin ℝ ζ (Icc 0 1) t := by
    rw [mfderivWithin_eq_fderivWithin]
    change fderivWithin ℝ (A ∘ ζ) (Icc 0 1) t = _
    rw [fderiv_comp_fderivWithin t A.differentiableAt
      (hζsmooth.differentiable one_ne_zero t).differentiableWithinAt
      (uniqueDiffOn_Icc zero_lt_one t ht), A.fderiv]
  have hderγ : mfderiv[Icc 0 1] γ t =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (η t)) ∘L mfderiv[Icc 0 1] η t := by
    apply mfderiv_comp_mfderivWithin
    · apply (mdifferentiableWithinAt_extChartAt_symm (hη ht).1).mdifferentiableAt
      simp
    · exact hηsmooth.mdifferentiable one_ne_zero |>.mdifferentiableAt.mdifferentiableWithinAt
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hder1 : mfderiv[Icc 0 1] γ t 1 =
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (η t)) ∘L A.toContinuousLinearMap) (fderivWithin ℝ ζ (Icc 0 1) t 1) := by
    rw [hderγ, hderη]
    rfl
  rw [hder1]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  exact (hη ht).2.le


set_option backward.isDefEq.respectTransparency false in
/-- The inverse distance estimate for the constructed tangent coordinates;
no condition on the original atlas is required. -/
theorem eventually_tangentCoordinates_edist_le [RegularSpace M] (x : M)
    {c : ℝ≥0} (hc : 1 < c) :
    ∀ᶠ y in 𝓝 x,
      edist (tangentCoordinates (E := E) x x) (tangentCoordinates (E := E) x y) ≤
        c * riemannianEDist 𝓘(ℝ, E) x y := by
  let A := tangentCoordinateEquiv (E := E) x
  let e := extChartAt 𝓘(ℝ, E) x
  let φ := tangentCoordinates (E := E) x
  have hφdiff (y : M) (hy : y ∈ e.source) :
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) φ y := by
    exact A.symm.contDiff.contMDiff.mdifferentiableAt one_ne_zero |>.comp y
      (mdifferentiableAt_extChartAt (by simpa [e] using hy))
  have hφder (y : M) (hy : y ∈ e.source) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) φ y =
        A.symm.toContinuousLinearMap ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) (A.symm ∘ e) y = _
    rw [mfderiv_comp y (A.symm.contDiff.contMDiff.mdifferentiableAt one_ne_zero)
      (mdifferentiableAt_extChartAt (by simpa [e] using hy)), mfderiv_eq_fderiv, A.symm.fderiv]
    rfl
  have hC : ∀ᶠ y in 𝓝 x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) φ y‖ₑ < c := by
    filter_upwards [eventually_norm_symmL_trivializationAt_self_comp_lt
      E (TangentSpace 𝓘(ℝ, E)) x (show (1 : ℝ) < c from hc),
      chart_source_mem_nhds E x] with y hy h'y
    rw [hφder y (by simpa [e] using h'y),
      ← TangentBundle.continuousLinearMapAt_trivializationAt h'y]
    have hA : A.symm.toContinuousLinearMap =
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ x :=
      Trivialization.symm_continuousLinearEquivAt_eq' _ _
    rw [hA]
    simp only [enorm, nnnorm]
    exact_mod_cast hy
  let U := {y : M | ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) φ y‖ₑ < c} ∩ e.source
  have hU : U ∈ 𝓝 x := inter_mem hC (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) x)
  obtain ⟨R, hRpos, hR⟩ := setOfPred_riemannianEDist_lt_subset_nhds 𝓘(ℝ, E) hU
  filter_upwards [eventually_riemannianEDist_lt 𝓘(ℝ, E) x
    (show (0 : ℝ≥0∞) < R from ENNReal.coe_pos.mpr hRpos)] with y hy
  let d := riemannianEDist 𝓘(ℝ, E) x y
  have hdR : d < R := hy
  have hdtop : d ≠ (∞ : ℝ≥0∞) := (hdR.trans ENNReal.coe_lt_top).ne
  have hεlim : Tendsto (fun ε : ℝ≥0∞ => ε) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hadd : Tendsto (fun ε : ℝ≥0∞ => d + ε) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 d) := by
    simpa using tendsto_const_nhds.add hεlim
  have hmul := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) hadd
    (Or.inr ENNReal.coe_ne_top)
  apply ge_of_tendsto hmul
  filter_upwards [(tendsto_order.1 hadd).2 (R : ℝ≥0∞) hdR,
    self_mem_nhdsWithin] with ε hεsmall hεpos
  have hdε : d < d + ε := ENNReal.lt_add_right hdtop (ne_of_gt hεpos)
  obtain ⟨γ, hγx, hγy, hγsmooth, hγlen, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hdε zero_lt_one
  have hγU : Icc (0 : ℝ) 1 ⊆ γ ⁻¹' U := by
    intro t ht
    apply hR
    have hprefix : riemannianEDist 𝓘(ℝ, E) x (γ t) ≤ pathELength 𝓘(ℝ, E) γ 0 t :=
      riemannianEDist_le_pathELength hγsmooth.contMDiffOn hγx rfl ht.1
    have hlen : pathELength 𝓘(ℝ, E) γ 0 t ≤ pathELength 𝓘(ℝ, E) γ 0 1 := by
      gcongr
      exact ht.2
    exact hprefix.trans_lt (hlen.trans_lt (hγlen.trans hεsmall))
  let γ' := φ ∘ γ
  have hγ' : ContDiffOn ℝ 1 γ' (Icc 0 1) := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact A.symm.contDiff.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt.comp (I' := 𝓘(ℝ, E)) (t := (chartAt E x).source)
        hγsmooth.contMDiffOn (fun t ht => by simpa [U, e] using (hγU ht).2))
  have hbound : ‖γ' 1 - γ' 0‖ₑ ≤ c * pathELength 𝓘(ℝ, E) γ 0 1 := by
    calc
      ‖γ' 1 - γ' 0‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin γ' (Icc 0 1) t‖ₑ :=
        enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hγ' zero_le_one
      _ = ∫⁻ t in Icc (0 : ℝ) 1, ‖fderivWithin ℝ γ' (Icc 0 1) t 1‖ₑ := by
        simp_rw [← fderivWithin_derivWithin]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, c * ‖mfderiv[Icc 0 1] γ t 1‖ₑ := by
        apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
        have hder : fderivWithin ℝ γ' (Icc 0 1) t =
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) φ (γ t)) ∘L
              mfderiv[Icc 0 1] γ t := by
          have hcomp := mfderiv_comp_mfderivWithin t (hφdiff _ (hγU ht).2)
            ((hγsmooth.mdifferentiable one_ne_zero).mdifferentiableOn _ ht)
            (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
                exact uniqueDiffOn_Icc zero_lt_one t ht)
          rw [mfderivWithin_eq_fderivWithin] at hcomp
          exact hcomp
        have hder1 : fderivWithin ℝ γ' (Icc 0 1) t 1 =
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) φ (γ t))
              (mfderiv[Icc 0 1] γ t 1) := congrArg (fun f => f 1) hder
        rw [hder1]
        apply (ContinuousLinearMap.le_opENorm _ _).trans
        gcongr
        exact (hγU ht).1.le
      _ = c * pathELength 𝓘(ℝ, E) γ 0 1 := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          pathELength_eq_lintegral_mfderivWithin_Icc]
  have heq : edist (tangentCoordinates (E := E) x x) (tangentCoordinates (E := E) x y) =
      ‖γ' 1 - γ' 0‖ₑ := by
    rw [edist_comm, edist_eq_enorm_sub]
    simp only [γ', φ, Function.comp_apply, hγx, hγy]
  rw [heq]
  apply hbound.trans
  gcongr

end ConditionedStableLaws
