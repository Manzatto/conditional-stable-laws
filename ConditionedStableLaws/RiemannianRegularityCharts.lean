import ConditionedStableLaws.RiemannianRegularity
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# First-order metric control in normalized Riemannian charts

The normalization condition concerns only the derivative of a chart at its
centre. Continuity of the Riemannian metric then gives arbitrarily sharp
local derivative bounds, which yield a length-distance comparison.
-/

open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

namespace ConditionedStableLaws

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- A chart is normalized at its centre when its tangent coordinate map and
inverse have operator norm at most one, equivalently are isometries. -/
def IsNormalizedRiemannianChartAt (x : M) : Prop :=
  ‖(trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x‖ ≤ 1 ∧
  ‖(trivializationAt E (TangentSpace I) x).symmL ℝ x‖ ≤ 1

omit [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem chart_tangent_inverse (x : M) :
    ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x) ∘L
      ((trivializationAt E (TangentSpace I) x).symmL ℝ x) =
      ContinuousLinearMap.id ℝ E := by
  ext v
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
    mem_baseSet_trivializationAt, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  convert! ((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x hx).apply_symm_apply v
  simp [Trivialization.coe_continuousLinearEquivAt_eq _ hx]

/-- Normalization at one point upgrades continuity of the Riemannian metric
to the sharp chart-derivative bound `1 + ε`, for every `ε > 0`. -/
theorem IsNormalizedRiemannianChartAt.eventually_norm_chart_lt {x : M}
    (hx : IsNormalizedRiemannianChartAt (I := I) x) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ y in 𝓝 x,
      ‖(trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ y‖ < c := by
  filter_upwards [eventually_norm_symmL_trivializationAt_self_comp_lt
    E (TangentSpace I) x hc] with y hy
  let e := trivializationAt E (TangentSpace I) x
  have hid := chart_tangent_inverse (I := I) x
  calc
    ‖e.continuousLinearMapAt ℝ y‖ =
        ‖(e.continuousLinearMapAt ℝ x) ∘L
          ((e.symmL ℝ x) ∘L (e.continuousLinearMapAt ℝ y))‖ := by
      rw [← ContinuousLinearMap.comp_assoc, hid, ContinuousLinearMap.id_comp]
    _ ≤ ‖e.continuousLinearMapAt ℝ x‖ *
        ‖(e.symmL ℝ x) ∘L (e.continuousLinearMapAt ℝ y)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(e.symmL ℝ x) ∘L (e.continuousLinearMapAt ℝ y)‖ :=
      mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _) hx.1
    _ < c := hy

/-- The inverse chart enjoys the same sharp derivative control. -/
theorem IsNormalizedRiemannianChartAt.eventually_norm_symm_chart_lt {x : M}
    (hx : IsNormalizedRiemannianChartAt (I := I) x) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ y in 𝓝 x, ‖(trivializationAt E (TangentSpace I) x).symmL ℝ y‖ < c := by
  filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt
    E (TangentSpace I) x hc] with y hy
  let e := trivializationAt E (TangentSpace I) x
  have hid := chart_tangent_inverse (I := I) x
  calc
    ‖e.symmL ℝ y‖ =
        ‖((e.symmL ℝ y) ∘L (e.continuousLinearMapAt ℝ x)) ∘L (e.symmL ℝ x)‖ := by
      rw [ContinuousLinearMap.comp_assoc, hid, ContinuousLinearMap.comp_id]
    _ ≤ ‖(e.symmL ℝ y) ∘L (e.continuousLinearMapAt ℝ x)‖ * ‖e.symmL ℝ x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(e.symmL ℝ y) ∘L (e.continuousLinearMapAt ℝ x)‖ :=
      mul_le_of_le_one_right (ContinuousLinearMap.opNorm_nonneg _) hx.2
    _ < c := hy

set_option backward.isDefEq.respectTransparency false in
theorem IsNormalizedRiemannianChartAt.eventually_mfderiv_symm_lt {x : M}
    (hx : IsNormalizedRiemannianChartAt (I := I) x) {c : ℝ≥0} (hc : 1 < c) :
    ∀ᶠ y in 𝓝[range I] (extChartAt I x x),
      ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < c := by
  have hC : ∀ᶠ y in 𝓝 x,
      ‖mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)‖ < (c : ℝ) := by
    filter_upwards [hx.eventually_norm_symm_chart_lt (show (1 : ℝ) < c from hc),
      chart_source_mem_nhds H x] with y hy h'y
    rw [TangentBundle.symmL_trivializationAt h'y] at hy
    have A : (extChartAt I x).symm (extChartAt I x y) = y :=
      (extChartAt I x).left_inv (by simpa using h'y)
    convert! hy using 3 <;> congr
  have hxx : 𝓝 x = 𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by simp
  rw [hxx] at hC
  have hcont : ContinuousAt (extChartAt I x).symm (extChartAt I x x) :=
    continuousAt_extChartAt_symm _
  filter_upwards [nhdsWithin_le_nhds (hcont.preimage_mem_nhds hC),
    extChartAt_target_mem_nhdsWithin x] with y hy h'y
  have hyid : y = (extChartAt I x) ((extChartAt I x).symm y) := by simp [-extChartAt, h'y]
  simp only [preimage_ofPred_eq, mem_ofPred_eq] at hy
  have hy' : ‖mfderiv[range I] (extChartAt I x).symm y‖ < (c : ℝ) := by
    convert! hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy'

set_option backward.isDefEq.respectTransparency false in
/-- In normalized coordinates, the Riemannian distance is locally at most
`c` times coordinate distance, for every `c > 1`. The proof uses a straight
coordinate segment and integrates the sharp inverse-derivative estimate. -/
theorem IsNormalizedRiemannianChartAt.eventually_riemannianEDist_le {x : M}
    (hx : IsNormalizedRiemannianChartAt (I := I) x) {c : ℝ≥0} (hc : 1 < c) :
    ∀ᶠ y in 𝓝 x,
      riemannianEDist I x y ≤ c * edist (extChartAt I x x) (extChartAt I x y) := by
  have hC := hx.eventually_mfderiv_symm_lt hc
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∩
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < c} :=
    mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  have A : (extChartAt I x) ⁻¹' (ball (extChartAt I x x) r ∩ range I) ∈ 𝓝 x := by
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ r_pos)
  filter_upwards [A, chart_source_mem_nhds H x] with y hy h'y
  let η := ContinuousAffineMap.lineMap (R := ℝ) (extChartAt I x x) (extChartAt I x y)
  set γ := (extChartAt I x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩
        {z | ‖mfderiv[range I] (extChartAt I x).symm z‖ₑ < c}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact (((convex_ball _ _).inter I.convex_range).segment_subset
      (by simp [r_pos]) hy).trans hr
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hdist : riemannianEDist I x y ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq, h'y]
  apply hdist.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hder : mfderiv[Icc 0 1] γ t =
      (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L
        (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hder1 : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range I] (extChartAt I x).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congrArg (fun f => f 1) hder
  rw [hder1]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

set_option backward.isDefEq.respectTransparency false in
/-- The reverse sharp comparison follows by integrating the chart derivative
along almost minimizing paths. Small-length paths stay in the chart because
their prefixes have at most the length of the whole path. -/
theorem IsNormalizedRiemannianChartAt.eventually_chartEDist_le
    [RegularSpace M] {x : M} (hx : IsNormalizedRiemannianChartAt (I := I) x)
    {c : ℝ≥0} (hc : 1 < c) :
    ∀ᶠ y in 𝓝 x,
      edist (extChartAt I x x) (extChartAt I x y) ≤ c * riemannianEDist I x y := by
  have hC : ∀ᶠ y in 𝓝 x, ‖mfderiv% (extChartAt I x) y‖ₑ < c := by
    filter_upwards [hx.eventually_norm_chart_lt (show (1 : ℝ) < c from hc),
      chart_source_mem_nhds H x] with y hy h'y
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt h'y]
    simp only [enorm, nnnorm]
    exact_mod_cast hy
  let U := {y : M | ‖mfderiv% (extChartAt I x) y‖ₑ < c} ∩ (extChartAt I x).source
  have hU : U ∈ 𝓝 x := inter_mem hC (extChartAt_source_mem_nhds (I := I) x)
  obtain ⟨R, hRpos, hR⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hU
  filter_upwards [eventually_riemannianEDist_lt I x
    (show (0 : ℝ≥0∞) < R from ENNReal.coe_pos.mpr hRpos)] with y hy
  let d := riemannianEDist I x y
  have hdR : d < R := hy
  have hdtop : d ≠ (∞ : ℝ≥0∞) := (hdR.trans (ENNReal.coe_lt_top)).ne
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
    have hprefix : riemannianEDist I x (γ t) ≤ pathELength I γ 0 t :=
      riemannianEDist_le_pathELength hγsmooth.contMDiffOn hγx rfl ht.1
    have hlen : pathELength I γ 0 t ≤ pathELength I γ 0 1 := by gcongr; exact ht.2
    exact hprefix.trans_lt (hlen.trans_lt (hγlen.trans hεsmall))
  let γ' := extChartAt I x ∘ γ
  have hγ' : CMDiff[Icc 0 1] 1 γ' :=
    contMDiffOn_extChartAt.comp (I' := I) (t := (chartAt H x).source)
      hγsmooth.contMDiffOn (fun t ht => by simpa [U] using (hγU ht).2)
  have hbound : ‖γ' 1 - γ' 0‖ₑ ≤ c * pathELength I γ 0 1 := by
    calc
      ‖γ' 1 - γ' 0‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin γ' (Icc 0 1) t‖ₑ := by
        apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ zero_le_one
        rwa [← contMDiffOn_iff_contDiffOn]
      _ = ∫⁻ t in Icc (0 : ℝ) 1, ‖mfderiv[Icc 0 1] γ' t 1‖ₑ := by
        simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
        rfl
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, c * ‖mfderiv[Icc 0 1] γ t 1‖ₑ := by
        apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
        have hder : mfderiv[Icc 0 1] γ' t =
            (mfderiv% (extChartAt I x) (γ t)) ∘L (mfderiv[Icc 0 1] γ t) := by
          apply mfderiv_comp_mfderivWithin
          · exact mdifferentiableAt_extChartAt (by simpa [U] using (hγU ht).2)
          · exact (hγsmooth.mdifferentiable one_ne_zero).mdifferentiableOn _ ht
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc zero_lt_one t ht
        have hder1 : mfderiv[Icc 0 1] γ' t 1 =
            (mfderiv% (extChartAt I x) (γ t)) (mfderiv[Icc 0 1] γ t 1) :=
          congrArg (fun f => f 1) hder
        rw [hder1]
        apply (ContinuousLinearMap.le_opENorm _ _).trans
        gcongr
        exact (hγU ht).1.le
      _ = c * pathELength I γ 0 1 := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          pathELength_eq_lintegral_mfderivWithin_Icc]
  have heq : edist (extChartAt I x x) (extChartAt I x y) = ‖γ' 1 - γ' 0‖ₑ := by
    rw [edist_comm, edist_eq_enorm_sub]
    simp only [γ', Function.comp_apply, hγx, hγy]
  rw [heq]
  apply hbound.trans
  gcongr

end ConditionedStableLaws
