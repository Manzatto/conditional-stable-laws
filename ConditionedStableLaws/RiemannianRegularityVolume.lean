import ConditionedStableLaws.RiemannianRegularityCharts

/-!
# Small geodesic balls and coordinate volume

Derivative normalization of a chart gives the two ball inclusions needed for a volume squeeze. The
local volume assumption is an exact change-of-coordinates identity for measures.
-/

open Bundle Set MeasureTheory MeasureTheory.Measure Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

namespace ConditionedStableLaws

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsManifold 𝓘(ℝ, E) 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- Sharp comparison for the Riemannian metric, in real-valued form. -/
theorem IsNormalizedRiemannianChartAt.eventually_dist_comparison {x : M}
    (hx : IsNormalizedRiemannianChartAt (I := 𝓘(ℝ, E)) x)
    {c : ℝ} (hc : 1 < c) :
    ∀ᶠ y in 𝓝 x,
      dist x y ≤ c * dist (extChartAt 𝓘(ℝ, E) x x) (extChartAt 𝓘(ℝ, E) x y) ∧
      dist (extChartAt 𝓘(ℝ, E) x x) (extChartAt 𝓘(ℝ, E) x y) ≤ c * dist x y := by
  let c' : ℝ≥0 := ⟨c, (lt_trans zero_lt_one hc).le⟩
  have hc' : 1 < c' := hc
  filter_upwards [hx.eventually_riemannianEDist_le hc',
    hx.eventually_chartEDist_le hc'] with y h1 h2
  rw [← IsRiemannianManifold.out] at h1 h2
  constructor
  · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) h1
    rw [ENNReal.toReal_mul] at h
    change (edist _ _).toReal ≤ (c : ℝ) * (edist _ _).toReal at h
    simpa only [← dist_edist] using h
  · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) h2
    rw [ENNReal.toReal_mul] at h
    change (edist _ _).toReal ≤ (c : ℝ) * (edist _ _).toReal at h
    simpa only [← dist_edist] using h

/-- Geodesic balls are sandwiched between coordinate balls with arbitrary
multiplicative distortion `c > 1`, once the radius is sufficiently small. -/
theorem IsNormalizedRiemannianChartAt.eventually_ball_comparison {x : M}
    (hx : IsNormalizedRiemannianChartAt (I := 𝓘(ℝ, E)) x)
    {c : ℝ} (hc : 1 < c) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ball (extChartAt 𝓘(ℝ, E) x x) (c⁻¹ * r) ⊆
          extChartAt 𝓘(ℝ, E) x '' ball x r ∧
      extChartAt 𝓘(ℝ, E) x '' ball x r ⊆
          ball (extChartAt 𝓘(ℝ, E) x x) (c * r) := by
  let e := extChartAt 𝓘(ℝ, E) x
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    ((hx.eventually_dist_comparison hc).and (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) x))
  have htarget : e.target ∈ 𝓝 (e x) := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, nhdsWithin_univ] using
      (extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) x)
  have hinv : e.symm ⁻¹' ball x δ ∈ 𝓝 (e x) := by
    have hcont : ContinuousAt e.symm (e x) := continuousAt_extChartAt_symm x
    apply hcont.preimage_mem_nhds
    simpa [e] using ball_mem_nhds x hδ
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hinv)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < min δ η :=
    (eventually_lt_nhds (lt_min hδ hη)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with r hr hrpos
  have hrδ := lt_of_lt_of_le hr (min_le_left _ _)
  have hrη := lt_of_lt_of_le hr (min_le_right _ _)
  constructor
  · intro z hz
    have hcr : c⁻¹ * r < r := by
      have hcInv : c⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc
      simpa only [one_mul] using mul_lt_mul_of_pos_right hcInv (show 0 < r from hrpos)
    have hzη : z ∈ ball (e x) η :=
      ball_subset_ball (hcr.le.trans hrη.le) hz
    obtain ⟨hztarget, hzδ⟩ := hηsub hzη
    have hestimate := (hδsub hzδ).1.1
    have hez : e (e.symm z) = z := e.right_inv hztarget
    refine ⟨e.symm z, ?_, hez⟩
    apply mem_ball.mpr
    have hzdist : dist (e x) z < c⁻¹ * r := by simpa only [dist_comm] using mem_ball.mp hz
    have hlt := mul_lt_mul_of_pos_left hzdist hcpos
    rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul] at hlt
    have hfinal : dist x (e.symm z) < r := by
      have hestimate' : dist x (e.symm z) ≤ c * dist (e x) z := by
        simpa only [← show e = extChartAt 𝓘(ℝ, E) x from rfl, hez] using hestimate
      exact hestimate'.trans_lt hlt
    simpa only [dist_comm] using hfinal
  · rintro z ⟨y, hy, rfl⟩
    have hyδ : y ∈ ball x δ := ball_subset_ball hrδ.le hy
    have hestimate := (hδsub hyδ).1.2
    have hydist : dist x y < r := by simpa only [dist_comm] using mem_ball.mp hy
    apply mem_ball.mpr
    simpa only [dist_comm] using
      hestimate.trans_lt (mul_lt_mul_of_pos_left hydist hcpos)

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- The small-ball constant transfers from the coordinate measure to a
Riemannian measure with the specified local change-of-coordinates identity.
The only normalization hypothesis concerns the chart derivative at `x`. -/
theorem isRegularAt_of_normalizedRiemannianChart {x : M}
    (hx : IsNormalizedRiemannianChartAt (I := 𝓘(ℝ, E)) x)
    {ρ : Measure M} {ν : Measure E} [IsFiniteMeasure ν]
    {d C : ℝ} (hreg : IsRegularAt ν (extChartAt 𝓘(ℝ, E) x x) d C)
    (hvolume : ∃ U ∈ 𝓝 x, ∀ s : Set M, MeasurableSet s → s ⊆ U →
      ρ s = ν (extChartAt 𝓘(ℝ, E) x '' s)) :
    IsRegularAt ρ x d C := by
  obtain ⟨U, hU, hvolume⟩ := hvolume
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  apply isRegularAt_of_sharp_ball_comparison hreg
  intro c hc
  filter_upwards [hx.eventually_ball_comparison hc,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hballs hr
  have hmass : ρ.real (ball x r) = ν.real (extChartAt 𝓘(ℝ, E) x '' ball x r) := by
    simp only [measureReal_def]
    rw [hvolume (ball x r) measurableSet_ball ((ball_subset_ball hr.le).trans hδU)]
  rw [hmass]
  exact ⟨measureReal_mono hballs.1, measureReal_mono hballs.2⟩

end ConditionedStableLaws
