import ConditionedStableLaws.RiemannianRegularityTangent

/-!
# Volume regularity on Riemannian manifolds

The atlas is arbitrary. Normalized coordinates are constructed using the inverse tangent
trivialization. The volume is specified by a local coordinate identity.
-/

open Bundle Set MeasureTheory MeasureTheory.Measure Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

namespace ConditionedStableLaws

section LocalChart
variable {X F : Type*} [MetricSpace X] [MetricSpace F]

/-- An asymptotically isometric local chart sandwiches small metric balls. -/
theorem eventually_ball_comparison_of_localChart
    (e : OpenPartialHomeomorph X F) {x : X} (hx : x ∈ e.source)
    {c : ℝ} (hc : 1 < c)
    (hcomp : ∀ᶠ y in 𝓝 x, dist x y ≤ c * dist (e x) (e y) ∧
      dist (e x) (e y) ≤ c * dist x y) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ball (e x) (c⁻¹ * r) ⊆ e '' ball x r ∧ e '' ball x r ⊆ ball (e x) (c * r) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hcomp
  have htarget : e.target ∈ 𝓝 (e x) := e.open_target.mem_nhds (e.map_source hx)
  have hinv : e.symm ⁻¹' ball x δ ∈ 𝓝 (e x) := by
    apply (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds
    simpa only [e.left_inv hx] using ball_mem_nhds x hδ
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
    have hzη : z ∈ ball (e x) η := ball_subset_ball (hcr.le.trans hrη.le) hz
    obtain ⟨hztarget, hzδ⟩ := hηsub hzη
    have hestimate := (hδsub hzδ).1
    have hez : e (e.symm z) = z := e.right_inv hztarget
    refine ⟨e.symm z, ?_, hez⟩
    apply mem_ball.mpr
    have hzdist : dist (e x) z < c⁻¹ * r := by simpa only [dist_comm] using mem_ball.mp hz
    have hlt := mul_lt_mul_of_pos_left hzdist hcpos
    rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul] at hlt
    have hfinal : dist x (e.symm z) < r := by
      rw [hez] at hestimate
      exact hestimate.trans_lt hlt
    simpa only [dist_comm] using hfinal
  · rintro z ⟨y, hy, rfl⟩
    have hyδ : y ∈ ball x δ := ball_subset_ball hrδ.le hy
    have hestimate := (hδsub hyδ).2
    have hydist : dist x y < r := by simpa only [dist_comm] using mem_ball.mp hy
    apply mem_ball.mpr
    simpa only [dist_comm] using hestimate.trans_lt (mul_lt_mul_of_pos_left hydist hcpos)

end LocalChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsManifold 𝓘(ℝ, E) 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The preferred chart postcomposed by its inverse tangent equivalence. -/
def tangentChart (x : M) : OpenPartialHomeomorph M (TangentSpace 𝓘(ℝ, E) x) :=
  (chartAt E x).transHomeomorph (tangentCoordinateEquiv (E := E) x).symm.toHomeomorph

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
@[simp] theorem tangentChart_apply (x y : M) :
    tangentChart (E := E) x y = tangentCoordinates (E := E) x y := by
  simp [tangentChart, tangentCoordinates]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
@[simp] theorem mem_tangentChart_source (x : M) : x ∈ (tangentChart (E := E) x).source := by
  simp [tangentChart, mem_chart_source]

/-- Arbitrary Riemannian charts admit sharp distance comparison after the
explicit tangent normalization. -/
theorem eventually_tangentChart_dist_comparison (x : M) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ y in 𝓝 x, dist x y ≤ c * dist (tangentChart (E := E) x x) (tangentChart (E := E) x y) ∧
      dist (tangentChart (E := E) x x) (tangentChart (E := E) x y) ≤ c * dist x y := by
  let c' : ℝ≥0 := ⟨c, (lt_trans zero_lt_one hc).le⟩
  have hc' : 1 < c' := hc
  filter_upwards [eventually_riemannianEDist_le_tangentCoordinates (E := E) x hc',
    eventually_tangentCoordinates_edist_le (E := E) x hc'] with y h1 h2
  rw [← IsRiemannianManifold.out] at h1 h2
  constructor
  · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) h1
    rw [ENNReal.toReal_mul] at h
    change (edist _ _).toReal ≤ (c : ℝ) * (edist _ _).toReal at h
    simpa only [← dist_edist, tangentChart_apply] using h
  · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) h2
    rw [ENNReal.toReal_mul] at h
    change (edist _ _).toReal ≤ (c : ℝ) * (edist _ _).toReal at h
    simpa only [← dist_edist, tangentChart_apply] using h

/-- Canonically normalized coordinate-ball bounds at every point. -/
theorem eventually_tangentChart_ball_comparison (x : M) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ball (tangentChart (E := E) x x) (c⁻¹ * r) ⊆ tangentChart (E := E) x '' ball x r ∧
      tangentChart (E := E) x '' ball x r ⊆ ball (tangentChart (E := E) x x) (c * r) :=
  eventually_ball_comparison_of_localChart (tangentChart (E := E) x)
    (mem_tangentChart_source x) hc (eventually_tangentChart_dist_comparison x hc)

variable [MeasurableSpace M] [BorelSpace M]

/-- Exact small-ball volume asymptotics for any Riemannian metric with a specified local coordinate
measure. No normalization condition on the atlas is needed. -/
theorem isRegularAt_of_tangentCoordinateMeasure (x : M)
    [MeasurableSpace (TangentSpace 𝓘(ℝ, E) x)]
    {ρ : Measure M} {ν : Measure (TangentSpace 𝓘(ℝ, E) x)} [IsFiniteMeasure ν]
    {d C : ℝ} (hreg : IsRegularAt ν (tangentChart (E := E) x x) d C)
    (hvolume : ∃ U ∈ 𝓝 x, ∀ s : Set M, MeasurableSet s → s ⊆ U →
      ρ s = ν (tangentChart (E := E) x '' s)) :
    IsRegularAt ρ x d C := by
  obtain ⟨U, hU, hvolume⟩ := hvolume
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  apply isRegularAt_of_sharp_ball_comparison hreg
  intro c hc
  filter_upwards [eventually_tangentChart_ball_comparison (E := E) x hc,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hballs hr
  have hmass : ρ.real (ball x r) = ν.real (tangentChart (E := E) x '' ball x r) := by
    simp only [measureReal_def]
    rw [hvolume (ball x r) measurableSet_ball ((ball_subset_ball hr.le).trans hδU)]
  rw [hmass]
  exact ⟨measureReal_mono hballs.1, measureReal_mono hballs.2⟩

end ConditionedStableLaws
