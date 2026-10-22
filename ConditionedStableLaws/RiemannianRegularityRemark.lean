import ConditionedStableLaws.RiemannianRegularityMetricDensity
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Interior regularity for Riemannian volume

The volume is given by its standard local identity: in any of the tangent charts, volume is Lebesgue
measure times the square root of the determinant of the metric tensor. The small-ball asymptotic
follows.
-/

open Module Bundle Set MeasureTheory MeasureTheory.Measure Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

namespace ConditionedStableLaws

section Restriction
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Restricting any regular measure to a domain preserves regularity at
interior points, without any boundary regularity assumption. -/
theorem IsRegularAt.restrict_of_mem_interior {ρ : Measure X} {x : X} {d C : ℝ}
    (hreg : IsRegularAt ρ x d C) {D : Set X} (hx : x ∈ interior D) :
    IsRegularAt (ρ.restrict D) x d C := by
  refine ⟨hreg.1, hreg.2.1, hreg.2.2.congr' ?_⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  filter_upwards [(eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr
  have hball : ball x r ⊆ D := (ball_subset_ball hr.le).trans hsub
  rw [measureReal_def, measureReal_def, Measure.restrict_apply measurableSet_ball,
    inter_eq_left.mpr hball]

end Restriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsManifold 𝓘(ℝ, E) 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local instance tangentMeasurableSpace (x : M) : MeasurableSpace (TangentSpace 𝓘(ℝ, E) x) :=
  borel (TangentSpace 𝓘(ℝ, E) x)

local instance tangentBorelSpace (x : M) : BorelSpace (TangentSpace 𝓘(ℝ, E) x) := ⟨rfl⟩

/-- A basis for each normalized tangent-coordinate space, constructed from
a basis of the model space through the inverse tangent trivialization. -/
def tangentVolumeBasis (x : M) :
    Basis (Fin (finrank ℝ E)) ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  (Module.finBasis ℝ E).map (tangentCoordinateEquiv (E := E) x).symm.toLinearEquiv

/-- The defining local formula for a Riemannian volume measure, with density `sqrt(det g)` for the
Riemannian metric tensor. -/
def HasRiemannianVolumeDensity (ρ : Measure M) : Prop :=
  ∀ x : M, ∀ s : Set M, MeasurableSet s → s ⊆ (tangentChart (E := E) x).source →
    ρ s = ((tangentVolumeBasis (E := E) x).addHaar.withDensity
      (fun z => ENNReal.ofReal (tangentVolumeDensity x (tangentVolumeBasis (E := E) x) z)))
      (tangentChart (E := E) x '' s)

/-- The leading small-ball constant, expressed in normalized tangent
coordinates. Its positivity is proved by regularity below. -/
def riemannianVolumeBallConstant (x : M) : ℝ :=
  (tangentVolumeBasis (E := E) x).addHaar.real
    (ball (0 : TangentSpace 𝓘(ℝ, E) x) 1) *
    tangentVolumeDensity x (tangentVolumeBasis (E := E) x) (tangentChart (E := E) x x)

/-- A Riemannian volume measure is regular at every point of a positive finite-dimensional manifold
with its geodesic distance. -/
theorem HasRiemannianVolumeDensity.isRegularAt {ρ : Measure M}
    (hρ : HasRiemannianVolumeDensity (E := E) ρ) (x : M) :
    IsRegularAt ρ x (finrank ℝ E : ℝ) (riemannianVolumeBallConstant (E := E) x) := by
  have : Nontrivial (TangentSpace 𝓘(ℝ, E) x) :=
    (tangentCoordinateEquiv (E := E) x).symm.injective.nontrivial
  let e := tangentChart (E := E) x
  let b := tangentVolumeBasis (E := E) x
  let w := tangentVolumeDensity x b
  let vol := b.addHaar
  have hx : e x ∈ e.target := e.map_source (mem_tangentChart_source x)
  obtain ⟨K, hK, hxK, hKtarget⟩ := exists_compact_subset e.open_target hx
  have hw : ContinuousOn w K := (continuousOn_tangentVolumeDensity x b).mono hKtarget
  have hwint : Integrable w (vol.restrict K) := hw.integrableOn_compact hK
  have hwpos : 0 < w (e x) := tangentVolumeDensity_pos x b
  have hwnonneg : ∀ z, 0 ≤ w z := fun z => Real.sqrt_nonneg _
  have hwcont : ContinuousAt w (e x) := hw.continuousAt (mem_interior_iff_mem_nhds.mp hxK)
  have : IsFiniteMeasure (vol.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := vol)⟩
  let ν := (vol.restrict K).withDensity (fun z => ENNReal.ofReal (w z))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    (ne_of_lt ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hwnonneg)).mp hwint.2))
  have hreg : IsRegularAt ν (e x) (finrank ℝ (TangentSpace 𝓘(ℝ, E) x) : ℝ)
      (vol.real (ball (0 : TangentSpace 𝓘(ℝ, E) x) 1) * w (e x)) :=
    (isRegularAt_restrict_addHaar vol hxK).withDensity_of_continuousAt
      hwint hwnonneg hwpos hwcont
  have hdim : finrank ℝ (TangentSpace 𝓘(ℝ, E) x) = finrank ℝ E :=
    (tangentCoordinateEquiv (E := E) x).toLinearEquiv.finrank_eq
  rw [hdim] at hreg
  apply isRegularAt_of_tangentCoordinateMeasure x hreg
  refine ⟨e.source ∩ e ⁻¹' K, inter_mem (e.open_source.mem_nhds (mem_tangentChart_source x))
    ((e.continuousAt (mem_tangentChart_source x)).preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hxK)), ?_⟩
  intro s hs hsU
  rw [hρ x s hs (hsU.trans inter_subset_left)]
  change (vol.withDensity (fun z => ENNReal.ofReal (w z))) (e '' s) = ν (e '' s)
  rw [show ν = (vol.withDensity (fun z => ENNReal.ofReal (w z))).restrict K from
    (restrict_withDensity hK.measurableSet _).symm,
    Measure.restrict_apply' hK.measurableSet]
  rw [inter_eq_left.mpr]
  rintro z ⟨y, hy, rfl⟩
  exact (hsU hy).2

/-- The local coordinate-volume definition also supplies local finiteness;
no global finite-volume hypothesis is required. -/
theorem HasRiemannianVolumeDensity.isLocallyFiniteMeasure {ρ : Measure M}
    (hρ : HasRiemannianVolumeDensity (E := E) ρ) : IsLocallyFiniteMeasure ρ := by
  constructor
  intro x
  have hreg := hρ.isRegularAt x
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (ball x r) := by
    filter_upwards [(tendsto_order.1 hreg.2.2).1 0 hreg.2.1,
      self_mem_nhdsWithin] with r hr hrpos
    exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hrpos _)).mp hr
  have hrpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hmass⟩ := (hrpos.and hpos).exists
  exact ⟨ball x r, ball_mem_nhds x hr, (ENNReal.toReal_pos_iff.mp hmass).2⟩

/-- Every interior point of a domain has the ambient-dimensional small-ball asymptotic for the
restricted Riemannian volume measure. Compactness is not needed. -/
theorem HasRiemannianVolumeDensity.isRegularAt_restrict {ρ : Measure M}
    (hρ : HasRiemannianVolumeDensity (E := E) ρ) {D : Set M} {x : M}
    (hx : x ∈ interior D) :
    IsRegularAt (ρ.restrict D) x (finrank ℝ E : ℝ)
      (riemannianVolumeBallConstant (E := E) x) :=
  (hρ.isRegularAt x).restrict_of_mem_interior hx

/-- A continuous positive density is admissible at every interior point of
a compact domain with Riemannian volume. -/
theorem HasRiemannianVolumeDensity.isAdmissibleAt_restrict_of_continuousAt
    {ρ : Measure M} (hρ : HasRiemannianVolumeDensity (E := E) ρ)
    {D : Set M} (hD : IsCompact D) {m : M → ℝ} (hm : Integrable m (ρ.restrict D))
    {x : M} (hx : x ∈ interior D) (hmpos : 0 < m x) (hmcont : ContinuousAt m x) :
    IsAdmissibleAt (ρ.restrict D) m x (finrank ℝ E : ℝ)
      (riemannianVolumeBallConstant (E := E) x) := by
  have : IsLocallyFiniteMeasure ρ := hρ.isLocallyFiniteMeasure
  have : IsFiniteMeasure (ρ.restrict D) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hD.measure_lt_top (μ := ρ)⟩
  exact isAdmissibleAt_of_continuousAt hm (hρ.isRegularAt_restrict hx) hmpos hmcont


end ConditionedStableLaws
