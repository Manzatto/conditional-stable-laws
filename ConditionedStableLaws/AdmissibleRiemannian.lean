import ConditionedStableLaws.RiemannianRegularityRemark
import ConditionedStableLaws.AdmissibleVitali

/-!
# Riemannian admissibility

The reference measure is given by the standard local Riemannian volume formula, using the metric
tensor in normalized tangent coordinates. It has ambient-dimensional small-ball regularity and is
locally finite. The Vitali argument then yields the exact open-ball Lebesgue-point condition,
including almost every point on the boundary of any measurable domain.
-/

open Module Bundle Set MeasureTheory MeasureTheory.Measure Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

namespace ConditionedStableLaws

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsManifold 𝓘(ℝ, E) 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

/-- The Lebesgue-point condition for Riemannian volume on a measurable domain. The ambient manifold
need not be compact or have finite volume, and no null-boundary condition is imposed on the domain.
-/
theorem HasRiemannianVolumeDensity.ae_tendsto_ball_abs_sub_average_restrict
    {ρ : Measure M} (hρ : HasRiemannianVolumeDensity (E := E) ρ)
    {D : Set M} (hD : MeasurableSet D) {m : M → ℝ} (hm : Integrable m (ρ.restrict D)) :
    ∀ᵐ x ∂ρ.restrict D, Tendsto
      (fun r => (∫ y in ball x r, |m y - m x| ∂ρ.restrict D) /
        (ρ.restrict D).real (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have : IsLocallyFiniteMeasure ρ := hρ.isLocallyFiniteMeasure
  exact ae_tendsto_ball_abs_sub_average_restrict_of_regular
    (fun x => ⟨riemannianVolumeBallConstant (E := E) x, hρ.isRegularAt x⟩) hD hm

/-- The same differentiation condition holds almost everywhere off the exceptional set `Z`, for any
`Z`. -/
theorem HasRiemannianVolumeDensity.ae_tendsto_ball_abs_sub_average_off_set
    {ρ : Measure M} (hρ : HasRiemannianVolumeDensity (E := E) ρ)
    {D : Set M} (hD : MeasurableSet D) {m : M → ℝ} (hm : Integrable m (ρ.restrict D))
    (Z : Set M) :
    ∀ᵐ x ∂(ρ.restrict D).restrict Zᶜ, Tendsto
      (fun r => (∫ y in ball x r, |m y - m x| ∂ρ.restrict D) /
        (ρ.restrict D).real (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ae_restrict_of_ae (hρ.ae_tendsto_ball_abs_sub_average_restrict hD hm)

/-- Almost every positive-density point of a measurable Riemannian domain is admissible, including
its boundary. -/
theorem HasRiemannianVolumeDensity.ae_isAdmissiblePoint_restrict
    {ρ : Measure M} (hρ : HasRiemannianVolumeDensity (E := E) ρ)
    {D : Set M} (hD : MeasurableSet D) {m : M → ℝ} (hm : Integrable m (ρ.restrict D)) :
    ∀ᵐ x ∂ρ.restrict D, 0 < m x →
      IsAdmissiblePoint (ρ.restrict D) m x (finrank ℝ E : ℝ) := by
  have : IsLocallyFiniteMeasure ρ := hρ.isLocallyFiniteMeasure
  exact ae_isAdmissiblePoint_restrict_of_regular
    (fun x => ⟨riemannianVolumeBallConstant (E := E) x, hρ.isRegularAt x⟩) hD hm

end ConditionedStableLaws
