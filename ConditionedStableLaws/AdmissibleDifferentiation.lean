import ConditionedStableLaws.LocalDensity
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Lebesgue points and interior volume regularity

An integrable density has the stated absolute-error ball average at almost every point, for measures
absolutely continuous with respect to finite-dimensional Haar volume. This includes restrictions of
volume and measures with a volume density. Volume regularity also holds at interior points of a
domain in a finite-dimensional normed space.
-/

open Filter MeasureTheory MeasureTheory.Measure Set Metric
open scoped Topology

noncomputable section

namespace ConditionedStableLaws

section LebesguePoints

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [HasBesicovitchCovering M]
  {ρ : Measure M} [IsLocallyFiniteMeasure ρ]

/-- The absolute-error Lebesgue differentiation theorem on closed balls.
The sole analytic assumption on the density is local integrability. -/
theorem ae_tendsto_closedBall_abs_sub_average {m : M → ℝ}
    (hm : LocallyIntegrable m ρ) :
    ∀ᵐ x ∂ρ, Tendsto
      (fun r => (∫ y in closedBall x r, |m y - m x| ∂ρ) /
        ρ.real (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [(Besicovitch.vitaliFamily ρ).ae_tendsto_average_norm_sub hm] with x hx
  have ht := hx.comp (Besicovitch.tendsto_filterAt ρ x)
  simpa only [Function.comp_def, setAverage_eq, Real.norm_eq_abs,
    smul_eq_mul, div_eq_inv_mul] using ht

/-- When positive-radius spheres are null, the closed-ball differentiation theorem gives the exact
open-ball condition in the definition of regular points. -/
theorem ae_tendsto_ball_abs_sub_average_of_sphere_null {m : M → ℝ}
    (hm : LocallyIntegrable m ρ)
    (hsphere : ∀ x : M, ∀ r : ℝ, 0 < r → ρ (sphere x r) = 0) :
    ∀ᵐ x ∂ρ, Tendsto
      (fun r => (∫ y in ball x r, |m y - m x| ∂ρ) /
        ρ.real (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_closedBall_abs_sub_average hm] with x hx
  apply hx.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have heq : closedBall x r =ᵐ[ρ] ball x r := by
    apply ae_eq_set.mpr
    constructor
    · simpa only [closedBall_sdiff_ball] using hsphere x r hr
    · rw [sdiff_eq_empty.mpr ball_subset_closedBall, measure_empty]
  rw [setIntegral_congr_set heq, measureReal_congr heq]

end LebesguePoints

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (volume : Measure E) [IsAddHaarMeasure volume]

/-- The Lebesgue-point assertion for any locally finite measure absolutely continuous with respect
to finite-dimensional volume. It applies in particular to volume restricted to a compact domain. -/
theorem ae_tendsto_ball_abs_sub_average_of_absolutelyContinuous
    {ρ : Measure E} [IsLocallyFiniteMeasure ρ] (hρ : ρ ≪ volume)
    {m : E → ℝ} (hm : Integrable m ρ) :
    ∀ᵐ x ∂ρ, Tendsto
      (fun r => (∫ y in ball x r, |m y - m x| ∂ρ) /
        ρ.real (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact ae_tendsto_ball_abs_sub_average_of_sphere_null hm.locallyIntegrable
    (fun x r hr => hρ (volume.addHaar_sphere_of_ne_zero x hr.ne'))

/-- Restricting the almost-everywhere assertion to the complement of the
exceptional set `Z` needs no regularity or measurability hypothesis on `Z`. -/
theorem ae_tendsto_ball_abs_sub_average_off_set
    {ρ : Measure E} [IsLocallyFiniteMeasure ρ] (hρ : ρ ≪ volume)
    {m : E → ℝ} (hm : Integrable m ρ) (Z : Set E) :
    ∀ᵐ x ∂ρ.restrict Zᶜ, Tendsto
      (fun r => (∫ y in ball x r, |m y - m x| ∂ρ) /
        ρ.real (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ae_restrict_of_ae (ae_tendsto_ball_abs_sub_average_of_absolutelyContinuous volume hρ hm)

/-- The volume constant in finite dimensions is the positive, finite measure of the unit ball. The
dimension must be positive. -/
theorem isRegularAt_addHaar [Nontrivial E] (x : E) :
    IsRegularAt volume x (Module.finrank ℝ E : ℝ) (volume.real (ball (0 : E) 1)) := by
  refine ⟨by exact_mod_cast Module.finrank_pos, ?_, ?_⟩
  · exact ENNReal.toReal_pos (measure_ball_pos volume (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    symm
    simp only [measureReal_def]
    rw [volume.addHaar_ball_of_pos x hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hr) _),
      Real.rpow_natCast]
    rw [mul_div_cancel_left₀ _ (pow_pos hr _).ne']

/-- Restriction to a domain does not change sufficiently small balls at an interior point. -/
theorem isRegularAt_restrict_addHaar [Nontrivial E] {D : Set E} {x : E}
    (hx : x ∈ interior D) :
    IsRegularAt (volume.restrict D) x (Module.finrank ℝ E : ℝ)
      (volume.real (ball (0 : E) 1)) := by
  have hreg := isRegularAt_addHaar volume x
  refine ⟨hreg.1, hreg.2.1, hreg.2.2.congr' ?_⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  filter_upwards [(eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr
  have hball : ball x r ⊆ D := (ball_subset_ball hr.le).trans hsub
  rw [measureReal_def, measureReal_def, Measure.restrict_apply measurableSet_ball,
    inter_eq_left.mpr hball]

/-- Almost every interior point with positive density is admissible for volume restricted to a
domain. -/
theorem ae_isAdmissiblePoint_restrict_addHaar [Nontrivial E]
    (D : Set E) {m : E → ℝ} (hm : Integrable m (volume.restrict D)) :
    ∀ᵐ x ∂volume.restrict D, x ∈ interior D → 0 < m x →
      IsAdmissiblePoint (volume.restrict D) m x (Module.finrank ℝ E : ℝ) := by
  filter_upwards [ae_tendsto_ball_abs_sub_average_of_absolutelyContinuous volume
    (Measure.absolutelyContinuous_restrict (μ := volume) (s := D)) hm] with x hx
  intro hD hmpos
  exact ⟨volume.real (ball (0 : E) 1), isRegularAt_restrict_addHaar volume hD, hmpos, hx⟩

end FiniteDimensional

end ConditionedStableLaws
