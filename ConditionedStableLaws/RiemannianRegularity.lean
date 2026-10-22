import ConditionedStableLaws.AdmissibleDifferentiation
import Mathlib.Topology.Instances.Matrix

/-!
# Analytic ingredients for Riemannian volume regularity

Small-ball regularity from a continuous positive volume density, and the coordinate formula for the
density `sqrt(det g)`, in local coordinates.
-/

open Filter MeasureTheory MeasureTheory.Measure Set Metric
open scoped Topology

noncomputable section

namespace ConditionedStableLaws

section ContinuousDensity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} [IsFiniteMeasure ρ]

omit [BorelSpace M] in
/-- The absolute-error form of the Lebesgue-point condition implies ordinary
convergence of the density average. -/
theorem ball_average_tendsto_of_abs_sub_average {w : M → ℝ} (hw : Integrable w ρ)
    (x : M) (hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (ball x r))
    (hLeb : Tendsto
      (fun r => (∫ y in ball x r, |w y - w x| ∂ρ) / ρ.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r => (∫ y in ball x r, w y ∂ρ) / ρ.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (w x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLeb
  filter_upwards [hpos] with r hr
  have hnum := norm_integral_le_integral_norm (μ := ρ.restrict (ball x r))
    (fun y => w y - w x)
  rw [integral_sub hw.restrict (integrable_const _), setIntegral_const,
    smul_eq_mul, Real.norm_eq_abs] at hnum
  simp only [Real.norm_eq_abs] at hnum ⊢
  have heq : (∫ y in ball x r, w y ∂ρ) / ρ.real (ball x r) - w x =
      ((∫ y in ball x r, w y ∂ρ) - ρ.real (ball x r) * w x) /
        ρ.real (ball x r) := by field_simp
  rw [heq, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right hnum hr.le

/-- Multiplying a finite reference measure by a continuous density multiplies its small-ball
constant by the value of that density at the centre. -/
theorem IsRegularAt.withDensity_of_continuousAt {x : M} {d C : ℝ}
    (hreg : IsRegularAt ρ x d C) {w : M → ℝ} (hw : Integrable w ρ)
    (hw_nonneg : ∀ y, 0 ≤ w y) (hw_pos : 0 < w x) (hw_cont : ContinuousAt w x) :
    IsRegularAt (ρ.withDensity (fun y => ENNReal.ofReal (w y))) x d (C * w x) := by
  have hadm := isAdmissibleAt_of_continuousAt hw hreg hw_pos hw_cont
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (ball x r) := by
    filter_upwards [(tendsto_order.1 hreg.2.2).1 0 hreg.2.1,
      self_mem_nhdsWithin] with r hr hrpos
    exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hrpos d)).mp hr
  have havg := ball_average_tendsto_of_abs_sub_average hw x hpos hadm.2.2
  refine ⟨hreg.1, mul_pos hreg.2.1 hw_pos, ?_⟩
  have hprod := havg.mul hreg.2.2
  rw [mul_comm (w x) C] at hprod
  apply hprod.congr'
  filter_upwards [hpos] with r hr
  rw [withDensity_ofReal_real_apply hw.aestronglyMeasurable hw_nonneg measurableSet_ball]
  field_simp

end ContinuousDensity

section CoordinateVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  (volume : Measure E) [IsAddHaarMeasure volume]

/-- A continuous positive density times volume, restricted to a compact
domain, has the expected volume constant at every interior point. -/
theorem isRegularAt_continuousDensity_restrict_addHaar
    {D : Set E} (hD : IsCompact D) {x : E} (hx : x ∈ interior D)
    {w : E → ℝ} (hw : Continuous w) (hw_nonneg : ∀ y, 0 ≤ w y)
    (hw_pos : 0 < w x) :
    IsRegularAt ((volume.restrict D).withDensity (fun y => ENNReal.ofReal (w y)))
      x (Module.finrank ℝ E : ℝ) (volume.real (ball (0 : E) 1) * w x) := by
  have : IsFiniteMeasure (volume.restrict D) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hD.measure_lt_top (μ := volume)⟩
  exact (isRegularAt_restrict_addHaar volume hx).withDensity_of_continuousAt
    (hw.continuousOn.integrableOn_compact hD) hw_nonneg hw_pos hw.continuousAt

/-- The coordinate expression for a volume element associated with a matrix field: a local density.
-/
def coordinateVolumeDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : E → Matrix ι ι ℝ) (x : E) : ℝ :=
  Real.sqrt (Matrix.det (g x))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Nontrivial E] in
/-- The square-root determinant density is continuous whenever the metric
matrix is continuous. -/
theorem continuous_coordinateVolumeDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : E → Matrix ι ι ℝ} (hg : Continuous g) :
    Continuous (coordinateVolumeDensity g) :=
  hg.matrix_det.sqrt

/-- The local coordinate-volume assertion, with the Riemannian Jacobian `sqrt(det g)`. Positivity of
the determinant is the usual pointwise positive-definiteness requirement. -/
theorem isRegularAt_coordinateVolumeDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : Set E} (hD : IsCompact D) {x : E} (hx : x ∈ interior D)
    {g : E → Matrix ι ι ℝ} (hg : Continuous g) (hg_pos : 0 < Matrix.det (g x)) :
    IsRegularAt ((volume.restrict D).withDensity
      (fun y => ENNReal.ofReal (coordinateVolumeDensity g y)))
      x (Module.finrank ℝ E : ℝ)
      (volume.real (ball (0 : E) 1) * Real.sqrt (Matrix.det (g x))) := by
  exact isRegularAt_continuousDensity_restrict_addHaar volume hD hx
    (continuous_coordinateVolumeDensity hg) (fun _ => Real.sqrt_nonneg _)
    (Real.sqrt_pos.2 hg_pos)

end CoordinateVolume

section BallComparison

variable {M E : Type*} [MetricSpace M] [MeasurableSpace M]
  [MetricSpace E] [MeasurableSpace E]

/-- A radius multiplied by a factor tending to one has the same normalized
small-ball limit. This is the rescaling step in a chart-ball squeeze. -/
theorem IsRegularAt.tendsto_scaled_ball {ν : Measure E} {x : E} {d C : ℝ}
    (hreg : IsRegularAt ν x d C) {a : ℝ → ℝ}
    (ha : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun r => ν.real (ball x (a r * r)) / r ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  have hap : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < a r :=
    (tendsto_order.1 ha).1 0 zero_lt_one
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hascale : Tendsto (fun r => a r * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using ha.mul hr, ?_⟩
    filter_upwards [hap, self_mem_nhdsWithin] with r har hrr
    exact mul_pos har hrr
  have hapow : Tendsto (fun r => a r ^ d) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using ha.rpow_const (p := d) (Or.inl one_ne_zero)
  have ht := (hreg.2.2.comp hascale).mul hapow
  simp only [mul_one, Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [hap, self_mem_nhdsWithin] with r har hrr
  rw [Real.mul_rpow har.le (le_of_lt hrr)]
  field_simp

/-- Constant-radius rescaling, retaining the factor `a^d` in the limit. -/
theorem IsRegularAt.tendsto_const_scaled_ball {ν : Measure E} {x : E} {d C a : ℝ}
    (hreg : IsRegularAt ν x d C) (ha : 0 < a) :
    Tendsto (fun r => ν.real (ball x (a * r)) / r ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 (C * a ^ d)) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hscale : Tendsto (fun r => a * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using hr.const_mul a, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hrpos
    exact mul_pos ha hrpos
  apply ((hreg.2.2.comp hscale).mul_const (a ^ d)).congr'
  filter_upwards [self_mem_nhdsWithin] with r hrpos
  dsimp only [Function.comp_def]
  rw [Real.mul_rpow ha.le (le_of_lt hrpos)]
  field_simp

/-- A family of arbitrarily sharp ball bounds forces the exact volume
constant. Each fixed `c > 1` may have its own neighborhood. -/
theorem isRegularAt_of_sharp_ball_comparison {ρ : Measure M} {ν : Measure E}
    {x : M} {z : E} {d C : ℝ} (hreg : IsRegularAt ν z d C)
    (hcompare : ∀ c : ℝ, 1 < c → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν.real (ball z (c⁻¹ * r)) ≤ ρ.real (ball x r) ∧
      ρ.real (ball x r) ≤ ν.real (ball z (c * r))) :
    IsRegularAt ρ x d C := by
  refine ⟨hreg.1, hreg.2.1, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro u hu
    have hid : Tendsto (fun c : ℝ => c) (𝓝[>] (1 : ℝ)) (𝓝 1) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    have hcLim : Tendsto (fun c : ℝ => C * (c⁻¹) ^ d)
        (𝓝[>] (1 : ℝ)) (𝓝 C) := by
      simpa using ((hid.inv₀ one_ne_zero).rpow_const (p := d)
        (Or.inl (by simp))).const_mul C
    have hcgt : ∀ᶠ c : ℝ in 𝓝[>] (1 : ℝ), 1 < c := self_mem_nhdsWithin
    obtain ⟨c, hc, huc⟩ :=
      (hcgt.and ((tendsto_order.mp hcLim).1 u hu)).exists
    have hcpos : 0 < c := lt_trans zero_lt_one hc
    have hlow := hreg.tendsto_const_scaled_ball (inv_pos.mpr hcpos)
    filter_upwards [(tendsto_order.mp hlow).1 u huc, hcompare c hc,
      self_mem_nhdsWithin] with r hr hcomp hrpos
    exact hr.trans_le (div_le_div_of_nonneg_right hcomp.1
      (Real.rpow_nonneg (le_of_lt hrpos) _))
  · intro u hu
    have hid : Tendsto (fun c : ℝ => c) (𝓝[>] (1 : ℝ)) (𝓝 1) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    have hcLim : Tendsto (fun c : ℝ => C * c ^ d) (𝓝[>] (1 : ℝ)) (𝓝 C) := by
      simpa using (hid.rpow_const (p := d) (Or.inl one_ne_zero)).const_mul C
    have hcgt : ∀ᶠ c : ℝ in 𝓝[>] (1 : ℝ), 1 < c := self_mem_nhdsWithin
    obtain ⟨c, hc, hcu⟩ :=
      (hcgt.and ((tendsto_order.mp hcLim).2 u hu)).exists
    have hhigh := hreg.tendsto_const_scaled_ball (lt_trans zero_lt_one hc)
    filter_upwards [(tendsto_order.mp hhigh).2 u hcu, hcompare c hc,
      self_mem_nhdsWithin] with r hr hcomp hrpos
    exact (div_le_div_of_nonneg_right hcomp.2
      (Real.rpow_nonneg (le_of_lt hrpos) _)).trans_lt hr

/-- The exact volume asymptotic follows from two geometric ball comparisons whose radius factors
tend to one. For a local chart, apply this lemma to its source with the restricted measure. -/
theorem isRegularAt_of_chart_ball_comparison
    {ρ : Measure M} {ν : Measure E} [IsFiniteMeasure ν]
    {chart : M → E} (hchart : MeasurableEmbedding chart) (hvolume : ρ.map chart = ν)
    {x : M} {d C : ℝ} (hreg : IsRegularAt ν (chart x) d C)
    {a b : ℝ → ℝ} (ha : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hb : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hballs : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ball (chart x) (a r * r) ⊆ chart '' ball x r ∧
      chart '' ball x r ⊆ ball (chart x) (b r * r)) :
    IsRegularAt ρ x d C := by
  refine ⟨hreg.1, hreg.2.1, ?_⟩
  have hmass (r : ℝ) : ν.real (chart '' ball x r) = ρ.real (ball x r) := by
    rw [← hvolume, measureReal_def, hchart.map_apply,
      hchart.injective.preimage_image, measureReal_def]
  apply (hreg.tendsto_scaled_ball ha).squeeze' (hreg.tendsto_scaled_ball hb)
  · filter_upwards [hballs, self_mem_nhdsWithin] with r hr hrpos
    exact div_le_div_of_nonneg_right
      ((measureReal_mono hr.1).trans_eq (hmass r)) (Real.rpow_nonneg (le_of_lt hrpos) _)
  · filter_upwards [hballs, self_mem_nhdsWithin] with r hr hrpos
    exact div_le_div_of_nonneg_right
      ((hmass r).symm.trans_le (measureReal_mono hr.2))
      (Real.rpow_nonneg (le_of_lt hrpos) _)

end BallComparison

end ConditionedStableLaws
