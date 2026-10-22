import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import ConditionedStableLaws.Tails

/-!
# Local density and weighted ball asymptotics

A Lebesgue point of an integrable density remains a point of the expected average after
multiplication by a continuous weight. The measure may be any finite measure.
-/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace ConditionedStableLaws

section Estimate

variable {M : Type*} [MeasurableSpace M] {ρ : Measure M} [IsFiniteMeasure ρ]

omit [IsFiniteMeasure ρ] in
/-- A density measure has the stated real mass on every measurable set. -/
theorem withDensity_ofReal_real_apply {f : M → ℝ}
    (hf : AEStronglyMeasurable f ρ) (hf₀ : ∀ y, 0 ≤ f y)
    {s : Set M} (hs : MeasurableSet s) :
    (ρ.withDensity (fun y => ENNReal.ofReal (f y))).real s = ∫ y in s, f y ∂ρ := by
  rw [measureReal_def, withDensity_apply _ hs]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall hf₀) hf.restrict).symm

/-- Quantitative weighted-density estimate on a measurable set of positive mass. -/
theorem weighted_setIntegral_ratio_bound {s : Set M} (hs : MeasurableSet s)
    {m η : M → ℝ} (hm : Integrable m ρ) (hη : AEStronglyMeasurable η ρ)
    {K η₀ m₀ ε : ℝ} (hK : ∀ y, |η y| ≤ K)
    (hosc : ∀ y ∈ s, |η y - η₀| ≤ ε) (hρ : 0 < ρ.real s) :
    |(∫ y in s, η y * m y ∂ρ) / ρ.real s - η₀ * m₀| ≤
      K * ((∫ y in s, |m y - m₀| ∂ρ) / ρ.real s) + |m₀| * ε := by
  have hprod : Integrable (fun y => η y * m y) ρ :=
    hm.bdd_mul hη (Eventually.of_forall (fun y => by simpa using hK y))
  have herr : Integrable (fun y => |m y - m₀|) (ρ.restrict s) :=
    (hm.restrict.sub (integrable_const m₀)).abs
  have hdom : Integrable (fun y => K * |m y - m₀| + |m₀| * ε) (ρ.restrict s) :=
    (herr.const_mul K).add (integrable_const _)
  have hpoint : ∀ᵐ y ∂ρ.restrict s,
      ‖η y * m y - η₀ * m₀‖ ≤ K * |m y - m₀| + |m₀| * ε := by
    filter_upwards [ae_restrict_mem hs] with y hy
    rw [Real.norm_eq_abs]
    calc
      |η y * m y - η₀ * m₀| = |η y * (m y - m₀) + m₀ * (η y - η₀)| := by
        congr 1
        ring
      _ ≤ |η y * (m y - m₀)| + |m₀ * (η y - η₀)| := abs_add_le _ _
      _ = |η y| * |m y - m₀| + |m₀| * |η y - η₀| := by rw [abs_mul, abs_mul]
      _ ≤ K * |m y - m₀| + |m₀| * ε :=
        add_le_add (mul_le_mul_of_nonneg_right (hK y) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hosc y hy) (abs_nonneg _))
  have hnum := norm_integral_le_of_norm_le hdom hpoint
  rw [integral_sub hprod.restrict (integrable_const _), setIntegral_const,
    smul_eq_mul, Real.norm_eq_abs,
    integral_add (herr.const_mul K) (integrable_const _), integral_const_mul,
    setIntegral_const, smul_eq_mul] at hnum
  have hrewrite :
      (∫ y in s, η y * m y ∂ρ) / ρ.real s - η₀ * m₀ =
      ((∫ y in s, η y * m y ∂ρ) - ρ.real s * (η₀ * m₀)) / ρ.real s := by
    field_simp
  rw [hrewrite, abs_div, abs_of_pos hρ]
  calc
    _ ≤ (K * (∫ y in s, |m y - m₀| ∂ρ) + ρ.real s * (|m₀| * ε)) / ρ.real s :=
      div_le_div_of_nonneg_right hnum hρ.le
    _ = K * ((∫ y in s, |m y - m₀| ∂ρ) / ρ.real s) + |m₀| * ε := by
      field_simp

end Estimate

section BallLimits

variable {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} [IsFiniteMeasure ρ]

/-- Admissible points: regularity, a positive density value, and the exact Lebesgue-point condition
for the chosen density representative. -/
def IsAdmissibleAt (ρ : Measure M) (m : M → ℝ) (x₀ : M) (d C : ℝ) : Prop :=
  IsRegularAt ρ x₀ d C ∧ 0 < m x₀ ∧
    Tendsto (fun r => (∫ y in Metric.ball x₀ r, |m y - m x₀| ∂ρ) /
      ρ.real (Metric.ball x₀ r)) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- The admissible-point predicate without fixing its volume constant. -/
def IsAdmissiblePoint (ρ : Measure M) (m : M → ℝ) (x₀ : M) (d : ℝ) : Prop :=
  ∃ C : ℝ, IsAdmissibleAt ρ m x₀ d C

omit [CompactSpace M] in
/-- A positive regular point at which the density is continuous is admissible. Only continuity at
the chosen point is needed. -/
theorem isAdmissibleAt_of_continuousAt {m : M → ℝ} (hm : Integrable m ρ)
    {x₀ : M} {d C : ℝ} (hregular : IsRegularAt ρ x₀ d C)
    (hm₀ : 0 < m x₀) (hmc : ContinuousAt m x₀) :
    IsAdmissibleAt ρ m x₀ d C := by
  refine ⟨hregular, hm₀, ?_⟩
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (Metric.ball x₀ r) := by
    filter_upwards [(tendsto_order.1 hregular.2.2).1 0 hregular.2.1,
      self_mem_nhdsWithin] with r hq hr
    exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hr d)).mp hq
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hmc (ε / 2) (by positivity)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hsmall] with r hr hrd
  have hint : IntegrableOn (fun y => |m y - m x₀|) (Metric.ball x₀ r) ρ :=
    (hm.sub (integrable_const _)).abs.restrict
  have hbound : (∫ y in Metric.ball x₀ r, |m y - m x₀| ∂ρ) ≤
      (ε / 2) * ρ.real (Metric.ball x₀ r) := by
    have hle := setIntegral_mono_on hint
      (integrableOn_const (C := ε / 2) (measure_lt_top ρ (Metric.ball x₀ r)).ne)
      Metric.isOpen_ball.measurableSet (fun y hy => by
        simpa only [Real.dist_eq] using
          (hcont (lt_trans (Metric.mem_ball.mp hy) hrd)).le)
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hle
  have hnonneg : 0 ≤ ∫ y in Metric.ball x₀ r, |m y - m x₀| ∂ρ :=
    integral_nonneg fun _ => abs_nonneg _
  have hquot_nonneg : 0 ≤ (∫ y in Metric.ball x₀ r, |m y - m x₀| ∂ρ) /
      ρ.real (Metric.ball x₀ r) := div_nonneg hnonneg hr.le
  have hquot_le : (∫ y in Metric.ball x₀ r, |m y - m x₀| ∂ρ) /
      ρ.real (Metric.ball x₀ r) ≤ ε / 2 := by
    rw [div_le_iff₀ hr]
    exact hbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hquot_nonneg]
  linarith

omit [CompactSpace M] in
/-- Version with the regularity constant existentially quantified. -/
theorem isAdmissiblePoint_of_continuousAt {m : M → ℝ} (hm : Integrable m ρ)
    {x₀ : M} {d : ℝ} (hregular : IsRegularPoint ρ x₀ d)
    (hm₀ : 0 < m x₀) (hmc : ContinuousAt m x₀) :
    IsAdmissiblePoint ρ m x₀ d := by
  obtain ⟨C, hC⟩ := hregular
  exact ⟨C, isAdmissibleAt_of_continuousAt hm hC hm₀ hmc⟩

/-- A continuous weight preserves the Lebesgue-point average of an integrable density. -/
theorem weighted_ball_average_tendsto {m η : M → ℝ} (hm : Integrable m ρ)
    (hη : Continuous η) (x₀ : M) (m₀ : ℝ)
    (hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (Metric.ball x₀ r))
    (hlebesgue : Tendsto
      (fun r => (∫ y in Metric.ball x₀ r, |m y - m₀| ∂ρ) /
        ρ.real (Metric.ball x₀ r)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r => (∫ y in Metric.ball x₀ r, η y * m y ∂ρ) /
      ρ.real (Metric.ball x₀ r)) (𝓝[>] (0 : ℝ)) (𝓝 (η x₀ * m₀)) := by
  obtain ⟨K₀, hK₀⟩ := isCompact_univ.exists_bound_of_continuousOn hη.continuousOn
  let K : ℝ := |K₀| + 1
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hK : ∀ y, |η y| ≤ K := by
    intro y
    have hy := hK₀ y (mem_univ y)
    rw [Real.norm_eq_abs] at hy
    dsimp [K]
    linarith [le_abs_self K₀]
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ₁ : ℝ := ε / (4 * K)
  let δ₂ : ℝ := ε / (4 * (|m₀| + 1))
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hδ₂ : 0 < δ₂ := by dsimp [δ₂]; positivity
  obtain ⟨r₀, hr₀, hcont⟩ :=
    Metric.continuousAt_iff.mp (hη.continuousAt : ContinuousAt η x₀) δ₂ hδ₂
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < r₀ :=
    (eventually_lt_nhds hr₀).filter_mono nhdsWithin_le_nhds
  have herror : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫ y in Metric.ball x₀ r, |m y - m₀| ∂ρ) /
        ρ.real (Metric.ball x₀ r) < δ₁ :=
    (tendsto_order.1 hlebesgue).2 δ₁ hδ₁
  filter_upwards [hpos, hsmall, herror] with r hr hrr hle
  rw [Real.dist_eq]
  have hosc : ∀ y ∈ Metric.ball x₀ r, |η y - η x₀| ≤ δ₂ := by
    intro y hy
    have hy' := hcont (lt_trans (Metric.mem_ball.mp hy) hrr)
    simpa only [Real.dist_eq] using hy'.le
  calc
    _ ≤ K * ((∫ y in Metric.ball x₀ r, |m y - m₀| ∂ρ) /
          ρ.real (Metric.ball x₀ r)) + |m₀| * δ₂ :=
      weighted_setIntegral_ratio_bound Metric.isOpen_ball.measurableSet hm
        hη.aestronglyMeasurable hK hosc hr
    _ ≤ K * δ₁ + (|m₀| + 1) * δ₂ :=
      add_le_add (mul_le_mul_of_nonneg_left hle.le hKpos.le)
        (mul_le_mul_of_nonneg_right (by linarith) hδ₂.le)
    _ = ε / 2 := by
      dsimp [δ₁, δ₂]
      field_simp
      ring
    _ < ε := by linarith

/-- Ball regularity and the Lebesgue-point assumption give the weighted ball asymptotic. Positivity
of the density and weight is not needed. -/
theorem weighted_ball_mass_asymptotic {m η : M → ℝ} (hm : Integrable m ρ)
    (hη : Continuous η) (x₀ : M) (m₀ d C : ℝ) (hC : 0 < C)
    (hregular : Tendsto (fun r : ℝ => ρ.real (Metric.ball x₀ r) / r ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hlebesgue : Tendsto
      (fun r => (∫ y in Metric.ball x₀ r, |m y - m₀| ∂ρ) /
        ρ.real (Metric.ball x₀ r)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ => (∫ y in Metric.ball x₀ r, η y * m y ∂ρ) / r ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 (η x₀ * m₀ * C)) := by
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (Metric.ball x₀ r) := by
    filter_upwards [(tendsto_order.1 hregular).1 0 hC,
      self_mem_nhdsWithin] with r hq hr
    exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hr d)).mp hq
  have havg := weighted_ball_average_tendsto hm hη x₀ m₀ hpos hlebesgue
  apply (havg.mul hregular).congr'
  filter_upwards [hpos] with r hr
  field_simp

/-- Measure-valued form of the weighted ball asymptotic. The density relation is stated as equality
of the ball masses and integrals. -/
theorem density_ball_mass_asymptotic (ν : Measure M) {m η : M → ℝ}
    (hm : Integrable m ρ) (hη : Continuous η) (x₀ : M) (m₀ d C : ℝ)
    (hC : 0 < C)
    (hν : ∀ r : ℝ, ν.real (Metric.ball x₀ r) =
      ∫ y in Metric.ball x₀ r, η y * m y ∂ρ)
    (hregular : Tendsto (fun r : ℝ => ρ.real (Metric.ball x₀ r) / r ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hlebesgue : Tendsto
      (fun r => (∫ y in Metric.ball x₀ r, |m y - m₀| ∂ρ) /
        ρ.real (Metric.ball x₀ r)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ => ν.real (Metric.ball x₀ r) / r ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 (η x₀ * m₀ * C)) := by
  simpa only [hν] using
    weighted_ball_mass_asymptotic hm hη x₀ m₀ d C hC hregular hlebesgue

/-- Admissibility transfers from the reference measure to the weighted measure. -/
theorem IsAdmissibleAt.weighted_regular {m η : M → ℝ} {x₀ : M} {d C : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ d C) (hm : Integrable m ρ)
    (hη : Continuous η) (hη₀ : 0 < η x₀) (ν : Measure M)
    (hν : ∀ r : ℝ, ν.real (Metric.ball x₀ r) =
      ∫ y in Metric.ball x₀ r, η y * m y ∂ρ) :
    IsRegularAt ν x₀ d (C * η x₀ * m x₀) := by
  refine ⟨hadm.1.1, mul_pos (mul_pos hadm.1.2.1 hη₀) hadm.2.1, ?_⟩
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    density_ball_mass_asymptotic ν hm hη x₀ (m x₀) d C hadm.1.2.1 hν
      hadm.1.2.2 hadm.2.2

/-- Tail asymptotics of the singular observable, including the normalized-tail conclusion. The
density hypothesis is equality of ball masses with the integral of `η*m`. -/
theorem tail_asymptotics (ν : Measure M) [IsFiniteMeasure ν]
    {m η : M → ℝ} (hm : Integrable m ρ) (hη : Continuous η)
    {x₀ : M} {d C β : ℝ} (hadm : IsAdmissibleAt ρ m x₀ d C)
    (hη₀ : 0 < η x₀) (hβ : 0 < β)
    (hν : ∀ r : ℝ, ν.real (Metric.ball x₀ r) =
      ∫ y in Metric.ball x₀ r, η y * m y ∂ρ) :
    Tendsto (fun t : ℝ => ν.real {x | t < singularObservable x₀ β x} /
      ((C * η x₀ * m x₀) * t ^ (-(d / β)))) atTop (𝓝 1) ∧
    ∀ u : ℝ, 0 < u → Tendsto (fun n : ℕ => (n : ℝ) * ν.real
      {x | u * powerScale (C * η x₀ * m x₀) (d / β) n <
        singularObservable x₀ β x}) atTop (𝓝 (u ^ (-(d / β)))) := by
  have hreg := hadm.weighted_regular hm hη hη₀ ν hν
  exact ⟨tail_asymptotic_of_regular hβ hreg,
    fun _ hu => singularObservable_normalized_tail hβ hreg hu⟩

/-- The same proposition with the weighted measure constructed by `withDensity`.

The finite measure instance for the weighted measure follows from integrability
of `m` and boundedness of the continuous weight on the compact state space.
-/
theorem tail_asymptotics_withDensity {m η : M → ℝ}
    (hm : Integrable m ρ) (hm₀ : ∀ y, 0 ≤ m y)
    (hη : Continuous η) (hηnonneg : ∀ y, 0 ≤ η y)
    {x₀ : M} {d C β : ℝ} (hadm : IsAdmissibleAt ρ m x₀ d C)
    (hη₀ : 0 < η x₀) (hβ : 0 < β) :
    let ν := ρ.withDensity (fun y => ENNReal.ofReal (η y * m y))
    Tendsto (fun t : ℝ => ν.real {x | t < singularObservable x₀ β x} /
      ((C * η x₀ * m x₀) * t ^ (-(d / β)))) atTop (𝓝 1) ∧
    ∀ u : ℝ, 0 < u → Tendsto (fun n : ℕ => (n : ℝ) * ν.real
      {x | u * powerScale (C * η x₀ * m x₀) (d / β) n <
        singularObservable x₀ β x}) atTop (𝓝 (u ^ (-(d / β)))) := by
  let ν := ρ.withDensity (fun y => ENNReal.ofReal (η y * m y))
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn hη.continuousOn
  have hprod : Integrable (fun y => η y * m y) ρ :=
    hm.bdd_mul hη.aestronglyMeasurable
      (Eventually.of_forall (fun y => hK y (mem_univ y)))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hprod.2
  apply tail_asymptotics ν hm hη hadm hη₀ hβ
  intro r
  exact withDensity_ofReal_real_apply hprod.aestronglyMeasurable
    (fun y => mul_nonneg (hηnonneg y) (hm₀ y)) Metric.isOpen_ball.measurableSet

end BallLimits

end ConditionedStableLaws
