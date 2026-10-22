import ConditionedStableLaws.TruncatedMoments
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Truncated second-moment asymptotics

Both the logarithmic asymptotic at exponent two and the power asymptotic below two are derived from
the tail hypothesis and the exact layer-cake identity. The weighted averaging lemmas use only local
integrability; continuity of the tail distribution is not needed.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace ConditionedStableLaws

/-- Logarithmic averaging: if `t g(t) → C`, the integral of `g` up to `t`,
divided by `log t`, tends to `C`. Local integrability suffices; continuity of
`g` is not needed. -/
theorem integral_div_log_tendsto (g : ℝ → ℝ) (C : ℝ)
    (hlocal : ∀ t : ℝ, 0 < t → IntervalIntegrable g volume 0 t)
    (hlim : Tendsto (fun t : ℝ => t * g t) atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => (∫ s in (0 : ℝ)..t, g s) / Real.log t)
      atTop (𝓝 C) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  let R : ℝ := max A 1
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRA : A ≤ R := le_max_left _ _
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  let D : ℝ := (∫ s in (0 : ℝ)..R, g s) - C * Real.log R
  have hD : Tendsto (fun t : ℝ => |D| / Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop R, eventually_gt_atTop (1 : ℝ),
    hD.eventually_lt_const (half_pos hε)] with t htR ht1 htD
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hgintegrable : IntervalIntegrable g volume R t :=
    (hlocal R hR).symm.trans (hlocal t ht0)
  have hinv : IntervalIntegrable (fun s : ℝ => s⁻¹) volume R t :=
    intervalIntegral.intervalIntegrable_inv
      (fun s hs => by
        have hs' : s ∈ Icc R t := by simpa only [Set.uIcc_of_le htR] using hs
        exact (hR.trans_le hs'.1).ne')
      continuousOn_id
  have hpoint : ∀ s ∈ Ioc R t, |g s - C * s⁻¹| ≤ (ε / 2) * s⁻¹ := by
    intro s hs
    have hsR : R ≤ s := hs.1.le
    have hs0 : 0 < s := hR.trans_le hsR
    have he' : |s * g s - C| < ε / 2 := by
      simpa only [Real.dist_eq] using hA s (hRA.trans hsR)
    have he := he'.le
    have heq : g s - C * s⁻¹ = (s * g s - C) / s := by
      field_simp
    rw [heq, abs_div, abs_of_pos hs0]
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right he hs0.le
  have herror : |∫ s in R..t, g s - C * s⁻¹| ≤
      (ε / 2) * (Real.log t - Real.log R) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun s => g s - C * s⁻¹) htR
      (Eventually.of_forall (fun s hs => by simpa only [Real.norm_eq_abs] using hpoint s hs))
      (hinv.const_mul (ε / 2))
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hR ht0, Real.log_div ht0.ne' hR.ne'] using hb
  have hsplit : (∫ s in (0 : ℝ)..t, g s) - C * Real.log t =
      D + ∫ s in R..t, g s - C * s⁻¹ := by
    rw [intervalIntegral.integral_sub hgintegrable (hinv.const_mul C),
      intervalIntegral.integral_const_mul, integral_inv_of_pos hR ht0,
      Real.log_div ht0.ne' hR.ne']
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hlocal R hR) hgintegrable
    dsimp [D]
    linarith
  have hnorm : |(∫ s in (0 : ℝ)..t, g s) - C * Real.log t| ≤
      |D| + (ε / 2) * Real.log t := by
    rw [hsplit]
    exact (abs_add_le _ _).trans
      (add_le_add le_rfl (herror.trans (by nlinarith)))
  rw [Real.dist_eq]
  have hquot : (∫ s in (0 : ℝ)..t, g s) / Real.log t - C =
      ((∫ s in (0 : ℝ)..t, g s) - C * Real.log t) / Real.log t := by
    field_simp
  rw [hquot, abs_div, abs_of_pos hlogt]
  calc
    _ ≤ (|D| + (ε / 2) * Real.log t) / Real.log t :=
      div_le_div_of_nonneg_right hnorm hlogt.le
    _ = |D| / Real.log t + ε / 2 := by field_simp
    _ < ε := by linarith

/-- Power-weighted averaging, proved by integrating the eventual error bound
and retaining the finite initial integral separately. -/
theorem integral_div_rpow_tendsto (g : ℝ → ℝ) (C q : ℝ) (hq : 0 < q)
    (hlocal : ∀ t : ℝ, 0 < t → IntervalIntegrable g volume 0 t)
    (hlim : Tendsto (fun t : ℝ => g t / t ^ (q - 1)) atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => (∫ s in (0 : ℝ)..t, g s) / t ^ q)
      atTop (𝓝 (C / q)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε * q / 2 := by positivity
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hlim (ε * q / 2) hδ
  let R : ℝ := max A 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hRA : A ≤ R := le_max_left _ _
  let D : ℝ := (∫ s in (0 : ℝ)..R, g s) - (C / q) * R ^ q
  have hD : Tendsto (fun t : ℝ => |D| / t ^ q) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hq)
  filter_upwards [eventually_ge_atTop R, eventually_gt_atTop (0 : ℝ),
    hD.eventually_lt_const (half_pos hε)] with t htR ht0 htD
  have htq : 0 < t ^ q := Real.rpow_pos_of_pos ht0 q
  have hgintegrable : IntervalIntegrable g volume R t :=
    (hlocal R hR).symm.trans (hlocal t ht0)
  have hpow : IntervalIntegrable (fun s : ℝ => s ^ (q - 1)) volume R t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpoint : ∀ s ∈ Ioc R t,
      |g s - C * s ^ (q - 1)| ≤ (ε * q / 2) * s ^ (q - 1) := by
    intro s hs
    have hs0 : 0 < s := hR.trans hs.1
    have hspow : 0 < s ^ (q - 1) := Real.rpow_pos_of_pos hs0 _
    have he : |g s / s ^ (q - 1) - C| < ε * q / 2 := by
      simpa only [Real.dist_eq] using hA s (hRA.trans hs.1.le)
    have heq : g s - C * s ^ (q - 1) =
        (g s / s ^ (q - 1) - C) * s ^ (q - 1) := by field_simp
    rw [heq, abs_mul, abs_of_pos hspow]
    exact mul_le_mul_of_nonneg_right he.le hspow.le
  have hprimitive : (∫ s in R..t, s ^ (q - 1)) = (t ^ q - R ^ q) / q := by
    rw [integral_rpow (Or.inl (show -1 < q - 1 by linarith))]
    simp
  have herror : |∫ s in R..t, g s - C * s ^ (q - 1)| ≤
      (ε / 2) * (t ^ q - R ^ q) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun s => g s - C * s ^ (q - 1)) htR
      (Eventually.of_forall (fun s hs => by simpa only [Real.norm_eq_abs] using hpoint s hs))
      (hpow.const_mul (ε * q / 2))
    rw [intervalIntegral.integral_const_mul, hprimitive] at hb
    have heq : (ε * q / 2) * ((t ^ q - R ^ q) / q) =
        (ε / 2) * (t ^ q - R ^ q) := by field_simp
    simpa only [Real.norm_eq_abs, heq] using hb
  have hsplit : (∫ s in (0 : ℝ)..t, g s) - (C / q) * t ^ q =
      D + ∫ s in R..t, g s - C * s ^ (q - 1) := by
    rw [intervalIntegral.integral_sub hgintegrable (hpow.const_mul C),
      intervalIntegral.integral_const_mul, hprimitive]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hlocal R hR) hgintegrable
    dsimp [D]
    rw [← hadd]
    ring
  have hnorm : |(∫ s in (0 : ℝ)..t, g s) - (C / q) * t ^ q| ≤
      |D| + (ε / 2) * t ^ q := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add le_rfl
      (herror.trans (by nlinarith [Real.rpow_nonneg hR.le q])))
  rw [Real.dist_eq]
  have heq : (∫ s in (0 : ℝ)..t, g s) / t ^ q - C / q =
      ((∫ s in (0 : ℝ)..t, g s) - (C / q) * t ^ q) / t ^ q := by field_simp
  rw [heq, abs_div, abs_of_pos htq]
  calc
    _ ≤ (|D| + (ε / 2) * t ^ q) / t ^ q :=
      div_le_div_of_nonneg_right hnorm htq.le
    _ = |D| / t ^ q + ε / 2 := by field_simp
    _ < ε := by linarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Finite measures make the weighted tail locally integrable, by monotonicity
of the tail function. -/
theorem intervalIntegrable_weighted_tail (f : Ω → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => s * μ.real {x | s < f x}) volume a b := by
  have hantitone : Antitone (fun s : ℝ => μ.real {x | s < f x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => lt_of_le_of_lt hst hx)
  exact hantitone.intervalIntegrable.continuousOn_mul continuousOn_id

omit [IsFiniteMeasure μ] in
/-- The tail assumption `μ(f>t) ∼ C t⁻²` is equivalent to convergence of the scaled tail to `C`. -/
theorem scaled_square_tail_tendsto (f : Ω → ℝ) (C : ℝ) (hC : 0 < C)
    (htail : Tendsto (fun t : ℝ => μ.real {x | t < f x} / (C * t ^ (-2 : ℝ)))
      atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => t ^ 2 * μ.real {x | t < f x}) atTop (𝓝 C) := by
  have h := htail.mul_const C
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht.le, Real.rpow_two]
  field_simp

/-- The Gaussian-boundary moment asymptotic, from the tail asymptotic and layer cake. `f²` need not
be integrable. -/
theorem truncated_second_moment_div_log_tendsto (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (C : ℝ) (hC : 0 < C)
    (htail : Tendsto (fun t : ℝ => μ.real {x | t < f x} / (C * t ^ (-2 : ℝ)))
      atTop (𝓝 1)) :
    Tendsto (fun t : ℝ =>
      (∫ x, {x | f x ≤ t}.indicator (fun x => f x ^ 2) x ∂μ) / Real.log t)
      atTop (𝓝 (2 * C)) := by
  have hscaled := scaled_square_tail_tendsto μ f C hC htail
  have hlog : Tendsto (fun t : ℝ =>
      (∫ s in (0 : ℝ)..t, s * μ.real {x | s < f x}) / Real.log t)
      atTop (𝓝 C) := by
    apply integral_div_log_tendsto _ C
      (fun t _ => intervalIntegrable_weighted_tail μ f 0 t)
    convert hscaled using 1
    funext t
    ring
  have hcorrection : Tendsto (fun t : ℝ =>
      t ^ 2 * μ.real {x | t < f x} / Real.log t) atTop (𝓝 0) :=
    hscaled.div_atTop Real.tendsto_log_atTop
  have h := (hlog.const_mul 2).sub hcorrection
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [truncated_second_moment μ f hf hf0 t ht]
  ring

omit [IsFiniteMeasure μ] in
/-- Scaling an arbitrary power tail removes its normalizing denominator. -/
theorem scaled_power_tail_tendsto (f : Ω → ℝ) (C α : ℝ) (hC : 0 < C)
    (htail : Tendsto (fun t : ℝ => μ.real {x | t < f x} / (C * t ^ (-α)))
      atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => t ^ α * μ.real {x | t < f x}) atTop (𝓝 C) := by
  have h := htail.mul_const C
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht.le]
  have hp : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
  field_simp

/-- The truncated second moment for a power-law tail below exponent two.
In the stable range `0<α<2`, this is the positive constant `α C/(2−α)`.
The proof needs only `α<2` and the stated tail limit. -/
theorem truncated_second_moment_div_rpow_tendsto (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (C α : ℝ) (hC : 0 < C)
    (hα : α < 2)
    (htail : Tendsto (fun t : ℝ => μ.real {x | t < f x} / (C * t ^ (-α)))
      atTop (𝓝 1)) :
    Tendsto (fun t : ℝ =>
      (∫ x, {x | f x ≤ t}.indicator (fun x => f x ^ 2) x ∂μ) / t ^ (2 - α))
      atTop (𝓝 (α * C / (2 - α))) := by
  have hscaled := scaled_power_tail_tendsto μ f C α hC htail
  have hmean : Tendsto (fun t : ℝ =>
      (∫ s in (0 : ℝ)..t, s * μ.real {x | s < f x}) / t ^ (2 - α))
      atTop (𝓝 (C / (2 - α))) := by
    apply integral_div_rpow_tendsto _ C (2 - α) (by linarith)
      (fun t _ => intervalIntegrable_weighted_tail μ f 0 t)
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [show 2 - α - 1 = 1 - α by ring, Real.rpow_sub ht, Real.rpow_one]
    have hp : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
    field_simp
  have hcorrection : Tendsto (fun t : ℝ =>
      t ^ 2 * μ.real {x | t < f x} / t ^ (2 - α)) atTop (𝓝 C) := by
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.rpow_sub ht, Real.rpow_two]
    have hp : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
    field_simp
  have h := (hmean.const_mul 2).sub hcorrection
  have hconstant : 2 * (C / (2 - α)) - C = α * C / (2 - α) := by
    have hne : 2 - α ≠ 0 := by linarith
    field_simp [hne]
    ring
  rw [hconstant] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [truncated_second_moment μ f hf hf0 t ht]
  ring

end ConditionedStableLaws
