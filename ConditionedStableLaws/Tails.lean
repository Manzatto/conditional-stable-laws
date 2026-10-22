import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-!
The singular observable and the stable normalization from a tail asymptotic.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ConditionedStableLaws

noncomputable section

open Classical

variable {M : Type*} [MetricSpace M]

/-- The singular observable `d(x, x₀)^{-β}`, with the value `1` at `x₀`. -/
def singularObservable (x₀ : M) (β : ℝ) (x : M) : ℝ :=
  if x = x₀ then 1 else dist x x₀ ^ (-β)

@[simp] theorem singularObservable_at_center (x₀ : M) (β : ℝ) :
    singularObservable x₀ β x₀ = 1 := by
  simp [singularObservable]

theorem singularObservable_pos (x₀ : M) (β : ℝ) (x : M) :
    0 < singularObservable x₀ β x := by
  by_cases h : x = x₀
  · simp [singularObservable, h]
  · simpa [singularObservable, h] using
      Real.rpow_pos_of_pos (dist_pos.mpr h) (-β)

@[fun_prop]
theorem measurable_singularObservable [MeasurableSpace M] [BorelSpace M]
    (x₀ : M) (β : ℝ) : Measurable (singularObservable x₀ β) := by
  unfold singularObservable
  exact Measurable.ite (measurableSet_singleton x₀) measurable_const
    ((continuous_id.dist continuous_const).measurable.pow_const (-β))

/-- Exact strict superlevel set, including the exceptional value at the centre. -/
theorem singularObservable_superlevel (x₀ : M) {β t : ℝ}
    (hβ : 0 < β) (ht : 1 < t) :
    {x | t < singularObservable x₀ β x} =
      Metric.ball x₀ (t ^ (-1 / β)) \ {x₀} := by
  ext x
  by_cases hx : x = x₀
  · subst x
    simp [singularObservable, not_lt.mpr ht.le]
  · have hd : 0 < dist x x₀ := dist_pos.mpr hx
    have he : (-β)⁻¹ = -1 / β := by simp [div_eq_mul_inv]
    simp only [singularObservable, ↓reduceIte, mem_ofPred_eq, Set.mem_sdiff,
      Metric.mem_ball, mem_singleton_iff, hx, not_false_eq_true, and_true]
    rw [← he]
    exact (Real.lt_rpow_inv_iff_of_neg hd (lt_trans zero_lt_one ht) (neg_neg_of_pos hβ)).symm

/-- Stable normalization `(C n)^{1/α}`. -/
def powerScale (C α : ℝ) (n : ℕ) : ℝ := (C * (n : ℝ)) ^ (1 / α)

theorem powerScale_pos {C α : ℝ} (hC : 0 < C) {n : ℕ} (hn : 0 < n) :
    0 < powerScale C α n :=
  Real.rpow_pos_of_pos (mul_pos hC (Nat.cast_pos.mpr hn)) _

theorem powerScale_rpow {C α : ℝ} (hC : 0 ≤ C) (hα : α ≠ 0) (n : ℕ) :
    powerScale C α n ^ α = C * (n : ℝ) := by
  rw [powerScale, ← Real.rpow_mul (mul_nonneg hC (Nat.cast_nonneg n))]
  simp [hα]

theorem powerScale_tendsto_atTop {C α : ℝ} (hC : 0 < C) (hα : 0 < α) :
    Tendsto (powerScale C α) atTop atTop := by
  exact (tendsto_rpow_atTop (one_div_pos.mpr hα)).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop hC)

theorem scaled_power_identity {C α u : ℝ} (hC : 0 < C) (hα : 0 < α)
    (hu : 0 < u) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (C * (u * powerScale C α n) ^ (-α)) = u ^ (-α) := by
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  rw [Real.mul_rpow hu.le (le_of_lt (powerScale_pos hC hn)),
    Real.rpow_neg (le_of_lt (powerScale_pos hC hn)), powerScale_rpow hC.le hα.ne']
  field_simp

/-- Tail asymptotics give the exact stable normalization. `T` may in particular be `fun t => ν.real
{x | t < f x}`. -/
theorem normalized_tail_limit {T : ℝ → ℝ} {C α : ℝ}
    (hC : 0 < C) (hα : 0 < α)
    (hT : Tendsto (fun t => T t / (C * t ^ (-α))) atTop (𝓝 1))
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * T (u * powerScale C α n)) atTop
      (𝓝 (u ^ (-α))) := by
  have harg : Tendsto (fun n => u * powerScale C α n) atTop atTop :=
    (powerScale_tendsto_atTop hC hα).const_mul_atTop hu
  have h := (hT.comp harg).mul_const (u ^ (-α))
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hb : 0 < C * (u * powerScale C α n) ^ (-α) :=
    mul_pos hC (Real.rpow_pos_of_pos (mul_pos hu (powerScale_pos hC hn)) _)
  simp only [Function.comp_apply]
  rw [← scaled_power_identity hC hα hu hn]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (mul_pos hu (powerScale_pos hC hn)) (-α))]

/-- The local volume regularity condition, with a specified constant. -/
def IsRegularAt [MeasurableSpace M] (ρ : Measure M) (x₀ : M) (d C : ℝ) : Prop :=
  0 < d ∧ 0 < C ∧
    Tendsto (fun r : ℝ => ρ.real (Metric.ball x₀ r) / r ^ d) (𝓝[>] 0) (𝓝 C)

/-- The regular-point predicate with an existentially quantified constant. -/
def IsRegularPoint [MeasurableSpace M] (ρ : Measure M) (x₀ : M) (d : ℝ) : Prop :=
  ∃ C : ℝ, IsRegularAt ρ x₀ d C

/-- Positive-dimensional regular points have zero singleton mass. -/
theorem IsRegularAt.measure_singleton_eq_zero [MeasurableSpace M]
    {ρ : Measure M} [IsFiniteMeasure ρ] {x₀ : M} {d C : ℝ}
    (h : IsRegularAt ρ x₀ d C) : ρ {x₀} = 0 := by
  obtain ⟨hd, _, hlim⟩ := h
  have hpow : Tendsto (fun r : ℝ => r ^ d) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow hd.ne'] using
      (Real.continuousAt_rpow_const 0 d (Or.inr hd.le)).tendsto.mono_left
        nhdsWithin_le_nhds
  have hball : Tendsto (fun r : ℝ => ρ.real (Metric.ball x₀ r)) (𝓝[>] 0) (𝓝 0) := by
    have hm := hlim.mul hpow
    simp only [mul_zero] at hm
    apply hm.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hr d))
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto hball
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact measureReal_mono (singleton_subset_iff.mpr (Metric.mem_ball_self hr))

/-- Nullity of the centre justifies the ball representation of the tail. -/
theorem singularObservable_tail_eq_ball [MeasurableSpace M]
    {ν : Measure M} [IsFiniteMeasure ν] {x₀ : M} {β t : ℝ}
    (hβ : 0 < β) (ht : 1 < t) (hnull : ν {x₀} = 0) :
    ν.real {x | t < singularObservable x₀ β x} =
      ν.real (Metric.ball x₀ (t ^ (-1 / β))) := by
  rw [singularObservable_superlevel x₀ hβ ht]
  exact measureReal_sdiff_null ((measureReal_eq_zero_iff).mpr hnull)

/-- A local ball asymptotic becomes a power tail under the singular observable. -/
theorem tail_asymptotic_of_regular [MeasurableSpace M]
    {ν : Measure M} [IsFiniteMeasure ν] {x₀ : M} {β d C : ℝ}
    (hβ : 0 < β) (hreg : IsRegularAt ν x₀ d C) :
    Tendsto (fun t : ℝ => ν.real {x | t < singularObservable x₀ β x} /
      (C * t ^ (-(d / β)))) atTop (𝓝 1) := by
  have hC := hreg.2.1
  have hr0 : Tendsto (fun t : ℝ => t ^ (-1 / β)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (one_div_pos.mpr hβ)
  have hr : Tendsto (fun t : ℝ => t ^ (-1 / β)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hr0, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact Real.rpow_pos_of_pos ht _
  have h := (hreg.2.2.comp hr).div_const C
  rw [div_self hC.ne'] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  simp only [Function.comp_apply]
  rw [singularObservable_tail_eq_ball hβ ht hreg.measure_singleton_eq_zero]
  rw [← Real.rpow_mul (by linarith : 0 ≤ t)]
  have he : (-1 / β) * d = -(d / β) := by ring
  rw [he]
  ring

theorem singularObservable_normalized_tail [MeasurableSpace M]
    {ν : Measure M} [IsFiniteMeasure ν] {x₀ : M} {β d C : ℝ}
    (hβ : 0 < β) (hreg : IsRegularAt ν x₀ d C) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real
      {x | u * powerScale C (d / β) n < singularObservable x₀ β x}) atTop
      (𝓝 (u ^ (-(d / β)))) :=
  normalized_tail_limit hreg.2.1 (div_pos hreg.1 hβ)
    (tail_asymptotic_of_regular hβ hreg) hu

/-- The deterministic remainder in the compensated-small-jump bound vanishes precisely in the range
`α < 2`. -/
theorem nat_div_powerScale_sq_tendsto_zero {C α : ℝ}
    (hC : 0 < C) (hα : 0 < α) (hα2 : α < 2) :
    Tendsto (fun n : ℕ => (n : ℝ) / (powerScale C α n) ^ 2) atTop (𝓝 0) := by
  have he : 0 < 2 / α - 1 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hα).mpr
    simpa using hα2
  have h := ((tendsto_rpow_neg_atTop he).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (C ^ (2 / α))⁻¹
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have he' : -(2 / α - 1) = 1 - 2 / α := by ring
  simp only [Function.comp_apply]
  rw [he', Real.rpow_sub hn', Real.rpow_one, powerScale,
    ← Real.rpow_two, ← Real.rpow_mul (mul_pos hC hn').le]
  have hexp : (1 / α) * 2 = 2 / α := by ring
  rw [hexp, Real.mul_rpow hC.le hn'.le]
  ring

end
end ConditionedStableLaws
