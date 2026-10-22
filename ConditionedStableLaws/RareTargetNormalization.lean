import ConditionedStableLaws.PowerIntensity
import ConditionedStableLaws.Tails
import ConditionedStableLaws.ShrinkingTargets
import ConditionedStableLaws.EigenfunctionSupport

/-!
# Normalization of the rare-event intervals

The scalar tail asymptotic gives the interval intensities appearing in Step 1 of the point-process
proof. Singular-observable targets eventually lie in any neighborhood of the singularity, even with
its finite-value convention. Combined with the eigenfunction support theorem this gives the uniform
small-target conclusion needed there.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace ConditionedStableLaws
noncomputable section

theorem powerIntensity_real_interval {α a b : ℝ}
    (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) :
    (powerIntensity α).real {y | ENNReal.ofReal a < y.val ∧ y.val ≤ ENNReal.ofReal b} =
      a ^ (-α) - b ^ (-α) := by
  have hb : 0 < b := ha.trans_le hab
  have hset : {y : ExtremeState | ENNReal.ofReal a < y.val ∧ y.val ≤ ENNReal.ofReal b} =
      {y | ENNReal.ofReal a < y.val} \ {y | ENNReal.ofReal b < y.val} := by
    ext y
    simp only [mem_ofPred_eq, Set.mem_sdiff, not_lt]
  have hfinite : powerIntensity α {y | ENNReal.ofReal a < y.val} ≠ ∞ := by
    rw [powerIntensity_Ioi hα ha]
    exact ENNReal.ofReal_ne_top
  rw [hset, measureReal_sdiff (h₁ := hfinite)]
  · simp only [Measure.real, powerIntensity_Ioi hα ha, powerIntensity_Ioi hα hb,
      ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hb.le _)]
  · intro y hy
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hab) hy
  · exact measurableSet_lt measurable_const measurable_subtype_coe

variable {M : Type*} [MeasurableSpace M] {ν : Measure M} [IsFiniteMeasure ν]

/-- Subtracting the two strict tails yields the finite half-open interval
normalization, with any positive normalization tending through time. -/
theorem normalized_interval_limit {f : M → ℝ} (hf : Measurable f)
    {B : ℕ → ℝ} (hB : ∀ᶠ n in atTop, 0 ≤ B n) {α a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (htail : ∀ t : ℝ, 0 < t → Tendsto
      (fun n : ℕ => (n : ℝ) * ν.real {x | t * B n < f x}) atTop (𝓝 (t ^ (-α)))) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real {x | a * B n < f x ∧ f x ≤ b * B n})
      atTop (𝓝 (a ^ (-α) - b ^ (-α))) := by
  apply ((htail a ha).sub (htail b (ha.trans_le hab))).congr'
  filter_upwards [hB] with n hn
  have hset : {x | a * B n < f x ∧ f x ≤ b * B n} =
      {x | a * B n < f x} \ {x | b * B n < f x} := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_sdiff, not_lt]
  rw [hset, measureReal_sdiff]
  · ring
  · intro x hx
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hab hn) hx
  · exact measurableSet_lt measurable_const hf

/-- Tail regular variation gives the exact interval mass of the constructed Poisson intensity. -/
theorem normalized_interval_tendsto_powerIntensity {f : M → ℝ} (hf : Measurable f)
    {C α a b : ℝ} (hC : 0 < C) (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (C * t ^ (-α)))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real
      {x | a * powerScale C α n < f x ∧ f x ≤ b * powerScale C α n}) atTop
      (𝓝 ((powerIntensity α).real
        {y | ENNReal.ofReal a < y.val ∧ y.val ≤ ENNReal.ofReal b})) := by
  rw [powerIntensity_real_interval hα ha hab]
  apply normalized_interval_limit hf ?_ ha hab
    (fun t ht => normalized_tail_limit hC hα htail ht)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (powerScale_pos hC hn).le

variable [MetricSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Large singular observations eventually belong to every neighborhood of
the singularity; no assertion that the finite-valued center lies in the target
is needed. -/
theorem singular_targets_eventually_subset {x₀ : M} {β C α a : ℝ}
    (hβ : 0 < β) (hC : 0 < C) (hα : 0 < α) (ha : 0 < a)
    {V : Set M} (hV : V ∈ 𝓝 x₀) :
    ∀ᶠ n in atTop, {x | a * powerScale C α n < singularObservable x₀ β x} ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have ht : Tendsto (fun n : ℕ => a * powerScale C α n) atTop atTop :=
    (powerScale_tendsto_atTop hC hα).const_mul_atTop ha
  have hr : Tendsto (fun n : ℕ => (a * powerScale C α n) ^ (-1 / β)) atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (one_div_pos.mpr hβ)).comp ht
  filter_upwards [ht.eventually (eventually_gt_atTop 1),
    (tendsto_order.mp hr).2 ε hε] with n hn hnε
  rw [singularObservable_superlevel x₀ hβ hn]
  exact (sdiff_subset.trans (Metric.ball_subset_ball hnε.le)).trans hball

namespace StandingHypothesis
variable [CompactSpace M] {ρ : Measure M} {K : KilledKernel M}

/-- Step 1's uniform kernel smallness for the singular-observation target follows from the tail
ratio and normalized spectral data. Containment in the nonescaping set is derived from continuity at
the target center. -/
theorem HypothesisH.singular_targets_uniform_small
    (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel)
    (hcont : Continuous d.weight) (μ : Measure M)
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {x₀ : M} (hx₀ : d.weight x₀ ≠ 0) {β C α a : ℝ}
    (hβ : 0 < β) (hC : 0 < C) (hα : 0 < α) (ha : 0 < a)
    (htail : Tendsto (fun t : ℝ => (μ.withDensity d.weight).real
      {x | t < singularObservable x₀ β x} / (C * t ^ (-α))) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x : M,
      (K.kernel x {y | a * powerScale C α n < singularObservable x₀ β y}).toReal < ε := by
  have : IsProbabilityMeasure (μ.withDensity d.weight) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  have hopen : IsOpen d.liveSet := by
    rw [d.liveSet_eq_positive]
    exact isOpen_lt continuous_const hcont
  have hsub := singular_targets_eventually_subset hβ hC hα ha (hopen.mem_nhds hx₀)
  apply h.uniform_small_targets_of_eigenData d hcont μ hleft hnorm
    (fun n => {y | a * powerScale C α n < singularObservable x₀ β y})
    (fun _ => measurableSet_lt measurable_const (measurable_singularObservable x₀ β))
  · filter_upwards [hsub] with n hn
    exact hn.trans d.liveSet_subset_survivingSet
  · exact target_measure_tendsto_zero _ (normalized_tail_limit hC hα htail ha)

end StandingHypothesis

end
end ConditionedStableLaws
