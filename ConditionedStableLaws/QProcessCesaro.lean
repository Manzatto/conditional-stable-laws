import ConditionedStableLaws.QProcessVariance
import ConditionedStableLaws.KernelCesaro
import ConditionedStableLaws.BoundedConvergence

/-!
# Pointwise Cesàro convergence for the Doob kernel

Bounded observables use the Q-process variance bound. The invariant measure and the positive-kernel
maximal inequality extend this to nonnegative integrable observables.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.QProcessCesaro

noncomputable section

open StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

theorem abs_average_le {X : Type*} {v : X → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |v x| ≤ B) (n : ℕ) (ω : ℕ → X) :
    |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, v (ω i)| ≤ B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hB0
  · have hnp : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hnp.le)]
    calc
      (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, v (ω i)| ≤
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |v (ω i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hnp.le)
      _ ≤ (n : ℝ)⁻¹ * ∑ _i ∈ Finset.range n, B := by
        gcongr with i _
        exact hB _
      _ = B := by simp [hnp.ne']

theorem bounded_kernel_cesaro (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {f : M → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : d.State) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      ∫ y, f y.val ∂(d.kernel ^ i) x) atTop (𝓝 (∫ y, f y ∂μ.withDensity d.weight)) := by
  set Γ := ∫ y, f y ∂μ.withDensity d.weight
  set Q := QProcessLimit.pathMeasure d.kernel x
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x.val)
  have hAm (n : ℕ) : Measurable (Cited.doobAverage d f n) :=
    RefinedLLN.measurable_doobAverage d hf n
  have hAb (n : ℕ) (ω : ℕ → d.State) : |Cited.doobAverage d f n ω| ≤ B :=
    abs_average_le hB0 (fun y : d.State => hB y.val) n ω
  have hAi (n : ℕ) : Integrable (Cited.doobAverage d f n) Q :=
    Integrable.of_bound (hAm n).aestronglyMeasurable B
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hAb n ω)
  have hprob := h.qProcess_lln d hc μ hleft hnorm hf hB x
  have hmean : Tendsto (fun n => ∫ ω, |Cited.doobAverage d f n ω - Γ| ∂Q)
      atTop (𝓝 0) := by
    apply BoundedConvergence.tendsto_integral_abs_of_bounded_in_probability
      (fun _ => Q) (fun n ω => Cited.doobAverage d f n ω - Γ)
      (fun n => (hAm n).sub_const Γ) (B + |Γ|)
    · intro n
      exact ae_of_all _ fun ω => (abs_sub _ _).trans (add_le_add (hAb n ω) le_rfl)
    · intro ε hε
      have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hprob ε hε)
      rw [ENNReal.toReal_zero] at ht
      convert ht using 1
      funext n
      rfl
  have heq (n : ℕ) : (∫ ω, Cited.doobAverage d f n ω ∂Q) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ y, f y.val ∂(d.kernel ^ i) x := by
    have hi (i : ℕ) : Integrable (fun ω : ℕ → d.State => f (ω i).val) Q :=
      Integrable.of_bound
        (hf.comp (measurable_subtype_coe.comp (measurable_pi_apply i))).aestronglyMeasurable B
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB _)
    unfold Cited.doobAverage
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => MarkovPairs.integral_single d.kernel x i
      (hf.comp measurable_subtype_coe)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [(tendsto_order.1 hmean).2 ε hε] with n hn
  rw [Real.dist_eq, ← heq n]
  have hb : |(∫ ω, Cited.doobAverage d f n ω ∂Q) - Γ| ≤
      ∫ ω, |Cited.doobAverage d f n ω - Γ| ∂Q := by
    have hΓ : (∫ _ : ℕ → d.State, Γ ∂Q) = Γ := by simp
    conv_lhs => rw [← hΓ]
    rw [← integral_sub (hAi n) (integrable_const Γ)]
    exact abs_integral_le_integral_abs
  exact hb.trans_lt hn

theorem nonneg_kernel_cesaro (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {g : d.State → ℝ} (hg : Measurable g)
    (hgi : Integrable g ((μ.withDensity d.weight).comap (Subtype.val : d.State → M)))
    (hg0 : ∀ x, 0 ≤ g x) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ y, g y ∂(d.kernel ^ i) x)
        atTop (𝓝 (∫ y, g y ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M))) := by
  let ν := (μ.withDensity d.weight).comap (Subtype.val : d.State → M)
  have : IsProbabilityMeasure ν := d.isProbabilityMeasure_weightedMeasure μ hnorm
  apply KernelCesaro.tendsto_ae_nonneg_kernel_sum (d.invariant_weightedMeasure μ hleft) ?_ hg hgi hg0
  intro v hvm hvb
  obtain ⟨B, hB⟩ := hvb
  let f : M → ℝ := Function.extend (Subtype.val : d.State → M) v (fun _ => 0)
  have hfm : Measurable f := d.live_embedding.measurable_extend hvm measurable_const
  have hfval (y : d.State) : f y.val = v y :=
    Subtype.val_injective.extend_apply _ _ y
  have hB0 : 0 ≤ B := by
    have : Nonempty d.State := nonempty_of_isProbabilityMeasure ν
    obtain ⟨y⟩ := this
    exact (abs_nonneg _).trans (hB y)
  have hfb (y : M) : |f y| ≤ B := by
    by_cases hy : ∃ z : d.State, z.val = y
    · obtain ⟨z, rfl⟩ := hy
      rw [hfval]
      exact hB z
    · change |Function.extend (Subtype.val : d.State → M) v (fun _ => 0) y| ≤ B
      rw [Function.extend_apply' _ _ _ hy, abs_zero]
      exact hB0
  have hmean : (∫ y, f y ∂μ.withDensity d.weight) = ∫ y, v y ∂ν := by
    rw [← RefinedLLN.integral_live d μ f]
    exact integral_congr_ae (ae_of_all _ hfval)
  apply ae_of_all
  intro x
  have hh := bounded_kernel_cesaro h d hc μ hleft hnorm hfm hfb x
  simpa only [hfval, hmean] using hh

end

end ConditionedStableLaws.QProcessCesaro
