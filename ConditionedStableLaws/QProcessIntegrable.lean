import ConditionedStableLaws.QProcessReference

/-! # The Q-process law of large numbers for observables in L1(nu) -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.QProcessIntegrable

noncomputable section

open StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem ae_integrable_coordinates (P : Kernel M M) [IsMarkovKernel P]
    (ν : Measure M) [IsProbabilityMeasure ν] (hinv : P ∘ₘ ν = ν)
    {g : M → ℝ} (hg : Integrable g ν) :
    ∀ᵐ x ∂ν, ∀ i : ℕ, Integrable (fun ω : ℕ → M => g (ω i)) (QProcessLimit.pathMeasure P x) := by
  have hi := ae_all_iff.2 fun i => Measure.ae_integrable_of_integrable_comp
    ((KernelMaximal.invariant_pow hinv i).symm ▸ hg)
  filter_upwards [hi] with x hx
  intro i
  have hm : Integrable g ((QProcessLimit.pathMeasure P x).map (fun ω => ω i)) := by
    rw [MarkovPairs.map_single]
    exact hx i
  exact hm.comp_measurable (measurable_pi_apply i)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem integral_average (d : DoobTransform.EigenData K.kernel) (x : d.State)
    {f : M → ℝ} (hf : Measurable f)
    (hi : ∀ i : ℕ, Integrable (fun ω : ℕ → d.State => f (ω i).val)
      (QProcessLimit.pathMeasure d.kernel x)) (n : ℕ) :
    (∫ ω, Cited.doobAverage d f n ω ∂QProcessLimit.pathMeasure d.kernel x) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ y, f y.val ∂(d.kernel^i) x := by
  unfold Cited.doobAverage
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => MarkovPairs.integral_single d.kernel x i
    (hf.comp measurable_subtype_coe)

theorem lln_mean (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {f : M → ℝ} (hf : Measurable f) (hfi : Integrable f (μ.withDensity d.weight)) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M),
      (∀ n, Integrable (fun ω => Cited.doobAverage d f n ω - ∫ y, f y ∂μ.withDensity d.weight)
        (QProcessLimit.pathMeasure d.kernel x)) ∧
      Tendsto (fun n => ∫ ω, |Cited.doobAverage d f n ω - ∫ y, f y ∂μ.withDensity d.weight|
        ∂QProcessLimit.pathMeasure d.kernel x) atTop (𝓝 0) := by
  set μ' := μ.withDensity d.weight
  set ν := μ'.comap (Subtype.val : d.State → M)
  have : IsProbabilityMeasure ν := d.isProbabilityMeasure_weightedMeasure μ hnorm
  set Γ := ∫ y, f y ∂μ'
  set v : ℕ → M → ℝ := fun k => {y | |f y| ≤ (k : ℝ)}.indicator f
  set t : ℕ → M → ℝ := fun k => {y | |f y| ≤ (k : ℝ)}ᶜ.indicator (fun y => |f y|)
  have hSm (k : ℕ) : MeasurableSet {y | |f y| ≤ (k : ℝ)} :=
    measurableSet_le hf.norm measurable_const
  have hvm (k : ℕ) : Measurable (v k) := hf.indicator (hSm k)
  have htm (k : ℕ) : Measurable (t k) := hf.norm.indicator (hSm k).compl
  have ht0 (k : ℕ) (y : M) : 0 ≤ t k y := indicator_nonneg (fun _ _ => abs_nonneg _) y
  have htb (k : ℕ) (y : M) : t k y ≤ |f y| := by
    by_cases hy : y ∈ {y | |f y| ≤ (k : ℝ)}ᶜ
    · simp [t, hy]
    · simp [t, hy, abs_nonneg]
  have hvb (k : ℕ) (y : M) : |v k y| ≤ k := by
    by_cases hy : y ∈ {y | |f y| ≤ (k : ℝ)}
    · simp only [v, indicator_of_mem hy]
      exact hy
    · simp [v, hy]
  have hti (k : ℕ) : Integrable (t k) μ' := hfi.abs.indicator (hSm k).compl
  have hvi (k : ℕ) : Integrable (v k) μ' := hfi.indicator (hSm k)
  have htail : Tendsto (fun k => ∫ y, t k y ∂μ') atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := μ') (F := t)
      (f := fun _ => (0 : ℝ)) (fun y => |f y|)
      (fun k => (htm k).aestronglyMeasurable) hfi.abs
      (fun k => ae_of_all _ fun y => by rw [Real.norm_of_nonneg (ht0 k y)]; exact htb k y)
      (ae_of_all _ fun y => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈|f y|⌉₊] with k hk
        have hy : |f y| ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
        simp [t, hy])
    simpa using hh
  have hces : ∀ᵐ x ∂ν, ∀ k : ℕ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ y, t k y.val ∂(d.kernel^i) x) atTop (𝓝 (∫ y, t k y ∂μ')) := by
    apply ae_all_iff.2
    intro k
    have hh := QProcessCesaro.nonneg_kernel_cesaro h d hc μ hleft hnorm
      (g := fun y : d.State => t k y.val) ((htm k).comp measurable_subtype_coe)
      (RefinedLLN.integrable_live d μ (hti k)) (fun y => ht0 k y.val)
    rw [RefinedLLN.integral_live] at hh
    exact hh
  have hcoord := ae_integrable_coordinates d.kernel ν (d.invariant_weightedMeasure μ hleft)
    (RefinedLLN.integrable_live d μ hfi)
  filter_upwards [hces, hcoord] with x hx hix
  set Q := QProcessLimit.pathMeasure d.kernel x
  have hi_dom {g : M → ℝ} (hgm : Measurable g) (hgb : ∀ y, |g y| ≤ |f y|) (i : ℕ) :
      Integrable (fun ω : ℕ → d.State => g (ω i).val) Q := by
    apply (hix i).norm.mono'
      (hgm.comp (measurable_subtype_coe.comp (measurable_pi_apply i))).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hgb (ω i).val
  have hi_t (k i : ℕ) : Integrable (fun ω : ℕ → d.State => t k (ω i).val) Q :=
    hi_dom (htm k) (fun y => by rw [abs_of_nonneg (ht0 k y)]; exact htb k y) i
  have hi_v (k i : ℕ) : Integrable (fun ω : ℕ → d.State => v k (ω i).val) Q := by
    apply hi_dom (hvm k) _ i
    intro y
    by_cases hy : y ∈ {y | |f y| ≤ (k : ℝ)} <;> simp [v, hy, abs_nonneg]
  have hi_avg {g : M → ℝ} (hi : ∀ i, Integrable (fun ω : ℕ → d.State => g (ω i).val) Q)
      (n : ℕ) : Integrable (Cited.doobAverage d g n) Q :=
    (integrable_finsetSum _ fun i _ => hi i).const_mul _
  have hAi (n : ℕ) : Integrable (Cited.doobAverage d f n) Q := hi_avg hix n
  have hAti (k n : ℕ) : Integrable (Cited.doobAverage d (t k) n) Q := hi_avg (hi_t k) n
  have hAvint (k n : ℕ) : Integrable (Cited.doobAverage d (v k) n) Q := hi_avg (hi_v k) n
  have hpt (k n : ℕ) (ω : ℕ → d.State) :
      |Cited.doobAverage d f n ω - Γ| ≤
        |Cited.doobAverage d (v k) n ω - ∫ y, v k y ∂μ'| +
          Cited.doobAverage d (t k) n ω + ∫ y, t k y ∂μ' := by
    have hdiff (y : M) : |f y - v k y| = t k y := by
      by_cases hy : y ∈ {y | |f y| ≤ (k : ℝ)} <;> simp [v, t, hy]
    have hmean : |Γ - ∫ y, v k y ∂μ'| ≤ ∫ y, t k y ∂μ' := by
      rw [← integral_sub hfi (hvi k)]
      simpa only [hdiff] using (abs_integral_le_integral_abs (μ := μ') (f := fun y => f y - v k y))
    have hsum : |Cited.doobAverage d f n ω - Cited.doobAverage d (v k) n ω| ≤
        Cited.doobAverage d (t k) n ω := by
      unfold Cited.doobAverage
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
      exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans_eq
        (Finset.sum_congr rfl fun i _ => hdiff _)) (inv_nonneg.2 (Nat.cast_nonneg n))
    have hh := abs_add_le
      ((Cited.doobAverage d f n ω - Cited.doobAverage d (v k) n ω) +
        (Cited.doobAverage d (v k) n ω - ∫ y, v k y ∂μ'))
      ((∫ y, v k y ∂μ') - Γ)
    have ht := abs_add_le (Cited.doobAverage d f n ω - Cited.doobAverage d (v k) n ω)
      (Cited.doobAverage d (v k) n ω - ∫ y, v k y ∂μ')
    have heq : (Cited.doobAverage d f n ω - Cited.doobAverage d (v k) n ω) +
        (Cited.doobAverage d (v k) n ω - ∫ y, v k y ∂μ') + ((∫ y, v k y ∂μ') - Γ) =
        Cited.doobAverage d f n ω - Γ := by ring
    rw [heq, abs_sub_comm (∫ y, v k y ∂μ') Γ] at hh
    linarith
  refine ⟨fun n => (hAi n).sub (integrable_const Γ), ?_⟩
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨k, hk⟩ := ((tendsto_order.1 htail).2 (ε / 4) (by linarith)).exists
  have hvmn : Tendsto (fun n => ∫ ω, |Cited.doobAverage d (v k) n ω - ∫ y, v k y ∂μ'| ∂Q)
      atTop (𝓝 0) := by
    apply BoundedConvergence.tendsto_integral_abs_of_bounded_in_probability
      (fun _ => Q) (fun n ω => Cited.doobAverage d (v k) n ω - ∫ y, v k y ∂μ')
      (fun n => (RefinedLLN.measurable_doobAverage d (hvm k) n).sub measurable_const)
      (k + |∫ y, v k y ∂μ'|)
    · intro n
      exact ae_of_all _ fun ω => (abs_sub _ _).trans (add_le_add
        (QProcessCesaro.abs_average_le (Nat.cast_nonneg k) (fun y : d.State => hvb k y.val) n ω) le_rfl)
    · intro δ hδ
      have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (h.qProcess_lln d hc μ hleft hnorm (hvm k) (hvb k) x δ hδ)
      rw [ENNReal.toReal_zero] at ht
      convert ht using 1
      funext n
      rfl
  have htmn : Tendsto (fun n => ∫ ω, Cited.doobAverage d (t k) n ω ∂Q) atTop
      (𝓝 (∫ y, t k y ∂μ')) :=
    (hx k).congr (fun n => (integral_average d x (htm k) (hi_t k) n).symm)
  filter_upwards [(tendsto_order.1 hvmn).2 (ε / 4) (by linarith),
    (tendsto_order.1 htmn).2 ((∫ y, t k y ∂μ') + ε / 4) (by linarith)] with n hn htn
  have hi := integral_mono_ae ((hAi n).sub (integrable_const Γ)).abs
    (((hAvint k n).sub (integrable_const _)).abs.add (hAti k n) |>.add (integrable_const _))
    (ae_of_all _ (hpt k n))
  rw [integral_add' (((hAvint k n).sub (integrable_const _)).abs.add (hAti k n)) (integrable_const _),
    integral_add' ((hAvint k n).sub (integrable_const _)).abs (hAti k n)] at hi
  simp only [Pi.sub_apply, integral_const, probReal_univ, one_smul] at hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  linarith

end

end ConditionedStableLaws.QProcessIntegrable
