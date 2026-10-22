import ConditionedStableLaws.QProcessCesaro

/-!
# A probability reference for arbitrary normalized invariant eigen-data

The spectral survival normalization fixes the pairing with a probability eigenmeasure supplied by H.
An arbitrary measure appearing in the LLN statement need not itself be a probability measure.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.QProcessReference

noncomputable section

open StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

theorem integral_weight_eq_one (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (s : SurvivalGapData h d)
    (μ : Measure M) [IsProbabilityMeasure μ] (hleft : K.kernel ∘ₘ μ = d.rate • μ) :
    (∫⁻ x, d.weight x ∂μ) = 1 := by
  set F : ℕ → M → ℝ≥0∞ := fun n x => (d.rate⁻¹)^n * (K.kernel^n) x univ
  have hFm (n : ℕ) : Measurable (F n) := measurable_const.mul ((K.kernel^n).measurable_coe MeasurableSet.univ)
  have hFt (n : ℕ) (x : M) : F n x ≠ ∞ := by
    have := killedKernel_power_isFinite K n
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 d.rate_ne_zero)) (measure_ne_top _ _)
  have hFint (n : ℕ) : (∫⁻ x, F n x ∂μ) = 1 := by
    dsimp only [F]
    rw [lintegral_const_mul _ ((K.kernel^n).measurable_coe MeasurableSet.univ)]
    have hk := RefinedLLN.kernel_pow_comp hleft n
    have hi := KernelLp.lintegral_lintegral_kernel hk (measurable_const : Measurable (fun _ : M => (1 : ℝ≥0∞)))
    simp only [lintegral_const, one_mul, measure_univ, mul_one] at hi
    rw [hi, ← mul_pow, ENNReal.inv_mul_cancel d.rate_ne_zero d.rate_ne_top, one_pow]
  have hreal (n : ℕ) : (∫ x, (F n x).toReal ∂μ) = 1 := by
    rw [integral_toReal (hFm n).aemeasurable (ae_of_all _ fun x => (hFt n x).lt_top), hFint n,
      ENNReal.toReal_one]
  have hlim : Tendsto (fun n => ∫ x, (F n x).toReal ∂μ) atTop
      (𝓝 (∫ x, (d.weight x).toReal ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => s.survivalBound)
      (fun n => (hFm n).ennreal_toReal.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact s.normalized_survival_real_le n x)
    exact ae_of_all _ fun x => s.normalized_survival_tendstoUniformly.tendsto_at x
  have heq : (∫ x, (d.weight x).toReal ∂μ) = 1 :=
    tendsto_nhds_unique hlim (by simpa only [hreal] using tendsto_const_nhds)
  rw [← ENNReal.toReal_eq_one_iff]
  rw [← integral_toReal d.measurable_weight.aemeasurable
    (ae_of_all _ fun x => (d.weight_ne_top x).lt_top)]
  exact heq

theorem exists_probability_reference (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (s : SurvivalGapData h d)
    (hne : ∃ x, d.weight x ≠ 0) :
    ∃ μ : ProbabilityMeasure M,
      K.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) ∧
      (∫⁻ x, d.weight x ∂(μ : Measure M)) = 1 := by
  obtain ⟨e, _, _, _, μ, hleft, _⟩ := h.exists_normalized_eigenData
  have hr := h.left_eigenvalue_eq d s.continuous_weight hne (μ : Measure M)
    e.rate_ne_zero e.rate_ne_top hleft
  rw [hr] at hleft
  exact ⟨μ, hleft, integral_weight_eq_one h d s μ hleft⟩

/-- Bounded pointwise Cesàro limits identify every invariant probability. -/
theorem invariant_probability_eq (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    (ν : Measure d.State) [IsProbabilityMeasure ν] (hinv : d.kernel ∘ₘ ν = ν) :
    ν = (μ.withDensity d.weight).comap (Subtype.val : d.State → M) := by
  set ν₀ := (μ.withDensity d.weight).comap (Subtype.val : d.State → M)
  have : IsProbabilityMeasure ν₀ := d.isProbabilityMeasure_weightedMeasure μ hnorm
  ext A hA
  let v : d.State → ℝ := A.indicator (fun _ => 1)
  have hvm : Measurable v := measurable_const.indicator hA
  have hvb (x : d.State) : |v x| ≤ 1 := by
    simp only [v]
    by_cases hx : x ∈ A <;> simp [hx]
  let f : M → ℝ := Function.extend (Subtype.val : d.State → M) v (fun _ => 0)
  have hfm : Measurable f := d.live_embedding.measurable_extend hvm measurable_const
  have hfval (x : d.State) : f x.val = v x := Subtype.val_injective.extend_apply _ _ x
  have hfb (x : M) : |f x| ≤ 1 := by
    by_cases hx : ∃ y : d.State, y.val = x
    · obtain ⟨y, rfl⟩ := hx
      rw [hfval]
      exact hvb y
    · change |Function.extend (Subtype.val : d.State → M) v (fun _ => 0) x| ≤ 1
      rw [Function.extend_apply' _ _ _ hx]
      norm_num
  have hvi : Integrable v ν := Integrable.of_bound hvm.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hvb x)
  set Av : ℕ → d.State → ℝ := fun n x => (n : ℝ)⁻¹ *
    ∑ i ∈ Finset.range n, ∫ y, v y ∂(d.kernel ^ i) x
  have hki (i : ℕ) : Integrable (KernelLp.kint (d.kernel^i) v) ν :=
    KernelMaximal.integrable_kint (KernelMaximal.invariant_pow hinv i) hvi
  have hkb (i : ℕ) (x : d.State) : |∫ y, v y ∂(d.kernel^i) x| ≤ 1 := by
    have := MarkovPairs.isMarkovKernel_pow d.kernel i
    have hb := norm_integral_le_of_norm_le_const (μ := (d.kernel^i) x) (f := v) (C := 1)
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hvb y)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
  have hAm (n : ℕ) : Measurable (Av n) := measurable_const.mul
    (Finset.measurable_sum _ fun i _ => (hvm.stronglyMeasurable.integral_kernel).measurable)
  have hAb (n : ℕ) (x : d.State) : |Av n x| ≤ 1 :=
    QProcessCesaro.abs_average_le zero_le_one (fun i => hkb i x) n id
  have hpoint (x : d.State) : Tendsto (fun n => Av n x) atTop (𝓝 (∫ y, v y ∂ν₀)) := by
    have hh := QProcessCesaro.bounded_kernel_cesaro h d hc μ hleft hnorm hfm hfb x
    have hm : (∫ y, f y ∂μ.withDensity d.weight) = ∫ y, v y ∂ν₀ := by
      rw [← RefinedLLN.integral_live d μ f]
      exact integral_congr_ae (ae_of_all _ hfval)
    simpa only [hfval, hm] using hh
  have hd : Tendsto (fun n => ∫ x, Av n x ∂ν) atTop (𝓝 (∫ y, v y ∂ν₀)) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := Av) (f := fun _ => ∫ y, v y ∂ν₀) (fun _ => (1 : ℝ))
      (fun n => (hAm n).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hAb n x)
      (ae_of_all _ hpoint)
    simpa using hh
  have hconst : ∀ᶠ n in atTop, (∫ x, Av n x ∂ν) = ∫ y, v y ∂ν := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp only [Av]
    rw [integral_const_mul]
    change (n : ℝ)⁻¹ * (∫ x, ∑ i ∈ Finset.range n, KernelLp.kint (d.kernel^i) v x ∂ν) = _
    rw [integral_finsetSum _ (fun i _ => hki i)]
    have heq (i : ℕ) : (∫ x, KernelLp.kint (d.kernel^i) v x ∂ν) = ∫ y, v y ∂ν := by
      have hi := KernelLp.integral_kint
        (show (d.kernel^i) ∘ₘ ν = (1 : ℝ≥0∞) • ν by
          simpa using KernelMaximal.invariant_pow hinv i) ENNReal.one_ne_top hvi
      simpa using hi
    change (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (∫ x, KernelLp.kint (d.kernel^i) v x ∂ν) = _
    simp only [heq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_mul]
  have hmean : (∫ y, v y ∂ν) = ∫ y, v y ∂ν₀ :=
    (tendsto_nhds_unique (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hconst)) hd)
  have hr : ν.real A = ν₀.real A := by
    simpa only [v, integral_indicator_const _ hA, smul_eq_mul, mul_one] using hmean
  rw [← ofReal_measureReal (μ := ν), ← ofReal_measureReal (μ := ν₀), hr]

end

end ConditionedStableLaws.QProcessReference
