import ConditionedStableLaws.QProcessIntegrable
import ConditionedStableLaws.DoobHistoryChange
import ConditionedStableLaws.WeightedProbabilityTransfer

/-! # Endpoint estimates for transferring Q-process probabilities -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.QProcessEndpoint

noncomputable section
open StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

theorem normalized_integral_tendsto (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {f : M → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : M) :
    Tendsto (fun n : ℕ => (d.rate.toReal)⁻¹ ^ n * ∫ y, f y ∂(K.kernel^n) x)
      atTop (𝓝 ((d.weight x).toReal * ∫ y, f y ∂μ)) := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  obtain ⟨s, hs⟩ := h.exists_survivalGapData_with_mean d hc μ hleft hnorm
  have hμρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  have hmem : MemLp f ∞ ρ := memLp_top_of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hB y)
  set F := hmem.toLp f
  have hFn : ‖F‖ ≤ B := by
    apply (Lp.norm_le_of_ae_bound (f := F) (C := B) ((abs_nonneg _).trans (hB x)) ?_).trans_eq
      (by simp)
    filter_upwards [hmem.coeFn_toLp] with y hy
    rw [hy, Real.norm_eq_abs]
    exact hB y
  set r := d.rate.toReal
  set T : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := r⁻¹ • h.transitionOperator
  set Pi := ConditionalMixing.rankOne s.mean s.eigenvector
  set S := h.smoothedOperator r⁻¹
  set Γ := ∫ y, f y ∂μ
  have hmean : s.mean F = Γ := by
    rw [hs]
    exact integral_congr_ae (hμρ.ae_eq hmem.coeFn_toLp)
  have hiter (n : ℕ) : r⁻¹ ^ (n + 1) * ∫ y, f y ∂(K.kernel^(n+1)) x = S ((T^n) F) x := by
    rw [← QProcessVariance.kernelIterate_eq_integral r⁻¹ (n+1) hf hB x,
      h.kernelIterate_succ_congr r⁻¹ n hmem.coeFn_toLp.symm x]
    exact (h.stepEvaluation_power r⁻¹ n F x).symm
  have hproj : S (Pi F) x = (d.weight x).toReal * Γ := by
    simp only [Pi, ConditionalMixing.rankOne, ContinuousLinearMap.smulRight_apply,
      map_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul, hmean]
    rw [h.smoothed_eigenvector d s.eigenvector s.eigenvector_ae]
    ring
  have hb (n : ℕ) : |r⁻¹ ^ (n+1) * ∫ y, f y ∂(K.kernel^(n+1)) x - (d.weight x).toReal * Γ| ≤
      (‖S‖ * s.fullConstant * B) * s.decay^n := by
    rw [hiter, ← hproj, ← BoundedContinuousFunction.sub_apply, ← map_sub, ← sub_apply]
    calc
      |S (((T^n) - Pi) F) x| ≤ ‖S (((T^n) - Pi) F)‖ := by
        simpa only [Real.norm_eq_abs] using (S (((T^n) - Pi) F)).norm_coe_le_norm x
      _ ≤ ‖S‖ * ‖((T^n) - Pi) F‖ := S.le_opNorm _
      _ ≤ ‖S‖ * (‖(T^n) - Pi‖ * ‖F‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg S)
      _ ≤ ‖S‖ * ((s.fullConstant * s.decay^n) * B) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg S)
        exact mul_le_mul (s.full_gap n) hFn (norm_nonneg F)
          (mul_nonneg s.fullConstant_nonneg (pow_nonneg s.decay_nonneg n))
      _ = _ := by ring
  apply (tendsto_add_atTop_iff_nat 1).1
  apply Metric.tendsto_nhds.2
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (‖S‖ * s.fullConstant * B) * s.decay^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one s.decay_nonneg s.decay_lt_one).const_mul
      (‖S‖ * s.fullConstant * B)
  filter_upwards [(tendsto_order.1 ht).2 ε hε] with n hn
  rw [Real.dist_eq]
  exact (hb n).trans_lt hn

def inverseWeight {κ : Kernel M M} (d : DoobTransform.EigenData κ) (n : ℕ) (ω : ℕ → d.State) : ℝ :=
  ((d.weight (ω n).val).toReal)⁻¹

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurable_inverseWeight (d : DoobTransform.EigenData K.kernel) (n : ℕ) :
    Measurable (inverseWeight d n) :=
  (d.measurable_weight.ennreal_toReal.inv.comp measurable_subtype_coe).comp (measurable_pi_apply n)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem integrable_inverseWeight (d : DoobTransform.EigenData K.kernel) (x : d.State) (n : ℕ) :
    Integrable (inverseWeight d n) (QProcessLimit.pathMeasure d.kernel x) := by
  have := killedKernel_power_isFinite K n
  apply RefinedLLN.integrable_of_lintegral_ne_top (measurable_inverseWeight d n)
    (fun _ => inv_nonneg.2 ENNReal.toReal_nonneg)
  have heq (y : d.State) : ENNReal.ofReal (((d.weight y.val).toReal)⁻¹) = (d.weight y.val)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos y.property (d.weight_ne_top _)),
      ENNReal.ofReal_toReal (d.weight_ne_top _)]
  have hl := MarkovPairs.lintegral_single d.kernel x n (g := fun y : d.State => (d.weight y.val)⁻¹)
    (d.measurable_weight.inv.comp measurable_subtype_coe)
  change (∫⁻ ω, ENNReal.ofReal (((d.weight (ω n).val).toReal)⁻¹)
    ∂QProcessLimit.pathMeasure d.kernel x) ≠ ∞
  simp_rw [heq]
  rw [hl, RefinedLLN.lintegral_doob_pow d n x (F := fun y => (d.weight y)⁻¹) d.measurable_weight.inv]
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 d.rate_ne_zero))
      (ENNReal.inv_ne_top.2 x.property)) (measure_ne_top ((K.kernel^n) x.val) univ))
  gcongr
  rw [← lintegral_one]
  apply lintegral_mono
  intro y
  change (d.weight y)⁻¹ * d.weight y ≤ 1
  by_cases hy : d.weight y = 0
  · simp [hy]
  · rw [ENNReal.inv_mul_cancel hy (d.weight_ne_top y)]

def smallWeightSet (d : DoobTransform.EigenData K.kernel) (δ : ℝ) : Set M :=
  {y | 0 < (d.weight y).toReal ∧ (d.weight y).toReal ≤ δ}

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurableSet_smallWeightSet (d : DoobTransform.EigenData K.kernel) (δ : ℝ) :
    MeasurableSet (smallWeightSet d δ) :=
  (measurableSet_lt measurable_const d.measurable_weight.ennreal_toReal).inter
    (measurableSet_le d.measurable_weight.ennreal_toReal measurable_const)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem integral_inverse_cutoff (d : DoobTransform.EigenData K.kernel) (x : d.State)
    (n : ℕ) (δ : ℝ) :
    (∫ ω in {ω | (ω n).val ∈ smallWeightSet d δ}, inverseWeight d n ω
      ∂QProcessLimit.pathMeasure d.kernel x) =
      (d.rate.toReal)⁻¹ ^ n * ((d.weight x.val).toReal)⁻¹ *
        ∫ y, (smallWeightSet d δ).indicator (fun _ => (1 : ℝ)) y ∂(K.kernel^n) x.val := by
  set A := smallWeightSet d δ
  have hA := measurableSet_smallWeightSet d δ
  have hm : Measurable (fun y : M => A.indicator (fun z => ((d.weight z).toReal)⁻¹) y) :=
    d.measurable_weight.ennreal_toReal.inv.indicator hA
  have hE : MeasurableSet {ω : ℕ → d.State | (ω n).val ∈ A} :=
    hA.preimage (measurable_subtype_coe.comp (measurable_pi_apply n))
  rw [← integral_indicator hE]
  have heq (ω : ℕ → d.State) : {ω | (ω n).val ∈ A}.indicator (inverseWeight d n) ω =
      A.indicator (fun z => ((d.weight z).toReal)⁻¹) (ω n).val := by
    by_cases hx : (ω n).val ∈ A <;> simp [inverseWeight, hx]
  simp_rw [heq]
  rw [MarkovPairs.integral_single d.kernel x n
    (a := fun y : d.State => A.indicator (fun z => ((d.weight z).toReal)⁻¹) y.val)
    (hm.comp measurable_subtype_coe),
    QProcessVariance.integral_doob_pow]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro y
  change (d.weight y).toReal * A.indicator (fun z => ((d.weight z).toReal)⁻¹) y =
    A.indicator (fun _ => (1 : ℝ)) y
  by_cases hy : y ∈ A
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    exact mul_inv_cancel₀ (ne_of_gt hy.1)
  · simp [indicator_of_notMem hy]

theorem inverse_cutoff_tendsto (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    (x : d.State) (δ : ℝ) :
    Tendsto (fun n => ∫ ω in {ω | (ω n).val ∈ smallWeightSet d δ}, inverseWeight d n ω
      ∂QProcessLimit.pathMeasure d.kernel x) atTop (𝓝 (μ.real (smallWeightSet d δ))) := by
  have hA := measurableSet_smallWeightSet d δ
  have hb (y : M) : |(smallWeightSet d δ).indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
    by_cases hy : y ∈ smallWeightSet d δ <;> simp [hy]
  have hh := normalized_integral_tendsto h d hc μ hleft hnorm
    (measurable_const.indicator hA) hb x.val
  have ht := hh.const_mul (((d.weight x.val).toReal)⁻¹)
  have hp : (d.weight x.val).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨x.property, d.weight_ne_top _⟩
  simp only [integral_indicator_const _ hA, smul_eq_mul, mul_one,
    ← mul_assoc, inv_mul_cancel₀ hp, one_mul] at ht
  apply ht.congr
  intro n
  rw [integral_inverse_cutoff, integral_indicator_const _ hA]
  simp only [smul_eq_mul, mul_one]
  ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem smallWeightSet_measure_tendsto (d : DoobTransform.EigenData K.kernel)
    (μ : Measure M) [IsProbabilityMeasure μ] :
    Tendsto (fun j : ℕ => μ.real (smallWeightSet d ((2 : ℝ)⁻¹ ^ j))) atTop (𝓝 0) := by
  set b : ℕ → ℝ := fun j => (2 : ℝ)⁻¹ ^ j
  have hb : Tendsto b atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hd := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun j => (smallWeightSet d (b j)).indicator (fun _ => (1 : ℝ)))
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun j => (measurable_const.indicator (measurableSet_smallWeightSet d _)).aestronglyMeasurable)
    (integrable_const _)
    (fun j => ae_of_all _ fun y => by
      by_cases hy : y ∈ smallWeightSet d (b j) <;> simp [hy])
    (ae_of_all _ fun y => by
      by_cases hy : 0 < (d.weight y).toReal
      · apply tendsto_const_nhds.congr'
        filter_upwards [(tendsto_order.1 hb).2 _ hy] with j hj
        exact (indicator_of_notMem (show y ∉ smallWeightSet d (b j) from fun hm => not_le_of_gt hj hm.2)
          (fun _ => (1 : ℝ))).symm
      · have heq (j : ℕ) : (smallWeightSet d (b j)).indicator (fun _ => (1 : ℝ)) y = 0 :=
          indicator_of_notMem (fun hm => hy hm.1) (fun _ => (1 : ℝ))
        simpa only [heq] using (tendsto_const_nhds (x := (0 : ℝ))))
  simpa only [integral_indicator_const _ (measurableSet_smallWeightSet d _),
    smul_eq_mul, mul_one, integral_zero] using hd

theorem inverseWeight_uniformly_integrable (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    (x : d.State) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      (∫ ω in {ω | B < inverseWeight d n ω}, inverseWeight d n ω
        ∂QProcessLimit.pathMeasure d.kernel x) ≤ ε := by
  intro ε hε
  obtain ⟨j, hj⟩ := ((tendsto_order.1 (smallWeightSet_measure_tendsto d μ)).2
    (ε / 2) (half_pos hε)).exists
  set δ : ℝ := (2 : ℝ)⁻¹ ^ j
  have hδ : 0 < δ := pow_pos (by norm_num) _
  refine ⟨δ⁻¹, inv_nonneg.2 hδ.le, ?_⟩
  have ht := inverse_cutoff_tendsto h d hc μ hleft hnorm x δ
  filter_upwards [(tendsto_order.1 ht).2 ε (by linarith)] with n hn
  apply le_trans _ hn.le
  apply setIntegral_mono_set (integrable_inverseWeight d x n).restrict
    (ae_of_all _ fun _ => inv_nonneg.2 ENNReal.toReal_nonneg)
  apply ae_of_all
  intro ω hω
  have hp : 0 < (d.weight (ω n).val).toReal :=
    ENNReal.toReal_pos (ω n).property (d.weight_ne_top _)
  exact ⟨hp, ((inv_lt_inv₀ hδ hp).1 hω).le⟩

theorem inverseWeight_mass_tendsto (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    (x : d.State) :
    0 < μ.real d.liveSet ∧ Tendsto
      (fun n => ∫ ω, inverseWeight d n ω ∂QProcessLimit.pathMeasure d.kernel x)
        atTop (𝓝 (μ.real d.liveSet)) := by
  obtain ⟨B, hB⟩ := L2Compactness.exists_eta_bound d hc
  have hle (y : M) : (d.weight y).toReal ≤ B := (le_abs_self _).trans (hB y)
  have hset : smallWeightSet d B = d.liveSet := by
    ext y
    constructor
    · intro hy
      exact (ENNReal.toReal_pos_iff.1 hy.1).1.ne'
    · intro hy
      exact ⟨ENNReal.toReal_pos hy (d.weight_ne_top y), hle y⟩
  have hevent (n : ℕ) : {ω : ℕ → d.State | (ω n).val ∈ smallWeightSet d B} = univ := by
    ext ω
    simp only [hset, mem_ofPred_eq, mem_univ, iff_true]
    exact (ω n).property
  have ht := inverse_cutoff_tendsto h d hc μ hleft hnorm x B
  have hmass (n : ℕ) : (∫ ω in {ω | (ω n).val ∈ smallWeightSet d B}, inverseWeight d n ω
      ∂QProcessLimit.pathMeasure d.kernel x) =
      ∫ ω, inverseWeight d n ω ∂QProcessLimit.pathMeasure d.kernel x := by
    rw [hevent n, Measure.restrict_univ]
  have ht' := ht.congr hmass
  rw [hset] at ht'
  refine ⟨?_, ht'⟩
  have hpos : 0 < ∫⁻ y, d.weight y ∂μ := by rw [hnorm]; exact zero_lt_one
  have hp := (lintegral_pos_iff_support d.measurable_weight).1 hpos
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

end
end ConditionedStableLaws.QProcessEndpoint
