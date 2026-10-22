import ConditionedStableLaws.EigenmeasurePositivity
import ConditionedStableLaws.PositiveEigenmeasure
import ConditionedStableLaws.QuasiStationary

/-!
# Normalized eigen-data and quasi-stationary existence from H

Normalizing the positive pairing of the left and right eigenvectors gives the stationary Doob
probability measure.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace ConditionedStableLaws
noncomputable section

namespace DoobTransform.EigenData
variable {M : Type*} [MeasurableSpace M] {K : Kernel M M}

/-- Multiplying the right eigenfunction by a positive finite constant preserves
the exact eigenrelation and the eigenvalue. -/
def rescale (d : DoobTransform.EigenData K) (c : ℝ≥0∞) (_hc : c ≠ 0) (hct : c ≠ ∞) :
    DoobTransform.EigenData K where
  rate := d.rate
  rate_ne_zero := d.rate_ne_zero
  rate_ne_top := d.rate_ne_top
  weight x := c * d.weight x
  measurable_weight := measurable_const.mul d.measurable_weight
  weight_ne_top x := ENNReal.mul_ne_top hct (d.weight_ne_top x)
  right_eigen x := by
    rw [lintegral_const_mul _ d.measurable_weight, d.right_eigen x]
    ac_rfl

theorem rescale_liveSet (d : DoobTransform.EigenData K) (c : ℝ≥0∞)
    (hc : c ≠ 0) (hct : c ≠ ∞) : (d.rescale c hc hct).liveSet = d.liveSet := by
  ext x
  simp [liveSet, rescale, hc]

variable [MetricSpace M] [CompactSpace M] [BorelSpace M]

theorem lintegral_weight_ne_top (d : DoobTransform.EigenData K)
    (hc : Continuous d.weight) (μ : Measure M) [IsFiniteMeasure μ] :
    (∫⁻ x, d.weight x ∂μ) ≠ ∞ := by
  have ht : Continuous (fun x => (d.weight x).toReal) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (ENNReal.continuousAt_toReal (d.weight_ne_top x)).comp hc.continuousAt)
  have hi := ht.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace (fun x => (d.weight x).toReal)) (μ := μ)
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all μ (fun x => ENNReal.toReal_nonneg))
  simpa only [ENNReal.ofReal_toReal (d.weight_ne_top _)] using
    he.symm.trans_ne ENNReal.ofReal_ne_top

end DoobTransform.EigenData

namespace StandingHypothesis
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Under H there are left/right eigen-data normalized by `μ(η)=1`. -/
theorem HypothesisH.exists_normalized_eigenData (h : HypothesisH ρ K) :
    ∃ d : DoobTransform.EigenData K.kernel, d.rate ≤ 1 ∧ Continuous d.weight ∧
      d.liveSet = survivingSet K.kernel ∧ ∃ μ : ProbabilityMeasure M,
      K.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) ∧
      (∫⁻ x, d.weight x ∂(μ : Measure M)) = 1 := by
  obtain ⟨d, hdr, hc, hne, hlive, μ, hleft⟩ := h.exists_eigenData_and_eigenmeasure
  let a : ℝ≥0∞ := ∫⁻ x, d.weight x ∂(μ : Measure M)
  have ha0 : a ≠ 0 := (h.eigenfunction_integral_pos d hc hne μ hleft).ne'
  have hat : a ≠ ∞ := d.lintegral_weight_ne_top hc μ
  let e := d.rescale a⁻¹ (ENNReal.inv_ne_zero.mpr hat) (ENNReal.inv_ne_top.mpr ha0)
  refine ⟨e, hdr, ?_, ?_, μ, hleft, ?_⟩
  · exact (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.mpr ha0)).comp hc
  · exact (d.rescale_liveSet _ _ _).trans hlive
  · change (∫⁻ x, a⁻¹ * d.weight x ∂(μ : Measure M)) = 1
    rw [lintegral_const_mul _ d.measurable_weight]
    exact ENNReal.inv_mul_cancel ha0 hat

/-- Existence of a quasi-stationary probability under the standing assumptions, including its
density with respect to the reference law. -/
theorem HypothesisH.exists_quasiStationary_density (h : HypothesisH ρ K) :
    ∃ μ : ProbabilityMeasure M, IsQuasiStationary K.kernel (μ : Measure M) ∧
      ∃ m : M → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ Integrable m ρ ∧
        (μ : Measure M) = ρ.withDensity (fun x => ENNReal.ofReal (m x)) := by
  obtain ⟨d, hdr, _, _, μ, hleft, _⟩ := h.exists_normalized_eigenData
  refine ⟨μ, ⟨inferInstance, d.rate, pos_iff_ne_zero.mpr d.rate_ne_zero, hdr, hleft⟩, ?_⟩
  exact h.exists_eigenmeasure_density μ d.rate_ne_zero hleft

/-- The Doob kernel and its stationary probability under H. -/
theorem HypothesisH.exists_stationary_Doob_probability (h : HypothesisH ρ K) :
    ∃ d : DoobTransform.EigenData K.kernel, d.rate ≤ 1 ∧ Continuous d.weight ∧
      d.liveSet = survivingSet K.kernel ∧ ∃ μ : ProbabilityMeasure M,
      K.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) ∧
      (∫⁻ x, d.weight x ∂(μ : Measure M)) = 1 ∧
      IsProbabilityMeasure (((μ : Measure M).withDensity d.weight).comap
        (Subtype.val : d.State → M)) ∧
      d.kernel ∘ₘ (((μ : Measure M).withDensity d.weight).comap
        (Subtype.val : d.State → M)) =
        (((μ : Measure M).withDensity d.weight).comap (Subtype.val : d.State → M)) := by
  obtain ⟨d, hdr, hc, hlive, μ, hleft, hnorm⟩ := h.exists_normalized_eigenData
  exact ⟨d, hdr, hc, hlive, μ, hleft, hnorm,
    d.isProbabilityMeasure_weightedMeasure μ hnorm, d.invariant_weightedMeasure μ hleft⟩

/-- Every positive probability eigenmeasure has the eigenvalue of any continuous positive right
eigenfunction, since their pairing is positive and finite. -/
theorem HypothesisH.left_eigenvalue_eq (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (hne : ∃ x, d.weight x ≠ 0) (μ : Measure M) [IsProbabilityMeasure μ]
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ∞) (hleft : K.kernel ∘ₘ μ = r • μ) :
    r = d.rate := by
  have hpos : 0 < ∫⁻ x, d.weight x ∂μ := by
    apply (lintegral_pos_iff_support d.measurable_weight).mpr
    change 0 < μ d.liveSet
    rw [h.eigenfunction_liveSet_eq d hc hne]
    exact h.eigenmeasure_surviving_mass_pos μ r hr0 hrt hleft
  have htop := d.lintegral_weight_ne_top hc μ
  have heq : r * (∫⁻ x, d.weight x ∂μ) = d.rate * (∫⁻ x, d.weight x ∂μ) := by
    calc
      _ = ∫⁻ x, d.weight x ∂(K.kernel ∘ₘ μ) := by
        rw [hleft, lintegral_smul_measure, smul_eq_mul]
      _ = ∫⁻ x, ∫⁻ y, d.weight y ∂K.kernel x ∂μ :=
        Measure.lintegral_bind K.kernel.aemeasurable d.measurable_weight.aemeasurable
      _ = _ := by simp_rw [d.right_eigen]; exact lintegral_const_mul _ d.measurable_weight
  exact (ENNReal.mul_left_inj hpos.ne' htop).mp heq

/-- The quasi-stationary rate is unique even before uniqueness of the law
itself has been established. -/
theorem HypothesisH.quasiStationary_rates_unique (h : HypothesisH ρ K)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r s : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ∞) (hs0 : s ≠ 0) (hst : s ≠ ∞)
    (hr : K.kernel ∘ₘ μ = r • μ) (hs : K.kernel ∘ₘ ν = s • ν) : r = s := by
  obtain ⟨d, _, hc, hne, _⟩ := h.exists_right_eigenData
  exact (h.left_eigenvalue_eq d hc hne μ hr0 hrt hr).trans
    (h.left_eigenvalue_eq d hc hne ν hs0 hst hs).symm

end StandingHypothesis
end
end ConditionedStableLaws
