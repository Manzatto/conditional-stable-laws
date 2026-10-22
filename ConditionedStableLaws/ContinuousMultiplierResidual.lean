import ConditionedStableLaws.ContinuousMultiplierTransfer
import ConditionedStableLaws.ContinuousMultiplierPowerCompensation
import ConditionedStableLaws.ContinuousMultiplierLargeJumps
import ConditionedStableLaws.GaussianBoundary

/-! Negligibility of the signed continuous-multiplier residual below index two. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open CanonicalChain StandingHypothesis NormalizationBridge SmallJumpMoment

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The full residual is negligible whenever its deterministic compensation agrees asymptotically
with every fixed truncation. -/
theorem residual_negligible_of_compensation (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα2 : dimension / β < 2)
    {g : M → ℝ} (hg : Continuous g) (c : ℕ → ℝ)
    (hcenter : ∀ R : ℝ, 1 ≤ R → Tendsto (fun n : ℕ =>
      (n : ℝ) / positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
        (dimension / β) n * (∫ y, cut (singularObservable x₀ β) (residual x₀ β g)
          (R * positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
            (dimension / β) n) y ∂μ.withDensity d.weight) -
      (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
        (dimension / β) n)⁻¹ * c n) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (C.conditionedMeasure x.val n).real {ω |
      ε < |(positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
        (dimension / β) n)⁻¹ * (pathBirkhoffSum (residual x₀ β g) n ω - c n)|})
      atTop (𝓝 0) := by
  let α := dimension / β
  have hα : 0 < α := div_pos hadm.1.1 hβ
  let Cc := volumeConstant * (d.weight x₀).toReal * m x₀
  have hC : 0 < Cc := mul_pos (mul_pos hadm.1.2.1
    (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  let f := singularObservable x₀ β
  let r := residual x₀ β g
  let ν := μ.withDensity d.weight
  let B := positivePowerScale Cc α
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  have hP (n : ℕ) : IsProbabilityMeasure (C.conditionedMeasure x.val n) :=
    C.conditionedMeasure_isProbability_of_surviving x.val hx n
  have hlarge : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 1 ≤ R ∧ ∀ᶠ n in atTop,
      (C.conditionedMeasure x.val n).real (largeEvent f (B n) R n) < δ := by
    intro δ hδ
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
      ((tendsto_rpow_neg_atTop hα).eventually_lt_const (half_pos hδ))
    let R := max 1 R₀
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hpow : 2 * R ^ (-α) < δ := by have := hR₀ R (le_max_right _ _); linarith
    refine ⟨R, le_max_left _ _, ?_⟩
    have he := large_jump_eventually C h d s.continuous_weight μ hleft hnorm
      m hm hm0 hμ x hadm hx₀ hβ ⟨R, hR.le⟩ (by exact_mod_cast hR)
    filter_upwards [he] with n hn
    exact hn.trans hpow
  obtain ⟨T, hT, a, ha, hlower⟩ := GaussianBoundary.exists_weight_lower C d s.continuous_weight hx₀ hβ
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  apply full_residual_negligible (fun n => C.conditionedMeasure x.val n) ν hlarge
  · intro R hR
    exact centered_cut_residual_negligible C h d s hlive μ hleft hnorm x
      (measurable_singularObservable x₀ β) (measurable_residual x₀ β hg)
      (fun y => (singularObservable_pos x₀ β y).le) (fun η hη => residual_bound hβ hg hη)
      hT.le ha hlower hC hα hα2 htail (lt_of_lt_of_le one_pos hR)
  · intro R hR
    simpa only [B, Cc, α, f, ν, div_eq_mul_inv] using hcenter R hR

/-- Full mean centering suffices for residuals when the index exceeds one. -/
theorem residual_full_mean_negligible (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : 1 < dimension / β) (hα2 : dimension / β < 2)
    {g : M → ℝ} (hg : Continuous g) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (C.conditionedMeasure x.val n).real {ω |
      ε < |(positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
        (dimension / β) n)⁻¹ * (pathBirkhoffSum (residual x₀ β g) n ω -
          n * ∫ y, residual x₀ β g y ∂μ.withDensity d.weight)|}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (μ.withDensity d.weight) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hC : 0 < volumeConstant * (d.weight x₀).toReal * m x₀ := mul_pos
    (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  apply residual_negligible_of_compensation C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ hα2 hg
  intro R hR
  have he := (full_center_tendsto_zero (μ.withDensity d.weight)
    (measurable_singularObservable x₀ β) (fun y => (singularObservable_pos x₀ β y).le)
    (measurable_residual x₀ β hg) (fun η hη => residual_bound hβ hg hη) hC hα1 htail
    (lt_of_lt_of_le one_pos hR)).neg
  simpa only [neg_zero] using he.congr (fun n => by ring)

/-- Truncating the residual mean at B suffices at index one (and below two). -/
theorem residual_cut_mean_negligible (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα2 : dimension / β < 2)
    {g : M → ℝ} (hg : Continuous g) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (C.conditionedMeasure x.val n).real {ω |
      ε < |(positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
        (dimension / β) n)⁻¹ * (pathBirkhoffSum (residual x₀ β g) n ω -
          n * ∫ y, cut (singularObservable x₀ β) (residual x₀ β g)
            (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
              (dimension / β) n) y ∂μ.withDensity d.weight)|}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (μ.withDensity d.weight) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hC : 0 < volumeConstant * (d.weight x₀).toReal * m x₀ := mul_pos
    (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  apply residual_negligible_of_compensation C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ hα2 hg
  intro R hR
  have he := cut_band_center_tendsto_zero (μ.withDensity d.weight)
    (measurable_singularObservable x₀ β) (measurable_residual x₀ β hg)
    (fun η hη => residual_bound hβ hg hη) hC (div_pos hadm.1.1 hβ) htail hR
  exact he.congr (fun n => by ring)

end
end ConditionedStableLaws.ContinuousMultiplier
