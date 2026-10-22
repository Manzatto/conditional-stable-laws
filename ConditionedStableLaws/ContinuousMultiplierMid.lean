import ConditionedStableLaws.ContinuousMultiplierResidual

/-! The continuous multiplier extension in the centered non-Gaussian range. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open CanonicalChain StandingHypothesis NormalizationBridge AnnularPoissonClouds

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- For `1 < α < 2`, center the signed multiplier observable by its full mean.
The normalizer is the original B, so the limit is multiplied by g(x₀). -/
theorem stable_law_mid_multiplier (h : HypothesisH ρ C.toKilledKernel)
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
    Integrable (observable x₀ β g) (μ.withDensity d.weight) ∧
    TendstoInDistribution
      (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
          (dimension / β) n)⁻¹ *
        (pathBirkhoffSum (observable x₀ β g) n ω -
          n * ∫ y, observable x₀ β g y ∂μ.withDensity d.weight)) atTop
      (fun ω => g x₀ * fullyCompensatedStable (dimension / β) (zero_lt_one.trans hα1) ω)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw (dimension / β) (zero_lt_one.trans hα1)) := by
  obtain ⟨hfi, hbase⟩ := StableLawCompensated.stable_law_mid C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ hα1 hα2
  let B := positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) (dimension / β)
  have : IsProbabilityMeasure (μ.withDensity d.weight) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hri := integrable_residual_of_bound (μ.withDensity d.weight) hfi
    (measurable_residual x₀ β hg) (fun η hη => residual_bound hβ hg hη)
  have hnear := residual_full_mean_negligible C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ hα1 hα2 hg
  have hgfi : Integrable (observable x₀ β g) (μ.withDensity d.weight) := by
    apply ((hfi.const_mul (g x₀)).add hri).congr
    apply ae_of_all
    intro y
    dsimp [observable, residual]
    ring
  refine ⟨hgfi, ?_⟩
  have hir : (∫ y, residual x₀ β g y ∂μ.withDensity d.weight) =
      (∫ y, observable x₀ β g y ∂μ.withDensity d.weight) -
        g x₀ * ∫ y, singularObservable x₀ β y ∂μ.withDensity d.weight := by
    rw [← integral_const_mul, ← integral_sub hgfi (hfi.const_mul (g x₀))]
    apply integral_congr_ae
    exact ae_of_all _ fun y => (observable_sub_center x₀ β g y).symm
  let X : ℕ → Path M → ℝ := fun n ω => (B n)⁻¹ *
    (pathBirkhoffSum (observable x₀ β g) n ω -
      n * ∫ y, observable x₀ β g y ∂μ.withDensity d.weight)
  let Y : ℕ → Path M → ℝ := fun n ω => g x₀ * ((B n)⁻¹ *
    (pathBirkhoffSum (singularObservable x₀ β) n ω -
      n * ∫ y, singularObservable x₀ β y ∂μ.withDensity d.weight))
  have hXm (n : ℕ) : Measurable (X n) :=
    ((measurable_pathBirkhoffSum (measurable_observable x₀ β hg) n).sub
      measurable_const).const_mul _
  have hYm (n : ℕ) : Measurable (Y n) :=
    (((measurable_pathBirkhoffSum (measurable_singularObservable x₀ β) n).sub
      measurable_const).const_mul _).const_mul _
  have hscaled := hbase.continuous_comp (g := fun z : ℝ => g x₀ * z)
    (continuous_const.mul continuous_id)
  apply tendstoInDistribution_of_varying_probability_approximation
    (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
    (powerLaw (dimension / β) (zero_lt_one.trans hα1)) X Y
    (fun ω => g x₀ * fullyCompensatedStable (dimension / β) (zero_lt_one.trans hα1) ω) hXm hYm hscaled
  intro ε hε
  apply (hnear ε hε).congr
  intro n
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  have he : X n ω - Y n ω = (B n)⁻¹ *
      (pathBirkhoffSum (residual x₀ β g) n ω -
        n * ∫ y, residual x₀ β g y ∂μ.withDensity d.weight) := by
    rw [path_residual_eq, hir]
    dsimp [X, Y]
    ring
  rw [he]

end
end ConditionedStableLaws.ContinuousMultiplier
