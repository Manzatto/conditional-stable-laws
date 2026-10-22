import ConditionedStableLaws.ContinuousMultiplierResidual

/-! Index-one continuous multipliers with a deterministic centering criterion. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open CanonicalChain StandingHypothesis NormalizationBridge AnnularPoissonClouds SmallJumpMoment

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Once g(x₀)=1, only the deterministic centering comparison remains; the random residual is
negligible by H and continuity. -/
theorem stable_law_one_multiplier_of_center (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : dimension / β = 1)
    {g : M → ℝ} (hg : Continuous g) (hg0 : g x₀ = 1) (A : ℕ → ℝ)
    (hcenter : Tendsto (fun n : ℕ =>
      (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n)⁻¹ *
        (A n - n * (∫ y, trunc (singularObservable x₀ β)
          (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n) y ∂μ.withDensity d.weight) -
          n * ∫ y, cut (singularObservable x₀ β) (residual x₀ β g)
            (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n) y ∂μ.withDensity d.weight))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n)⁻¹ *
        (pathBirkhoffSum (observable x₀ β g) n ω - A n)) atTop
      (unitCompensatedStable 1 one_pos)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw 1 one_pos) := by
  have hbase := StableLawCompensated.stable_law_one C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ hα1
  let B := positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1
  let F : ℕ → ℝ := fun n => ∫ y, trunc (singularObservable x₀ β) (B n) y ∂μ.withDensity d.weight
  let R : ℕ → ℝ := fun n => ∫ y, cut (singularObservable x₀ β) (residual x₀ β g) (B n) y ∂μ.withDensity d.weight
  have hnear := residual_cut_mean_negligible C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ (by rw [hα1]; norm_num) hg
  rw [hα1] at hnear
  let X : ℕ → Path M → ℝ := fun n ω => (B n)⁻¹ * (pathBirkhoffSum (observable x₀ β g) n ω - A n)
  let Y : ℕ → Path M → ℝ := fun n ω => (B n)⁻¹ * (pathBirkhoffSum (singularObservable x₀ β) n ω - n * F n)
  have hXm (n : ℕ) : Measurable (X n) :=
    ((measurable_pathBirkhoffSum (measurable_observable x₀ β hg) n).sub measurable_const).const_mul _
  have hYm (n : ℕ) : Measurable (Y n) :=
    ((measurable_pathBirkhoffSum (measurable_singularObservable x₀ β) n).sub measurable_const).const_mul _
  apply tendstoInDistribution_of_varying_probability_approximation
    (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
    (powerLaw 1 one_pos) X Y (unitCompensatedStable 1 one_pos) hXm hYm hbase
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ (hnear (ε / 2) (half_pos hε))
  have hevent := Metric.tendsto_nhds.mp hcenter (ε / 2) (half_pos hε)
  filter_upwards [hevent] with n hn
  apply measureReal_mono
  · intro ω hω
    change ε / 2 < |(B n)⁻¹ * (pathBirkhoffSum (residual x₀ β g) n ω - n * R n)|
    change ε < |X n ω - Y n ω| at hω
    simp only [Real.dist_eq, sub_zero] at hn
    have he : X n ω - Y n ω =
        (B n)⁻¹ * (pathBirkhoffSum (residual x₀ β g) n ω - n * R n) -
          (B n)⁻¹ * (A n - n * F n - n * R n) := by
      rw [path_residual_eq, hg0, one_mul]
      dsimp [X, Y]
      ring
    rw [he] at hω
    have hab := abs_sub_le
      ((B n)⁻¹ * (pathBirkhoffSum (residual x₀ β g) n ω - n * R n)) 0
      ((B n)⁻¹ * (A n - n * F n - n * R n))
    simp only [sub_zero, zero_sub, abs_neg] at hab
    change |(B n)⁻¹ * (A n - n * F n - n * R n)| < ε / 2 at hn
    linarith
  · exact measure_ne_top _ _

end
end ConditionedStableLaws.ContinuousMultiplier
