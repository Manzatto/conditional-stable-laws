import ConditionedStableLaws.ContinuousMultiplierOneNormalized
import ConditionedStableLaws.CenterValue

/-!
Signed continuous multipliers at exponent one.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open CanonicalChain StandingHypothesis NormalizationBridge AnnularPoissonClouds
  MultiplierReflection

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Continuous multipliers, α=1.** The normalization is `|g(x₀)| Bₙ`, the centering truncates by
the absolute value of the signed observable, and negative g(x₀) reflects the stable law. Every fixed
finite value at the centre is permitted. -/
theorem stable_law_one_signed (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : dimension / β = 1)
    {g : M → ℝ} (hg : Continuous g) (hg0 : g x₀ ≠ 0) (v : ℝ) :
    TendstoInDistribution
      (fun n ω => (|g x₀| * positivePowerScale
        (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n)⁻¹ *
        (pathBirkhoffSum (setCenterValue (observable x₀ β g) x₀ v) n ω - n * ∫ y,
          absTrunc (setCenterValue (observable x₀ β g) x₀ v)
            (|g x₀| * positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n) y
              ∂μ.withDensity d.weight)) atTop
      (fun ω => (g x₀ / |g x₀|) * unitCompensatedStable 1 one_pos ω)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw 1 one_pos) := by
  let g' : M → ℝ := fun y => g y / g x₀
  have hg' : Continuous g' := hg.div_const _
  have hg0' : g' x₀ = 1 := div_self hg0
  have hobs : (fun y => g x₀ * observable x₀ β g' y) = observable x₀ β g := by
    funext y
    dsimp [observable, g']
    field_simp [hg0]
  have hbase := stable_law_one_multiplier_normalized C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ hα1 hg' hg0'
  have hs := normalized_path_const_mul_tendsto hbase (g x₀)
  rw [hobs] at hs
  let B := positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1
  have hcent (n : ℕ) : g x₀ * ((n : ℝ) * ∫ y, absTrunc (observable x₀ β g') (B n) y ∂μ.withDensity d.weight) =
      n * ∫ y, absTrunc (observable x₀ β g) (|g x₀| * B n) y ∂μ.withDensity d.weight := by
    rw [← hobs, integral_absTrunc_const_mul _ _ _ hg0]
    ring
  dsimp only [B] at hcent
  have hs' : TendstoInDistribution
      (fun n ω => (|g x₀| * B n)⁻¹ *
        (pathBirkhoffSum (observable x₀ β g) n ω -
          n * ∫ y, absTrunc (observable x₀ β g) (|g x₀| * B n) y ∂μ.withDensity d.weight)) atTop
      (fun ω => (g x₀ / |g x₀|) * unitCompensatedStable 1 one_pos ω)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw 1 one_pos) := by
    simpa only [B, hcent] using hs
  have hC : 0 < volumeConstant * (d.weight x₀).toReal * m x₀ := mul_pos
    (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  have ht := C.limit_setCenterValue _ h d x hadm.1 (measurable_observable x₀ β hg) v
    (fun n => n * ∫ y, absTrunc (observable x₀ β g) (|g x₀| * B n) y ∂μ.withDensity d.weight)
    (fun n => |g x₀| * B n)
    ((positivePowerScale_tendsto_atTop hC one_pos).const_mul_atTop (abs_pos.mpr hg0)) hs'
  have hnull := C.quasiErgodic_center_null h d μ hleft hadm.1
  simpa only [integral_absTrunc_setCenterValue (observable x₀ β g) hnull v] using ht

end
end ConditionedStableLaws.ContinuousMultiplier
