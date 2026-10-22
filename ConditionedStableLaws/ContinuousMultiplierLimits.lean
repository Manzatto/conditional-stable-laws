import ConditionedStableLaws.ContinuousMultiplierSmall
import ConditionedStableLaws.CenterValue
import ConditionedStableLaws.ContinuousMultiplierGaussian
import ConditionedStableLaws.ContinuousMultiplierMid
import ConditionedStableLaws.ContinuousMultiplierOneSigned

/-!
# Continuous multipliers: normalization, reflection and centre value

The conclusions use `|g(x₀)| Bₙ`, the reflected stable law, and an arbitrary fixed finite value at
the centre. The approximation is derived from H and continuity of the multiplier.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

noncomputable section
namespace ConditionedStableLaws.ContinuousMultiplier
open CanonicalChain StandingHypothesis NormalizationBridge AnnularPoissonClouds

/-- A reflected centered Gaussian is exactly the same probability law. -/
theorem gaussian_reflected_limit
    {Ω : Type*} [MeasurableSpace Ω]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : ℕ → Ω → ℝ} (v : ℝ≥0) {c : ℝ} (hc : c ≠ 0)
    (h : TendstoInDistribution X atTop (fun z : ℝ => (c / |c|) * z) P (gaussianReal 0 v)) :
    TendstoInDistribution X atTop (fun z : ℝ => z) P (gaussianReal 0 v) := by
  refine ⟨h.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa only [show (fun z : ℝ => z) = id from rfl,
    MultiplierReflection.gaussian_map_sign v hc, Measure.map_id] using h.tendsto

/-- The tail constant `|g₀|^α C₀` of the multiplied observable. -/
def multiplierTailConstant (g₀ α C₀ : ℝ) : ℝ := |g₀| ^ α * C₀

theorem multiplierTailConstant_pos {g₀ α C₀ : ℝ} (hg₀ : g₀ ≠ 0) (hC₀ : 0 < C₀) :
    0 < multiplierTailConstant g₀ α C₀ :=
  mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr hg₀) _) hC₀

/-- The transformed tail constant gives the power normalization scaled by `|g₀|`. -/
theorem powerScale_multiplierTailConstant {g₀ α C₀ : ℝ}
    (hα : 0 < α) (hC₀ : 0 < C₀) (n : ℕ) :
    powerScale (multiplierTailConstant g₀ α C₀) α n = |g₀| * powerScale C₀ α n := by
  unfold powerScale multiplierTailConstant
  rw [mul_assoc, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (by positivity),
    ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hα.ne', Real.rpow_one]

/-- At the boundary, the transformed constant gives the same absolute-value scaling. -/
theorem bScale_multiplierTailConstant (g₀ C₀ : ℝ) (n : ℕ) :
    GaussianBoundary.bScale (multiplierTailConstant g₀ 2 C₀) n =
      |g₀| * GaussianBoundary.bScale C₀ n := by
  unfold GaussianBoundary.bScale multiplierTailConstant
  rw [Real.rpow_two]
  have he : |g₀| ^ 2 * C₀ * n * Real.log n = |g₀| ^ 2 * (C₀ * n * Real.log n) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Finite centre changes preserve both integrability and the mean-centered limit. -/
theorem mean_limit_setCenterValue
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : HypothesisH ρ C.toKilledKernel) (d : DoobTransform.EigenData C.killedTransition)
    (μ : Measure M) (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (x : d.State)
    {x₀ : M} {dimension volumeConstant : ℝ}
    (hreg : IsRegularAt ρ x₀ dimension volumeConstant)
    {f : M → ℝ} (hf : Measurable f) (hfi : Integrable f (μ.withDensity d.weight))
    (v : ℝ) (B : ℕ → ℝ) (hB : Tendsto B atTop atTop) {Z : Ω → ℝ}
    (hlim : TendstoInDistribution
      (fun n ω => (B n)⁻¹ * (pathBirkhoffSum f n ω - n * ∫ y, f y ∂μ.withDensity d.weight))
      atTop Z (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q) :
    Integrable (setCenterValue f x₀ v) (μ.withDensity d.weight) ∧
    TendstoInDistribution
      (fun n ω => (B n)⁻¹ * (pathBirkhoffSum (setCenterValue f x₀ v) n ω -
        n * ∫ y, setCenterValue f x₀ v y ∂μ.withDensity d.weight)) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q := by
  have hn := C.quasiErgodic_center_null h d μ hleft hreg
  refine ⟨hfi.congr (setCenterValue_ae_eq f hn v).symm, ?_⟩
  simpa only [integral_setCenterValue f hn v] using
    C.limit_setCenterValue Q h d x hreg hf v
      (fun n => n * ∫ y, f y ∂μ.withDensity d.weight) B hB hlim

/-- **Continuous multipliers, 0 < α < 1.** The limit is unchanged for a positive multiplier at the
centre and reflected for a negative multiplier. Every finite convention at the centre is allowed. -/
theorem stable_law_small_signed (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : dimension / β < 1)
    {g : M → ℝ} (hg : Continuous g) (hg0 : g x₀ ≠ 0) (v : ℝ) :
    TendstoInDistribution
      (fun n ω => (|g x₀| * positivePowerScale
        (volumeConstant * (d.weight x₀).toReal * m x₀) (dimension / β) n)⁻¹ *
        pathBirkhoffSum (setCenterValue (observable x₀ β g) x₀ v) n ω) atTop
      (fun ω => (g x₀ / |g x₀|) * positiveIntegral ω)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw (dimension / β) (div_pos hadm.1.1 hβ)) := by
  have hC : 0 < volumeConstant * (d.weight x₀).toReal * m x₀ :=
    mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  have hb := stable_law_small_multiplier C h d s hlive μ hleft hnorm m hm hm0 hμ
    x hadm hx₀ hβ hα1 hg
  have hs := MultiplierReflection.rescale_normalizer_tendsto
    (A := fun _ => 0) (g x₀) (by simpa only [sub_zero] using hb)
  have ht := C.limit_setCenterValue _ h d x hadm.1
    (measurable_observable x₀ β hg) v (fun _ => 0) _
    ((positivePowerScale_tendsto_atTop hC (div_pos hadm.1.1 hβ)).const_mul_atTop
      (abs_pos.mpr hg0)) hs
  simpa only [sub_zero] using ht

/-- **Continuous multipliers, α=2.** The mean-centered Gaussian law is unchanged for either sign of
`g(x₀)`, on the `|g(x₀)| Bₙ` scale. -/
theorem stable_law_boundary_signed (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα : dimension / β = 2)
    {g : M → ℝ} (hg : Continuous g) (hg0 : g x₀ ≠ 0) (v : ℝ) :
    Integrable (setCenterValue (observable x₀ β g) x₀ v) (μ.withDensity d.weight) ∧
    TendstoInDistribution
      (fun n ω => (|g x₀| * GaussianBoundary.bScale
        (volumeConstant * (d.weight x₀).toReal * m x₀) n)⁻¹ *
        (pathBirkhoffSum (setCenterValue (observable x₀ β g) x₀ v) n ω -
          n * ∫ y, setCenterValue (observable x₀ β g) x₀ v y ∂μ.withDensity d.weight)) atTop
      (fun z : ℝ => z)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (gaussianReal 0 1) := by
  have hC : 0 < volumeConstant * (d.weight x₀).toReal * m x₀ :=
    mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  obtain ⟨hi, hb⟩ := stable_law_boundary_multiplier C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ hα hg
  have hs := MultiplierReflection.rescale_normalizer_tendsto (g x₀) hb
  have ht := gaussian_reflected_limit 1 hg0 hs
  exact mean_limit_setCenterValue C _ h d μ hleft x hadm.1
    (measurable_observable x₀ β hg) hi v _
    ((GaussianBoundary.bScale_tendsto hC).const_mul_atTop (abs_pos.mpr hg0)) ht

/-- **Continuous multipliers, 1 < α < 2.** The full mean centering, absolute-value scale, reflected
limit and arbitrary finite centre value. -/
theorem stable_law_mid_signed (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : 1 < dimension / β) (hα2 : dimension / β < 2)
    {g : M → ℝ} (hg : Continuous g) (hg0 : g x₀ ≠ 0) (v : ℝ) :
    Integrable (setCenterValue (observable x₀ β g) x₀ v) (μ.withDensity d.weight) ∧
    TendstoInDistribution
      (fun n ω => (|g x₀| * positivePowerScale
        (volumeConstant * (d.weight x₀).toReal * m x₀) (dimension / β) n)⁻¹ *
        (pathBirkhoffSum (setCenterValue (observable x₀ β g) x₀ v) n ω -
          n * ∫ y, setCenterValue (observable x₀ β g) x₀ v y ∂μ.withDensity d.weight)) atTop
      (fun ω => (g x₀ / |g x₀|) * fullyCompensatedStable (dimension / β) (zero_lt_one.trans hα1) ω)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw (dimension / β) (zero_lt_one.trans hα1)) := by
  have hC : 0 < volumeConstant * (d.weight x₀).toReal * m x₀ :=
    mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  obtain ⟨hi, hb⟩ := stable_law_mid_multiplier C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ hα1 hα2 hg
  have hs := MultiplierReflection.rescale_normalizer_tendsto (g x₀) hb
  exact mean_limit_setCenterValue C _ h d μ hleft x hadm.1
    (measurable_observable x₀ β hg) hi v _
    ((positivePowerScale_tendsto_atTop hC (zero_lt_one.trans hα1)).const_mul_atTop
      (abs_pos.mpr hg0)) hs

end ConditionedStableLaws.ContinuousMultiplier
