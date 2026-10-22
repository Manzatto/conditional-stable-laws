import ConditionedStableLaws.SpectralRadiusIdentification
import ConditionedStableLaws.QuasiErgodic

/-!
# The L∞ spectral decomposition under H

The positive eigen-data, its spectral-radius identification, and the exact projection/remainder
identities for the killed operator.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- The right vector in the survival package is fixed by the normalized operator, as an equality of
L∞ classes. -/
theorem SurvivalGapData.normalizedOperator_eigenvector (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (s : SurvivalGapData h d) :
    ((d.rate.toReal)⁻¹ • h.transitionOperator) s.eigenvector = s.eigenvector := by
  rw [← (h.smoothing_factorization (d.rate.toReal)⁻¹).1]
  apply Lp.ext
  change h.continuousEmbedding (h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector) =ᵐ[ρ] _
  filter_upwards [h.continuousEmbedding_ae
    (h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector), s.eigenvector_ae] with x hx hy
  rw [hx, h.smoothed_eigenvector d s.eigenvector s.eigenvector_ae]
  exact hy.symm

/-- All analytic and algebraic conclusions of the normalized L∞ decomposition
are obtained from H alone, with the mean identified as the derived measure. -/
theorem HypothesisH.exists_spectral_decomposition (h : HypothesisH ρ K) :
    ∃ d : DoobTransform.EigenData K.kernel,
      d.rate ≤ 1 ∧ Continuous d.weight ∧ d.liveSet = survivingSet K.kernel ∧
      ∃ μ : ProbabilityMeasure M,
        K.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) ∧
        (∫⁻ y, d.weight y ∂(μ : Measure M)) = 1 ∧
        spectralRadius ℝ h.transitionOperator = d.rate ∧
        ∃ s : SurvivalGapData h d,
          (∀ f : Lp ℝ ∞ ρ, s.mean f = ∫ y, f y ∂(μ : Measure M)) ∧
          let Q := (d.rate.toReal)⁻¹ • h.transitionOperator
          let piOp := s.mean.smulRight s.eigenvector
          let R := Q-piOp
          piOp*piOp = piOp ∧ piOp*R = 0 ∧ R*piOp = 0 ∧
          (∀ n : ℕ, 1 ≤ n → Q^n = piOp+R^n) ∧
          ∀ n : ℕ, 1 ≤ n → ‖R^n‖ ≤ s.constant*s.decay^n := by
  obtain ⟨d, hdr, hc, hlive, μ, hleft, hnorm⟩ := h.exists_normalized_eigenData
  obtain ⟨s, hs, hsleft⟩ := h.exists_survivalGapData_with_mean_invariant d hc μ hleft hnorm
  have hr : 0 < d.rate.toReal := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  have hleft' : K.kernel ∘ₘ (μ : Measure M) = ENNReal.ofReal d.rate.toReal • (μ : Measure M) := by
    rwa [ENNReal.ofReal_toReal d.rate_ne_top]
  let η := h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector
  have hη (x : M) : η x = (d.weight x).toReal :=
    h.smoothed_eigenvector d s.eigenvector s.eigenvector_ae x
  have hηnorm : (∫ y, η y ∂(μ : Measure M)) = 1 := by
    simp_rw [hη]
    rw [integral_toReal d.measurable_weight.aemeasurable
      (ae_of_all _ (fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y))), hnorm]
    simp
  have hηeig : h.continuousKernelOperator η = d.rate.toReal • η := by
    ext x
    rw [h.continuousKernelOperator_apply]
    simp_rw [hη]
    change (∫ y, (d.weight y).toReal ∂K.kernel x) = d.rate.toReal*η x
    rw [hη]
    rw [integral_toReal d.measurable_weight.aemeasurable
      (ae_of_all _ (fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y))), d.right_eigen,
      ENNReal.toReal_mul]
  have hrad : spectralRadius ℝ h.transitionOperator = d.rate := by
    rw [h.transitionOperator_spectralRadius_eq μ hr hleft' η hηeig hηnorm,
      ENNReal.ofReal_toReal d.rate_ne_top]
  have hmeanη : s.mean s.eigenvector = 1 := by
    rw [hs]
    rw [← hηnorm]
    apply integral_congr_ae
    exact ((h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft).ae_eq s.eigenvector_ae).trans
      (ae_of_all _ (fun y => (hη y).symm))
  let Q := (d.rate.toReal)⁻¹ • h.transitionOperator
  let piOp := s.mean.smulRight s.eigenvector
  have hpp : piOp*piOp = piOp := by
    ext f
    simp [piOp, mul_apply_eq_comp, hmeanη]
  have hpq : piOp*Q = piOp := by
    ext1 f
    change s.mean (Q f) • s.eigenvector = s.mean f • s.eigenvector
    rw [show s.mean (Q f) = s.mean f from hsleft f]
  have hqp : Q*piOp = piOp := by
    ext1 f
    change Q (s.mean f • s.eigenvector) = s.mean f • s.eigenvector
    rw [map_smul, show Q s.eigenvector = s.eigenvector from s.normalizedOperator_eigenvector h d]
  have hann := SpectralAlgebra.projection_sub_annihilation Q piOp hpp hpq hqp
  have hpow := SpectralAlgebra.operator_pow_eq_projection_add Q piOp hpp hpq hqp
  refine ⟨d, hdr, hc, hlive, μ, hleft, hnorm, hrad, s, hs, hpp, hann.1, hann.2, hpow, ?_⟩
  intro n hn
  have he : (Q-piOp)^n = Q^n-piOp := by rw [hpow n hn]; abel
  rw [he]
  exact s.gap n hn

end
end ConditionedStableLaws.StandingHypothesis
