import ConditionedStableLaws.StationaryClusters
import ConditionedStableLaws.CompactSpectral

/-!
# Refined short-return estimates

The first transition into a small target is kept in the norm bound. This is
the small factor needed in PPP Step 2; an unrefined mixing error would not
suffice when summing all short internal cluster gaps.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BoundedContinuousFunction
noncomputable section
namespace ConditionedStableLaws.StandingHypothesis
open ConditionalMixing
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Smoothing supplies a continuous representative of the normalized L∞ operator. -/
theorem HypothesisH.smoothedOperator_ae (h : HypothesisH ρ K) (c : ℝ) (f : Lp ℝ ∞ ρ) :
    (h.smoothedOperator c f : M → ℝ) =ᵐ[ρ] (c • h.transitionOperator) f := by
  filter_upwards [h.transitionOperator_ae f, Lp.coeFn_smul c (h.transitionOperator f)] with y hy hs
  rw [h.smoothedOperator_apply, h.stepEvaluation_apply]
  change c * ∫ z, f z ∂K.kernel y = (c • h.transitionOperator f) y
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hy]

/-- Full support of the reference measure upgrades an essential norm bound
on a continuous representative to a bound at every starting state. -/
theorem HypothesisH.continuous_representative_bound (h : HypothesisH ρ K)
    (F : M →ᵇ ℝ) (f : Lp ℝ ∞ ρ) (hF : (F : M → ℝ) =ᵐ[ρ] f) (x : M) :
    ‖F x‖ ≤ ‖f‖ := by
  have : ρ.IsOpenPosMeasure := h.reference_fullSupport
  have hb : ∀ᵐ y ∂ρ, ‖F y‖ ≤ ‖f‖ := by
    filter_upwards [hF, lp_infinity_ae_norm_le f] with y hy hb
    rwa [hy]
  have hd := (Measure.dense_of_ae hb) x
  have hc : IsClosed {y : M | ‖F y‖ ≤ ‖f‖} :=
    isClosed_le F.continuous.norm continuous_const
  rwa [hc.closure_eq] at hd

/-- After keeping one initial transition inside the small norm, the remaining
spectral error is `C θ^n ‖Q f‖`. Continuity and full support make the estimate
pointwise, avoiding any loss of a second transition. -/
theorem HypothesisH.refined_power_error (h : HypothesisH ρ K) (c : ℝ)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (η f : Lp ℝ ∞ ρ)
    (hη : (c • h.transitionOperator) η = η)
    (hmean : mean ((c • h.transitionOperator) f) = mean f)
    (n : ℕ) (ε : ℝ) (_hε : 0 ≤ ε)
    (hgap : ‖(c • h.transitionOperator) ^ n - rankOne mean η‖ ≤ ε) (x : M) :
    |h.smoothedOperator c (((c • h.transitionOperator) ^ n) f) x -
        mean f * h.smoothedOperator c η x| ≤
      ε * ‖(c • h.transitionOperator) f‖ := by
  let Q := c • h.transitionOperator
  let v : Lp ℝ ∞ ρ := (Q ^ n) (Q f) - mean f • η
  let F : M →ᵇ ℝ := h.smoothedOperator c ((Q ^ n) f) - mean f • h.smoothedOperator c η
  have hv : v = (Q ^ n - rankOne mean η) (Q f) := by
    change (Q ^ n) (Q f) - mean f • η = (Q ^ n) (Q f) - mean (Q f) • η
    rw [hmean]
  have hp : Q ((Q ^ n) f) = (Q ^ n) (Q f) := by
    change (Q * Q ^ n) f = (Q ^ n * Q) f
    rw [← pow_succ', ← pow_succ]
  have hFa : (F : M → ℝ) =ᵐ[ρ] v := by
    have hsη := h.smoothedOperator_ae c η
    rw [hη] at hsη
    filter_upwards [h.smoothedOperator_ae c ((Q ^ n) f), hsη,
      Lp.coeFn_sub ((Q ^ n) (Q f)) (mean f • η), Lp.coeFn_smul (mean f) η]
      with y hy hηy hsub hmul
    change h.smoothedOperator c ((Q ^ n) f) y - mean f * h.smoothedOperator c η y = v y
    rw [hy, hp, hηy]
    simp only [Pi.sub_apply] at hsub
    simp only [Pi.smul_apply, smul_eq_mul] at hmul
    exact (hsub.trans (by rw [hmul])).symm
  calc
    _ = ‖F x‖ := rfl
    _ ≤ ‖v‖ := h.continuous_representative_bound F v hFa x
    _ ≤ ε * ‖Q f‖ := by
      rw [hv]
      exact ((Q ^ n - rankOne mean η).le_opNorm (Q f)).trans
        (mul_le_mul_of_nonneg_right hgap (norm_nonneg _))

/-- The smoothed norm retains the target's one-step mass. The input class is a weighted target
indicator, specified by its measurable representative. -/
theorem HypothesisH.target_operator_norm_le (h : HypothesisH ρ K)
    (c B δ : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (U : Set M) (hU : MeasurableSet U) (η : M → ℝ)
    (hη : ∀ y, 0 ≤ η y ∧ η y ≤ B)
    (f : Lp ℝ ∞ ρ) (hrep : f =ᵐ[ρ] U.indicator η)
    (hsmall : ∀ y, (K.kernel y).real U ≤ δ) :
    ‖(c • h.transitionOperator) f‖ ≤ c * B * δ := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hb (x : M) : ‖∫ y, f y ∂K.kernel x‖ ≤ B * δ := by
    rw [integral_congr_ae ((h.absolutelyContinuous x).ae_eq hrep), integral_indicator hU]
    have hηb : ∀ᵐ y ∂(K.kernel x).restrict U, ‖η y‖ ≤ B :=
      Eventually.of_forall (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hη y).1]; exact (hη y).2)
    exact (norm_setIntegral_le_of_norm_le_const_ae (measure_ne_top _ _).lt_top hηb).trans
      (mul_le_mul_of_nonneg_left (hsmall x) hB)
  have hpoint : ∀ᵐ x ∂ρ, ‖((c • h.transitionOperator) f) x‖ ≤ c * B * δ := by
    filter_upwards [h.smoothedOperator_ae c f] with x hx
    rw [← hx, h.smoothedOperator_apply, h.stepEvaluation_apply, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left (hb x) hc).trans_eq (by ring)
  simpa using Lp.norm_le_of_ae_bound (by positivity : 0 ≤ c * B * δ) hpoint


omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The weighted target class is constructed by restricting an L∞ eigenvector. -/
def weightedTargetVector (η : Lp ℝ ∞ ρ) (U : Set M) (hU : MeasurableSet U) : Lp ℝ ∞ ρ :=
  (MemLp.indicator hU.nullMeasurableSet (Lp.memLp η)).toLp (U.indicator η)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem weightedTargetVector_ae (η : Lp ℝ ∞ ρ) (U : Set M) (hU : MeasurableSet U)
    (g : M → ℝ) (hη : η =ᵐ[ρ] g) :
    weightedTargetVector η U hU =ᵐ[ρ] U.indicator g := by
  refine (MemLp.indicator hU.nullMeasurableSet (Lp.memLp η)).coeFn_toLp.trans ?_
  filter_upwards [hη] with y hy
  by_cases hyU : y ∈ U <;> simp [hyU, hy]

/-- The measurable eigenfunction represents an eigenvector of the constructed
normalized operator. -/
theorem HypothesisH.normalized_eigenvector (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (η : Lp ℝ ∞ ρ)
    (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal) :
    ((d.rate.toReal)⁻¹ • h.transitionOperator) η = η := by
  apply Lp.ext
  refine (h.smoothedOperator_ae (d.rate.toReal)⁻¹ η).symm.trans ?_
  filter_upwards [hη] with y hy
  exact (h.smoothed_eigenvector d η hη y).trans hy.symm

/-- The smoothed positive-time target vector is exactly the Doob return probability multiplied by
the eigenfunction. -/
theorem HypothesisH.smoothed_target_doob (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (η : Lp ℝ ∞ ρ)
    (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal)
    (U : Set M) (hU : MeasurableSet U) (f : Lp ℝ ∞ ρ)
    (hrep : f =ᵐ[ρ] U.indicator (fun y => (d.weight y).toReal))
    (n : ℕ) (x : d.State) :
    h.smoothedOperator (d.rate.toReal)⁻¹
        ((((d.rate.toReal)⁻¹ • h.transitionOperator) ^ n) f) x.val =
      (d.weight x.val).toReal * ((d.kernel ^ (n + 1)) x).real (Subtype.val ⁻¹' U) := by
  obtain ⟨R, hR0, hRt, hR⟩ := h.weight_bounded d η hη
  let g : M → ℝ≥0∞ := U.indicator d.weight
  have hg : Measurable g := d.measurable_weight.indicator hU
  have hgb : ∀ y, g y ≤ R := fun y => by
    by_cases hy : y ∈ U
    · simpa [g, hy] using hR y
    · simp [g, hy]
  have hc := StationaryClusters.kernelWord_toReal_bounded K
    [(n + 1, fun _ => (1 : ℝ≥0∞))] (by simp) (by simp)
    g hg R hR0 hRt hgb x.val
  have hgr : (fun y => (g y).toReal) = U.indicator (fun y => (d.weight y).toReal) := by
    funext y
    by_cases hy : y ∈ U <;> simp [g, hy]
  simp only [PathMixing.kernelWord, one_mul, PathMixing.realKernelWord,
    ENNReal.toReal_one, hgr] at hc
  have hd := d.lintegral_power_ambient (n + 1) x
    (U.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hU)
  have hind : (fun y => d.weight y * U.indicator (fun _ => (1 : ℝ≥0∞)) y) = g := by
    funext y
    by_cases hy : y ∈ U <;> simp [g, hy]
  have hlive : (fun y : d.State => U.indicator (fun _ => (1 : ℝ≥0∞)) y.val) =
      (Subtype.val ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext y
    rfl
  rw [hlive, lintegral_indicator (hU.preimage measurable_subtype_coe),
    lintegral_one, Measure.restrict_apply_univ, hind] at hd
  have hdreal := congrArg ENNReal.toReal hd
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, hc] at hdreal
  rw [h.smoothedOperator_apply, h.stepEvaluation_power,
    h.kernelIterate_succ_congr _ n hrep, kernelIterate_normalization]
  change _ = (d.weight x.val).toReal * ((d.kernel ^ (n + 1)) x (Subtype.val ⁻¹' U)).toReal
  rw [hdreal]
  have hx : (d.weight x.val).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨x.property, d.weight_ne_top x.val⟩
  field_simp

/-- Doob return probabilities, with the one-step small-target mass retained in the error. Here `mean
f` is the stationary weighted target mass once the eigenfunctional is identified with the
eigenmeasure. -/
theorem HypothesisH.doob_return_bound (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (η : Lp ℝ ∞ ρ)
    (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal)
    (U : Set M) (hU : MeasurableSet U) (f : Lp ℝ ∞ ρ)
    (hrep : f =ᵐ[ρ] U.indicator (fun y => (d.weight y).toReal))
    (hmean : mean (((d.rate.toReal)⁻¹ • h.transitionOperator) f) = mean f)
    (B δ ηstar : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hηstar : 0 < ηstar)
    (hweight : ∀ y, (d.weight y).toReal ≤ B)
    (hsmall : ∀ y, (K.kernel y).real U ≤ δ)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ‖((d.rate.toReal)⁻¹ • h.transitionOperator) ^ n - rankOne mean η‖ ≤ ε)
    (x : d.State) (hx : ηstar ≤ (d.weight x.val).toReal) :
    ((d.kernel ^ (n + 1)) x).real (Subtype.val ⁻¹' U) ≤
      mean f + (ε * (d.rate.toReal)⁻¹ * B / ηstar) * δ := by
  have hc : 0 ≤ (d.rate.toReal)⁻¹ := by positivity
  have he := h.refined_power_error (d.rate.toReal)⁻¹ mean η f
    (h.normalized_eigenvector d η hη) hmean n ε hε hgap x.val
  rw [h.smoothed_target_doob d η hη U hU f hrep n x,
    h.smoothed_eigenvector d η hη] at he
  have hn := h.target_operator_norm_le (d.rate.toReal)⁻¹ B δ hc hB hδ U hU
    (fun y => (d.weight y).toReal) (fun y => ⟨ENNReal.toReal_nonneg, hweight y⟩)
    f hrep hsmall
  have he' := (le_abs_self _).trans (he.trans (mul_le_mul_of_nonneg_left hn hε))
  have hp : 0 < (d.weight x.val).toReal := hηstar.trans_le hx
  have hb : ε * (d.rate.toReal)⁻¹ * B * δ / (d.weight x.val).toReal ≤
      ε * (d.rate.toReal)⁻¹ * B * δ / ηstar :=
    div_le_div_of_nonneg_left (by positivity) hηstar hx
  have hret : ((d.kernel ^ (n + 1)) x).real (Subtype.val ⁻¹' U) ≤
      mean f + ε * (d.rate.toReal)⁻¹ * B * δ / (d.weight x.val).toReal := by
    have hh : ((d.kernel ^ (n + 1)) x).real (Subtype.val ⁻¹' U) - mean f ≤
        ε * (d.rate.toReal)⁻¹ * B * δ / (d.weight x.val).toReal := by
      apply (le_div_iff₀ hp).mpr
      nlinarith [he']
    linarith
  calc
    _ ≤ mean f + ε * (d.rate.toReal)⁻¹ * B * δ / (d.weight x.val).toReal := hret
    _ ≤ mean f + ε * (d.rate.toReal)⁻¹ * B * δ / ηstar := add_le_add_right hb _
    _ = _ := by ring


omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The spectral functional evaluated on a weighted target indicator is the mass of that target for
the weighted measure. -/
theorem weighted_target_mean (d : DoobTransform.EigenData K.kernel)
    (μ : Measure M) (hμρ : μ ≪ ρ) (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ)
    (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (U : Set M) (hU : MeasurableSet U) (f : Lp ℝ ∞ ρ)
    (hrep : f =ᵐ[ρ] U.indicator (fun y => (d.weight y).toReal)) :
    mean f = (μ.withDensity d.weight).real U := by
  rw [hmean, integral_congr_ae (hμρ.ae_eq hrep), integral_indicator hU,
    integral_toReal d.measurable_weight.aemeasurable
      (ae_of_all _ (fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y)))]
  exact congrArg ENNReal.toReal (withDensity_apply d.weight hU).symm

/-- Step 2 of the rare-event argument, including the first return. The zero-th spectral error is
absorbed into the constant, so no positive gap is lost. The leading term is the weighted target
mass. -/
theorem HypothesisH.doob_short_return (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel)
    (μ : Measure M) (hμρ : μ ≪ ρ) (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ)
    (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (η : Lp ℝ ∞ ρ) (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal)
    (U : Set M) (hU : MeasurableSet U) (f : Lp ℝ ∞ ρ)
    (hrep : f =ᵐ[ρ] U.indicator (fun y => (d.weight y).toReal))
    (hleft : mean (((d.rate.toReal)⁻¹ • h.transitionOperator) f) = mean f)
    (B δ ηstar A θ : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hηstar : 0 < ηstar)
    (hA : 0 ≤ A) (hθ : 0 ≤ θ)
    (hweight : ∀ y, (d.weight y).toReal ≤ B)
    (hsmall : ∀ y, (K.kernel y).real U ≤ δ)
    (hgap : ∀ n : ℕ, 1 ≤ n →
      ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n - rankOne mean η‖ ≤ A * θ^n)
    (n : ℕ) (x : d.State) (hx : ηstar ≤ (d.weight x.val).toReal) :
    ((d.kernel ^ (n + 1)) x).real (Subtype.val ⁻¹' U) ≤
      (μ.withDensity d.weight).real U +
        (max A ‖1 - rankOne mean η‖ * (d.rate.toReal)⁻¹ * B / ηstar) * θ^n * δ := by
  let A' := max A ‖1 - rankOne mean η‖
  have hA' : 0 ≤ A' := hA.trans (le_max_left _ _)
  have hgap' : ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n - rankOne mean η‖ ≤ A' * θ^n := by
    rcases n with _ | n
    · simp [A']
    · exact (hgap (n + 1) (Nat.le_add_left 1 n)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ _))
  have hb := h.doob_return_bound d mean η hη U hU f hrep hleft B δ ηstar
    hB hδ hηstar hweight hsmall n (A' * θ^n) (mul_nonneg hA' (pow_nonneg hθ _)) hgap' x hx
  rw [weighted_target_mean d μ hμρ mean hmean U hU f hrep] at hb
  convert hb using 1
  dsimp [A']
  ring

end ConditionedStableLaws.StandingHypothesis
