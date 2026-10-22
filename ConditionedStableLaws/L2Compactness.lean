import ConditionedStableLaws.KernelLp
import ConditionedStableLaws.RestrictLp
import ConditionedStableLaws.LpCompatibility
import ConditionedStableLaws.LpMidpointInterpolation
import ConditionedStableLaws.LpCompactInterpolation
import ConditionedStableLaws.HypothesisSpectralGap
import ConditionedStableLaws.EigenmeasureDensity
import ConditionedStableLaws.SpectralAlgebra

/-!
# Compactness and the spectral gap on `L∞(μ)` and `L²(μ)`

Let `μ` be the normalized quasi-stationary measure, `η` the normalized eigenfunction and `λ` the
eigenvalue. The normalized operator `P̂ f = λ⁻¹ ∫ f(y) K(·,dy)` and the remainder `R = P̂ - Π`, `Π f
= μ(f) η`, are compact on `L∞(μ)` and `L²(μ)`, and `‖Rᵐ‖_{L²(μ)} ≤ C κᵐ` for `m ≥ 1`. The proof:

* `P̂` and `R` act on `L¹(μ)` with `‖Rᵐ‖ ≤ 2` (left eigenmeasure);
* compactness and the exponential gap pass from `L∞(ρ)` to `L∞(μ)` through the restriction map,
  using norm-preserving lifts of bounded representatives;
* the `L²(μ)` operators are constructed directly from the kernel by integral Cauchy–Schwarz;
* compactness of the `L²` remainder follows from the finite-measure `L¹`–`L∞` midpoint compact
  interpolation theorem, compactness of `P̂` then follows from `P̂ = R + Π`, and the `L²` decay uses
  the midpoint norm interpolation estimate.

All interpolated operators are identified with the direct kernel realization by their action on
representatives.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.L2Compactness

noncomputable section

open KernelLp

section Identities

/-! ### Projection identities for any realization of `P̂`, `Π` on some `Lᵖ(μ)` -/

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} {μ : Measure M} {c : ℝ≥0∞}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A rank-one operator is compact. -/
theorem isCompactOperator_smulRight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E →L[ℝ] ℝ) (v : E) : IsCompactOperator (φ.smulRight v) := by
  have h := (isCompactOperator_of_locallyCompactSpace_dom φ).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℝ v)
  convert h using 1
  funext x
  simp

/-- The three projection identities `ΠΠ = Π`, `ΠP̂ = Π`, `P̂Π = Π`, for any
operator acting as the normalized kernel integral, the integral functional,
and a representative of a normalized eigenfunction. -/
theorem projection_identities (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) (hc0 : c ≠ 0)
    (η : M → ℝ) (hηK : ∀ x, kint K η x = c.toReal * η x) (hημ : ∫ x, η x ∂μ = 1)
    (hint : ∀ f : Lp ℝ p μ, Integrable (f : M → ℝ) μ)
    (P : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (hP : ∀ f, P f =ᵐ[μ] fun x => (c.toReal)⁻¹ * kint K f x)
    (mean : Lp ℝ p μ →L[ℝ] ℝ) (hmean : ∀ f, mean f = ∫ x, f x ∂μ)
    (e : Lp ℝ p μ) (he : (e : M → ℝ) =ᵐ[μ] η) :
    let Pr := mean.smulRight e
    Pr * Pr = Pr ∧ Pr * P = Pr ∧ P * Pr = Pr := by
  intro Pr
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  have hme : mean e = 1 := by rw [hmean, integral_congr_ae he, hημ]
  have hmP (f : Lp ℝ p μ) : mean (P f) = mean f := by
    rw [hmean, hmean, integral_congr_ae (hP f), integral_const_mul,
      integral_kint hK hc (hint f), inv_mul_cancel_left₀ hcr.ne']
  have hPe : P e = e := by
    apply Lp.ext
    filter_upwards [hP e, kint_congr hK he, he] with x h1 h2 h3
    rw [h1, h2, hηK, inv_mul_cancel_left₀ hcr.ne', h3]
  refine ⟨?_, ?_, ?_⟩
  · ext1 f
    simp [Pr, hme]
  · ext1 f
    simp [Pr, hmP]
  · ext1 f
    simp [Pr, hPe]

/-- Positive powers: `P̂ⁿ = Π + Rⁿ` with `R = P̂ - Π`. -/
theorem pow_eq_projection_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P Pr : E →L[ℝ] E} (h : Pr * Pr = Pr ∧ Pr * P = Pr ∧ P * Pr = Pr) (n : ℕ) (hn : 1 ≤ n) :
    (P - Pr) ^ n = P ^ n - Pr := by
  rw [SpectralAlgebra.operator_pow_eq_projection_add P Pr h.1 h.2.1 h.2.2 n hn]
  abel

end Identities


section Concrete

/-! ### The concrete operators from Hypothesis H -/

open StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M} (d : DoobTransform.EigenData K.kernel)
  (μ : Measure M) [IsProbabilityMeasure μ]

/-- The eigenfunction `η` as a real function. -/
def eta : M → ℝ := fun x => (d.weight x).toReal

/-- The eigenvalue `λ`. -/
def rate : ℝ := d.rate.toReal

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem rate_pos : 0 < rate d := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem eta_nonneg (x : M) : 0 ≤ eta d x := ENNReal.toReal_nonneg

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurable_eta : Measurable (eta d) := d.measurable_weight.ennreal_toReal

omit [CompactSpace M] [BorelSpace M] in
theorem continuous_eta (hc : Continuous d.weight) : Continuous (eta d) :=
  continuous_iff_continuousAt.mpr fun x =>
    (ENNReal.continuousAt_toReal (d.weight_ne_top x)).comp hc.continuousAt

omit [BorelSpace M] in
theorem exists_eta_bound (hc : Continuous d.weight) : ∃ B : ℝ, ∀ x, ‖eta d x‖ ≤ B := by
  let f : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨_, continuous_eta d hc⟩
  exact ⟨‖f‖, fun x => f.norm_coe_le_norm x⟩

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The right eigen-relation `∫ η dK(x) = λ η(x)`. -/
theorem kint_eta (x : M) : kint K.kernel (eta d) x = rate d * eta d x := by
  change (∫ y, (d.weight y).toReal ∂K.kernel x) = d.rate.toReal * (d.weight x).toReal
  rw [integral_toReal d.measurable_weight.aemeasurable
    (ae_of_all _ (fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y))), d.right_eigen,
    ENNReal.toReal_mul]

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] [IsProbabilityMeasure μ] in
theorem integral_eta (hnorm : ∫⁻ x, d.weight x ∂μ = 1) : ∫ x, eta d x ∂μ = 1 := by
  change (∫ x, (d.weight x).toReal ∂μ) = 1
  rw [integral_toReal d.measurable_weight.aemeasurable
    (ae_of_all _ (fun x => lt_top_iff_ne_top.mpr (d.weight_ne_top x))), hnorm]
  simp

omit [BorelSpace M] in
omit [IsProbabilityMeasure μ] in
theorem memLp_eta (hc : Continuous d.weight) : MemLp (eta d) ∞ μ :=
  memLp_top_of_bound (measurable_eta d).aestronglyMeasurable _
    (ae_of_all _ (exists_eta_bound d hc).choose_spec)

/-- `η` in `L∞(μ)`, `L²(μ)`, and `L¹(μ)`. -/
def etaInf (hc : Continuous d.weight) : Lp ℝ ∞ μ := (memLp_eta d μ hc).toLp _
def etaL2 (hc : Continuous d.weight) : Lp ℝ 2 μ :=
  ((memLp_eta d μ hc).mono_exponent le_top).toLp _
def etaL1 (hc : Continuous d.weight) : Lp ℝ 1 μ :=
  ((memLp_eta d μ hc).mono_exponent le_top).toLp _

variable (hleft : K.kernel ∘ₘ μ = d.rate • μ)

/-- The normalized operator `P̂` on `L∞(μ)`, `L²(μ)`, and `L¹(μ)`. -/
def PInf : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ := (rate d)⁻¹ • opLinf hleft
def P2 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (rate d)⁻¹ • opL2 hleft d.rate_ne_top
def P1 : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ := (rate d)⁻¹ • opL1 hleft d.rate_ne_top

/-- Integration against the probability measure `μ` on `L²(μ)`, realized as
the inner product with the constant-one function. -/
def oneL2 : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp _
def meanL2 : Lp ℝ 2 μ →L[ℝ] ℝ := innerSL ℝ (oneL2 (μ := μ))

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem meanL2_apply (f : Lp ℝ 2 μ) : meanL2 (μ := μ) f = ∫ x, f x ∂μ := by
  rw [meanL2, innerSL_apply_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (μ := μ) (p := 2) (1 : ℝ)).coeFn_toLp] with x hx
  simp [oneL2]

/-- The projection `Π f = μ(f) η` and remainder `R = P̂ - Π`. -/
def PrInf (hc : Continuous d.weight) : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ :=
  meanLinf.smulRight (etaInf d μ hc)
def Pr2 (hc : Continuous d.weight) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (meanL2 (μ := μ)).smulRight (etaL2 d μ hc)
def Pr1 (hc : Continuous d.weight) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ :=
  meanL1.smulRight (etaL1 d μ hc)
def RInf (hc : Continuous d.weight) := PInf d μ hleft - PrInf d μ hc
def R2 (hc : Continuous d.weight) := P2 d μ hleft - Pr2 d μ hc
def R1 (hc : Continuous d.weight) := P1 d μ hleft - Pr1 d μ hc

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem PInf_ae (f : Lp ℝ ∞ μ) :
    PInf d μ hleft f =ᵐ[μ] fun x => (rate d)⁻¹ * kint K.kernel f x := by
  filter_upwards [Lp.coeFn_smul (rate d)⁻¹ (opLinf hleft f), opLinf_ae hleft f] with x h1 h2
  simp only [PInf, smul_apply, h1, Pi.smul_apply, h2, smul_eq_mul]

omit [IsProbabilityMeasure μ] in
omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem P1_ae (f : Lp ℝ 1 μ) :
    P1 d μ hleft f =ᵐ[μ] fun x => (rate d)⁻¹ * kint K.kernel f x := by
  filter_upwards [Lp.coeFn_smul (rate d)⁻¹ (opL1 hleft d.rate_ne_top f),
    opL1_ae hleft d.rate_ne_top f] with x h1 h2
  simp only [P1, smul_apply, h1, Pi.smul_apply, h2, smul_eq_mul]

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem P2_ae (f : Lp ℝ 2 μ) :
    P2 d μ hleft f =ᵐ[μ] fun x => (rate d)⁻¹ * kint K.kernel f x := by
  filter_upwards [Lp.coeFn_smul (rate d)⁻¹ (opL2 hleft d.rate_ne_top f),
    opL2_ae hleft d.rate_ne_top f] with x h1 h2
  simp only [P2, smul_apply, h1, Pi.smul_apply, h2, smul_eq_mul]

omit [BorelSpace M] in
theorem R2_ae (hc : Continuous d.weight) (f : Lp ℝ 2 μ) : R2 d μ hleft hc f =ᵐ[μ]
    fun x => (rate d)⁻¹ * kint K.kernel f x - (∫ y, f y ∂μ) * eta d x := by
  filter_upwards [Lp.coeFn_sub (P2 d μ hleft f) (Pr2 d μ hc f), P2_ae d μ hleft f,
    Lp.coeFn_smul (meanL2 (μ := μ) f) (etaL2 d μ hc),
    ((memLp_eta d μ hc).mono_exponent le_top).coeFn_toLp] with x h1 h2 h3 h4
  have h4' : (etaL2 d μ hc : M → ℝ) x = eta d x := h4
  rw [R2, sub_apply, h1, Pi.sub_apply, h2]
  change _ - ((meanL2 (μ := μ) f • etaL2 d μ hc : Lp ℝ 2 μ) : M → ℝ) x = _
  rw [h3, Pi.smul_apply, h4', meanL2_apply, smul_eq_mul]

omit [BorelSpace M] in
theorem identitiesInf (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (hc : Continuous d.weight) :
    PrInf d μ hc * PrInf d μ hc = PrInf d μ hc ∧ PrInf d μ hc * PInf d μ hleft = PrInf d μ hc ∧
      PInf d μ hleft * PrInf d μ hc = PrInf d μ hc :=
  projection_identities hleft d.rate_ne_top d.rate_ne_zero (eta d) (kint_eta d)
    (integral_eta d μ hnorm) integrable_of_Linf _ (PInf_ae d μ hleft) meanLinf
    meanLinf_apply _ (memLp_eta d μ hc).coeFn_toLp

omit [BorelSpace M] in
theorem identities1 (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (hc : Continuous d.weight) :
    Pr1 d μ hc * Pr1 d μ hc = Pr1 d μ hc ∧ Pr1 d μ hc * P1 d μ hleft = Pr1 d μ hc ∧
      P1 d μ hleft * Pr1 d μ hc = Pr1 d μ hc :=
  projection_identities hleft d.rate_ne_top d.rate_ne_zero (eta d) (kint_eta d)
    (integral_eta d μ hnorm) (fun f => L1.integrable_coeFn f) _ (P1_ae d μ hleft) meanL1
    meanL1_apply _ ((memLp_eta d μ hc).mono_exponent le_top).coeFn_toLp

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The `L¹` and `L∞` realizations of `P̂` and of `R` are compatible. -/
theorem P_compatible : Cited.LpCompatible (P1 d μ hleft) (PInf d μ hleft) :=
  LpCompatibility.smul _ (opL1_opLinf_compatible hleft d.rate_ne_top)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The direct `L²` realization agrees with the `L¹` realization on their
common domain. -/
theorem P2_compatible1 : Cited.LpCompatible (P2 d μ hleft) (P1 d μ hleft) := by
  intro f₂ f₁ hf
  filter_upwards [P2_ae d μ hleft f₂, P1_ae d μ hleft f₁,
    kint_congr hleft hf] with x h2 h1 hk
  rw [h2, h1, hk]

omit [BorelSpace M] in
theorem Pr2_compatible1 (hc : Continuous d.weight) :
    Cited.LpCompatible (Pr2 d μ hc) (Pr1 d μ hc) := by
  intro f₂ f₁ hf
  have hm : meanL2 (μ := μ) f₂ = meanL1 (μ := μ) f₁ := by
    rw [meanL2_apply, meanL1_apply, integral_congr_ae hf]
  filter_upwards [Lp.coeFn_smul (meanL2 (μ := μ) f₂) (etaL2 d μ hc),
    Lp.coeFn_smul (meanL1 (μ := μ) f₁) (etaL1 d μ hc),
    ((memLp_eta d μ hc).mono_exponent le_top).coeFn_toLp,
    ((memLp_eta d μ hc).mono_exponent le_top).coeFn_toLp] with x h2 h1 he2 he1
  have he2' : (etaL2 d μ hc : M → ℝ) x = eta d x := he2
  have he1' : (etaL1 d μ hc : M → ℝ) x = eta d x := he1
  change ((meanL2 (μ := μ) f₂ • etaL2 d μ hc : Lp ℝ 2 μ) : M → ℝ) x =
    ((meanL1 (μ := μ) f₁ • etaL1 d μ hc : Lp ℝ 1 μ) : M → ℝ) x
  rw [h2, h1, Pi.smul_apply, Pi.smul_apply, he2', he1', hm]

omit [BorelSpace M] in
theorem R2_compatible1 (hc : Continuous d.weight) :
    Cited.LpCompatible (R2 d μ hleft hc) (R1 d μ hleft hc) :=
  LpCompatibility.sub (P2_compatible1 d μ hleft) (Pr2_compatible1 d μ hc)

omit [BorelSpace M] in
theorem R_compatible (hc : Continuous d.weight) :
    Cited.LpCompatible (R1 d μ hleft hc) (RInf d μ hleft hc) := by
  refine LpCompatibility.sub (P_compatible d μ hleft) ?_
  intro f g hfg
  have hm : meanL1 (μ := μ) f = meanLinf (μ := μ) g := by
    rw [meanL1_apply, meanLinf_apply, integral_congr_ae hfg]
  filter_upwards [Lp.coeFn_smul (meanL1 (μ := μ) f) (etaL1 d μ hc),
    Lp.coeFn_smul (meanLinf (μ := μ) g) (etaInf d μ hc),
    ((memLp_eta d μ hc).mono_exponent le_top).coeFn_toLp, (memLp_eta d μ hc).coeFn_toLp]
    with x h1 h2 h3 h4
  have h3' : (etaL1 d μ hc : M → ℝ) x = eta d x := h3
  have h4' : (etaInf d μ hc : M → ℝ) x = eta d x := h4
  change ((meanL1 (μ := μ) f • etaL1 d μ hc : Lp ℝ 1 μ) : M → ℝ) x =
    ((meanLinf (μ := μ) g • etaInf d μ hc : Lp ℝ ∞ μ) : M → ℝ) x
  rw [h1, h2, Pi.smul_apply, Pi.smul_apply, h3', h4', hm]

omit [BorelSpace M] in
/-- `‖Rⁿ‖ ≤ 2` on `L¹(μ)` for every `n ≥ 1`. -/
theorem norm_R1_pow_le (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (hc : Continuous d.weight) (n : ℕ) (hn : 1 ≤ n) :
    ‖R1 d μ hleft hc ^ n‖ ≤ 2 := by
  have hP : ‖P1 d μ hleft‖ ≤ 1 := by
    calc ‖P1 d μ hleft‖ ≤ ‖(rate d)⁻¹‖ * ‖opL1 hleft d.rate_ne_top‖ := by
          rw [P1]; exact norm_smul_le (rate d)⁻¹ (opL1 hleft d.rate_ne_top)
      _ ≤ (rate d)⁻¹ * d.rate.toReal := by
          rw [Real.norm_of_nonneg (inv_nonneg.2 (rate_pos d).le)]
          exact mul_le_mul_of_nonneg_left (norm_opL1_le _ _) (inv_nonneg.2 (rate_pos d).le)
      _ = 1 := inv_mul_cancel₀ (rate_pos d).ne'
  have hPr : ‖Pr1 d μ hc‖ ≤ 1 := by
    rw [Pr1, ContinuousLinearMap.norm_smulRight_apply]
    have he : ‖etaL1 d μ hc‖ = 1 := by
      rw [L1.norm_eq_integral_norm, ← integral_eta d μ hnorm]
      apply integral_congr_ae
      filter_upwards [((memLp_eta d μ hc).mono_exponent le_top).coeFn_toLp] with x hx
      rw [etaL1, hx, Real.norm_of_nonneg (eta_nonneg d x)]
    rw [he, mul_one]
    exact norm_meanL1_le
  rw [R1, pow_eq_projection_add (identities1 d μ hleft hnorm hc) n hn]
  calc ‖P1 d μ hleft ^ n - Pr1 d μ hc‖ ≤ ‖P1 d μ hleft ^ n‖ + ‖Pr1 d μ hc‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add ((norm_pow_le' _ (by omega)).trans (pow_le_one₀ (norm_nonneg _) hP))
        hPr
    _ = 2 := by norm_num

/-- On `L∞(μ)`: `P̂` and `R` are compact and `‖Rⁿ‖ ≤ C θⁿ` for `n ≥ 1`. Both are transferred from
the operator on `L∞(ρ)` through the restriction map. -/
theorem linf_compact_gap (h : HypothesisH ρ K) (hc : Continuous d.weight)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    IsCompactOperator (PInf d μ hleft) ∧ IsCompactOperator (RInf d μ hleft hc) ∧
      ∃ C θ : ℝ, 0 ≤ C ∧ 0 ≤ θ ∧ θ < 1 ∧
        ∀ n : ℕ, 1 ≤ n → ‖RInf d μ hleft hc ^ n‖ ≤ C * θ ^ n := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hμρ : μ ≪ ρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  obtain ⟨s, hs⟩ := h.exists_survivalGapData_with_mean d hc μ hleft hnorm
  set J := RestrictLp.restrictInf hμρ
  have hlift := RestrictLp.exists_lift hμρ
  set T : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := (rate d)⁻¹ • h.transitionOperator with hT
  have hJP : (PInf d μ hleft).comp J = J.comp T := by
    ext1 f
    apply Lp.ext
    filter_upwards [PInf_ae d μ hleft (J f),
      kint_congr hleft (RestrictLp.restrictInf_ae hμρ f),
      RestrictLp.restrictInf_ae hμρ (T f),
      hμρ.ae_le (Lp.coeFn_smul (rate d)⁻¹ (h.transitionOperator f)),
      hμρ.ae_le (h.transitionOperator_ae f)] with x h1 h2 h3 h4 h5
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, h3, hT,
      smul_apply, h4, Pi.smul_apply, h5, smul_eq_mul]
    rfl
  have hJe : J s.eigenvector = etaInf d μ hc := by
    apply Lp.ext
    filter_upwards [RestrictLp.restrictInf_ae hμρ s.eigenvector,
      hμρ.ae_le s.eigenvector_ae, (memLp_eta d μ hc).coeFn_toLp] with x h1 h2 h3
    rw [h1, h2]
    exact h3.symm
  have hJPr : (PrInf d μ hc).comp J = J.comp (s.mean.smulRight s.eigenvector) := by
    ext1 f
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, PrInf,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply, map_smul, hJe,
      meanLinf_apply, hs, integral_congr_ae (RestrictLp.restrictInf_ae hμρ f)]
  have hPcomp : IsCompactOperator (PInf d μ hleft) := by
    apply RestrictLp.isCompactOperator_of_intertwine J hlift hJP
    rw [hT, FunLike.coe_smul]
    exact h.transitionOperator_isCompact.smul _
  refine ⟨hPcomp, ?_, s.constant, s.decay, s.constant_nonneg, s.decay_nonneg,
    s.decay_lt_one, fun n hn => ?_⟩
  · rw [RInf, FunLike.coe_sub]
    exact hPcomp.sub (isCompactOperator_smulRight _ _)
  · rw [RInf, pow_eq_projection_add (identitiesInf d μ hleft hnorm hc) n hn]
    refine (RestrictLp.opNorm_le_of_intertwine J (RestrictLp.norm_restrictInf_le hμρ) hlift
      (B := T ^ n - s.mean.smulRight s.eigenvector) ?_).trans (s.gap n hn)
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      RestrictLp.intertwine_pow J hJP n, hJPr]

end Concrete


section L2

open StandingHypothesis

theorem sqrt_geometric_le {C θ κ : ℝ} (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hκ : Real.sqrt θ ≤ κ)
    (m : ℕ) : Real.sqrt (C * θ ^ m) ≤ Real.sqrt C * κ ^ m := by
  have hpow : Real.sqrt (θ ^ m) = Real.sqrt θ ^ m := by
    rw [show θ ^ m = (Real.sqrt θ ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hθ]]
    exact Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg θ) m)
  rw [Real.sqrt_mul hC, hpow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg θ) hκ m)
    (Real.sqrt_nonneg C)

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

private theorem r2_geometric_decay_aux
    (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel)
    (hc : Continuous d.weight) (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ κ < 1 ∧
      ∀ m : ℕ, 1 ≤ m → ∀ f, ‖(R2 d μ hleft hc ^ m) f‖ ≤ C * κ ^ m * ‖f‖ := by
  obtain ⟨-, -, C, θ, hC, hθ, hθ1, hgap⟩ := linf_compact_gap d μ hleft h hc hnorm
  set κ := (1 + Real.sqrt θ) / 2
  have hsθ1 : Real.sqrt θ < 1 := by
    rw [Real.sqrt_lt' one_pos]
    simpa using hθ1
  have hκ : Real.sqrt θ ≤ κ := by simp only [κ]; linarith
  have hκpos : 0 < κ := by simp only [κ]; linarith [Real.sqrt_nonneg θ]
  have hκ1 : κ < 1 := by simp only [κ]; linarith
  refine ⟨Real.sqrt (4 * 2) * 2 * Real.sqrt C + 1, κ, by positivity, hκpos, hκ1,
    fun m hm f => ?_⟩
  have hi := LpMidpointInterpolation.midpoint_interpolation_norm
    (R1 d μ hleft hc ^ m) (R2 d μ hleft hc ^ m) (RInf d μ hleft hc ^ m)
    (LpCompatibility.pow (R2_compatible1 d μ hleft hc) m)
    (LpCompatibility.pow (R_compatible d μ hleft hc) m)
    zero_le_two (mul_nonneg hC (pow_nonneg hθ m))
    (fun g => ((R1 d μ hleft hc ^ m).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right (norm_R1_pow_le d μ hleft hnorm hc m hm) (norm_nonneg g)))
    (fun g => ((RInf d μ hleft hc ^ m).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right (hgap m hm) (norm_nonneg g))) f
  refine hi.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg f))
  have hsqrt4 (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hsqrt4 (C * θ ^ m) (mul_nonneg hC (pow_nonneg hθ m))]
  calc
    Real.sqrt (4 * 2) * (2 * Real.sqrt (C * θ ^ m)) ≤
        Real.sqrt (4 * 2) * (2 * (Real.sqrt C * κ ^ m)) := by
      gcongr
      exact sqrt_geometric_le hC hθ hκ m
    _ ≤ (Real.sqrt (4 * 2) * 2 * Real.sqrt C + 1) * κ ^ m := by
      nlinarith [pow_pos hκpos m, Real.sqrt_nonneg (4 * 2)]

/-- The normalized kernel operator and its remainder extend to `L²(μ)`, and the remainder has a
geometric `L²` power bound. The operators are constructed directly from the kernel, and the
geometric power estimate uses the real `L¹`/`L∞` midpoint interpolation bound. -/
theorem _root_.ConditionedStableLaws.StandingHypothesis.HypothesisH.l2_extension_decay
    (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel)
    (hc : Continuous d.weight) (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    (∀ f, PInf d μ hleft f =ᵐ[μ] fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x) ∧
    (∀ f, RInf d μ hleft hc f =ᵐ[μ]
      fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x - (∫ y, f y ∂μ) * eta d x) ∧
    ∃ P₂ R₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      (∀ f, P₂ f =ᵐ[μ] fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x) ∧
      (∀ f, R₂ f =ᵐ[μ]
        fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x - (∫ y, f y ∂μ) * eta d x) ∧
      ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ κ < 1 ∧
        ∀ m : ℕ, 1 ≤ m → ∀ f, ‖(R₂ ^ m) f‖ ≤ C * κ ^ m * ‖f‖ := by
  have hRInf_ae (f : Lp ℝ ∞ μ) : RInf d μ hleft hc f =ᵐ[μ]
      fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x - (∫ y, f y ∂μ) * eta d x := by
    filter_upwards [Lp.coeFn_sub (PInf d μ hleft f) (PrInf d μ hc f), PInf_ae d μ hleft f,
      Lp.coeFn_smul (meanLinf (μ := μ) f) (etaInf d μ hc), (memLp_eta d μ hc).coeFn_toLp]
      with x h1 h2 h3 h4
    have h4' : (etaInf d μ hc : M → ℝ) x = eta d x := h4
    rw [RInf, sub_apply, h1, Pi.sub_apply, h2]
    change _ - ((meanLinf (μ := μ) f • etaInf d μ hc : Lp ℝ ∞ μ) : M → ℝ) x = _
    rw [h3, Pi.smul_apply, h4', meanLinf_apply, smul_eq_mul]
    rfl
  refine ⟨fun f => PInf_ae d μ hleft f, hRInf_ae, P2 d μ hleft, R2 d μ hleft hc,
    fun f => P2_ae d μ hleft f, fun f => R2_ae d μ hleft hc f, ?_⟩
  exact r2_geometric_decay_aux h d hc μ hleft hnorm

/-- **Compactness and spectral gap in `L²(μ)`.** For normalized eigen-data supplied by H, the
normalized operator `P̂` and the remainder `R = P̂ - Π` are compact on `L∞(μ)` and on `L²(μ)`; there
are `C > 0` and `κ ∈ (0,1)` with `‖Rᵐ f‖_{L²(μ)} ≤ C κᵐ ‖f‖_{L²(μ)}` for `m ≥ 1`; and every `Rᵐ`, `m
≥ 1`, is compact on `L²(μ)`. The operators are identified by their action on representatives: `P̂ f
= λ⁻¹ ∫ f dK(·)` and `R f = P̂ f - μ(f) η`. -/
theorem _root_.ConditionedStableLaws.StandingHypothesis.HypothesisH.l2_compactness (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel)
    (hc : Continuous d.weight) (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    -- the `L∞(μ)` operators
    (∀ f, PInf d μ hleft f =ᵐ[μ] fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x) ∧
    (∀ f, RInf d μ hleft hc f =ᵐ[μ]
      fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x - (∫ y, f y ∂μ) * eta d x) ∧
    IsCompactOperator (PInf d μ hleft) ∧ IsCompactOperator (RInf d μ hleft hc) ∧
    -- the `L²(μ)` operators
    ∃ P₂ R₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      (∀ f, P₂ f =ᵐ[μ] fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x) ∧
      (∀ f, R₂ f =ᵐ[μ]
        fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x - (∫ y, f y ∂μ) * eta d x) ∧
      IsCompactOperator P₂ ∧ IsCompactOperator R₂ ∧
      ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ κ < 1 ∧
        (∀ m : ℕ, 1 ≤ m → ∀ f, ‖(R₂ ^ m) f‖ ≤ C * κ ^ m * ‖f‖) ∧
        ∀ m : ℕ, 1 ≤ m → IsCompactOperator (R₂ ^ m) := by
  obtain ⟨hPc, hRc, C, θ, hC, hθ, hθ1, hgap⟩ := linf_compact_gap d μ hleft h hc hnorm
  have hRInf_ae (f : Lp ℝ ∞ μ) : RInf d μ hleft hc f =ᵐ[μ]
      fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x - (∫ y, f y ∂μ) * eta d x := by
    filter_upwards [Lp.coeFn_sub (PInf d μ hleft f) (PrInf d μ hc f), PInf_ae d μ hleft f,
      Lp.coeFn_smul (meanLinf (μ := μ) f) (etaInf d μ hc), (memLp_eta d μ hc).coeFn_toLp]
      with x h1 h2 h3 h4
    have h4' : (etaInf d μ hc : M → ℝ) x = eta d x := h4
    rw [RInf, sub_apply, h1, Pi.sub_apply, h2]
    change _ - ((meanLinf (μ := μ) f • etaInf d μ hc : Lp ℝ ∞ μ) : M → ℝ) x = _
    rw [h3, Pi.smul_apply, h4', meanLinf_apply, smul_eq_mul]
    rfl
  refine ⟨fun f => PInf_ae d μ hleft f, hRInf_ae, hPc, hRc, ?_⟩
  let P₂ := P2 d μ hleft
  let R₂ := R2 d μ hleft hc
  have hR₂1 : Cited.LpCompatible R₂ (R1 d μ hleft hc) := R2_compatible1 d μ hleft hc
  have hR₂c : IsCompactOperator R₂ :=
    LpCompactInterpolation.midpoint_compact_interpolation
      (R1 d μ hleft hc) R₂ (RInf d μ hleft hc)
      hR₂1 (R_compatible d μ hleft hc) hRc
  have hPr₂c : IsCompactOperator (Pr2 d μ hc) := isCompactOperator_smulRight _ _
  have hP₂eq : P₂ = R₂ + Pr2 d μ hc := by
    simp only [P₂, R₂, R2]
    abel
  have hP₂c : IsCompactOperator P₂ := hP₂eq ▸ hR₂c.add hPr₂c
  have hP₂_ae (f : Lp ℝ 2 μ) :
      P₂ f =ᵐ[μ] fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x :=
    P2_ae d μ hleft f
  have hR₂_ae (f : Lp ℝ 2 μ) : R₂ f =ᵐ[μ]
      fun x => (rate d)⁻¹ * ∫ y, f y ∂K.kernel x - (∫ y, f y ∂μ) * eta d x :=
    R2_ae d μ hleft hc f
  obtain ⟨C₂, κ, hC₂, hκ, hκ1, hdecay⟩ := r2_geometric_decay_aux h d hc μ hleft hnorm
  refine ⟨P₂, R₂, hP₂_ae, hR₂_ae, hP₂c, hR₂c, C₂, κ,
    hC₂, hκ, hκ1, hdecay, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp]
  exact hR₂c.comp_clm _

end L2

end

end ConditionedStableLaws.L2Compactness
