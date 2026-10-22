import ConditionedStableLaws.Concentration
import ConditionedStableLaws.MGFConvergence
import ConditionedStableLaws.SecondMoment
import ConditionedStableLaws.KernelMixing
import ConditionedStableLaws.EndpointChainBounds

/-!
# Asymptotic variance for bounded observables

For bounded measurable `g`, `ḡ = g - ν(g)` and every `x ∈ M \ Z`, under `ℙₓ(· | τ > n)`, `n^{-1/2}
∑_{j<n} ḡ(X_j) → 𝒩(0, σ_g²)`, `σ_g² = ν(ḡ²) + 2 ∑_{m ≥ 1} μ(ḡ λ^{-m} 𝒫ᵐ(η ḡ))`, the series
converging absolutely and `σ_g² ≥ 0` (for `σ_g² = 0` the limit is `δ₀ = 𝒩(0,0)`). The theorem is the
case `g_n = ḡ`, `a_n = √n` of the conditional triangular-array CLT.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.ConditionalCLT

noncomputable section

open StandingHypothesis CanonicalChain TwistedOperators Concentration

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The centred observable `ḡ = g - ν(g)`. -/
def centered (μ : Measure M) (d : DoobTransform.EigenData C.killedTransition) (g : M → ℝ) :
    M → ℝ :=
  fun y => g y - ∫ z, g z ∂μ.withDensity d.weight

/-- The `m`-th correlation term `μ(ḡ λ^{-(m+1)} 𝒫^{m+1}(η ḡ))`. -/
def correlation (μ : Measure M) (d : DoobTransform.EigenData C.killedTransition) (g : M → ℝ)
    (m : ℕ) : ℝ :=
  ∫ y, centered C μ d g y * ((d.rate.toReal)⁻¹ ^ (m + 1) *
    SecondMoment.kpow C (m + 1) (fun z => (d.weight z).toReal * centered C μ d g z) y) ∂μ

/-- The asymptotic variance `σ_g²`. -/
def asymptoticVariance (μ : Measure M) (d : DoobTransform.EigenData C.killedTransition)
    (g : M → ℝ) : ℝ :=
  ∫ y, centered C μ d g y ^ 2 ∂μ.withDensity d.weight + 2 * ∑' m : ℕ, correlation C μ d g m

/-- Normalized kernel powers on `L∞(ρ)` classes are the normalized kernel iterates. -/
theorem normalized_pow_ae (h : HypothesisH ρ C.toKilledKernel) [IsFiniteMeasure ρ] (r : ℝ)
    (W : Lp ℝ ∞ ρ) {w : M → ℝ} (hw : Measurable w) {B : ℝ} (hB : ∀ y, |w y| ≤ B)
    (hWw : (W : M → ℝ) =ᵐ[ρ] w) (m : ℕ) :
    ((((r⁻¹ • h.transitionOperator : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ) ^ m) W : Lp ℝ ∞ ρ) : M → ℝ)
      =ᵐ[ρ] fun y => r⁻¹ ^ m * SecondMoment.kpow C m w y := by
  induction m with
  | zero =>
    rw [pow_zero, one_apply_eq_self]
    filter_upwards [hWw] with y hy
    rw [hy, SecondMoment.kpow_zero C w hw]
    simp
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp, smul_apply]
    set V : Lp ℝ ∞ ρ := ((r⁻¹ • h.transitionOperator) ^ m) W
    filter_upwards [Lp.coeFn_smul r⁻¹ (h.transitionOperator V), h.transitionOperator_ae V]
      with y h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have h3 : ∫ z, V z ∂C.toKilledKernel.kernel y =
        ∫ z, r⁻¹ ^ m * SecondMoment.kpow C m w z ∂C.killedTransition y :=
      integral_congr_ae ((h.absolutelyContinuous y).ae_eq ih)
    rw [h3, integral_const_mul, SecondMoment.kpow_succ C m hw hB y, pow_succ]
    ring

end

end ConditionedStableLaws.ConditionalCLT
