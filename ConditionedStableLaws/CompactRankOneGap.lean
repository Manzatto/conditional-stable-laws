import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Tactic
import ConditionedStableLaws.SpectralAlgebra

/-!
# A strict spectral gap after removing a simple peripheral eigenvalue

This applies to the kernel operator once positivity, simplicity, and peripheral exclusion are known.
Compact Fredholm theory and compactness of the spectrum give the strict gap.
-/

open Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.CompactRankOneGap
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def remainder (T : E →L[ℂ] E) (r : ℝ) (η : E) (ℓ : E →L[ℂ] ℂ) : E →L[ℂ] E :=
  T - ℓ.smulRight ((r : ℂ) • η)

omit [CompleteSpace E] in
theorem remainder_isCompact (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (r : ℝ) (η : E) (ℓ : E →L[ℂ] ℂ) : IsCompactOperator (remainder T r η ℓ) := by
  apply hT.sub
  exact (isCompactOperator_of_locallyCompactSpace_dom ℓ).continuous_comp
    (continuous_id.smul continuous_const)

omit [CompleteSpace E] in
theorem mean_remainder (T : E →L[ℂ] E) (r : ℝ) (η : E) (ℓ : E →L[ℂ] ℂ)
    (hℓη : ℓ η = 1) (hℓT : ∀ f, ℓ (T f) = (r : ℂ) * ℓ f) (f : E) :
    ℓ (remainder T r η ℓ f) = 0 := by
  change ℓ (T f - ℓ f • ((r : ℂ) • η)) = 0
  simp only [map_sub, map_smul, hℓT, hℓη, smul_eq_mul, mul_one]
  ring

/-- Every spectral point of the rank-one remainder lies strictly inside the leading circle. The
peripheral exclusion and simplicity inputs are eigenfunction statements. -/
theorem norm_mem_spectrum_remainder_lt (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {r : ℝ} (hr : 0 < r) (η : E) (ℓ : E →L[ℂ] ℂ)
    (hℓη : ℓ η = 1) (hℓT : ∀ f, ℓ (T f) = (r : ℂ) * ℓ f)
    (hbound : ∀ (f : E), f ≠ 0 → ∀ z : ℂ, T f = z • f → ‖z‖ ≤ r)
    (hperipheral : ∀ (f : E), f ≠ 0 → ∀ z : ℂ, T f = z • f → ‖z‖ = r → z = (r : ℂ))
    (hsimple : ∀ f : E, T f = (r : ℂ) • f → ∃ c : ℂ, f = c • η)
    {z : ℂ} (hz : z ∈ spectrum ℂ (remainder T r η ℓ)) : ‖z‖ < r := by
  by_cases hz0 : z = 0
  · simpa [hz0] using hr
  have hRe := ((remainder_isCompact T hT r η ℓ).hasEigenvalue_iff_mem_spectrum hz0).mpr hz
  obtain ⟨f, hf⟩ := hRe.exists_hasEigenvector
  have hRf : remainder T r η ℓ f = z • f := hf.apply_eq_smul
  have hℓf : ℓ f = 0 := by
    have he := congrArg ℓ hRf
    rw [mean_remainder T r η ℓ hℓη hℓT, map_smul, smul_eq_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hz0
  have hTf : T f = z • f := by
    change T f - ℓ f • ((r : ℂ) • η) = z • f at hRf
    simpa only [hℓf, zero_smul, sub_zero] using hRf
  apply lt_of_le_of_ne (hbound f hf.2 z hTf)
  intro heq
  have hzr := hperipheral f hf.2 z hTf heq
  obtain ⟨c, hc⟩ := hsimple f (by rwa [← hzr])
  have hc0 : c = 0 := by
    rw [hc, map_smul, hℓη, smul_eq_mul, mul_one] at hℓf
    exact hℓf
  exact hf.2 (by rw [hc, hc0, zero_smul])

/-- Compactness of the complex spectrum upgrades pointwise strictness to a
strict spectral-radius inequality. -/
theorem spectralRadius_remainder_lt [Nontrivial E]
    (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {r : ℝ} (hr : 0 < r) (η : E) (ℓ : E →L[ℂ] ℂ)
    (hℓη : ℓ η = 1) (hℓT : ∀ f, ℓ (T f) = (r : ℂ) * ℓ f)
    (hbound : ∀ (f : E), f ≠ 0 → ∀ z : ℂ, T f = z • f → ‖z‖ ≤ r)
    (hperipheral : ∀ (f : E), f ≠ 0 → ∀ z : ℂ, T f = z • f → ‖z‖ = r → z = (r : ℂ))
    (hsimple : ∀ f : E, T f = (r : ℂ) • f → ∃ c : ℂ, f = c • η) :
    spectralRadius ℂ (remainder T r η ℓ) < ENNReal.ofReal r := by
  rw [ENNReal.ofReal_eq_coe_nnreal hr.le]
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro z hz
  exact norm_mem_spectrum_remainder_lt T hT hr η ℓ hℓη hℓT hbound hperipheral hsimple hz

omit [CompleteSpace E] in
/-- The exact normalized power error is the normalized remainder power. -/
theorem normalized_power_error (T : E →L[ℂ] E) {r : ℝ} (hr : r ≠ 0)
    (η : E) (ℓ : E →L[ℂ] ℂ) (hℓη : ℓ η = 1)
    (hTη : T η = (r : ℂ) • η) (hℓT : ∀ f, ℓ (T f) = (r : ℂ) * ℓ f)
    (n : ℕ) (hn : 1 ≤ n) :
    (((r : ℂ)⁻¹ • T)^n - ℓ.smulRight η) = (r : ℂ)⁻¹^n • (remainder T r η ℓ)^n := by
  let piOp := ℓ.smulRight η
  let Q := (r : ℂ)⁻¹ • T
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hpp : piOp*piOp = piOp := by
    ext f
    simp [piOp, mul_apply_eq_comp, hℓη]
  have hpq : piOp*Q = piOp := by
    ext f
    change ℓ ((r : ℂ)⁻¹ • T f) • η = ℓ f • η
    rw [map_smul, hℓT, smul_eq_mul, inv_mul_cancel_left₀ hrC]
  have hqp : Q*piOp = piOp := by
    ext f
    change (r : ℂ)⁻¹ • T (ℓ f • η) = ℓ f • η
    rw [map_smul, hTη, smul_comm (ℓ f) (r : ℂ), inv_smul_smul₀ hrC]
  have hpower := SpectralAlgebra.operator_pow_eq_projection_add Q piOp hpp hpq hqp n hn
  have hscaled : Q-piOp = (r : ℂ)⁻¹ • remainder T r η ℓ := by
    ext f
    change (r : ℂ)⁻¹ • T f - ℓ f • η = (r : ℂ)⁻¹ • (T f - ℓ f • ((r : ℂ) • η))
    rw [smul_sub, smul_smul, mul_comm _ (ℓ f), ← smul_smul, inv_smul_smul₀ hrC]
  change Q^n - piOp = _
  rw [hpower, add_sub_cancel_left, hscaled, smul_pow]

end
end ConditionedStableLaws.CompactRankOneGap
