import ConditionedStableLaws.L2WeakConvergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Covariance series with a compact spectral remainder

Exponential operator bounds give absolute summability of the covariance
series. For uniformly bounded, weakly null normalized observables, compactness
at each fixed lag and dominated convergence make the entire series vanish.
-/

open Filter
open scoped Topology InnerProductSpace

namespace ConditionedStableLaws

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Quantitative domination of a quadratic operator correlation. -/
theorem norm_inner_operator_le
    (T : E →L[ℝ] E) (v : E) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hv : ‖v‖ ≤ C) (hT : ‖T‖ ≤ D) :
    ‖⟪v, T v⟫_ℝ‖ ≤ C ^ 2 * D := by
  calc
    ‖⟪v, T v⟫_ℝ‖ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm _ _
    _ ≤ C * (D * C) := by
      apply mul_le_mul hv ?_ (norm_nonneg _) hC
      exact (T.le_opNorm v).trans (mul_le_mul hT hv (norm_nonneg _) hD)
    _ = C ^ 2 * D := by ring

/-- Exponential operator decay makes the corresponding covariance series
absolutely convergent. -/
theorem summable_abs_operator_correlations
    (T : ℕ → E →L[ℝ] E) {D θ : ℝ} (hD : 0 ≤ D)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hT : ∀ k, ‖T k‖ ≤ D * θ ^ k) (v : E) :
    Summable (fun k => |⟪v, T k v⟫_ℝ|) := by
  have hs : Summable (fun k : ℕ => ‖v‖ ^ 2 * (D * θ ^ k)) :=
    ((summable_geometric_of_lt_one hθ hθ1).mul_left D).mul_left (‖v‖ ^ 2)
  apply hs.of_norm_bounded
  intro k
  simpa only [Real.norm_eq_abs, abs_abs] using
    norm_inner_operator_le (T k) v (norm_nonneg v)
      (mul_nonneg hD (pow_nonneg hθ k)) le_rfl (hT k)

/-- Dominated convergence for all compact lag operators simultaneously. -/
theorem compact_correlation_series_tendsto_zero [CompleteSpace E]
    (T : ℕ → E →L[ℝ] E) (hcompact : ∀ k, IsCompactOperator (T k))
    {D θ : ℝ} (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hT : ∀ k, ‖T k‖ ≤ D * θ ^ k)
    (u : ℕ → E) (C : ℝ) (hbound : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ v : E, Tendsto (fun n => ⟪v, u n⟫_ℝ) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' k, ⟪u n, T k (u n)⟫_ℝ) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hbound 0)
  have hs : Summable (fun k : ℕ => C ^ 2 * (D * θ ^ k)) :=
    ((summable_geometric_of_lt_one hθ hθ1).mul_left D).mul_left (C ^ 2)
  have h := tendsto_tsum_of_dominated_convergence hs
    (fun k => inner_compactOperator_tendsto_zero (T k) (hcompact k) u C hbound hweak)
    (Eventually.of_forall fun n k => norm_inner_operator_le (T k) (u n) hC
      (mul_nonneg hD (pow_nonneg hθ k)) (hbound n) (hT k))
  simpa using h

/-- Absolute covariance sums also vanish, a stronger conclusion than signed
covariance convergence. -/
theorem compact_abs_correlation_series_tendsto_zero [CompleteSpace E]
    (T : ℕ → E →L[ℝ] E) (hcompact : ∀ k, IsCompactOperator (T k))
    {D θ : ℝ} (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hT : ∀ k, ‖T k‖ ≤ D * θ ^ k)
    (u : ℕ → E) (C : ℝ) (hbound : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ v : E, Tendsto (fun n => ⟪v, u n⟫_ℝ) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' k, |⟪u n, T k (u n)⟫_ℝ|) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hbound 0)
  have hs : Summable (fun k : ℕ => C ^ 2 * (D * θ ^ k)) :=
    ((summable_geometric_of_lt_one hθ hθ1).mul_left D).mul_left (C ^ 2)
  have h := tendsto_tsum_of_dominated_convergence hs
    (fun k => (inner_compactOperator_tendsto_zero (T k) (hcompact k) u C hbound hweak).abs)
    (Eventually.of_forall fun n k => by
      simpa only [Real.norm_eq_abs, abs_abs] using
        norm_inner_operator_le (T k) (u n) hC
          (mul_nonneg hD (pow_nonneg hθ k)) (hbound n) (hT k))
  simpa using h

/-- The positive powers of a compact spectral remainder stay compact, including after composition
with a bounded multiplication operator. -/
theorem compact_spectral_lag_operator
    (R A : E →L[ℝ] E) (hR : IsCompactOperator R) (k : ℕ) :
    IsCompactOperator ((R ^ (k + 1)).comp A) := by
  have hpow : IsCompactOperator (R ^ (k + 1)) := by
    rw [pow_succ]
    exact hR.clm_comp (R ^ k)
  exact hpow.comp_clm A

/-- The α=2 covariance-series step for L² observables: boundedness and almost-everywhere convergence
give the weak convergence needed by compactness. The exponential L² spectral estimate is a
hypothesis. -/
theorem L2_covariance_series_tendsto_zero
    {M : Type*} [MeasurableSpace M] {μ : MeasureTheory.Measure M}
    [MeasureTheory.IsFiniteMeasure μ]
    (R A : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ)
    (hR : IsCompactOperator R)
    {D θ : ℝ} (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hdecay : ∀ k : ℕ, ‖R ^ (k + 1)‖ ≤ D * θ ^ k)
    (u : ℕ → MeasureTheory.Lp ℝ 2 μ) (C : ℝ) (hbound : ∀ n, ‖u n‖ ≤ C)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' k, |⟪u n, (R ^ (k + 1)) (A (u n))⟫_ℝ|)
      atTop (𝓝 0) := by
  apply compact_abs_correlation_series_tendsto_zero
    (fun k => (R ^ (k + 1)).comp A) (compact_spectral_lag_operator R A hR)
    (D := D * ‖A‖) (θ := θ) (mul_nonneg hD (norm_nonneg A)) hθ hθ1
    ?_ u C hbound (L2_inner_tendsto_of_bounded_ae u C hbound hae)
  intro k
  calc
    ‖(R ^ (k + 1)).comp A‖ ≤ ‖R ^ (k + 1)‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (D * θ ^ k) * ‖A‖ := mul_le_mul_of_nonneg_right (hdecay k) (norm_nonneg A)
    _ = (D * ‖A‖) * θ ^ k := by ring

end ConditionedStableLaws
