import ConditionedStableLaws.CompactWeakConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# L² weak convergence from boundedness and L¹ convergence

The density argument in the Gaussian boundary proof. Uniform L² boundedness
and convergence to zero in L¹ imply weak convergence to zero in L²; applying
a fixed compact operator makes the quadratic correlation vanish.
-/

open Filter MeasureTheory Set
open scoped Topology InnerProductSpace

namespace ConditionedStableLaws

noncomputable section

variable {M : Type*} [MeasurableSpace M] {μ : Measure M} [IsFiniteMeasure μ]

/-- On a finite measure space, a uniform L² bound and almost-everywhere
convergence to zero imply L¹ convergence to zero. The proof truncates at a
constant height and controls the tail by the square integral. -/
theorem L1_tendsto_zero_of_L2_bounded_ae
    (u : ℕ → Lp ℝ 2 μ) (C : ℝ) (hbound : ∀ n, ‖u n‖ ≤ C)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |u n x| ∂μ) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hbound 0)
  have hu (n : ℕ) : Integrable (fun x => u n x) μ :=
    (Lp.memLp (u n)).integrable (by norm_num)
  have hsq (n : ℕ) : ∫ x, (u n x) ^ 2 ∂μ = ‖u n‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [L2.inner_def, Real.inner_apply, pow_two]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let t : ℝ := 2 * C ^ 2 / ε + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hCt : C ^ 2 / t < ε / 2 := by
    apply (div_lt_iff₀ ht).mpr
    dsimp [t]
    field_simp
    nlinarith
  have hminint (n : ℕ) : Integrable (fun x => min |u n x| t) μ :=
    (hu n).abs.inf (integrable_const t)
  have hminlim : Tendsto (fun n => ∫ x, min |u n x| t ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ : M => (0 : ℝ))
      (fun _ : M => t)
      (fun n => (hminint n).aestronglyMeasurable) (integrable_const t)
      (fun n => Eventually.of_forall fun x => ?_) ?_
    · simpa using h
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) ht.le)]
      exact min_le_right _ _
    · filter_upwards [hae] with x hx
      simpa [ht.le] using hx.abs.min (tendsto_const_nhds (x := t))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hminlim (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hpoint (x : M) : |u n x| ≤ min |u n x| t + (u n x) ^ 2 / t := by
    by_cases hx : |u n x| ≤ t
    · rw [min_eq_left hx]
      exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) ht.le)
    · rw [min_eq_right (le_of_not_ge hx)]
      have hs : |u n x| ≤ (u n x) ^ 2 / t := by
        apply (le_div_iff₀ ht).mpr
        have hsquare : |u n x| ^ 2 = (u n x) ^ 2 := sq_abs _
        nlinarith [abs_nonneg (u n x)]
      linarith
  have hinequality : (∫ x, |u n x| ∂μ) ≤ (∫ x, min |u n x| t ∂μ) + C ^ 2 / t := by
    calc
      (∫ x, |u n x| ∂μ) ≤ ∫ x, min |u n x| t + (u n x) ^ 2 / t ∂μ :=
        integral_mono (hu n).abs
          ((hminint n).add ((Lp.memLp (u n)).integrable_sq.div_const t)) hpoint
      _ = (∫ x, min |u n x| t ∂μ) + ‖u n‖ ^ 2 / t := by
        rw [integral_add (hminint n) ((Lp.memLp (u n)).integrable_sq.div_const t),
          integral_div, hsq n]
      _ ≤ (∫ x, min |u n x| t ∂μ) + C ^ 2 / t := by gcongr; exact hbound n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have hnmin : (∫ x, min |u n x| t ∂μ) < ε / 2 :=
    (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hN n hn)
  linarith

/-- Pairing with a simple L² function is controlled by the L¹ norm. -/
theorem simpleFunc_inner_tendsto_of_L1
    (u : ℕ → Lp ℝ 2 μ)
    (hL1 : Tendsto (fun n => ∫ x, |u n x| ∂μ) atTop (𝓝 0))
    (v : Lp.simpleFunc ℝ 2 μ) :
    Tendsto (fun n => ⟪(v : Lp ℝ 2 μ), u n⟫_ℝ) atTop (𝓝 0) := by
  let s := Lp.simpleFunc.toSimpleFunc v
  obtain ⟨B, hB⟩ := s.finite_range.isBounded.exists_norm_le
  have hbs : ∀ x, ‖s x‖ ≤ B := fun x => hB _ (mem_range_self x)
  have heq (n : ℕ) : ⟪(v : Lp ℝ 2 μ), u n⟫_ℝ = ∫ x, s x * u n x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun v] with x hx
    simp only [Real.inner_apply, ← hx, mul_comm, s]
  apply squeeze_zero_norm (fun n => ?_) (by simpa using hL1.const_mul B)
  rw [heq n]
  have hu : Integrable (fun x => u n x) μ :=
    (Lp.memLp (u n)).integrable (by norm_num)
  calc
    ‖∫ x, s x * u n x ∂μ‖ ≤ ∫ x, ‖s x * u n x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B * |u n x| ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hu.abs.const_mul B)
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [norm_mul, Real.norm_eq_abs (u n x)]
        exact mul_le_mul_of_nonneg_right (hbs x) (abs_nonneg _)
    _ = B * ∫ x, |u n x| ∂μ := integral_const_mul _ _

/-- Uniform L² bounds extend the convergence against simple functions to every L² test function. -/
theorem L2_inner_tendsto_of_bounded_L1
    (u : ℕ → Lp ℝ 2 μ) (C : ℝ) (hbound : ∀ n, ‖u n‖ ≤ C)
    (hL1 : Tendsto (fun n => ∫ x, |u n x| ∂μ) atTop (𝓝 0))
    (g : Lp ℝ 2 μ) :
    Tendsto (fun n => ⟪g, u n⟫_ℝ) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hbound 0)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v, hv⟩ :=
    (Lp.simpleFunc.denseRange (E := ℝ) (μ := μ) (p := 2) (by norm_num)).exists_dist_lt
      g (show 0 < ε / (2 * (C + 1)) by positivity)
  have hvlim := simpleFunc_inner_tendsto_of_L1 u hL1 v
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hvlim (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hdist : ‖g - (v : Lp ℝ 2 μ)‖ < ε / (2 * (C + 1)) := by
    simpa only [dist_eq_norm] using hv
  have hsmall : ‖g - (v : Lp ℝ 2 μ)‖ * C < ε / 2 := by
    have hmul : ‖g - (v : Lp ℝ 2 μ)‖ * (C + 1) < ε / 2 := by
      apply (lt_div_iff₀ (by positivity : 0 < C + 1)).mp
      simpa only [div_div] using hdist
    nlinarith [norm_nonneg (g - (v : Lp ℝ 2 μ))]
  rw [dist_zero_right]
  calc
    ‖⟪g, u n⟫_ℝ‖ = ‖⟪g - (v : Lp ℝ 2 μ), u n⟫_ℝ + ⟪(v : Lp ℝ 2 μ), u n⟫_ℝ‖ := by
      rw [inner_sub_left, sub_add_cancel]
    _ ≤ ‖⟪g - (v : Lp ℝ 2 μ), u n⟫_ℝ‖ + ‖⟪(v : Lp ℝ 2 μ), u n⟫_ℝ‖ := norm_add_le _ _
    _ ≤ ‖g - (v : Lp ℝ 2 μ)‖ * C + ‖⟪(v : Lp ℝ 2 μ), u n⟫_ℝ‖ := by
      gcongr
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _))
    _ < ε / 2 + ε / 2 := add_lt_add hsmall (by simpa only [dist_zero_right] using hN n hn)
    _ = ε := add_halves ε

/-- The fixed-lag compact-operator covariance conclusion used at α=2. -/
theorem L2_inner_tendsto_of_bounded_ae
    (u : ℕ → Lp ℝ 2 μ) (C : ℝ) (hbound : ∀ n, ‖u n‖ ≤ C)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 0))
    (g : Lp ℝ 2 μ) :
    Tendsto (fun n => ⟪g, u n⟫_ℝ) atTop (𝓝 0) :=
  L2_inner_tendsto_of_bounded_L1 u C hbound
    (L1_tendsto_zero_of_L2_bounded_ae u C hbound hae) g

/-- The fixed-lag compact-operator covariance conclusion used at α=2. -/
theorem L2_compact_correlation_tendsto_zero
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : IsCompactOperator T)
    (u : ℕ → Lp ℝ 2 μ) (C : ℝ) (hbound : ∀ n, ‖u n‖ ≤ C)
    (hL1 : Tendsto (fun n => ∫ x, |u n x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ⟪u n, T (u n)⟫_ℝ) atTop (𝓝 0) :=
  inner_compactOperator_tendsto_zero T hT u C hbound
    (L2_inner_tendsto_of_bounded_L1 u C hbound hL1)

end
end ConditionedStableLaws
