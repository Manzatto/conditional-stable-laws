import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic

/-! Two-sided geometric boundary errors disappear in Cesàro averages. -/

open Filter Finset
open scoped Topology

namespace ConditionedStableLaws.GeometricCesaro
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A triangular array with a geometric error from each endpoint has its
row averages converging to the common bulk value. -/
theorem tendsto_average (u : ℕ → ℕ → E) (v : E) {B θ : ℝ}
    (_hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (herror : ∀ n : ℕ, 1 ≤ n → ∀ i ∈ range n,
      ‖u n i - v‖ ≤ B*(θ^i + θ^(n-1-i))) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ range n, u n i) atTop (𝓝 v) := by
  have ht : Tendsto (fun n : ℕ => 2*B*((n : ℝ)⁻¹ * ∑ i ∈ range n, θ^i)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).cesaro.const_mul (2*B)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heq : (n : ℝ)⁻¹ • ∑ i ∈ range n, u n i - v =
      (n : ℝ)⁻¹ • ∑ i ∈ range n, (u n i - v) := by
    rw [sum_sub_distrib, smul_sub, sum_const, card_range,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hnR, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (n : ℝ)⁻¹ * ‖∑ i ∈ range n, (u n i-v)‖
        ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ‖u n i-v‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, B*(θ^i+θ^(n-1-i)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (herror n hn)) (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = 2*B*((n : ℝ)⁻¹ * ∑ i ∈ range n, θ^i) := by
      rw [← mul_sum, sum_add_distrib, sum_range_reflect]
      ring

end
end ConditionedStableLaws.GeometricCesaro
