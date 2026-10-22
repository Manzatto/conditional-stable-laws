import ConditionedStableLaws.GeometricCesaro
import ConditionedStableLaws.ConditionalMixing

/-! The operator Cesàro estimate underlying quasi-ergodic expectations. -/

open Filter Finset
open scoped Topology

namespace ConditionedStableLaws.OperatorCesaro
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Explicit two-sided boundary error for one observation operator. -/
theorem two_sided_error (Q P A : E →L[ℝ] E) {C U θ : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hθ : 0 ≤ θ)
    (hP : ‖P‖ ≤ U) (hQ : ∀ n : ℕ, ‖Q^n‖ ≤ U)
    (hgap : ∀ n : ℕ, ‖Q^n-P‖ ≤ C*θ^n) (i j : ℕ) :
    ‖Q^i*A*Q^j-P*A*P‖ ≤ C*U*‖A‖*(θ^i+θ^j) := by
  have heq : Q^i*A*Q^j-P*A*P = (Q^i-P)*A*Q^j+P*A*(Q^j-P) := by noncomm_ring
  rw [heq]
  calc
    ‖(Q^i-P)*A*Q^j+P*A*(Q^j-P)‖
        ≤ ‖Q^i-P‖*‖A‖*‖Q^j‖+‖P‖*‖A‖*‖Q^j-P‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))))
    _ ≤ (C*θ^i)*‖A‖*U+U*‖A‖*(C*θ^j) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right (hgap i) (norm_nonneg _)) (hQ j)
          (norm_nonneg _) (mul_nonneg (mul_nonneg hC (pow_nonneg hθ _)) (norm_nonneg _))
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) (hgap j)
          (norm_nonneg _) (mul_nonneg hU (norm_nonneg _))
    _ = C*U*‖A‖*(θ^i+θ^j) := by ring

/-- Cesàro convergence for an observation between two normalized powers. -/
theorem tendsto_operator_average (Q P A : E →L[ℝ] E) {C U θ : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hP : ‖P‖ ≤ U) (hQ : ∀ n : ℕ, ‖Q^n‖ ≤ U)
    (hgap : ∀ n : ℕ, ‖Q^n-P‖ ≤ C*θ^n) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ range n, Q^i*A*Q^(n-1-i))
      atTop (𝓝 (P*A*P)) :=
  GeometricCesaro.tendsto_average _ _
    (mul_nonneg (mul_nonneg hC hU) (norm_nonneg A)) hθ0 hθ1
    (fun n _ i _ => two_sided_error Q P A hC hU hθ0 hP hQ hgap i (n-1-i))

/-- A rank-one operator gap gives the scalar conditional Cesàro limit.
The numerator is the exact averaged operator correlation; the denominator
is the corresponding normalized survival coefficient. -/
theorem tendsto_conditional_average (Q A : E →L[ℝ] E) (μ ev : E →L[ℝ] ℝ)
    (η one : E) (hone : μ one = 1) (ha : 0 < ev η) {C θ : ℝ}
    (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hgap : ∀ n : ℕ, ‖Q^n-μ.smulRight η‖ ≤ C*θ^n) :
    Tendsto (fun n : ℕ =>
      ev (((n : ℝ)⁻¹ • ∑ i ∈ range n, Q^i*A*Q^(n-1-i)) one) /
        ev ((Q^(n-1)) one)) atTop (𝓝 (μ (A η))) := by
  let P := μ.smulRight η
  let U := ‖P‖+C
  have hU : 0 ≤ U := add_nonneg (norm_nonneg _) hC
  have hP : ‖P‖ ≤ U := le_add_of_nonneg_right hC
  have hQ (n : ℕ) : ‖Q^n‖ ≤ U := by
    calc
      ‖Q^n‖ ≤ ‖Q^n-P‖+‖P‖ := by
        simpa only [sub_add_cancel] using norm_add_le (Q^n-P) P
      _ ≤ C*θ^n+‖P‖ := add_le_add (hgap n) le_rfl
      _ ≤ U := by dsimp [U]; nlinarith [pow_le_one₀ (n := n) hθ0 hθ1.le]
  let V := ev.comp (ContinuousLinearMap.apply ℝ E one)
  have hnum := V.continuous.continuousAt.tendsto.comp
    (tendsto_operator_average Q P A hC hU hθ0 hθ1 hP hQ hgap)
  have hpow : Tendsto (fun n : ℕ => Q^n) atTop (𝓝 P) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hgap (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul C)
  have hden := V.continuous.continuousAt.tendsto.comp
    (hpow.comp (tendsto_sub_atTop_nat 1))
  have hVp : V P = ev η := by simp [V, P, hone]
  have hVpap : V (P*A*P) = μ (A η)*ev η := by
    simp [V, P, mul_apply_eq_comp, hone, smul_eq_mul]
  rw [hVp] at hden
  rw [hVpap] at hnum
  have hlim := hnum.div hden ha.ne'
  convert! hlim using 1
  rw [mul_div_cancel_right₀ _ ha.ne']

end
end ConditionedStableLaws.OperatorCesaro
