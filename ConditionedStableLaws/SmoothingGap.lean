import ConditionedStableLaws.ExponentialSpectralGap

/-! Transfer of an operator gap through a smoothing factorization. -/

namespace ConditionedStableLaws.SmoothingGap
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem factor_power (A : E →L[ℝ] F) (J : F →L[ℝ] E) (n : ℕ) :
    (J.comp A)^(n+1) = (J.comp ((A.comp J)^n)).comp A := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [pow_succ', ih, pow_succ']
    ext x
    rfl

theorem factor_power_error (A : E →L[ℝ] F) (J : F →L[ℝ] E)
    (ℓ : F →L[ℝ] ℝ) (η : F) (n : ℕ) :
    (J.comp A)^(n+1) - (ℓ.comp A).smulRight (J η) =
      (J.comp ((A.comp J)^n - ℓ.smulRight η)).comp A := by
  rw [factor_power]
  ext x
  simp

/-- A positive-time gap on the smoothed space gives a positive-time gap on
the original space. Only the factorization and operator norms are used. -/
theorem transfer (A : E →L[ℝ] F) (J : F →L[ℝ] E)
    (ℓ : F →L[ℝ] ℝ) (η : F) {θ C : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hgap : ∀ n : ℕ, 1 ≤ n → ‖(A.comp J)^n - ℓ.smulRight η‖ ≤ C*θ^n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n →
      ‖(J.comp A)^n - (ℓ.comp A).smulRight (J η)‖ ≤ D*θ^n := by
  let B := C + ‖(1 : F →L[ℝ] F) - ℓ.smulRight η‖
  have hB : 0 ≤ B := add_nonneg hC (norm_nonneg _)
  have hfull (n : ℕ) : ‖(A.comp J)^n - ℓ.smulRight η‖ ≤ B*θ^n := by
    cases n with
    | zero => simp [B, hC]
    | succ n =>
      exact (hgap (n+1) (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _))
          (pow_nonneg hθ.le _))
  refine ⟨‖J‖*B*‖A‖/θ, div_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hB)
    (norm_nonneg _)) hθ.le, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ n =>
    rw [factor_power_error]
    calc
      ‖(J.comp ((A.comp J)^n - ℓ.smulRight η)).comp A‖
          ≤ (‖J‖*‖(A.comp J)^n - ℓ.smulRight η‖)*‖A‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (‖J‖*(B*θ^n))*‖A‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfull n) (norm_nonneg _)) (norm_nonneg _)
      _ = (‖J‖*B*‖A‖/θ)*θ^(n+1) := by
        rw [pow_succ]
        field_simp

end
end ConditionedStableLaws.SmoothingGap
