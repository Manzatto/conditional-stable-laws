import ConditionedStableLaws.OperatorGrowth

/-!
# Positive Neumann vectors above the norm-growth rate

The operator series is constructed using the growth bounds, even when its scaled operator has norm
greater than one. Positivity gives a vector `fa ≥ 1` satisfying the exact equation `P fa = a (fa -
1)`.
-/

open Set Filter
open scoped Topology BoundedContinuousFunction

namespace ConditionedStableLaws.PositiveResolvent
noncomputable section

theorem scaled_powers_summable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) {r a : ℝ} (hr : 0 ≤ r) (ha : r < a)
    (hupper : ∀ q : ℝ, r < q → ∀ᶠ n : ℕ in atTop, ‖T^n‖ ≤ q^n) :
    Summable (fun n : ℕ => (a⁻¹ • T)^n) := by
  obtain ⟨q, hrq, hqa⟩ := exists_between ha
  have hapos : 0 < a := hr.trans_lt ha
  have hqpos : 0 < q := hr.trans_lt hrq
  apply (summable_geometric_of_lt_one (div_nonneg hqpos.le hapos.le)
    ((div_lt_one hapos).mpr hqa)).of_norm_bounded_eventually_nat
  filter_upwards [hupper q hrq] with n hn
  rw [smul_pow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hapos.le) n)]
  calc
    a⁻¹^n * ‖T^n‖ ≤ a⁻¹^n * q^n := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (q/a)^n := by rw [div_eq_mul_inv, mul_pow, mul_comm]

variable {M : Type*} [TopologicalSpace M]

theorem scaled_power_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (a : ℝ) (n : ℕ) (f : E) :
    ((a • T)^n) f = a^n • (T^n) f := by
  rw [smul_pow]
  rfl

theorem pow_nonneg (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hT : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x)
    (f : M →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : M) : 0 ≤ (T^n) f x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    rw [pow_succ' T, mul_apply_eq_comp]
    exact hT _ ih x

/-- The Neumann series applied to the constant-one function. -/
def vector (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) (a : ℝ) : M →ᵇ ℝ :=
  ∑' n : ℕ, ((a⁻¹ • T)^n) 1

theorem vector_summable (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) {a : ℝ}
    (hsum : Summable (fun n : ℕ => (a⁻¹ • T)^n)) :
    Summable (fun n : ℕ => ((a⁻¹ • T)^n) 1) := by
  exact (ContinuousLinearMap.apply ℝ (M →ᵇ ℝ) 1).summable hsum

theorem vector_eq_operator_sum (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) {a : ℝ}
    (hsum : Summable (fun n : ℕ => (a⁻¹ • T)^n)) :
    vector T a = (∑' n : ℕ, (a⁻¹ • T)^n) 1 := by
  exact ((ContinuousLinearMap.apply ℝ (M →ᵇ ℝ) 1).map_tsum hsum).symm

theorem vector_apply (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) {a : ℝ}
    (hsum : Summable (fun n : ℕ => (a⁻¹ • T)^n)) (x : M) :
    vector T a x = ∑' n : ℕ, ((a⁻¹ • T)^n) 1 x := by
  exact (BoundedContinuousFunction.evalCLM ℝ x).map_tsum (vector_summable T hsum)

theorem vector_ge_one (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hT : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x)
    {a : ℝ} (ha : 0 < a) (hsum : Summable (fun n : ℕ => (a⁻¹ • T)^n)) (x : M) :
    1 ≤ vector T a x := by
  have hnonneg : ∀ n : ℕ, ∀ y : M, 0 ≤ ((a⁻¹ • T)^n) 1 y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y
      rw [pow_succ', mul_apply_eq_comp]
      exact mul_nonneg (inv_nonneg.mpr ha.le) (hT _ ih y)
  rw [vector_apply T hsum]
  have hs := (BoundedContinuousFunction.evalCLM ℝ x).summable (vector_summable T hsum)
  simpa using hs.le_tsum 0 (fun n _ => hnonneg n x)

theorem vector_antitone (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hT : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsa : Summable (fun n : ℕ => (a⁻¹ • T)^n))
    (hsb : Summable (fun n : ℕ => (b⁻¹ • T)^n)) (x : M) :
    vector T b x ≤ vector T a x := by
  rw [vector_apply T hsb, vector_apply T hsa]
  apply Summable.tsum_le_tsum _ ((BoundedContinuousFunction.evalCLM ℝ x).summable
    (vector_summable T hsb)) ((BoundedContinuousFunction.evalCLM ℝ x).summable
    (vector_summable T hsa))
  intro n
  change (((b⁻¹ • T)^n) 1) x ≤ (((a⁻¹ • T)^n) 1) x
  rw [scaled_power_apply, scaled_power_apply]
  change b⁻¹^n * (T^n) 1 x ≤ a⁻¹^n * (T^n) 1 x
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (inv_nonneg.mpr (ha.le.trans hab)) (inv_anti₀ ha hab) n)
    (pow_nonneg T hT 1 (fun _ => zero_le_one) n x)

theorem vector_norm_antitone (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hT : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsa : Summable (fun n : ℕ => (a⁻¹ • T)^n))
    (hsb : Summable (fun n : ℕ => (b⁻¹ • T)^n)) :
    ‖vector T b‖ ≤ ‖vector T a‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (vector_ge_one T hT (ha.trans_le hab) hsb x))]
  exact (vector_antitone T hT ha hab hsa hsb x).trans
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      BoundedContinuousFunction.norm_coe_le_norm (vector T a) x))

theorem vector_equation (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    {a : ℝ} (ha : a ≠ 0) (hsum : Summable (fun n : ℕ => (a⁻¹ • T)^n)) :
    T (vector T a) = a • (vector T a - 1) := by
  have hs := vector_summable T hsum
  have hshift : (∑' n : ℕ, ((a⁻¹ • T)^(n+1)) 1) = vector T a - 1 := by
    have he := hs.tsum_eq_zero_add
    change vector T a = 1 + ∑' n : ℕ, ((a⁻¹ • T)^(n+1)) 1 at he
    rw [he]
    abel
  have he' : a⁻¹ • T (vector T a) = vector T a - 1 := by
    change (a⁻¹ • T) (∑' n : ℕ, ((a⁻¹ • T)^n) 1) = _
    rw [(a⁻¹ • T).map_tsum hs]
    simpa only [pow_succ' (a⁻¹ • T), mul_apply_eq_comp] using hshift
  have hh := congrArg (fun f : M →ᵇ ℝ => a • f) he'
  simpa only [smul_inv_smul₀ ha] using hh

/-- The Neumann resolvent as a bounded operator. -/
def operatorSum (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) (a : ℝ) :
    (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ) := ∑' n : ℕ, (a⁻¹ • T)^n

theorem operatorSum_apply (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) {a : ℝ}
    (hs : Summable (fun n : ℕ => (a⁻¹ • T)^n)) (f : M →ᵇ ℝ) :
    operatorSum T a f = ∑' n : ℕ, ((a⁻¹ • T)^n) f :=
  (ContinuousLinearMap.apply ℝ (M →ᵇ ℝ) f).map_tsum hs

theorem operatorSum_one (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) {a : ℝ}
    (hs : Summable (fun n : ℕ => (a⁻¹ • T)^n)) : operatorSum T a 1 = vector T a :=
  (vector_eq_operator_sum T hs).symm

theorem operatorSum_nonneg (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hT : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x)
    {a : ℝ} (ha : 0 < a) (hs : Summable (fun n : ℕ => (a⁻¹ • T)^n))
    (f : M →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : M) : 0 ≤ operatorSum T a f x := by
  rw [operatorSum_apply T hs]
  have hs' : Summable (fun n : ℕ => ((a⁻¹ • T)^n) f) :=
    (ContinuousLinearMap.apply ℝ (M →ᵇ ℝ) f).summable hs
  rw [← BoundedContinuousFunction.evalCLM_apply ℝ x,
    (BoundedContinuousFunction.evalCLM ℝ x).map_tsum hs']
  apply tsum_nonneg
  intro n
  change 0 ≤ (((a⁻¹ • T)^n) f) x
  rw [scaled_power_apply]
  exact mul_nonneg (by positivity) (pow_nonneg T hT f hf n x)

theorem commute_scaled_power_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (a : ℝ) (n : ℕ) (f : E) :
    ((a • T)^n) (T f) = T (((a • T)^n) f) := by
  have hcomm : Commute T (a • T) := by
    ext g
    simp only [mul_apply_eq_comp, smul_apply, map_smul]
  exact congrArg (fun A : E →L[ℝ] E => A f) (hcomm.pow_right n).eq.symm

/-- The resolvent's exact right equation, used by normalized evaluation
functionals to construct a left eigenmeasure. -/
theorem operatorSum_right_equation (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    {a : ℝ} (ha : a ≠ 0) (hs : Summable (fun n : ℕ => (a⁻¹ • T)^n)) (f : M →ᵇ ℝ) :
    operatorSum T a (T f) = a • (operatorSum T a f - f) := by
  have hsf : Summable (fun n : ℕ => ((a⁻¹ • T)^n) f) :=
    (ContinuousLinearMap.apply ℝ (M →ᵇ ℝ) f).summable hs
  have hshift : (∑' n : ℕ, ((a⁻¹ • T)^(n+1)) f) = operatorSum T a f - f := by
    have he := hsf.tsum_eq_zero_add
    rw [← operatorSum_apply T hs] at he
    change operatorSum T a f = f + ∑' n : ℕ, ((a⁻¹ • T)^(n+1)) f at he
    rw [he]
    abel
  have he' : a⁻¹ • T (operatorSum T a f) = operatorSum T a f - f := by
    change (a⁻¹ • T) (operatorSum T a f) = _
    rw [operatorSum_apply T hs, (a⁻¹ • T).map_tsum hsf]
    simpa only [pow_succ' (a⁻¹ • T), mul_apply_eq_comp, operatorSum_apply T hs] using hshift
  have he : T (operatorSum T a f) = a • (operatorSum T a f - f) := by
    simpa only [smul_inv_smul₀ ha] using congrArg (fun g : M →ᵇ ℝ => a • g) he'
  rw [← he, operatorSum_apply T hs, operatorSum_apply T hs, T.map_tsum hsf]
  exact tsum_congr (fun n => commute_scaled_power_apply T a⁻¹ n f)

end
end ConditionedStableLaws.PositiveResolvent
