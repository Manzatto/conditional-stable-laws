import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Order-unit estimates for positive operators on bounded continuous real functions. -/

open scoped BoundedContinuousFunction
open Filter
open scoped Topology

namespace ConditionedStableLaws.PositiveOrderUnit
noncomputable section

variable {M : Type*} [TopologicalSpace M]
  (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
  (hT : ∀ g : M →ᵇ ℝ, (∀ x, 0 ≤ g x) → ∀ x, 0 ≤ T g x)

include hT

theorem map_le_map (u v : M →ᵇ ℝ) (huv : ∀ x, u x ≤ v x) (x : M) :
    T u x ≤ T v x := by
  have hh := hT (v - u) (fun y => sub_nonneg.mpr (huv y)) x
  simpa only [map_sub, BoundedContinuousFunction.sub_apply, sub_nonneg] using hh

theorem abs_apply_le_of_order_bound (f g : M →ᵇ ℝ) (c : ℝ)
    (hbound : ∀ x, |g x| ≤ c * f x) (x : M) : |T g x| ≤ c * T f x := by
  have hlo : ∀ y, ((-c) • f) y ≤ g y := fun y => by
    have hh := (abs_le.mp (hbound y)).1
    simpa using hh
  have hhi : ∀ y, g y ≤ (c • f) y := fun y => (abs_le.mp (hbound y)).2
  have hl := map_le_map T hT _ _ hlo x
  have hu := map_le_map T hT _ _ hhi x
  simp only [map_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul] at hl hu
  exact abs_le.mpr ⟨by simpa using hl, hu⟩

/-- A positive order-unit supersolution controls every iterate pointwise. -/
theorem abs_pow_apply_le (f : M →ᵇ ℝ) (hf : ∀ x, 1 ≤ f x)
    {a : ℝ} (ha : 0 ≤ a) (hTf : ∀ x, T f x ≤ a * f x)
    (n : ℕ) (g : M →ᵇ ℝ) (x : M) :
    |(T ^ n) g x| ≤ a ^ n * ‖g‖ * f x := by
  induction n generalizing x with
  | zero =>
      change |g x| ≤ a ^ 0 * ‖g‖ * f x
      simp only [pow_zero, one_mul]
      exact (g.norm_coe_le_norm x).trans
        (le_mul_of_one_le_right (norm_nonneg g) (hf x))
  | succ n ih =>
      rw [pow_succ']
      change |T ((T ^ n) g) x| ≤ a ^ (n + 1) * ‖g‖ * f x
      calc
        _ ≤ (a ^ n * ‖g‖) * T f x :=
          abs_apply_le_of_order_bound T hT f ((T ^ n) g) (a ^ n * ‖g‖)
            (fun y => ih (x := y)) x
        _ ≤ (a ^ n * ‖g‖) * (a * f x) :=
          mul_le_mul_of_nonneg_left (hTf x) (mul_nonneg (pow_nonneg ha _) (norm_nonneg _))
        _ = a ^ (n + 1) * ‖g‖ * f x := by rw [pow_succ]; ring

/-- If `f≥1` and `Tf≤a f`, positivity implies `‖T^n‖≤‖f‖ a^n`. -/
theorem norm_pow_le (f : M →ᵇ ℝ) (hf : ∀ x, 1 ≤ f x)
    {a : ℝ} (ha : 0 ≤ a) (hTf : ∀ x, T f x ≤ a * f x) (n : ℕ) :
    ‖T ^ n‖ ≤ ‖f‖ * a ^ n := by
  apply (T ^ n).opNorm_le_bound (mul_nonneg (norm_nonneg _) (pow_nonneg ha _))
  intro g
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  calc
    ‖(T ^ n) g x‖ = |(T ^ n) g x| := Real.norm_eq_abs _
    _ ≤ a ^ n * ‖g‖ * f x := abs_pow_apply_le T hT f hf ha hTf n g x
    _ ≤ a ^ n * ‖g‖ * ‖f‖ := mul_le_mul_of_nonneg_left (f.apply_le_norm x) (by positivity)
    _ = (‖f‖ * a ^ n) * ‖g‖ := by ring

/-- A positive resolvent cannot remain bounded at a positive lower growth
rate. Such a critical solution would give a strictly smaller exponential
bound for all operator powers. -/
theorem critical_resolvent_impossible {r : ℝ} (hr : 0 < r)
    (hgrowth : ∀ n : ℕ, r ^ n ≤ ‖T ^ n‖)
    (f : M →ᵇ ℝ) (hf : ∀ x, 1 ≤ f x)
    (heq : ∀ x, T f x = r * (f x - 1)) : False := by
  let b : ℝ := ‖f‖ / (‖f‖ + 1)
  have hB : 0 < ‖f‖ + 1 := by positivity
  have hb0 : 0 ≤ b := div_nonneg (norm_nonneg _) hB.le
  have hb1 : b < 1 := (div_lt_one hB).mpr (by linarith)
  have hmul : b * (‖f‖ + 1) = ‖f‖ := div_mul_cancel₀ _ hB.ne'
  have hTf : ∀ x, T f x ≤ (r * b) * f x := by
    intro x
    rw [heq x]
    have hfx := f.apply_le_norm x
    have hineq : f x - 1 ≤ b * f x := by
      apply (mul_le_mul_iff_right₀ hB).mp
      nlinarith [mul_nonneg (sub_nonneg.mpr hfx) (show 0 ≤ (1 : ℝ) by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hineq hr.le]
  have hge (n : ℕ) : 1 ≤ ‖f‖ * b ^ n := by
    have hbound := (hgrowth n).trans
      (norm_pow_le T hT f hf (mul_nonneg hr.le hb0) hTf n)
    rw [mul_pow] at hbound
    apply (mul_le_mul_iff_left₀ (pow_pos hr n)).mp
    nlinarith
  have ht : Tendsto (fun n : ℕ => ‖f‖ * b ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1)
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hge)
  norm_num at hbad

end
end ConditionedStableLaws.PositiveOrderUnit
