import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

/-!
# Uniform power bounds near an exponentially decaying operator

A strict bound for one finite power persists in a neighborhood. Strong induction then controls every
power with uniform constants.
-/

open Filter Metric
open scoped Topology

namespace ConditionedStableLaws.PowerStability
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]

omit [NormOneClass A] in
/-- One contracting block and bounds for its finite initial segment control
all powers. -/
theorem power_bound_of_block (T : A) {N : ℕ} (hN : 0 < N) {q D : ℝ}
    (hq : 0 ≤ q) (hD : 0 ≤ D) (hblock : ‖T^N‖ ≤ q^N)
    (hinitial : ∀ i < N, ‖T^i‖ ≤ D*q^i) (n : ℕ) : ‖T^n‖ ≤ D*q^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N
    · exact hinitial n hn
    · have hNn : N ≤ n := le_of_not_gt hn
      have he : n = (n-N)+N := (Nat.sub_add_cancel hNn).symm
      have hsmall : n-N < n := by omega
      calc
        ‖T^n‖ = ‖T^(n-N)*T^N‖ := by rw [← pow_add, ← he]
        _ ≤ ‖T^(n-N)‖*‖T^N‖ := norm_mul_le _ _
        _ ≤ (D*q^(n-N))*q^N :=
          mul_le_mul (ih (n-N) hsmall) hblock (norm_nonneg _)
            (mul_nonneg hD (pow_nonneg hq _))
        _ = D*q^n := by rw [mul_assoc, ← pow_add, ← he]

/-- Uniform finite initial-segment bounds obtained from a bound on the
operator itself. -/
theorem power_bound_of_norm_and_block (T : A) {N : ℕ} (hN : 0 < N) {q B : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hB : 1 ≤ B)
    (hT : ‖T‖ ≤ B) (hblock : ‖T^N‖ ≤ q^N) (n : ℕ) :
    ‖T^n‖ ≤ (B/q)^N*q^n := by
  have hBq : 1 ≤ B/q := (le_div_iff₀ hq).mpr (by linarith)
  apply power_bound_of_block T hN hq.le (pow_nonneg (by positivity) _) hblock _ n
  intro i hi
  calc
    ‖T^i‖ ≤ ‖T‖^i := norm_pow_le _ _
    _ ≤ B^i := pow_le_pow_left₀ (norm_nonneg _) hT i
    _ = (B/q)^i*q^i := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hq.ne')]
    _ ≤ (B/q)^N*q^i := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hBq hi.le) (pow_nonneg hq.le _)

/-- Exponential decay of the powers of `R` persists uniformly on a neighborhood
of `R`, with a possibly larger rate strictly below one. -/
theorem eventually_geometric_bound (R : A) {C r : ℝ}
    (_hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hpow : ∀ n : ℕ, ‖R^n‖ ≤ C*r^n) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ T : A in 𝓝 R, ∀ n : ℕ, ‖T^n‖ ≤ D*q^n := by
  let q := (r+1)/2
  have hq : 0 < q := by dsimp [q]; linarith
  have hrq : r < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hratio : r/q < 1 := (div_lt_one hq).mpr hrq
  have hlim : Tendsto (fun n : ℕ => C*(r/q)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr0 hq.le) hratio).const_mul C
  have hevent : ∀ᶠ n : ℕ in atTop, C*(r/q)^n < 1 := hlim.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨N, hN, hNb⟩ := ((eventually_ge_atTop 1).and hevent).exists
  have hstrict : ‖R^N‖ < q^N := by
    apply (hpow N).trans_lt
    have he : C*r^N = (C*(r/q)^N)*q^N := by
      rw [div_pow]
      field_simp
    rw [he]
    simpa using mul_lt_mul_of_pos_right hNb (pow_pos hq N)
  have hnear : ∀ᶠ T : A in 𝓝 R, ‖T^N‖ < q^N :=
    ((continuous_id.pow N).norm.continuousAt.tendsto).eventually (gt_mem_nhds hstrict)
  have hnorm : ∀ᶠ T : A in 𝓝 R, ‖T‖ < ‖R‖+1 :=
    continuous_norm.continuousAt.tendsto.eventually (gt_mem_nhds (by linarith))
  let B := ‖R‖+1
  refine ⟨q, hq, hq1, (B/q)^N, pow_nonneg (by dsimp [B]; positivity) _, ?_⟩
  filter_upwards [hnear, hnorm] with T hT hTB
  exact power_bound_of_norm_and_block T (by omega) hq hq1.le (by dsimp [B]; linarith [norm_nonneg R])
    hTB.le hT.le

/-- A concrete positive-radius ball has a common geometric power bound. -/
theorem exists_ball_geometric_bound (R : A) {C r : ℝ}
    (_hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hpow : ∀ n : ℕ, ‖R^n‖ ≤ C*r^n) :
    ∃ ε q D : ℝ, 0 < ε ∧ 0 < q ∧ q < 1 ∧ 0 ≤ D ∧
      ∀ T : A, ‖T-R‖ < ε → ∀ n : ℕ, ‖T^n‖ ≤ D*q^n := by
  obtain ⟨q, hq, hq1, D, hD, he⟩ := eventually_geometric_bound R _hC hr0 hr1 hpow
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨ε, q, D, hε, hq, hq1, hD, fun T hT => he (by simpa only [dist_eq_norm] using hT)⟩

end
end ConditionedStableLaws.PowerStability
