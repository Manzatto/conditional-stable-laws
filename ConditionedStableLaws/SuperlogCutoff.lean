import ConditionedStableLaws.RareEventMoments

/-! One sublinear gap cutoff that suppresses geometric errors of every
fixed polynomial order. -/

open Filter
open scoped Topology

namespace ConditionedStableLaws
noncomputable section

def superlogCutoff (n : ℕ) : ℕ := 1 + ⌈Real.log n ^ 2⌉₊

theorem superlogCutoff_pos (n : ℕ) : 1 ≤ superlogCutoff n := by
  simp [superlogCutoff]

theorem superlogCutoff_div_tendsto_zero :
    Tendsto (fun n : ℕ => (superlogCutoff n : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n ^ 2 / n) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop) using 1
    ext n
    simp
  have hbound := hlog.add (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  simp only [zero_add] at hbound
  apply squeeze_zero (fun n => by positivity) _ hbound
  intro n
  have hceil := (Nat.ceil_lt_add_one (sq_nonneg (Real.log n))).le
  have hq : (superlogCutoff n : ℝ) ≤ Real.log n ^ 2 + 2 := by
    simp only [superlogCutoff, Nat.cast_add, Nat.cast_one]
    linarith
  calc
    (superlogCutoff n : ℝ) / n ≤ (Real.log n ^ 2 + 2) / n :=
      div_le_div_of_nonneg_right hq (Nat.cast_nonneg n)
    _ = _ := by ring

theorem logCutoff_le_superlogCutoff_sub_one (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, logCutoff a n ≤ superlogCutoff n - 1 := by
  have ht : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (max a 0)] with n hn
  have h0 : 0 ≤ Real.log n := (le_max_right a 0).trans hn
  have ha : a ≤ Real.log n := (le_max_left a 0).trans hn
  change ⌈a * Real.log n⌉₊ ≤ 1 + ⌈Real.log n ^ 2⌉₊ - 1
  rw [Nat.add_sub_cancel_left]
  apply Nat.ceil_le_ceil
  nlinarith

/-- A single cutoff works for every fixed moment order. -/
theorem scaled_geometric_superlogCutoff_sub_one_tendsto_zero {θ C : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (r : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^r * (C * θ^(superlogCutoff n - 1))) atTop (𝓝 0) := by
  let a : ℝ := -((r + 1 : ℕ) : ℝ) / Real.log θ
  have hl : Real.log θ ≠ 0 := (Real.log_neg hθ hθ1).ne
  have ha : a * Real.log θ ≤ -((r + 1 : ℕ) : ℝ) := by
    dsimp [a]
    rw [div_mul_cancel₀ _ hl]
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _
    (scaled_geometric_logCutoff_tendsto_zero hθ hθ1.le hC r ha)
  filter_upwards [logCutoff_le_superlogCutoff_sub_one a] with n hn
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ.le hθ1.le hn) hC)
    (pow_nonneg (Nat.cast_nonneg n) r)

theorem scaled_geometric_superlogCutoff_tendsto_zero {θ C : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (r : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^r * (C * θ^superlogCutoff n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) _
    (scaled_geometric_superlogCutoff_sub_one_tendsto_zero hθ hθ1 hC r)
  intro n
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ.le hθ1.le (Nat.sub_le _ _)) hC)
    (pow_nonneg (Nat.cast_nonneg n) r)

theorem superlogCutoff_sub_one_eventually_pos :
    ∀ᶠ n : ℕ in atTop, 0 < superlogCutoff n - 1 := by
  have ht : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 1] with n hn
  have hsq : (1 : ℝ) ≤ Real.log n ^ 2 := by nlinarith
  have hc : (1 : ℝ) ≤ (⌈Real.log n ^ 2⌉₊ : ℝ) := hsq.trans (Nat.le_ceil _)
  have hc' : 1 ≤ ⌈Real.log n ^ 2⌉₊ := by exact_mod_cast hc
  simp only [superlogCutoff, Nat.add_sub_cancel_left]
  omega

theorem scaled_geometric_superlogCutoff_sub_one_tendsto_zero_of_nonneg {θ C : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (r : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^r * (C * θ^(superlogCutoff n - 1))) atTop (𝓝 0) := by
  rcases hθ.eq_or_lt with rfl | hθ
  · apply tendsto_const_nhds.congr'
    filter_upwards [superlogCutoff_sub_one_eventually_pos] with n hn
    simp [zero_pow hn.ne']
  · exact scaled_geometric_superlogCutoff_sub_one_tendsto_zero hθ hθ1 hC r

theorem scaled_geometric_superlogCutoff_tendsto_zero_of_nonneg {θ C : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (r : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^r * (C * θ^superlogCutoff n)) atTop (𝓝 0) := by
  rcases hθ.eq_or_lt with rfl | hθ
  · convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
    funext n
    simp [zero_pow (by have := superlogCutoff_pos n; omega : superlogCutoff n ≠ 0)]
  · exact scaled_geometric_superlogCutoff_tendsto_zero hθ hθ1 hC r

end
end ConditionedStableLaws
