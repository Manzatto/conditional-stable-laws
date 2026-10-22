import ConditionedStableLaws.ContinuousMultiplierMoments

/-!
# Truncating a continuous multiplier error

The cutoff is applied to the original positive observable. The error itself
may have either sign. Uniform smallness relative to the original singularity
implies both vanishing normalized sup norm and vanishing second moments.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ConditionedStableLaws.ContinuousMultiplier

noncomputable section

section General
variable {M : Type*}

/-- Truncate `r` according to the size of the original observable `f`. -/
def cut (f r : M → ℝ) (t : ℝ) : M → ℝ := {x | f x ≤ t}.indicator r

theorem abs_cut_le {f r : M → ℝ} {η K t : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (ht : 0 ≤ t) (h : ∀ x, |r x| ≤ η * f x + K) (x : M) :
    |cut f r t x| ≤ η * t + K := by
  by_cases hx : f x ≤ t
  · rw [cut, indicator_of_mem (show x ∈ {x | f x ≤ t} from hx)]
    have hh := mul_le_mul_of_nonneg_left hx hη
    linarith [h x]
  · rw [cut, indicator_of_notMem (show x ∉ {x | f x ≤ t} from hx), abs_zero]
    exact add_nonneg (mul_nonneg hη ht) hK

theorem cut_sq_le {f r : M → ℝ} {η K t : ℝ}
    (h : ∀ x, |r x| ≤ η * f x + K) (x : M) :
    cut f r t x ^ 2 ≤ 2 * η ^ 2 * (SmallJumpMoment.trunc f t x) ^ 2 + 2 * K ^ 2 := by
  by_cases hx : f x ≤ t
  · simp only [cut, SmallJumpMoment.trunc, indicator_of_mem
      (show x ∈ {x | f x ≤ t} from hx)]
    have hh := pow_le_pow_left₀ (abs_nonneg (r x)) (h x) 2
    rw [sq_abs] at hh
    nlinarith [sq_nonneg (η * f x - K)]
  · simp only [cut, SmallJumpMoment.trunc, indicator_of_notMem
      (show x ∉ {x | f x ≤ t} from hx), zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
    positivity

variable [MeasurableSpace M]

theorem measurable_cut {f r : M → ℝ} (hf : Measurable f) (hr : Measurable r) (t : ℝ) :
    Measurable (cut f r t) := hr.indicator (measurableSet_le hf measurable_const)

/-- A quantitative second-moment comparison, valid for signed residuals. -/
theorem integral_cut_sq_le (μ : Measure M) [IsProbabilityMeasure μ]
    {f r : M → ℝ} (hfm : Measurable f) (hrm : Measurable r) (hf : ∀ x, 0 ≤ f x)
    {η K t : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (h : ∀ x, |r x| ≤ η * f x + K) :
    (∫ x, cut f r t x ^ 2 ∂μ) ≤
      2 * η ^ 2 * (∫ x, SmallJumpMoment.trunc f t x ^ 2 ∂μ) + 2 * K ^ 2 := by
  have hfb : ∀ x, |SmallJumpMoment.trunc f t x| ≤ t := fun x => by
    rw [abs_of_nonneg (SmallJumpMoment.trunc_nonneg hf t x)]
    exact SmallJumpMoment.trunc_le ht x
  have hfi := SecondMoment.integrable_of_bdd (ν := μ)
    ((SmallJumpMoment.measurable_trunc hfm t).pow_const 2) (SecondMoment.sq_bdd hfb)
  calc
    _ ≤ ∫ x, (2 * η ^ 2 * SmallJumpMoment.trunc f t x ^ 2 + 2 * K ^ 2) ∂μ :=
      integral_mono (SecondMoment.integrable_of_bdd
        ((measurable_cut hfm hrm t).pow_const 2)
        (SecondMoment.sq_bdd (abs_cut_le hη hK ht h)))
        ((hfi.const_mul _).add (integrable_const _)) (cut_sq_le h)
    _ = _ := by
      rw [integral_add (hfi.const_mul _) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul]

/-- A residual which is smaller than every positive multiple of `f`, modulo
bounded terms, has negligible truncated second moments on every fixed scale. -/
theorem scaled_residual_second_moment_zero (μ : Measure M) [IsProbabilityMeasure μ]
    {f r : M → ℝ} (hfm : Measurable f) (hrm : Measurable r) (hf : ∀ x, 0 ≤ f x)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |r x| ≤ η * f x + K)
    {B : ℕ → ℝ} (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) / B n ^ 2) atTop (𝓝 0))
    (hf2 : ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / B n ^ 2 * ∫ x, SmallJumpMoment.trunc f (t n) x ^ 2 ∂μ ≤ L) :
    Tendsto (fun n : ℕ => (n : ℝ) / B n ^ 2 * ∫ x, cut f r (t n) x ^ 2 ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨L, hL, hLbound⟩ := hf2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := Real.sqrt (ε / (8 * (L + 1)))
  have hη : 0 < η := Real.sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = ε / (8 * (L + 1)) := Real.sq_sqrt (by positivity)
  have hηsmall : 2 * η ^ 2 * L < ε / 2 := by
    rw [hη2]
    have hden : 0 < 8 * (L + 1) := by positivity
    apply (mul_lt_mul_iff_of_pos_right hden).mp
    field_simp
    nlinarith
  obtain ⟨K, hK, hbound⟩ := hr η hη
  have hsmall : ∀ᶠ n : ℕ in atTop, 2 * K ^ 2 * ((n : ℝ) / B n ^ 2) < ε / 2 := by
    have hh : Tendsto (fun n : ℕ => 2 * K ^ 2 * ((n : ℝ) / B n ^ 2)) atTop (𝓝 0) := by
      simpa using ha.const_mul (2 * K ^ 2)
    exact hh.eventually_lt_const (half_pos hε)
  filter_upwards [hLbound, hsmall] with n hn hnsmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg
    (div_nonneg (Nat.cast_nonneg n) (sq_nonneg _)) (integral_nonneg fun x => sq_nonneg _))]
  have hbound2 := integral_cut_sq_le μ hfm hrm hf hη.le hK (ht n) hbound
  have hh := mul_le_mul_of_nonneg_left hbound2
    (div_nonneg (Nat.cast_nonneg n) (sq_nonneg (B n)))
  have hhL := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2 * η ^ 2 by positivity)
  nlinarith

end General

section UniformBounds
variable {M : Type*} [Nonempty M]

/-- The normalized signed residuals on a fixed cutoff have a deterministic
sup-norm bound tending to zero. -/
theorem exists_cut_bound_tendsto_zero {f r : M → ℝ}
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |r x| ≤ η * f x + K)
    {B : ℕ → ℝ} (hB : ∀ n, 0 < B n) (hBlim : Tendsto B atTop atTop)
    {R : ℝ} (hR : 0 < R) :
    ∃ G : ℕ → ℝ, (∀ n, 0 ≤ G n) ∧
      (∀ n x, |(B n)⁻¹ * cut f r (R * B n) x| ≤ G n) ∧ Tendsto G atTop (𝓝 0) := by
  let q : ℕ → M → ℝ := fun n x => (B n)⁻¹ * cut f r (R * B n) x
  have hb : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ n x,
      |q n x| ≤ η * R + K / B n := by
    intro η hη
    obtain ⟨K, hK, h⟩ := hr η hη
    refine ⟨K, hK, fun n x => ?_⟩
    rw [show q n x = (B n)⁻¹ * cut f r (R * B n) x from rfl,
      abs_mul, abs_of_pos (inv_pos.mpr (hB n))]
    calc
      _ ≤ (B n)⁻¹ * (η * (R * B n) + K) :=
        mul_le_mul_of_nonneg_left (abs_cut_le hη.le hK (mul_pos hR (hB n)).le h x)
          (inv_nonneg.mpr (hB n).le)
      _ = _ := by field_simp [(hB n).ne']
  have hbdd (n : ℕ) : BddAbove (Set.range fun x => |q n x|) := by
    obtain ⟨K, _, hK⟩ := hb 1 one_pos
    exact ⟨R + K / B n, by rintro _ ⟨x, rfl⟩; simpa using hK n x⟩
  let G : ℕ → ℝ := fun n => ⨆ x, |q n x|
  have hqG (n : ℕ) (x : M) : |q n x| ≤ G n := le_ciSup (hbdd n) x
  have hG0 (n : ℕ) : 0 ≤ G n :=
    (abs_nonneg (q n (Classical.choice inferInstance))).trans (hqG n _)
  refine ⟨G, hG0, hqG, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, _, hK⟩ := hb (ε / (2 * R)) (by positivity)
  have hsmall : ∀ᶠ n in atTop, K / B n < ε / 2 :=
    (hBlim.const_div_atTop K).eventually_lt_const (half_pos hε)
  filter_upwards [hsmall] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hG0 n)]
  have hle : G n ≤ ε / (2 * R) * R + K / B n := ciSup_le (hK n)
  have heq : ε / (2 * R) * R = ε / 2 := by field_simp
  rw [heq] at hle
  linarith

end UniformBounds
end
end ConditionedStableLaws.ContinuousMultiplier
