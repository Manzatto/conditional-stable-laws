import ConditionedStableLaws.ContinuousMultiplierTruncation
import ConditionedStableLaws.ContinuousMultiplierMomentComparison

/-!
# Centered continuous-multiplier residuals on a fixed cutoff

The second-moment and sup-norm estimates are derived from the original tail
asymptotic. In particular the residual need not be integrable or nonnegative.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open CanonicalChain StandingHypothesis NormalizationBridge SmallJumpMoment

section General
variable {M : Type*}

theorem trunc_sq_eq (f : M → ℝ) (t : ℝ) (x : M) :
    trunc f t x ^ 2 = {y | f y ≤ t}.indicator (fun y => f y ^ 2) x := by
  simp only [trunc, indicator]
  split <;> simp

variable [MeasurableSpace M]
theorem normalized_cut_second_moment (μ : Measure M) (f r : M → ℝ)
    (B t : ℝ) (n : ℕ) :
    (n : ℝ) * (∫ x, (B⁻¹ * cut f r t x) ^ 2 ∂μ) =
      (n : ℝ) / B ^ 2 * ∫ x, cut f r t x ^ 2 ∂μ := by
  simp_rw [mul_pow]
  rw [integral_const_mul]
  simp only [div_eq_mul_inv, inv_pow]
  ring
end General

section Chain
variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- For every fixed upper cutoff `R B_n`, the centered multiplier residual
is negligible. The original tail and the local lower bound for η suffice. -/
theorem centered_cut_residual_negligible (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {f r : M → ℝ} (hfm : Measurable f) (hrm : Measurable r)
    (hf : ∀ y, 0 ≤ f y)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |r y| ≤ η * f y + K)
    {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hlower : ∀ y, T < f y → a ≤ (d.weight y).toReal)
    {Cc α : ℝ} (hC : 0 < Cc) (hα : 0 < α) (hα2 : α < 2)
    (htail : Tendsto (fun t : ℝ => (μ.withDensity d.weight).real {y | t < f y} /
      (Cc * t ^ (-α))) atTop (𝓝 1)) {R : ℝ} (hR : 0 < R) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (C.conditionedMeasure x.val n).real {ω | ε <
        |(positivePowerScale Cc α n)⁻¹ * pathBirkhoffSum
            (cut f r (R * positivePowerScale Cc α n)) n ω -
          n * (positivePowerScale Cc α n)⁻¹ * ∫ y,
            cut f r (R * positivePowerScale Cc α n) y ∂μ.withDensity d.weight|})
      atTop (𝓝 0) := by
  have : Nonempty M := ⟨x.val⟩
  let ν := μ.withDensity d.weight
  have : IsProbabilityMeasure ν :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  let B := positivePowerScale Cc α
  have hB : ∀ n, 0 < B n := positivePowerScale_pos hC
  have hna : Tendsto (fun n : ℕ => (n : ℝ) / B n ^ 2) atTop (𝓝 0) := by
    apply (nat_div_powerScale_sq_tendsto_zero hC hα hα2).congr'
    filter_upwards [positivePowerScale_eventually_eq Cc α] with n hn
    rw [show B n = powerScale Cc α n from hn]
  let L := α / (2 - α) * R ^ (2 - α) + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hνbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / B n ^ 2 * ∫ y, trunc f (R * B n) y ^ 2 ∂ν ≤ L := by
    have hh := CompensationAsymptotics.scaled_second_moment hfm hf hC hα hα2 htail hR
    have he := hh.eventually (ge_mem_nhds (show α / (2 - α) * R ^ (2 - α) < L by dsimp [L]; linarith))
    simpa only [trunc_sq_eq] using he
  have hμbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / B n ^ 2 * ∫ y, trunc f (R * B n) y ^ 2 ∂μ ≤ a⁻¹ * L + T ^ 2 := by
    filter_upwards [hνbound, hna.eventually (ge_mem_nhds one_pos)] with n hn hna'
    have hc := trunc_second_moment_mu_le (K := C.toKilledKernel) d s.continuous_weight μ hfm hf hT ha hlower
      (R * B n) (mul_pos hR (hB n)).le
    have hh := mul_le_mul_of_nonneg_left hc (div_nonneg (Nat.cast_nonneg n) (sq_nonneg (B n)))
    have hh1 := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ha.le)
    have hh2 := mul_le_mul_of_nonneg_right hna' (sq_nonneg T)
    nlinarith
  have hμr := scaled_residual_second_moment_zero μ hfm hrm hf hr
    (fun n => R * B n) (fun n => (mul_pos hR (hB n)).le) hna
    ⟨a⁻¹ * L + T ^ 2, by positivity, hμbound⟩
  have hνr := scaled_residual_second_moment_zero ν hfm hrm hf hr
    (fun n => R * B n) (fun n => (mul_pos hR (hB n)).le) hna ⟨L, hL, hνbound⟩
  obtain ⟨G, hG0, hqG, hG⟩ := exists_cut_bound_tendsto_zero hr hB
    (positivePowerScale_tendsto_atTop hC hα) hR
  let q : ℕ → M → ℝ := fun n y => (B n)⁻¹ * cut f r (R * B n) y
  have hqm (n : ℕ) : Measurable (q n) := (measurable_cut hfm hrm _).const_mul _
  have hμq : Tendsto (fun n : ℕ => (n : ℝ) * ∫ y, q n y ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [q, normalized_cut_second_moment] using hμr
  have hνq : Tendsto (fun n : ℕ => (n : ℝ) * ∫ y, q n y ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa only [q, normalized_cut_second_moment] using hνr
  have hresult := centered_array_negligible C h d s hlive μ hleft hnorm x q hqm G hG0 hqG hG hμq hνq
  simpa only [q, pathBirkhoffSum_const_mul, integral_const_mul, mul_assoc] using hresult

end Chain
end
end ConditionedStableLaws.ContinuousMultiplier
