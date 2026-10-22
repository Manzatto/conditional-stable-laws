import ConditionedStableLaws.FirstMoments
import ConditionedStableLaws.NormalizationBridge

/-!
# Scaled truncated moments and compensation constants

Deterministic asymptotics for the stable laws with `1 ≤ α < 2`. For a nonnegative observable with
`ν(f > t) ∼ C t^{-α}` and `B_n = (C n)^{1/α}`:

* `n ν(f > u B_n) → u^{-α}` for `u > 0`;
* `(n/B_n²) ν(f² 1_{f ≤ εB_n}) → α/(2-α) ε^{2-α}` for `α < 2`;
* for `α = 1`, `(n/B_n) ν(f 1_{εB_n < f ≤ B_n}) → log(1/ε)` for `0 < ε ≤ 1`;
* for `α > 1`, `(n/B_n) ν(f 1_{f > εB_n}) → α/(α-1) ε^{1-α}`.

The last two are the centring constants `∫_{(ε,1]} y υ_n(dy)` and `∫_{(ε,∞]} y υ_n(dy)`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.CompensationAsymptotics

noncomputable section

open NormalizationBridge

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ}
  {Cc α : ℝ}

theorem eventually_scale_rpow (hC : 0 < Cc) (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, positivePowerScale Cc α n ^ α = Cc * n := by
  filter_upwards [positivePowerScale_eventually_eq Cc α] with n hn
  rw [hn, powerScale_rpow hC.le hα.ne']

theorem antitone_tail (f : Ω → ℝ) : Antitone fun s : ℝ => ν.real {x | s < f x} :=
  fun _ _ hst => measureReal_mono (fun _ hx => lt_of_le_of_lt hst hx)

omit [IsFiniteMeasure ν] in
/-- `n ν(f > B_n u) → u^{-α}`. -/
theorem scaled_tail (hC : 0 < Cc) (hα : 0 < α)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-α))) atTop (𝓝 1))
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real {x | positivePowerScale Cc α n * u < f x}) atTop
      (𝓝 (u ^ (-α))) := by
  have harg : Tendsto (fun n : ℕ => positivePowerScale Cc α n * u) atTop atTop :=
    (positivePowerScale_tendsto_atTop hC hα).atTop_mul_const hu
  have h := (htail.comp harg).mul_const (u ^ (-α))
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_scale_rpow hC hα, eventually_gt_atTop 0] with n hn hn0
  have hB := positivePowerScale_pos hC (α := α) n
  simp only [Function.comp_apply]
  rw [Real.mul_rpow hB.le hu.le, Real.rpow_neg hB.le, hn]
  have : u ^ (-α) ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp

/-- `(n/B_n²) ν(f² 1_{f ≤ εB_n}) → α/(2-α) ε^{2-α}`. -/
theorem scaled_second_moment (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hC : 0 < Cc)
    (hα : 0 < α) (hα2 : α < 2)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-α))) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) / positivePowerScale Cc α n ^ 2 *
      ∫ y, {y | f y ≤ ε * positivePowerScale Cc α n}.indicator (fun y => f y ^ 2) y ∂ν) atTop
      (𝓝 (α / (2 - α) * ε ^ (2 - α))) := by
  set B := positivePowerScale Cc α
  have hm := truncated_second_moment_div_rpow_tendsto (μ := ν) f hf hf0 Cc α hC hα2 htail
  have harg : Tendsto (fun n : ℕ => ε * B n) atTop atTop :=
    (positivePowerScale_tendsto_atTop hC hα).const_mul_atTop hε
  have hcomp := (hm.comp harg).mul_const (ε ^ (2 - α) / Cc)
  have hval : α * Cc / (2 - α) * (ε ^ (2 - α) / Cc) = α / (2 - α) * ε ^ (2 - α) := by
    field_simp
  rw [hval] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_scale_rpow hC hα, eventually_gt_atTop 0] with n hBα hn0
  have hBpos : 0 < B n := positivePowerScale_pos hC n
  simp only [Function.comp_apply]
  have hpow : (ε * B n) ^ (2 - α) = ε ^ (2 - α) * (B n ^ α)⁻¹ * B n ^ 2 := by
    rw [Real.mul_rpow hε.le hBpos.le, Real.rpow_sub hBpos, Real.rpow_two, div_eq_mul_inv]
    ring
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hεp : ε ^ (2 - α) ≠ 0 := (Real.rpow_pos_of_pos hε _).ne'
  rw [hpow, hBα]
  field_simp

/-- At tail exponent one: `(n/B_n)(ν(f 1_{f ≤ B_n}) - ν(f 1_{f ≤ εB_n})) → log(1/ε)`. -/
theorem scaled_band_mean (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hC : 0 < Cc)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-(1 : ℝ))))
      atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Tendsto (fun n : ℕ => (n : ℝ) / positivePowerScale Cc 1 n *
      ((∫ y, {y | f y ≤ positivePowerScale Cc 1 n}.indicator f y ∂ν) -
        ∫ y, {y | f y ≤ ε * positivePowerScale Cc 1 n}.indicator f y ∂ν)) atTop
      (𝓝 (Real.log (1 / ε))) := by
  set B := positivePowerScale Cc 1
  set T : ℝ → ℝ := fun s => ν.real {x | s < f x} with hT
  have hTa : Antitone T := antitone_tail f
  have hD (u : ℝ) (hu : 0 < u) := scaled_tail hC one_pos htail hu
  -- The band integral converges by dominated convergence.
  have hint : Tendsto (fun n : ℕ => ∫ u in ε..1, (n : ℝ) * T (B n * u)) atTop
      (𝓝 (∫ u in ε..1, u⁻¹)) := by
    have hev := (hD ε hε).eventually (gt_mem_nhds (show ε ^ (-(1 : ℝ)) < ε⁻¹ + 1 by
      rw [Real.rpow_neg_one]; linarith))
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => ε⁻¹ + 1) (Eventually.of_forall fun n => ?_) ?_ intervalIntegrable_const ?_
    · have hB := positivePowerScale_pos hC (α := 1) n
      have : Antitone fun u : ℝ => (n : ℝ) * T (B n * u) := fun u v huv =>
        mul_le_mul_of_nonneg_left (hTa (mul_le_mul_of_nonneg_left huv hB.le)) (Nat.cast_nonneg n)
      exact this.measurable.aestronglyMeasurable
    · filter_upwards [hev] with n hn
      refine Eventually.of_forall fun u hu => ?_
      rw [uIoc_of_le hε1] at hu
      have hB := positivePowerScale_pos hC (α := 1) n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)]
      calc (n : ℝ) * T (B n * u) ≤ n * T (B n * ε) :=
            mul_le_mul_of_nonneg_left (hTa (mul_le_mul_of_nonneg_left hu.1.le hB.le))
              (Nat.cast_nonneg n)
        _ ≤ ε⁻¹ + 1 := hn.le
    · refine Eventually.of_forall fun u hu => ?_
      rw [uIoc_of_le hε1] at hu
      have := hD u (hε.trans hu.1)
      rwa [Real.rpow_neg_one] at this
  rw [integral_inv_of_pos hε one_pos] at hint
  have h1 := hD 1 one_pos
  simp only [Real.one_rpow, mul_one] at h1
  have hε' := (hD ε hε).const_mul ε
  rw [Real.rpow_neg_one, mul_inv_cancel₀ hε.ne'] at hε'
  have hsum := (hint.sub h1).add hε'
  rw [sub_add_cancel] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn0
  have hB := positivePowerScale_pos hC (α := 1) n
  rw [truncated_first_moment ν f hf hf0 _ hB, truncated_first_moment ν f hf hf0 _ (mul_pos hε hB),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun s => T s)
      hB.ne', smul_eq_mul, mul_one]
  have hsub := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_real_tail ν f 0 (B n)) (intervalIntegrable_real_tail ν f 0 (ε * B n))
  have e1 : ∫ s in (0 : ℝ)..B n, ν.real {x | s < f x} =
      (∫ s in (0 : ℝ)..ε * B n, ν.real {x | s < f x}) + ∫ s in ε * B n..B n, T s := by
    rw [← hsub]; ring
  rw [e1, show B n * ε = ε * B n by ring]
  simp only [hT, B]
  field_simp
  ring

/-- Above tail exponent one: `(n/B_n)(ν(f) - ν(f 1_{f ≤ εB_n})) → α/(α-1) ε^{1-α}`. -/
theorem scaled_tail_mean (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hC : 0 < Cc)
    (hα1 : 1 < α)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-α))) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) / positivePowerScale Cc α n *
      ((∫ y, f y ∂ν) - ∫ y, {y | f y ≤ ε * positivePowerScale Cc α n}.indicator f y ∂ν)) atTop
      (𝓝 (α / (α - 1) * ε ^ (1 - α))) := by
  have hα : 0 < α := zero_lt_one.trans hα1
  set B := positivePowerScale Cc α
  set T : ℝ → ℝ := fun s => ν.real {x | s < f x} with hT
  have hTa : Antitone T := antitone_tail f
  have hfi : Integrable f ν := integrable_of_power_tail_asymptotic ν f hf hf0 Cc α hC hα1 htail
  -- The tail function is integrable on `(0, ∞)` by the layer-cake formula.
  have hTint : IntegrableOn T (Ioi 0) := by
    have key := lintegral_eq_lintegral_meas_lt ν (ae_of_all _ hf0) hf.aemeasurable
    have hfin : (∫⁻ t in Ioi 0, ν {x | t < f x}) ≠ ∞ := by
      rw [← key]; exact (hfi.lintegral_lt_top).ne
    have hmeas : AEMeasurable (fun t : ℝ => ν {x | t < f x}) (volume.restrict (Ioi 0)) := by
      have : Antitone fun t : ℝ => ν {x | t < f x} :=
        fun _ _ hst => measure_mono (fun _ hx => lt_of_le_of_lt hst hx)
      exact this.measurable.aemeasurable
    exact integrable_toReal_of_lintegral_ne_top hmeas hfin
  have hsplit (t : ℝ) (ht : 0 < t) : (∫ y, f y ∂ν) - ∫ y, {y | f y ≤ t}.indicator f y ∂ν =
      (∫ s in Ioi t, T s) + t * T t := by
    rw [hfi.integral_eq_integral_meas_lt (ae_of_all _ hf0),
      ← intervalIntegral.integral_interval_add_Ioi hTint (hTint.mono_set (Ioi_subset_Ioi ht.le)),
      truncated_first_moment ν f hf hf0 t ht]
    simp only [hT]
    ring
  have hD (u : ℝ) (hu : 0 < u) := scaled_tail hC hα htail hu
  -- A uniform power bound for the tail far out.
  obtain ⟨t0, ht0⟩ := eventually_atTop.1 (htail.eventually (gt_mem_nhds one_lt_two))
  have hbound : ∀ t, max t0 1 ≤ t → T t ≤ 2 * Cc * t ^ (-α) := by
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans_le ((le_max_right _ _).trans ht)
    have h := ht0 t ((le_max_left _ _).trans ht)
    have hp : 0 < Cc * t ^ (-α) := mul_pos hC (Real.rpow_pos_of_pos htpos _)
    rw [div_lt_iff₀ hp] at h
    linarith
  have hint : Tendsto (fun n : ℕ => ∫ u in Ioi ε, (n : ℝ) * T (B n * u)) atTop
      (𝓝 (∫ u in Ioi ε, u ^ (-α))) := by
    have hlarge : ∀ᶠ n : ℕ in atTop, max t0 1 ≤ B n * ε :=
      ((positivePowerScale_tendsto_atTop hC hα).atTop_mul_const hε).eventually
        (eventually_ge_atTop _)
    refine tendsto_integral_filter_of_dominated_convergence (fun u => 2 * u ^ (-α))
      (Eventually.of_forall fun n => ?_) ?_ ((integrableOn_Ioi_rpow_of_lt (by linarith) hε).const_mul 2) ?_
    · have hB := positivePowerScale_pos hC (α := α) n
      have : Antitone fun u : ℝ => (n : ℝ) * T (B n * u) := fun u v huv =>
        mul_le_mul_of_nonneg_left (hTa (mul_le_mul_of_nonneg_left huv hB.le)) (Nat.cast_nonneg n)
      exact this.measurable.aestronglyMeasurable
    · filter_upwards [hlarge, eventually_scale_rpow hC hα, eventually_gt_atTop 0] with n hn hBα hn0
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hB := positivePowerScale_pos hC (α := α) n
      have hu0 : 0 < u := hε.trans hu
      have hle : max t0 1 ≤ B n * u := hn.trans (mul_le_mul_of_nonneg_left hu.le hB.le)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)]
      calc (n : ℝ) * T (B n * u) ≤ n * (2 * Cc * (B n * u) ^ (-α)) :=
            mul_le_mul_of_nonneg_left (hbound _ hle) (Nat.cast_nonneg n)
        _ = 2 * u ^ (-α) := by
            rw [Real.mul_rpow hB.le hu0.le, Real.rpow_neg hB.le, hBα]
            have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
            field_simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hD u (hε.trans hu)
  rw [integral_Ioi_rpow_of_lt (by linarith) hε] at hint
  have hε' := (hD ε hε).const_mul ε
  have hsum := hint.add hε'
  have hval : -ε ^ (-α + 1) / (-α + 1) + ε * ε ^ (-α) = α / (α - 1) * ε ^ (1 - α) := by
    have e : ε * ε ^ (-α) = ε ^ (1 - α) := by
      rw [show 1 - α = 1 + -α by ring, Real.rpow_add hε, Real.rpow_one]
    rw [e, show -α + 1 = 1 - α by ring]
    have : α - 1 ≠ 0 := by linarith
    have : 1 - α ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn0
  have hB := positivePowerScale_pos hC (α := α) n
  rw [hsplit _ (mul_pos hε hB), integral_const_mul,
    integral_comp_mul_left_Ioi (fun s => T s) ε hB, smul_eq_mul]
  simp only [hT, B, show positivePowerScale Cc α n * ε = ε * positivePowerScale Cc α n by ring]
  field_simp

end

end ConditionedStableLaws.CompensationAsymptotics
