import ConditionedStableLaws.L2CLT
import ConditionedStableLaws.StableLawCompensated
import ConditionedStableLaws.TruncatedAsymptotics

/-!
# The Gaussian boundary case `α = 2`

With `B_n = √(C n log n)` and the truncation level `u_n = √(C n) (log n)^{1/4}` (equal to `B_n/(log
n)^{1/4}` once `log n > 0`), the centred truncations `g_n = f 1_{f ≤ u_n} - ν(f 1_{f ≤ u_n})`
satisfy the hypotheses of the conditional triangular-array CLT with `a_n = B_n` and `σ² = 1` (steps
1–3); observations above `u_n` are conditionally negligible (step 4); and Slutsky's theorem returns
to `f - ν(f)` (step 5).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ConditionedStableLaws.GaussianBoundary

noncomputable section

open NormalizationBridge CompensationAsymptotics

/-- The normalization `B_n = √(C n log n)`. -/
def bScale (Cc : ℝ) (n : ℕ) : ℝ := Real.sqrt (Cc * n * Real.log n)

/-- The truncation level `u_n = √(C n) (log n)^{1/4}`. -/
def uScale (Cc : ℝ) (n : ℕ) : ℝ := Real.sqrt (Cc * n) * Real.log n ^ (1 / 4 : ℝ)

/-! ### Deterministic scales -/

section Scales

variable {Cc : ℝ}

theorem tendsto_log_nat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem eventually_one_le_log : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
  tendsto_log_nat.eventually_ge_atTop 1

theorem tendsto_sqrt_mul_nat (hC : 0 < Cc) :
    Tendsto (fun n : ℕ => Real.sqrt (Cc * n)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hC)

theorem bScale_tendsto (hC : 0 < Cc) : Tendsto (bScale Cc) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => Cc * n * Real.log n) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hC).atTop_mul_atTop₀ tendsto_log_nat
  exact Real.tendsto_sqrt_atTop.comp h1

theorem bScale_eq (hC : 0 < Cc) {n : ℕ} (hn : 1 ≤ Real.log n) :
    bScale Cc n = uScale Cc n * Real.log n ^ (1 / 4 : ℝ) := by
  have hl : 0 ≤ Real.log n := zero_le_one.trans hn
  unfold bScale uScale
  rw [Real.sqrt_mul (by positivity), mul_assoc, ← Real.rpow_add (by linarith),
    Real.sqrt_eq_rpow (Real.log n)]
  norm_num

theorem uScale_pos (hC : 0 < Cc) {n : ℕ} (hn : 1 ≤ Real.log n) : 0 < uScale Cc n := by
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hn; linarith
    · exact_mod_cast h
  unfold uScale
  exact mul_pos (Real.sqrt_pos.2 (mul_pos hC hn0)) (Real.rpow_pos_of_pos (by linarith) _)

theorem sqrt_le_uScale (_hC : 0 < Cc) {n : ℕ} (hn : 1 ≤ Real.log n) :
    Real.sqrt (Cc * n) ≤ uScale Cc n := by
  unfold uScale
  exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_rpow hn (by norm_num))

theorem uScale_tendsto (hC : 0 < Cc) : Tendsto (uScale Cc) atTop atTop :=
  tendsto_atTop_mono' atTop (eventually_one_le_log.mono fun _n hn => sqrt_le_uScale hC hn)
    (tendsto_sqrt_mul_nat hC)

theorem uScale_div_bScale_tendsto (hC : 0 < Cc) :
    Tendsto (fun n => uScale Cc n / bScale Cc n) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp tendsto_log_nat
  refine h.congr' ?_
  filter_upwards [eventually_one_le_log] with n hn
  simp only [Function.comp_apply]
  rw [bScale_eq hC hn, div_mul_cancel_left₀ (uScale_pos hC hn).ne',
    Real.rpow_neg (by linarith)]

theorem uScale_sq (hC : 0 < Cc) {n : ℕ} (hn : 1 ≤ Real.log n) :
    uScale Cc n ^ 2 = Cc * n * Real.sqrt (Real.log n) := by
  have hl : 0 ≤ Real.log n := zero_le_one.trans hn
  unfold uScale
  rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hl,
    Real.sqrt_eq_rpow]
  norm_num

theorem nat_div_uScale_sq_tendsto (hC : 0 < Cc) :
    Tendsto (fun n : ℕ => (n : ℝ) / uScale Cc n ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Cc⁻¹ * (Real.sqrt (Real.log n))⁻¹) atTop (𝓝 0) := by
    have := (Real.tendsto_sqrt_atTop.comp tendsto_log_nat).inv_tendsto_atTop.const_mul Cc⁻¹
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_one_le_log, eventually_gt_atTop 0] with n hn hn0
  rw [uScale_sq hC hn]
  have : (0 : ℝ) < n := by exact_mod_cast hn0
  have : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.2 (by linarith)
  field_simp

theorem log_uScale_div_log_tendsto (hC : 0 < Cc) :
    Tendsto (fun n : ℕ => Real.log (uScale Cc n) / Real.log n) atTop (𝓝 (1 / 2)) := by
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_log_nat
    simpa [Function.comp_def] using this
  have hc : Tendsto (fun n : ℕ => Real.log Cc / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_nat
  have h := ((hc.const_mul (1 / 2)).add (hll.const_mul (1 / 4))).const_add (1 / 2)
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_one_le_log, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hl : 0 < Real.log n := by linarith
  unfold uScale
  rw [Real.log_mul (Real.sqrt_pos.2 (mul_pos hC hn')).ne' (Real.rpow_pos_of_pos hl _).ne',
    Real.log_sqrt (mul_pos hC hn').le, Real.log_mul hC.ne' hn'.ne', Real.log_rpow hl]
  field_simp
  ring

/-- `n / B_n = (n / √(C n)) (log n)^{-1/2}`. -/
theorem nat_div_bScale_eq (hC : 0 < Cc) {n : ℕ} (hn : 1 ≤ Real.log n) :
    (n : ℝ) / bScale Cc n =
      (n : ℝ) / positivePowerScale Cc 2 n * (Real.sqrt (Real.log n))⁻¹ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn; linarith
  have hp : positivePowerScale Cc 2 n = Real.sqrt (Cc * n) := by
    rw [positivePowerScale, ite_eq_right hn0, powerScale, Real.sqrt_eq_rpow]
  rw [hp, bScale, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Cc * n), div_mul_eq_div_div,
    div_eq_mul_inv _ (Real.sqrt _)]

end Scales

/-! ### Moment asymptotics under `ν(f > t) ∼ C t⁻²` -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ}
  {Cc : ℝ}

/-- `ν(f² 1_{f ≤ u_n}) ∼ 2C log u_n ∼ C log n`. -/
theorem trunc_sq_div_log_tendsto (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hC : 0 < Cc)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-2 : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (∫ x, {x | f x ≤ uScale Cc n}.indicator (fun x => f x ^ 2) x ∂ν) /
      Real.log n) atTop (𝓝 Cc) := by
  have h1 := (truncated_second_moment_div_log_tendsto ν f hf hf0 Cc hC htail).comp
    (uScale_tendsto hC)
  have h2 := h1.mul (log_uScale_div_log_tendsto hC)
  rw [show 2 * Cc * (1 / 2) = Cc by ring] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_one_le_log,
    (Real.tendsto_log_atTop.comp (uScale_tendsto hC)).eventually_gt_atTop 0] with n hn hlu
  simp only [Function.comp_apply] at hlu ⊢
  have hl : 0 < Real.log n := by linarith
  field_simp

omit [IsProbabilityMeasure ν] in
/-- `n ν(f > u_n) → 0`. -/
theorem nat_mul_tail_tendsto (hC : 0 < Cc)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-2 : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real {x | uScale Cc n < f x}) atTop (𝓝 0) := by
  have h1 := (scaled_square_tail_tendsto ν f Cc hC htail).comp (uScale_tendsto hC)
  have h2 := h1.mul (nat_div_uScale_sq_tendsto hC)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_one_le_log] with n hn
  simp only [Function.comp_apply]
  have := (uScale_pos hC hn).ne'
  field_simp

/-- `(n/B_n) ν(f 1_{f > u_n}) → 0`. -/
theorem tail_mean_tendsto (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hC : 0 < Cc)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-2 : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) / bScale Cc n *
      ∫ x, {x | uScale Cc n < f x}.indicator f x ∂ν) atTop (𝓝 0) := by
  have htail' : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-(2 : ℝ)))) atTop
      (𝓝 1) := htail
  have hfi : Integrable f ν :=
    integrable_of_power_tail_asymptotic ν f hf hf0 Cc 2 hC one_lt_two htail'
  have hmean := scaled_tail_mean (ν := ν) hf hf0 hC one_lt_two htail' one_pos
  have hlim := ((Real.tendsto_sqrt_atTop.comp tendsto_log_nat).inv_tendsto_atTop).mul hmean
  rw [zero_mul] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hlim
  · have hb : 0 ≤ bScale Cc n := Real.sqrt_nonneg _
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) hb)
      (integral_nonneg fun x => indicator_nonneg (fun y _ => hf0 y) x)
  filter_upwards [eventually_one_le_log, positivePowerScale_eventually_eq Cc 2,
    eventually_gt_atTop 0] with n hn hpe hn0
  set B' := positivePowerScale Cc 2 n
  have hB'u : 1 * B' ≤ uScale Cc n := by
    have hp : B' = Real.sqrt (Cc * n) := by
      rw [hpe, powerScale, Real.sqrt_eq_rpow]
    rw [one_mul, hp]; exact sqrt_le_uScale hC hn
  have hsplit : ∫ x, {x | uScale Cc n < f x}.indicator f x ∂ν =
      (∫ x, f x ∂ν) - ∫ x, {x | f x ≤ uScale Cc n}.indicator f x ∂ν := by
    have hS : MeasurableSet {x | f x ≤ uScale Cc n} := measurableSet_le hf measurable_const
    rw [eq_sub_iff_add_eq, ← integral_add (hfi.indicator (measurableSet_lt measurable_const hf))
      (hfi.indicator hS)]
    congr 1; funext x
    by_cases hx : f x ≤ uScale Cc n
    · simp [indicator, hx, not_lt.2 hx]
    · simp [indicator, hx, lt_of_not_ge hx]
  have hmono : ∫ x, {x | f x ≤ 1 * B'}.indicator f x ∂ν ≤
      ∫ x, {x | f x ≤ uScale Cc n}.indicator f x ∂ν :=
    integral_mono (hfi.indicator (measurableSet_le hf measurable_const))
      (hfi.indicator (measurableSet_le hf measurable_const))
      (indicator_le_indicator_of_subset (fun x hx => le_trans hx hB'u) (fun x => hf0 x))
  rw [nat_div_bScale_eq hC hn, hsplit]
  have hB'0 : 0 < B' := positivePowerScale_pos hC n
  have hc : 0 ≤ (n : ℝ) / B' := div_nonneg (Nat.cast_nonneg n) hB'0.le
  have hs : 0 ≤ (Real.sqrt (Real.log n))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  calc (n : ℝ) / B' * (Real.sqrt (Real.log n))⁻¹ *
        ((∫ x, f x ∂ν) - ∫ x, {x | f x ≤ uScale Cc n}.indicator f x ∂ν)
      ≤ (n : ℝ) / B' * (Real.sqrt (Real.log n))⁻¹ *
        ((∫ x, f x ∂ν) - ∫ x, {x | f x ≤ 1 * B'}.indicator f x ∂ν) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hs)
    _ = _ := by simp only [Pi.inv_apply, Function.comp_apply]; ring

end Moments

/-!
### The covariance series is negligible
-/

section Covariance

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

open StandingHypothesis CanonicalChain ConditionalCLT L2Variance

set_option maxHeartbeats 4000000 in
/-- If `μ(q_n²) = O(ℓ_n)` with `ℓ_n → ∞` and `q_n` converges pointwise to a
finite limit, then the covariance series of `q_n` is `o(ℓ_n)`: compactness of
the `L²(μ)` remainder turns the weak convergence `η q_n/√ℓ_n ⇀ 0` into strong
convergence. -/
theorem correlation_series_div_tendsto (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (q : ℕ → M → ℝ) (hqm : ∀ n, Measurable (q n)) (Q : ℕ → ℝ)
    (hqQ : ∀ n y, |q n y| ≤ Q n)
    (hqν : ∀ n, ∫ y, q n y ∂μ.withDensity d.weight = 0)
    (ℓ : ℕ → ℝ) (hℓ1 : ∀ n, 1 ≤ ℓ n) (hℓ : Tendsto ℓ atTop atTop)
    (K : ℝ) (hK : ∀ n, ∫ y, q n y ^ 2 ∂μ ≤ K * ℓ n)
    (qlim : M → ℝ) (hqlim : ∀ y, Tendsto (fun n => q n y) atTop (𝓝 (qlim y))) :
    Tendsto (fun n => (∑' m, correlation C μ d (q n) m) / ℓ n) atTop (𝓝 0) := by
  obtain ⟨-, -, -, -, P2, R2, -, hR2, -, hR2c, L, κ, hL, hκ0, hκ1, hdec, -⟩ :=
    h.l2_compactness (K := C.toKilledKernel) d s.continuous_weight μ hleft hnorm
  obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d
    s.continuous_weight
  set η : M → ℝ := fun y => (d.weight y).toReal with hη_def
  have hηm : Measurable η := d.measurable_weight.ennreal_toReal
  have hηL : MemLp η ∞ μ := memLp_top_of_bound hηm.aestronglyMeasurable Bη (ae_of_all _ hBη)
  set A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2 (hηL.toLp η) with hA_def
  have hA : ∀ u : Lp ℝ 2 μ, (A u : M → ℝ) =ᵐ[μ] fun y => η y * u y := by
    intro u
    change ((ContinuousLinearMap.mul ℝ ℝ).holder (2 : ℝ≥0∞) (hηL.toLp η) u : M → ℝ) =ᵐ[μ] _
    filter_upwards [ContinuousLinearMap.coeFn_holder (r := (2 : ℝ≥0∞))
      (ContinuousLinearMap.mul ℝ ℝ) (hηL.toLp η) u, hηL.coeFn_toLp] with y h1 h2
    rw [h1, h2]; rfl
  have hK0 : 0 ≤ K := by
    have h0 := hK 0
    have hi : 0 ≤ ∫ y, q 0 y ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
    nlinarith [hℓ1 0]
  have hcen : ∀ n, centered C μ d (q n) = q n := fun n => by
    funext y; simp [centered, hqν n]
  have hq2 : ∀ n, MemLp (q n) 2 μ := fun n =>
    MemLp.of_bound (hqm n).aestronglyMeasurable (Q n)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hqQ n y)
  have hw2 : ∀ n, MemLp (fun y => η y * q n y) 2 μ := fun n =>
    MemLp.of_bound (hηm.mul (hqm n)).aestronglyMeasurable (Bη * Q n)
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        have := hBη y; rw [Real.norm_eq_abs] at this
        exact mul_le_mul this (hqQ n y) (abs_nonneg _) ((abs_nonneg _).trans this))
  have hw0 : ∀ n, ∫ y, η y * q n y ∂μ = 0 := fun n => by
    rw [← hqν n, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
    rfl
  set u : ℕ → Lp ℝ 2 μ := fun n => (hq2 n).toLp (q n) with hu_def
  have hv : ∀ n, (hw2 n).toLp (fun y => η y * q n y) = A (u n) := fun n => by
    apply Lp.ext
    filter_upwards [(hw2 n).coeFn_toLp, hA (u n), (hq2 n).coeFn_toLp] with y h1 h2 h3
    rw [h1, h2, hu_def]; simp only; rw [h3]
  have hcorr : ∀ n m, correlation C μ d (q n) m = ⟪u n, (R2 ^ (m + 1)) (A (u n))⟫_ℝ := by
    intro n m
    have hpow := remainder_pow_ae_nkp C d s.continuous_weight μ hleft hnorm R2 hR2
      (show Measurable fun y => η y * q n y from hηm.mul (hqm n)) (hw2 n) (hw0 n) (m + 1)
    rw [hv n] at hpow
    unfold correlation
    rw [hcen n, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hq2 n).coeFn_toLp, hpow] with y h1 h2
    simp only [Real.inner_apply, hu_def]
    rw [h1, h2]
    simp only [SecondMoment.nkp, η]
  set w : ℕ → Lp ℝ 2 μ := fun n => (Real.sqrt (ℓ n))⁻¹ • u n with hw_def
  have hsq : ∀ n, Real.sqrt (ℓ n) * Real.sqrt (ℓ n) = ℓ n := fun n =>
    Real.mul_self_sqrt (zero_le_one.trans (hℓ1 n))
  have hsqpos : ∀ n, 0 < Real.sqrt (ℓ n) := fun n => Real.sqrt_pos.2 (by linarith [hℓ1 n])
  have huw : ∀ n, u n = Real.sqrt (ℓ n) • w n := fun n => by
    rw [hw_def]; simp only; rw [smul_smul, mul_inv_cancel₀ (hsqpos n).ne', one_smul]
  have hscale : ∀ n m, ⟪u n, (R2 ^ (m + 1)) (A (u n))⟫_ℝ =
      ℓ n * ⟪w n, (R2 ^ (m + 1)) (A (w n))⟫_ℝ := fun n m => by
    rw [huw n, map_smul, map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      hsq n]
  have hnorm_u : ∀ n, ‖u n‖ ^ 2 = ∫ y, q n y ^ 2 ∂μ := fun n => by
    rw [SecondMoment.norm_sq_L2]
    exact integral_congr_ae (by filter_upwards [(hq2 n).coeFn_toLp] with y hy; rw [hy])
  have hbound : ∀ n, ‖w n‖ ≤ Real.sqrt K := fun n => by
    rw [hw_def]; simp only
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hsqpos n)]
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, inv_pow, Real.sq_sqrt (zero_le_one.trans (hℓ1 n)), hnorm_u n]
    rw [inv_mul_le_iff₀ (by linarith [hℓ1 n]), mul_comm]
    exact hK n
  have hae : ∀ᵐ y ∂μ, Tendsto (fun n => (w n : M → ℝ) y) atTop (𝓝 0) := by
    have hall : ∀ᵐ y ∂μ, ∀ n, (w n : M → ℝ) y = (Real.sqrt (ℓ n))⁻¹ * q n y := by
      rw [ae_all_iff]
      intro n
      filter_upwards [Lp.coeFn_smul (Real.sqrt (ℓ n))⁻¹ (u n), (hq2 n).coeFn_toLp] with y h1 h2
      rw [hw_def]; simp only; rw [h1, Pi.smul_apply, smul_eq_mul, hu_def]; simp only; rw [h2]
    filter_upwards [hall] with y hy
    simp only [hy]
    have := ((Real.tendsto_sqrt_atTop.comp hℓ).inv_tendsto_atTop).mul (hqlim y)
    rwa [zero_mul] at this
  have hdecay : ∀ k : ℕ, ‖R2 ^ (k + 1)‖ ≤ (L * κ) * κ ^ k := fun k =>
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f =>
      (hdec (k + 1) (by omega) f).trans (le_of_eq (by rw [pow_succ]; ring))
  have hmain := L2_covariance_series_tendsto_zero R2 A hR2c (by positivity) hκ0.le hκ1 hdecay
    w (Real.sqrt K) hbound hae
  have hsumm : ∀ n, Summable (fun m => ‖⟪w n, (R2 ^ (m + 1)) (A (w n))⟫_ℝ‖) := by
    intro n
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((summable_geometric_of_lt_one hκ0.le hκ1).mul_left
        (Real.sqrt K * (L * κ) * ‖A‖ * Real.sqrt K))
    calc ‖⟪w n, (R2 ^ (m + 1)) (A (w n))⟫_ℝ‖ ≤ ‖w n‖ * ‖(R2 ^ (m + 1)) (A (w n))‖ :=
          norm_inner_le_norm _ _
      _ ≤ Real.sqrt K * ((L * κ) * κ ^ m * (‖A‖ * Real.sqrt K)) := by
          apply mul_le_mul (hbound n) _ (norm_nonneg _) (Real.sqrt_nonneg _)
          calc ‖(R2 ^ (m + 1)) (A (w n))‖ ≤ ‖R2 ^ (m + 1)‖ * ‖A (w n)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ ((L * κ) * κ ^ m) * (‖A‖ * Real.sqrt K) :=
                mul_le_mul (hdecay m) ((ContinuousLinearMap.le_opNorm _ _).trans
                  (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _))) (norm_nonneg _)
                  (by positivity)
      _ = Real.sqrt K * (L * κ) * ‖A‖ * Real.sqrt K * κ ^ m := by ring
  refine squeeze_zero_norm (fun n => ?_) hmain
  have he : (∑' m, correlation C μ d (q n) m) / ℓ n =
      ∑' m, ⟪w n, (R2 ^ (m + 1)) (A (w n))⟫_ℝ := by
    simp_rw [hcorr n, hscale n]
    rw [tsum_mul_left, mul_div_cancel_left₀ _ (by linarith [hℓ1 n] : ℓ n ≠ 0)]
  rw [he]
  refine (norm_tsum_le_tsum_norm (hsumm n)).trans (le_of_eq ?_)
  simp only [Real.norm_eq_abs]

end Covariance

/-! ### Auxiliary facts -/

theorem exists_forall_le_of_eventually {w : ℕ → ℝ} {K : ℝ} (h : ∀ᶠ n in atTop, w n ≤ K) :
    ∃ B, ∀ n, w n ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨max K (∑ i ∈ Finset.range N, |w i|), fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_max_left _ _)
  · exact (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (w i))
      (Finset.mem_range.2 (by omega))).trans (le_max_right _ _))

theorem tendsto_measure_gt_zero {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    [IsFiniteMeasure ρ] {f : X → ℝ} (hf : Measurable f) :
    Tendsto (fun t : ℝ => ρ {x | t < f x}) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := ρ) (s := fun t : ℝ => {x | t < f x})
    (fun t => (measurableSet_lt measurable_const hf).nullMeasurableSet)
    (fun s t hst x hx => lt_of_le_of_lt hst hx) ⟨0, measure_ne_top _ _⟩
  have hI : (⋂ t : ℝ, {x | t < f x}) = ∅ := by
    ext x
    simp only [mem_iInter, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨f x, le_refl _⟩
  rwa [hI, measure_empty] at h

section Chain

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

open StandingHypothesis CanonicalChain ConditionalCLT L2Variance

omit [CompactSpace M] [BorelSpace M] in
/-- Large values of `f_β` occur only where `η` is bounded below. -/
theorem exists_weight_lower (d : DoobTransform.EigenData C.killedTransition)
    (hc : Continuous d.weight) {x₀ : M} (hx₀ : d.weight x₀ ≠ 0) {β : ℝ} (hβ : 0 < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ a : ℝ, 0 < a ∧
      ∀ z, T₀ < singularObservable x₀ β z → a ≤ (d.weight z).toReal := by
  have hη : Continuous (fun y => (d.weight y).toReal) := continuous_iff_continuousAt.mpr
    (fun y => (ENNReal.continuousAt_toReal (d.weight_ne_top y)).comp hc.continuousAt)
  have hpos : 0 < (d.weight x₀).toReal := ENNReal.toReal_pos hx₀ (d.weight_ne_top _)
  set a := (d.weight x₀).toReal / 2
  have hV : {y | a < (d.weight y).toReal} ∈ 𝓝 x₀ :=
    (isOpen_lt continuous_const hη).mem_nhds (half_lt_self hpos)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨max 1 (r ^ (-β)), lt_of_lt_of_le one_pos (le_max_left _ _), a, half_pos hpos,
    fun z hz => ?_⟩
  by_cases hzx : z = x₀
  · subst hzx
    rw [singularObservable_at_center] at hz
    exact absurd hz (not_lt.2 (le_max_left _ _))
  · have hd : 0 < dist z x₀ := dist_pos.2 hzx
    have hz' : r ^ (-β) < dist z x₀ ^ (-β) := by
      have : singularObservable x₀ β z = dist z x₀ ^ (-β) := by
        simp [singularObservable, hzx]
      rw [this] at hz
      exact lt_of_le_of_lt (le_max_right _ _) hz
    have hdr : dist z x₀ < r := by
      by_contra hcon
      exact absurd hz' (not_lt.2 (Real.rpow_le_rpow_of_nonpos hr (not_lt.1 hcon)
        (by linarith)))
    exact (hball (Metric.mem_ball.2 hdr)).le

set_option maxHeartbeats 16000000 in
/-- **Gaussian boundary case** `α = d/β = 2`: `f_β ∈ L¹(ν)` and, with `B_n = √(C n log n)`, `B_n⁻¹
(∑_{j<n} f_β(X_j) - n ν(f_β)) → 𝒩(0,1)` under `ℙ_x(· | τ > n)`. -/
theorem stable_law_boundary (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα : dimension / β = 2) :
    Integrable (singularObservable x₀ β) (μ.withDensity d.weight) ∧
    TendstoInDistribution
      (fun n ω => (bScale (volumeConstant * (d.weight x₀).toReal * m x₀) n)⁻¹ *
        (pathBirkhoffSum (singularObservable x₀ β) n ω -
          n * ∫ y, singularObservable x₀ β y ∂μ.withDensity d.weight)) atTop id
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (gaussianReal 0 1) := by
  have := h.reference_probability
  set Cc := volumeConstant * (d.weight x₀).toReal * m x₀ with hCc
  have hC : 0 < Cc := mul_pos (mul_pos hadm.1.2.1
    (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  set f := singularObservable x₀ β with hf_def
  have hfm : Measurable f := measurable_singularObservable x₀ β
  have hf0 : ∀ z, 0 ≤ f z := fun z => (singularObservable_pos x₀ β z).le
  set ν := μ.withDensity d.weight with hν_def
  have hνP : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have htail0 := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  rw [hα] at htail0
  have htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-2 : ℝ))) atTop
      (𝓝 1) := htail0
  have hfi : Integrable f ν :=
    integrable_of_power_tail_asymptotic ν f hfm hf0 Cc 2 hC one_lt_two htail
  refine ⟨hfi, ?_⟩
  have hνeq : ∀ k : M → ℝ, ∫ y, k y ∂ν = ∫ y, (d.weight y).toReal * k y ∂μ := fun k => by
    rw [hν_def, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
    rfl
  -- Truncation.
  set u := uScale Cc with hu_def
  set b := bScale Cc with hb_def
  set F := ∫ y, f y ∂ν with hF_def
  set c : ℕ → ℝ := fun n => ∫ y, {y | f y ≤ u n}.indicator f y ∂ν with hc_def
  set g : ℕ → M → ℝ := fun n y => {y | f y ≤ u n}.indicator f y - c n with hg_def
  have hS : ∀ n, MeasurableSet {y | f y ≤ u n} := fun n => measurableSet_le hfm measurable_const
  have hind0 : ∀ n y, 0 ≤ {y | f y ≤ u n}.indicator f y := fun n y =>
    indicator_nonneg (fun z _ => hf0 z) y
  have hind_le : ∀ n y, {y | f y ≤ u n}.indicator f y ≤ f y := fun n y =>
    indicator_le_self' (fun z _ => hf0 z) y
  have hindu : ∀ n y, {y | f y ≤ u n}.indicator f y ≤ u n := fun n y => by
    by_cases hy : f y ≤ u n
    · rw [indicator_of_mem (show y ∈ {y | f y ≤ u n} from hy)]; exact hy
    · rw [indicator_of_notMem (show y ∉ {y | f y ≤ u n} from hy)]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Real.log_natCast_nonneg n) _)
  have hc0 : ∀ n, 0 ≤ c n := fun n => integral_nonneg (hind0 n)
  have hcF : ∀ n, c n ≤ F := fun n => integral_mono (hfi.indicator (hS n)) hfi (hind_le n)
  have hF0 : 0 ≤ F := (hc0 0).trans (hcF 0)
  have hgm : ∀ n, Measurable (g n) := fun n => (hfm.indicator (hS n)).sub measurable_const
  have hgG : ∀ n y, |g n y| ≤ u n + F := fun n y => by
    rw [abs_le]
    constructor
    · have := hind0 n y; have := hcF n; have := (hind0 n y).trans (hindu n y)
      simp only [hg_def]; linarith
    · have := hindu n y; have := hc0 n; simp only [hg_def]; linarith
  have hgν : ∀ n, ∫ y, g n y ∂ν = 0 := fun n => by
    simp only [hg_def]
    rw [integral_sub (hfi.indicator (hS n)) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  -- The normalization.
  set a : ℕ → ℝ := fun n => max (b n) 1 with ha_def
  have ha : ∀ n, 0 < a n := fun n => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hab : ∀ᶠ n in atTop, a n = b n :=
    ((bScale_tendsto hC).eventually_ge_atTop 1).mono fun n hn => max_eq_left hn
  have ha_lim : Tendsto a atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) (bScale_tendsto hC)
  have hb_sq : ∀ᶠ n in atTop, b n ^ 2 = Cc * n * Real.log n :=
    eventually_one_le_log.mono fun n hn => by
      rw [hb_def, bScale, Real.sq_sqrt (by positivity)]
  -- Step 1.
  have hi : Tendsto (fun n => (u n + F) / a n) atTop (𝓝 0) := by
    have h1 := (uScale_div_bScale_tendsto hC).add
      ((tendsto_const_nhds (x := F)).div_atTop (bScale_tendsto hC))
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hab] with n hn
    rw [hn, add_div]
  -- Moments.
  set S2 : ℕ → ℝ := fun n => ∫ y, {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y ∂ν
    with hS2_def
  have hS2 := trunc_sq_div_log_tendsto (ν := ν) hfm hf0 hC htail
  have hsq_ind : ∀ n y, ({y | f y ≤ u n}.indicator f y) ^ 2 =
      {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y := fun n y => by
    by_cases hy : f y ≤ u n
    · simp [indicator, hy]
    · simp [indicator, hy]
  have hind2_int : ∀ n (κ : Measure M) [IsFiniteMeasure κ],
      Integrable ({y | f y ≤ u n}.indicator (fun y => f y ^ 2)) κ := fun n κ _ =>
    SecondMoment.integrable_of_bdd ((hfm.pow_const 2).indicator (hS n)) (B := u n ^ 2)
      (fun y => by
        rw [← hsq_ind, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hind0 n y) (hindu n y) 2)
  have hind_int : ∀ n (κ : Measure M) [IsFiniteMeasure κ],
      Integrable ({y | f y ≤ u n}.indicator f) κ := fun n κ _ =>
    SecondMoment.integrable_of_bdd (hfm.indicator (hS n)) (B := u n)
      (fun y => by rw [abs_of_nonneg (hind0 n y)]; exact hindu n y)
  have hνg2 : ∀ n, ∫ y, g n y ^ 2 ∂ν = S2 n - c n ^ 2 := fun n => by
    have e : ∀ y, g n y ^ 2 = {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y -
        2 * c n * {y | f y ≤ u n}.indicator f y + c n ^ 2 := fun y => by
      simp only [hg_def]; rw [← hsq_ind]; ring
    simp_rw [e]
    have i1 : Integrable (fun y => {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y -
        2 * c n * {y | f y ≤ u n}.indicator f y) ν :=
      (hind2_int n ν).sub ((hind_int n ν).const_mul (2 * c n))
    rw [integral_add i1 (integrable_const _),
      integral_sub (hind2_int n ν) ((hind_int n ν).const_mul (2 * c n)), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    simp only [hS2_def, hc_def]; ring
  obtain ⟨T₀, hT₀, aη, haη, hlow⟩ := exists_weight_lower C d s.continuous_weight hx₀ hβ
  have hμ2 : ∀ n, ∫ y, {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y ∂μ ≤
      T₀ ^ 2 + aη⁻¹ * S2 n := fun n => by
    have hpt : ∀ y, {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y ≤
        T₀ ^ 2 + aη⁻¹ * ((d.weight y).toReal *
          {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y) := fun y => by
      have hnn : 0 ≤ {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y :=
        indicator_nonneg (fun z _ => sq_nonneg _) y
      by_cases hy : T₀ < f y
      · have hl := hlow y hy
        have : {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y ≤
            aη⁻¹ * ((d.weight y).toReal * {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y) := by
          rw [← mul_assoc]
          refine le_mul_of_one_le_left hnn ?_
          rw [inv_mul_eq_div, le_div_iff₀ haη, one_mul]; exact hl
        nlinarith [sq_nonneg T₀]
      · have h1 : {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y ≤ T₀ ^ 2 := by
          rw [← hsq_ind]
          exact pow_le_pow_left₀ (hind0 n y) ((hind_le n y).trans (le_of_not_gt hy)) 2
        have h2 : 0 ≤ aη⁻¹ * ((d.weight y).toReal *
            {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y) :=
          mul_nonneg (inv_nonneg.2 haη.le) (mul_nonneg ENNReal.toReal_nonneg hnn)
        linarith
    have hwint : Integrable (fun y => (d.weight y).toReal *
        {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y) μ := by
      obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d
        s.continuous_weight
      refine (hind2_int n μ).bdd_mul (c := Bη) d.measurable_weight.ennreal_toReal.aestronglyMeasurable
        (ae_of_all _ fun y => hBη y)
    calc ∫ y, {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y ∂μ
        ≤ ∫ y, (T₀ ^ 2 + aη⁻¹ * ((d.weight y).toReal *
            {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y)) ∂μ :=
          integral_mono (hind2_int n μ) ((integrable_const _).add (hwint.const_mul _)) hpt
      _ = T₀ ^ 2 + aη⁻¹ * S2 n := by
          rw [integral_add (integrable_const _) (hwint.const_mul _), integral_const,
            probReal_univ, one_smul, integral_const_mul]
          rw [show S2 n = ∫ y, {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y ∂ν from rfl, hνeq]
  have hμg2 : ∀ n, ∫ y, g n y ^ 2 ∂μ ≤ 2 * (T₀ ^ 2 + aη⁻¹ * S2 n) + 2 * F ^ 2 := fun n => by
    have hgint : Integrable (fun y => g n y ^ 2) μ :=
      SecondMoment.integrable_of_bdd ((hgm n).pow_const 2) (B := (u n + F) ^ 2) (fun y => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hgG n y) 2)
    have hpt : ∀ y, g n y ^ 2 ≤ 2 * {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y +
        2 * F ^ 2 := fun y => by
      rw [← hsq_ind]
      have := hc0 n; have := hcF n
      simp only [hg_def]
      nlinarith [sq_nonneg ({y | f y ≤ u n}.indicator f y + c n)]
    calc ∫ y, g n y ^ 2 ∂μ ≤ ∫ y, (2 * {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y +
          2 * F ^ 2) ∂μ :=
          integral_mono hgint (((hind2_int n μ).const_mul _).add (integrable_const _)) hpt
      _ = 2 * ∫ y, {y | f y ≤ u n}.indicator (fun y => f y ^ 2) y ∂μ + 2 * F ^ 2 := by
          rw [integral_add ((hind2_int n μ).const_mul _) (integrable_const _),
            integral_const_mul, integral_const, probReal_univ, one_smul]
      _ ≤ _ := by linarith [hμ2 n]
  have hS2nn : ∀ n, 0 ≤ S2 n := fun n => integral_nonneg fun y =>
    indicator_nonneg (fun z _ => sq_nonneg _) y
  -- Step 2.
  have hii : ∃ B : ℝ, ∀ n : ℕ, n * (∫ y, g n y ^ 2 ∂ν + ∫ y, g n y ^ 2 ∂μ) / a n ^ 2 ≤ B := by
    set v : ℕ → ℝ := fun n => ((1 + 2 * aη⁻¹) * (S2 n / Real.log n) +
      (2 * T₀ ^ 2 + 2 * F ^ 2) / Real.log n) / Cc
    have hv : Tendsto v atTop (𝓝 (((1 + 2 * aη⁻¹) * Cc + 0) / Cc)) :=
      ((hS2.const_mul _).add (tendsto_const_nhds.div_atTop tendsto_log_nat)).div_const _
    refine exists_forall_le_of_eventually (K := ((1 + 2 * aη⁻¹) * Cc + 0) / Cc + 1) ?_
    filter_upwards [hv.eventually (gt_mem_nhds (lt_add_one _)), hab, hb_sq,
      eventually_one_le_log, eventually_gt_atTop 0] with n hvn hn hbn hln hn0
    refine le_trans ?_ hvn.le
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hl : 0 < Real.log n := by linarith
    rw [hn, hbn]
    simp only [v]
    rw [div_le_div_iff₀ (by positivity) hC]
    have h1 := hνg2 n
    have h2 := hμg2 n
    have h3 : 0 ≤ c n ^ 2 := sq_nonneg _
    rw [show ((1 + 2 * aη⁻¹) * (S2 n / Real.log n) + (2 * T₀ ^ 2 + 2 * F ^ 2) / Real.log n) =
      ((1 + 2 * aη⁻¹) * S2 n + (2 * T₀ ^ 2 + 2 * F ^ 2)) / Real.log n by field_simp]
    rw [div_mul_eq_mul_div, le_div_iff₀ hl]
    have : n * (∫ y, g n y ^ 2 ∂ν + ∫ y, g n y ^ 2 ∂μ) ≤
        n * ((1 + 2 * aη⁻¹) * S2 n + (2 * T₀ ^ 2 + 2 * F ^ 2)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hn'.le
    calc n * (∫ y, g n y ^ 2 ∂ν + ∫ y, g n y ^ 2 ∂μ) * Cc * Real.log n
        ≤ n * ((1 + 2 * aη⁻¹) * S2 n + (2 * T₀ ^ 2 + 2 * F ^ 2)) * Cc * Real.log n := by
          gcongr
      _ = _ := by ring
  -- Step 3.
  have hqlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 (f y - F)) := by
    have hcl : Tendsto c atTop (𝓝 F) := by
      refine tendsto_integral_of_dominated_convergence f
        (fun n => (hfm.indicator (hS n)).aestronglyMeasurable) hfi
        (fun n => ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hind0 n y)]; exact hind_le n y)
        (ae_of_all _ fun y => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(uScale_tendsto hC).eventually_ge_atTop (f y)] with n hn
      rw [indicator_of_mem (show y ∈ {y | f y ≤ u n} from hn)]
    intro y
    refine (Tendsto.sub ?_ hcl)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(uScale_tendsto hC).eventually_ge_atTop (f y)] with n hn
    rw [indicator_of_mem (show y ∈ {y | f y ≤ u n} from hn)]
  set ℓ : ℕ → ℝ := fun n => max (Real.log n) 1 with hℓ_def
  have hℓ1 : ∀ n, 1 ≤ ℓ n := fun n => le_max_right _ _
  have hℓ : Tendsto ℓ atTop atTop := tendsto_atTop_mono (fun n => le_max_left _ _) tendsto_log_nat
  have hℓlog : ∀ᶠ n in atTop, ℓ n = Real.log n :=
    eventually_one_le_log.mono fun n hn => max_eq_left hn
  obtain ⟨Kμ, hKμ⟩ : ∃ K, ∀ n, (∫ y, g n y ^ 2 ∂μ) / ℓ n ≤ K := by
    set v : ℕ → ℝ := fun n => 2 * aη⁻¹ * (S2 n / Real.log n) +
      (2 * T₀ ^ 2 + 2 * F ^ 2) / Real.log n
    have hv : Tendsto v atTop (𝓝 (2 * aη⁻¹ * Cc + 0)) :=
      (hS2.const_mul _).add (tendsto_const_nhds.div_atTop tendsto_log_nat)
    refine exists_forall_le_of_eventually (K := 2 * aη⁻¹ * Cc + 0 + 1) ?_
    filter_upwards [hv.eventually (gt_mem_nhds (lt_add_one _)), hℓlog, eventually_one_le_log]
      with n hvn hln hl1
    refine le_trans ?_ hvn.le
    rw [hln]
    have hl : 0 < Real.log n := by linarith
    simp only [v]
    rw [show 2 * aη⁻¹ * (S2 n / Real.log n) + (2 * T₀ ^ 2 + 2 * F ^ 2) / Real.log n =
      (2 * (T₀ ^ 2 + aη⁻¹ * S2 n) + 2 * F ^ 2) / Real.log n by field_simp; ring]
    exact div_le_div_of_nonneg_right (hμg2 n) hl.le
  have hcorr := correlation_series_div_tendsto C h d s μ hleft hnorm g hgm (fun n => u n + F)
    hgG hgν ℓ hℓ1 hℓ Kμ (fun n => by
      have := hKμ n; rwa [div_le_iff₀ (by linarith [hℓ1 n])] at this) (fun y => f y - F) hqlim
  have hcen : ∀ n, centered C μ d (g n) = g n := fun n => by
    funext y
    show g n y - ∫ z, g n z ∂ν = g n y
    rw [hgν n, sub_zero]
  have hiii : Tendsto (fun n : ℕ => n * asymptoticVariance C μ d (g n) / a n ^ 2) atTop
      (𝓝 1) := by
    have hc2 : Tendsto (fun n => c n ^ 2 / Real.log n) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_
        ((tendsto_const_nhds (x := F ^ 2)).div_atTop tendsto_log_nat)
      · exact div_nonneg (sq_nonneg _) (Real.log_natCast_nonneg n)
      filter_upwards [eventually_one_le_log] with n hn
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (hc0 n) (hcF n) 2)
        (zero_le_one.trans hn)
    have hcorr' : Tendsto (fun n => (∑' k, correlation C μ d (g n) k) / Real.log n) atTop
        (𝓝 0) := hcorr.congr' (hℓlog.mono fun n hn => by simp only; rw [hn])
    have h := ((hS2.sub hc2).add (hcorr'.const_mul 2)).div_const Cc
    rw [sub_zero, mul_zero, add_zero, div_self hC.ne'] at h
    refine h.congr' ?_
    filter_upwards [hab, hb_sq, eventually_one_le_log, eventually_gt_atTop 0]
      with n hn hbn hln hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hl : 0 < Real.log n := by linarith
    rw [hn, hbn, asymptoticVariance, hcen n, hνg2 n]
    field_simp
    ring
  obtain ⟨-, hY⟩ := TriangularCLT.conditional_triangular_clt C h d s hlive μ hleft hnorm g hgm
    (fun n => u n + F) hgG hgν a ha ha_lim hi hii hiii x
  rw [Real.toNNReal_one] at hY
  -- Steps 4–5: Slutsky.
  set A : ℕ → Set M := fun n => {y | u n < f y} with hA_def
  have hA : ∀ n, MeasurableSet (A n) := fun n => measurableSet_lt measurable_const hfm
  have hρA : Tendsto (fun n => ρ (A n)) atTop (𝓝 0) :=
    (tendsto_measure_gt_zero ρ hfm).comp (uScale_tendsto hC)
  have hμA : Tendsto (fun n : ℕ => (n : ℝ) * μ.real (A n)) atTop (𝓝 0) := by
    have hν := (nat_mul_tail_tendsto (ν := ν) hC htail).const_mul aη⁻¹
    rw [mul_zero] at hν
    refine squeeze_zero' (Eventually.of_forall fun n =>
      mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg) ?_ hν
    filter_upwards [(uScale_tendsto hC).eventually_ge_atTop T₀] with n hn
    have hpt : ∀ y, (A n).indicator (fun _ => (1 : ℝ)) y ≤
        aη⁻¹ * ((d.weight y).toReal * (A n).indicator (fun _ => (1 : ℝ)) y) := fun y => by
      by_cases hy : y ∈ A n
      · have hl := hlow y (lt_of_le_of_lt hn hy)
        simp only [indicator_of_mem hy, mul_one]
        rw [inv_mul_eq_div, le_div_iff₀ haη, one_mul]; exact hl
      · simp [indicator_of_notMem hy]
    have hμle : μ.real (A n) ≤ aη⁻¹ * ν.real (A n) := by
      obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d
        s.continuous_weight
      have hwint : Integrable (fun y => (d.weight y).toReal *
          (A n).indicator (fun _ => (1 : ℝ)) y) μ :=
        ((integrable_const (1 : ℝ)).indicator (hA n)).bdd_mul (c := Bη)
          d.measurable_weight.ennreal_toReal.aestronglyMeasurable (ae_of_all _ fun y => hBη y)
      rw [← integral_indicator_one (hA n), ← integral_indicator_one (hA n), hνeq,
        ← integral_const_mul]
      exact integral_mono ((integrable_const (1 : ℝ)).indicator (hA n)) (hwint.const_mul _) hpt
    calc (n : ℝ) * μ.real (A n) ≤ n * (aη⁻¹ * ν.real (A n)) :=
          mul_le_mul_of_nonneg_left hμle (Nat.cast_nonneg n)
      _ = aη⁻¹ * (n * ν.real {x | uScale Cc n < f x}) := by ring
  have hxA : ∀ᶠ n in atTop, x.val ∉ A n :=
    ((uScale_tendsto hC).eventually_ge_atTop (f x.val)).mono fun n hn hx => absurd hx (not_lt.2 hn)
  have hsumA := sum_targets_tendsto_zero C h d s hlive μ hleft hnorm x A hA hρA hμA hxA
  have htm := tail_mean_tendsto (ν := ν) hfm hf0 hC htail
  set P : ℕ → Measure (Path M) := fun n =>
    (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)) with hP_def
  have hPc : ∀ n, P n = C.conditionedMeasure x.val n := fun n => rfl
  refine tendstoInDistribution_of_varying_probability_approximation P (gaussianReal 0 1)
    _ (fun n ω => (a n)⁻¹ * pathBirkhoffSum (g n) n ω) id
    (fun n => ((measurable_pathBirkhoffSum hfm n).sub_const _).const_mul _)
    (fun n => (measurable_pathBirkhoffSum (hgm n) n).const_mul _) hY (fun ε hε => ?_)
  have hsplitT : ∀ n, ∫ y, (A n).indicator f y ∂ν = F - c n := fun n => by
    rw [eq_sub_iff_add_eq, ← integral_add (hfi.indicator (hA n)) (hfi.indicator (hS n))]
    congr 1; funext y
    by_cases hy : f y ≤ u n
    · simp [hA_def, indicator, hy, not_lt.2 hy]
    · simp [hA_def, indicator, hy, lt_of_not_ge hy]
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hsumA
  filter_upwards [hab, htm.eventually (gt_mem_nhds hε),
    (bScale_tendsto hC).eventually_gt_atTop 0] with n hn htn hbn
  rw [hPc n]
  have : IsProbabilityMeasure (C.conditionedMeasure x.val n) :=
    C.conditionedMeasure_isProbability_of_surviving x.val
      (d.liveSet_subset_survivingSet x.property) n
  set T := ⋃ i ∈ Finset.range n, {omega : Path M | omega i ∈ Option.some '' A n} with hT_def
  have hN : C.conditionedMeasure x.val n {ω | ω ∉ survival n} = 0 :=
    ae_iff.1 (C.ae_survival_conditionedMeasure x.val n)
  have hsub : {ω | ε < |(b n)⁻¹ * (pathBirkhoffSum f n ω - n * F) -
      (a n)⁻¹ * pathBirkhoffSum (g n) n ω|} ⊆ T ∪ {ω | ω ∉ survival n} := by
    intro ω hω
    by_cases hsurv : ω ∈ survival n
    · left
      by_contra hnot
      have havoid : ∀ i < n, ∀ y, ω i = some y → f y ≤ u n := by
        intro i hi y hy
        by_contra hfy
        exact hnot (mem_biUnion (Finset.mem_range.2 hi) ⟨y, lt_of_not_ge hfy, hy.symm⟩)
      have hsumg : pathBirkhoffSum (g n) n ω = pathBirkhoffSum f n ω - n * c n := by
        rw [show g n = fun z => {y | f y ≤ u n}.indicator f z - c n from rfl,
          SmallJumpMoment.pathBirkhoffSum_sub_const _ _ hsurv]
        congr 1
        unfold pathBirkhoffSum birkhoffSum
        refine Finset.sum_congr rfl fun i hi => ?_
        obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hsurv i (Finset.mem_range.1 hi).le)
        show zeroExtension _ (ω i) = zeroExtension f (ω i)
        rw [hy, zeroExtension_some, zeroExtension_some,
          indicator_of_mem (show y ∈ {y | f y ≤ u n} from havoid i (Finset.mem_range.1 hi) y hy)]
      have hdiff : (b n)⁻¹ * (pathBirkhoffSum f n ω - n * F) -
          (a n)⁻¹ * pathBirkhoffSum (g n) n ω = -((n : ℝ) / b n * ∫ y, (A n).indicator f y ∂ν) := by
        rw [hsumg, hn, hsplitT n]
        field_simp
        ring
      have hT0 : 0 ≤ (n : ℝ) / b n * ∫ y, (A n).indicator f y ∂ν :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg n) hbn.le)
          (integral_nonneg fun y => indicator_nonneg (fun z _ => hf0 z) y)
      have hω' : ε < |(b n)⁻¹ * (pathBirkhoffSum f n ω - n * F) -
          (a n)⁻¹ * pathBirkhoffSum (g n) n ω| := hω
      rw [hdiff, abs_neg, abs_of_nonneg hT0] at hω'
      exact absurd htn (not_lt.2 hω'.le)
    · right; exact hsurv
  calc (C.conditionedMeasure x.val n).real {ω | ε < |(b n)⁻¹ * (pathBirkhoffSum f n ω - n * F) -
        (a n)⁻¹ * pathBirkhoffSum (g n) n ω|}
      ≤ (C.conditionedMeasure x.val n).real (T ∪ {ω | ω ∉ survival n}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (C.conditionedMeasure x.val n).real T +
        (C.conditionedMeasure x.val n).real {ω | ω ∉ survival n} := measureReal_union_le _ _
    _ = (C.conditionedMeasure x.val n).real T := by
        rw [show (C.conditionedMeasure x.val n).real {ω | ω ∉ survival n} = 0 by
          rw [measureReal_def, hN, ENNReal.toReal_zero], add_zero]
    _ ≤ ∑ i ∈ Finset.range n, (C.conditionedMeasure x.val n).real
        {omega | omega i ∈ Option.some '' A n} := measureReal_biUnion_finset_le _ _

end Chain

end

end ConditionedStableLaws.GaussianBoundary
