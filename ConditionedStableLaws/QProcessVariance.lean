import ConditionedStableLaws.RefinedLLN
import ConditionedStableLaws.MarkovPairs
import ConditionedStableLaws.L2Compactness

/-!
# Exponential decay of Q-process correlations and the Q-process LLN

For a bounded measurable observable `h` and every `x ∈ M \ Z`,

* `|E^ℚₓ[h̄(Xᵢ) h̄(Xⱼ)]| ≤ Cₓ ϑ^{j-i}` with `h̄ = h - ν(h)`, from the Doob formula and a pointwise
  exponential bound for `λ⁻ᵐ ∫ F dKᵐ(z)` when `μ(F) = 0`;
* `E^ℚₓ[(Γₙ - ν(h))²] = O(1/n)`, hence `Γₙ → ν(h)` in `ℚₓ`-probability.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.QProcessVariance

noncomputable section

open StandingHypothesis RefinedLLN

/-! ### The Doob kernel against signed functions -/

section Doob

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} [IsSFiniteKernel K]
  (d : DoobTransform.EigenData K)

/-- `∫ F dℚⁱ(x) = λ⁻ⁱ η(x)⁻¹ ∫ η F dKⁱ(x)` for every measurable real `F`. -/
theorem integral_doob_pow (i : ℕ) (x : d.State) {F : M → ℝ} :
    ∫ y, F y.val ∂(d.kernel ^ i) x =
      (d.rate.toReal)⁻¹ ^ i * ((d.weight x.val).toReal)⁻¹ *
        ∫ y, (d.weight y).toReal * F y ∂(K ^ i) x.val := by
  rw [doob_kernel_pow_eq, integral_smul_measure, integral_live d ((K ^ i) x.val) F,
    integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]

end Doob

/-! ### Pointwise exponential bound -/

section Mixing

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem kernelIterate_eq_integral (c : ℝ) (m : ℕ) {F : M → ℝ} (hF : Measurable F)
    {B : ℝ} (hB : ∀ y, |F y| ≤ B) (x : M) :
    kernelIterate c K m F x = c ^ m * ∫ y, F y ∂(K.kernel ^ m) x := by
  induction m generalizing x with
  | zero =>
      simp only [kernelIterate, pow_zero, one_mul]
      change F x = ∫ y, F y ∂(Kernel.id x)
      rw [Kernel.id_apply, integral_dirac' _ _ hF.stronglyMeasurable]
  | succ m ih =>
      have := killedKernel_power_isFinite K m
      simp only [kernelIterate, ih]
      rw [integral_const_mul (c ^ m) (fun y => ∫ z, F z ∂(K.kernel ^ m) y), pow_succ', mul_assoc]
      congr 1
      rw [pow_succ]
      congr 1
      refine (Kernel.integral_comp (η := K.kernel ^ m) (κ := K.kernel) (a := x) (f := F) ?_).symm
      refine Integrable.of_bound hF.aestronglyMeasurable B (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      exact hB y

/-- **Pointwise exponential decay.** There are `A ≥ 0` and `θ ∈ [0,1)` with
`|λ⁻⁽ᵏ⁺¹⁾ ∫ F dKᵏ⁺¹(z)| ≤ A θᵏ sup|F|` for every bounded measurable `F` with
`μ(F) = 0`, every `k` and every `z ∈ M`. -/
theorem _root_.ConditionedStableLaws.StandingHypothesis.HypothesisH.exists_pointwise_decay (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    ∃ A θ : ℝ, 0 ≤ A ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ (F : M → ℝ), Measurable F → ∀ B : ℝ,
      (∀ y, |F y| ≤ B) → ∫ y, F y ∂μ = 0 → ∀ (k : ℕ) (z : M),
        |(d.rate.toReal)⁻¹ ^ (k + 1) * ∫ y, F y ∂(K.kernel ^ (k + 1)) z| ≤ A * θ ^ k * B := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  obtain ⟨s, hs⟩ := h.exists_survivalGapData_with_mean d hc μ hleft hnorm
  have hμρ : μ ≪ ρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  set r := d.rate.toReal
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  set T : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := r⁻¹ • h.transitionOperator
  refine ⟨r⁻¹ * max s.constant 1, s.decay,
    mul_nonneg (inv_nonneg.2 hr.le) (le_max_of_le_right zero_le_one), s.decay_nonneg,
    s.decay_lt_one, fun F hF B hB hF0 k z => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB z)
  have hmem : MemLp F ∞ ρ := memLp_top_of_bound hF.aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  set Fρ := hmem.toLp F
  have hFρ : ‖Fρ‖ ≤ B := by
    refine (Lp.norm_le_of_ae_bound (f := Fρ) (C := B) hB0 ?_).trans_eq (by simp)
    filter_upwards [hmem.coeFn_toLp] with y hy
    rw [hy, Real.norm_eq_abs]
    exact hB y
  -- Point evaluation after one step is a contraction up to `λ⁻¹`.
  have heval (v : Lp ℝ ∞ ρ) : |h.stepEvaluation r⁻¹ z v| ≤ r⁻¹ * ‖v‖ := by
    rw [h.stepEvaluation_apply, abs_mul, abs_of_nonneg (inv_nonneg.2 hr.le)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hr.le)
    have hb := (h.absolutelyContinuous z).ae_le (lp_infinity_ae_norm_le v)
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le_const hb).trans ?_
    have hm : (K.kernel z).real univ ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact K.mass_le_one z)
    nlinarith [norm_nonneg v, measureReal_nonneg (μ := K.kernel z) (s := univ)]
  -- Identify the iterate with point evaluation of the operator power.
  have hiter : r⁻¹ ^ (k + 1) * ∫ y, F y ∂(K.kernel ^ (k + 1)) z =
      h.stepEvaluation r⁻¹ z ((T ^ k) Fρ) := by
    rw [← kernelIterate_eq_integral r⁻¹ (k + 1) hF hB z,
      h.kernelIterate_succ_congr r⁻¹ k hmem.coeFn_toLp.symm z, ← h.stepEvaluation_power]
  rw [hiter]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_apply_eq_self, mul_one]
    calc |h.stepEvaluation r⁻¹ z Fρ| ≤ r⁻¹ * ‖Fρ‖ := heval Fρ
      _ ≤ r⁻¹ * max s.constant 1 * B := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (hFρ.trans (le_mul_of_one_le_left hB0 (le_max_right _ _))) (inv_nonneg.2 hr.le)
  · -- The projection annihilates `Fρ`.
    have hPi : ConditionalMixing.rankOne s.mean s.eigenvector Fρ = 0 := by
      simp only [ConditionalMixing.rankOne, ContinuousLinearMap.smulRight_apply, hs]
      rw [integral_congr_ae (hμρ.ae_eq hmem.coeFn_toLp), hF0, zero_smul]
    have hdec : (T ^ k) Fρ = ((T ^ k) - ConditionalMixing.rankOne s.mean s.eigenvector) Fρ := by
      rw [sub_apply, hPi, sub_zero]
    rw [hdec]
    calc |h.stepEvaluation r⁻¹ z (((T ^ k) - ConditionalMixing.rankOne s.mean s.eigenvector) Fρ)|
        ≤ r⁻¹ * ‖((T ^ k) - ConditionalMixing.rankOne s.mean s.eigenvector) Fρ‖ := heval _
      _ ≤ r⁻¹ * (s.constant * s.decay ^ k * B) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hr.le)
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          exact mul_le_mul (s.gap k hk) hFρ (norm_nonneg _)
            (mul_nonneg s.constant_nonneg (pow_nonneg s.decay_nonneg _))
      _ ≤ r⁻¹ * (max s.constant 1 * s.decay ^ k * B) := by
          gcongr
          · exact pow_nonneg s.decay_nonneg _
          · exact le_max_left _ _
      _ = r⁻¹ * max s.constant 1 * s.decay ^ k * B := by ring

end Mixing

/-! ### Correlations of the Q-process -/

section Correlation

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- **Q-process correlation bound.** For a bounded measurable `H₀` with `ν(H₀) = 0` and `x ∈ M \ Z`,
`|E^ℚₓ[H₀(Xᵢ) H₀(Xᵢ₊ₘ)]| ≤ D θᵐ` for `m ≥ 1`. -/
theorem _root_.ConditionedStableLaws.StandingHypothesis.HypothesisH.qProcess_correlation (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {H₀ : M → ℝ} (hH : Measurable H₀) {B : ℝ} (hB : ∀ y, |H₀ y| ≤ B)
    (hcent : ∫ y, (d.weight y).toReal * H₀ y ∂μ = 0) (x : d.State) :
    ∃ D θ : ℝ, 0 ≤ D ∧ 0 < θ ∧ θ < 1 ∧ ∀ i m : ℕ, 1 ≤ m →
      |∫ ω, H₀ (ω i).val * H₀ (ω (i + m)).val ∂QProcessLimit.pathMeasure d.kernel x| ≤
        D * θ ^ m := by
  obtain ⟨A, θ, hA, hθ0, hθ1, hdecay⟩ := h.exists_pointwise_decay d hc μ hleft hnorm
  obtain ⟨s, -⟩ := h.exists_survivalGapData_with_mean d hc μ hleft hnorm
  obtain ⟨Bη, hBη⟩ : ∃ C : ℝ, ∀ y, (d.weight y).toReal ≤ C := by
    let f : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨_, s.continuous_weight_toReal⟩
    exact ⟨‖f‖, fun y => (le_abs_self _).trans (f.norm_coe_le_norm y)⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x.val)
  have hBη0 : 0 ≤ Bη := ENNReal.toReal_nonneg.trans (hBη x.val)
  set r := d.rate.toReal
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  set ηx := (d.weight x.val).toReal
  have hηx : 0 < ηx := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  set θ' := (1 + θ) / 2
  have hθ'0 : 0 < θ' := by simp only [θ']; linarith
  have hθ'1 : θ' < 1 := by simp only [θ']; linarith
  have hθθ' : θ ≤ θ' := by simp only [θ']; linarith
  set Bs := s.survivalBound
  refine ⟨ηx⁻¹ * Bs * B * (A * (Bη * B)) / θ', θ', by
    have := s.survivalBound_nonneg; positivity, hθ'0, hθ'1, fun i m hm => ?_⟩
  -- The centred observable weighted by `η`.
  set F : M → ℝ := fun z => (d.weight z).toReal * H₀ z
  have hFm : Measurable F := d.measurable_weight.ennreal_toReal.mul hH
  have hFb (z : M) : |F z| ≤ Bη * B := by
    simp only [F, abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg : 0 ≤ (d.weight z).toReal)]
    exact mul_le_mul (hBη z) (hB z) (abs_nonneg _) hBη0
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  set ψ : M → ℝ := fun z => r⁻¹ ^ (k + 1) * ∫ y, F y ∂(K.kernel ^ (k + 1)) z
  have hψm : Measurable ψ := measurable_const.mul
    (hFm.stronglyMeasurable.integral_kernel (κ := K.kernel ^ (k + 1))).measurable
  have hψb (z : M) : |ψ z| ≤ A * θ ^ k * (Bη * B) := hdecay F hFm _ hFb hcent k z
  -- The inner integral against `ℚᵏ⁺¹`.
  set G : M → ℝ := fun z => H₀ z * (((d.weight z).toReal)⁻¹ * ψ z)
  have hinner (y : d.State) : ∫ z, H₀ z.val ∂(d.kernel ^ (k + 1)) y =
      ((d.weight y.val).toReal)⁻¹ * ψ y.val := by
    rw [integral_doob_pow]
    simp only [ψ, F]
    ring
  have hGm : Measurable G := hH.mul (d.measurable_weight.ennreal_toReal.inv.mul hψm)
  have hinnerb (y : d.State) : |∫ z, H₀ z.val ∂(d.kernel ^ (k + 1)) y| ≤
      ((d.weight y.val).toReal)⁻¹ * (A * θ ^ k * (Bη * B)) := by
    rw [hinner, abs_mul, abs_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)]
    exact mul_le_mul_of_nonneg_left (hψb _) (inv_nonneg.2 ENNReal.toReal_nonneg)
  -- Two-time law, then the Doob formula for the outer integral.
  have hpair := MarkovPairs.integral_pair d.kernel x i (k + 1)
    (a := fun y : d.State => H₀ y.val) (b := fun y : d.State => H₀ y.val)
    (hH.comp measurable_subtype_coe) (hH.comp measurable_subtype_coe)
    (fun y => hB y.val) (fun y => hB y.val)
  have houter : ∫ y, H₀ y.val * ∫ z, H₀ z.val ∂(d.kernel ^ (k + 1)) y ∂(d.kernel ^ i) x =
      r⁻¹ ^ i * ηx⁻¹ * ∫ z, (d.weight z).toReal * G z ∂(K.kernel ^ i) x.val := by
    rw [← integral_doob_pow d i x (F := G)]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by simp only [G, hinner]
  rw [hpair, houter]
  have hwG (z : M) : |(d.weight z).toReal * G z| ≤ B * (A * θ ^ k * (Bη * B)) := by
    simp only [G]
    by_cases hz : (d.weight z).toReal = 0
    · rw [hz, zero_mul, abs_zero]
      have := hψb z
      have := abs_nonneg (ψ z)
      positivity
    · rw [show (d.weight z).toReal * (H₀ z * (((d.weight z).toReal)⁻¹ * ψ z)) = H₀ z * ψ z by
        field_simp]
      rw [abs_mul]
      exact mul_le_mul (hB z) (hψb z) (abs_nonneg _) hB0
  have := killedKernel_power_isFinite K i
  have hint := norm_integral_le_of_norm_le_const (μ := (K.kernel ^ i) x.val)
    (C := B * (A * θ ^ k * (Bη * B)))
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hwG z)
  have hsurv := s.normalized_survival_real_le i x.val
  rw [normalized_survival_toReal] at hsurv
  have hmass : 0 ≤ ((K.kernel ^ i) x.val).real univ := measureReal_nonneg
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.2 hr.le) _),
    abs_of_nonneg (inv_nonneg.2 hηx.le)]
  rw [Real.norm_eq_abs] at hint
  have hθk : θ ^ k ≤ θ' ^ (k + 1) / θ' := by
    rw [pow_succ, mul_div_assoc, div_self hθ'0.ne', mul_one]
    exact pow_le_pow_left₀ hθ0 hθθ' k
  have hC0 : 0 ≤ B * (A * θ ^ k * (Bη * B)) := by positivity
  calc r⁻¹ ^ i * ηx⁻¹ * |∫ z, (d.weight z).toReal * G z ∂(K.kernel ^ i) x.val|
      ≤ r⁻¹ ^ i * ηx⁻¹ * (B * (A * θ ^ k * (Bη * B)) * ((K.kernel ^ i) x.val).real univ) := by
        gcongr
    _ = ηx⁻¹ * (r⁻¹ ^ i * ((K.kernel ^ i) x.val).real univ) * B * (A * (Bη * B)) * θ ^ k := by
        ring
    _ ≤ ηx⁻¹ * Bs * B * (A * (Bη * B)) * (θ' ^ (k + 1) / θ') := by
        have := s.survivalBound_nonneg
        gcongr
    _ = ηx⁻¹ * Bs * B * (A * (Bη * B)) / θ' * θ' ^ (k + 1) := by ring

end Correlation

/-! ### Second moments and the Q-process law of large numbers -/

section QLLN

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Variance bound from summable correlations: `E[(∑_{i<n} φ(Xᵢ))²] ≤ n V`. -/
theorem sq_sum_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : ℕ → Ω → ℝ) (hφ : ∀ i, Measurable (φ i)) {B D θ : ℝ} (hB : ∀ i ω, |φ i ω| ≤ B)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hD : 0 ≤ D)
    (hcor : ∀ j m, 1 ≤ m → |∫ ω, φ j ω * φ (j + m) ω ∂P| ≤ D * θ ^ m) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, φ i ω) ^ 2 ∂P ≤ n * (B ^ 2 + 2 * D * (1 - θ)⁻¹) := by
  have hbdd (i : ℕ) : ∀ ω, ‖φ i ω‖ ≤ B := fun ω => by rw [Real.norm_eq_abs]; exact hB i ω
  have hint (i : ℕ) : Integrable (φ i) P :=
    Integrable.of_bound (hφ i).aestronglyMeasurable B (Eventually.of_forall (hbdd i))
  have hSm (n : ℕ) : Measurable (fun ω => ∑ i ∈ Finset.range n, φ i ω) :=
    Finset.measurable_sum _ fun i _ => hφ i
  have hSb (n : ℕ) (ω : Ω) : ‖∑ i ∈ Finset.range n, φ i ω‖ ≤ n * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range n, ‖φ i ω‖ ≤ ∑ _i ∈ Finset.range n, B :=
          Finset.sum_le_sum fun i _ => hbdd i ω
      _ = n * B := by simp
  have hSint (n : ℕ) : Integrable (fun ω => ∑ i ∈ Finset.range n, φ i ω) P :=
    Integrable.of_bound (hSm n).aestronglyMeasurable _ (Eventually.of_forall (hSb n))
  have hgeo (n : ℕ) : ∑ j ∈ Finset.range n, θ ^ (n - j) ≤ (1 - θ)⁻¹ := by
    calc ∑ j ∈ Finset.range n, θ ^ (n - j) ≤ ∑ j ∈ Finset.range n, θ ^ (n - 1 - j) := by
          apply Finset.sum_le_sum
          intro j hj
          exact pow_le_pow_of_le_one hθ0 hθ1.le (by have := Finset.mem_range.1 hj; omega)
      _ = ∑ j ∈ Finset.range n, θ ^ j := Finset.sum_range_reflect (fun j => θ ^ j) n
      _ ≤ (1 - θ)⁻¹ := by
          rw [← tsum_geometric_of_lt_one hθ0 hθ1]
          exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hθ0 j)
            (summable_geometric_of_lt_one hθ0 hθ1)
  induction n with
  | zero => simp
  | succ n ih =>
      set S := fun ω => ∑ i ∈ Finset.range n, φ i ω
      have hexp : (fun ω => (∑ i ∈ Finset.range (n + 1), φ i ω) ^ 2) =
          fun ω => S ω ^ 2 + (2 * (S ω * φ n ω) + φ n ω ^ 2) := by
        funext ω
        rw [Finset.sum_range_succ]
        ring
      have hS2 : Integrable (fun ω => S ω ^ 2) P := by
        simpa [pow_two] using (hSint n).mul_bdd (hSm n).aestronglyMeasurable
          (Eventually.of_forall (hSb n))
      have hSφ : Integrable (fun ω => S ω * φ n ω) P :=
        (hSint n).mul_bdd (hφ n).aestronglyMeasurable (Eventually.of_forall (hbdd n))
      have hφ2 : Integrable (fun ω => φ n ω ^ 2) P := by
        simpa [pow_two] using (hint n).mul_bdd (hφ n).aestronglyMeasurable
          (Eventually.of_forall (hbdd n))
      have h2 : Integrable (fun ω => 2 * (S ω * φ n ω)) P := hSφ.const_mul 2
      have h3 : Integrable (fun ω => 2 * (S ω * φ n ω) + φ n ω ^ 2) P := h2.add hφ2
      rw [hexp, integral_add hS2 h3, integral_add h2 hφ2, integral_const_mul]
      have hcross : ∫ ω, S ω * φ n ω ∂P ≤ D * (1 - θ)⁻¹ := by
        have heq : ∫ ω, S ω * φ n ω ∂P = ∑ j ∈ Finset.range n, ∫ ω, φ j ω * φ n ω ∂P := by
          simp only [S, Finset.sum_mul]
          exact MeasureTheory.integral_finsetSum _ fun j _ =>
            (hint j).mul_bdd (hφ n).aestronglyMeasurable (Eventually.of_forall (hbdd n))
        rw [heq]
        calc ∑ j ∈ Finset.range n, ∫ ω, φ j ω * φ n ω ∂P
            ≤ ∑ j ∈ Finset.range n, D * θ ^ (n - j) := by
              apply Finset.sum_le_sum
              intro j hj
              have hjn := Finset.mem_range.1 hj
              have h1 := hcor j (n - j) (by omega)
              rw [Nat.add_sub_cancel' hjn.le] at h1
              exact (le_abs_self _).trans h1
          _ = D * ∑ j ∈ Finset.range n, θ ^ (n - j) := by rw [Finset.mul_sum]
          _ ≤ D * (1 - θ)⁻¹ := mul_le_mul_of_nonneg_left (hgeo n) hD
      have hdiag : ∫ ω, φ n ω ^ 2 ∂P ≤ B ^ 2 := by
        have := norm_integral_le_of_norm_le_const (μ := P) (C := B ^ 2)
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hB n ω) 2)
        simp only [probReal_univ, mul_one] at this
        exact (le_abs_self _).trans (by rwa [← Real.norm_eq_abs])
      push_cast
      nlinarith [ih, hcross, hdiag]

/-- **Q-process law of large numbers for bounded observables**: for every `x ∈ M \ Z`, `Γₙ → ν(h)`
in `ℚₓ`-probability. -/
theorem _root_.ConditionedStableLaws.StandingHypothesis.HypothesisH.qProcess_lln
    (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {f : M → ℝ} (hf : Measurable f) {B : ℝ} (hfb : ∀ y, |f y| ≤ B) (x : d.State) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => QProcessLimit.pathMeasure d.kernel x
      {ω | ε < |Cited.doobAverage d f n ω - ∫ y, f y ∂μ.withDensity d.weight|}) atTop (𝓝 0) := by
  intro ε hε
  set Γ := ∫ y, f y ∂μ.withDensity d.weight
  set H₀ : M → ℝ := fun y => f y - Γ
  have hH : Measurable H₀ := hf.sub measurable_const
  have hHb (y : M) : |H₀ y| ≤ B + |Γ| := (abs_sub _ _).trans (add_le_add (hfb y) le_rfl)
  obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound d hc
  have hwint : Integrable (fun y => (d.weight y).toReal) μ :=
    Integrable.of_bound d.measurable_weight.ennreal_toReal.aestronglyMeasurable Bη
      (Eventually.of_forall hBη)
  have hwf : Integrable (fun y => (d.weight y).toReal * f y) μ :=
    hwint.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hfb y)
  have hcent : ∫ y, (d.weight y).toReal * H₀ y ∂μ = 0 := by
    have h1 : ∫ y, (d.weight y).toReal * f y ∂μ = Γ := by
      simp only [Γ]
      rw [integral_withDensity_eq_integral_toReal_smul d.measurable_weight
        (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
      rfl
    have h2 : ∫ y, (d.weight y).toReal ∂μ = 1 := L2Compactness.integral_eta d μ hnorm
    simp only [H₀, mul_sub]
    rw [integral_sub hwf (hwint.mul_const Γ), integral_mul_const, h1, h2, one_mul, sub_self]
  obtain ⟨D, θ, hD, hθ0, hθ1, hcor⟩ := h.qProcess_correlation d hc μ hleft hnorm hH hHb hcent x
  set P := QProcessLimit.pathMeasure d.kernel x
  set φ : ℕ → (ℕ → d.State) → ℝ := fun i ω => H₀ (ω i).val
  have hφ (i : ℕ) : Measurable (φ i) := hH.comp (measurable_subtype_coe.comp (measurable_pi_apply i))
  set V := (B + |Γ|) ^ 2 + 2 * D * (1 - θ)⁻¹
  have hvar (n : ℕ) := sq_sum_le P φ hφ (fun i ω => hHb _) hθ0.le hθ1 hD (fun j m hm => hcor j m hm) n
  have hV : 0 ≤ V := by
    have := inv_nonneg.2 (sub_nonneg.2 hθ1.le)
    positivity
  -- Chebyshev.
  have hcheb : ∀ n : ℕ, 1 ≤ n → P.real {ω | ε < |Cited.doobAverage d f n ω - Γ|} ≤
      V / (ε ^ 2 * n) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hrel (ω : ℕ → d.State) : Cited.doobAverage d f n ω - Γ =
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, φ i ω := by
      simp only [Cited.doobAverage, φ, H₀, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      field_simp
    have hsub : {ω | ε < |Cited.doobAverage d f n ω - Γ|} ⊆
        {ω | (ε * n) ^ 2 ≤ (∑ i ∈ Finset.range n, φ i ω) ^ 2} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, hrel, abs_mul, abs_inv, Nat.abs_cast] at hω ⊢
      rw [inv_mul_eq_div, lt_div_iff₀ hn'] at hω
      rw [← sq_abs (∑ i ∈ Finset.range n, φ i ω)]
      exact pow_le_pow_left₀ (by positivity) hω.le 2
    have hSint : Integrable (fun ω => (∑ i ∈ Finset.range n, φ i ω) ^ 2) P := by
      refine Integrable.of_bound ((Finset.measurable_sum _ fun i _ => hφ i).pow_const 2).aestronglyMeasurable
        ((n * (B + |Γ|)) ^ 2) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_pow]
      apply pow_le_pow_left₀ (abs_nonneg _)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range n, |φ i ω| ≤ ∑ _i ∈ Finset.range n, (B + |Γ|) :=
            Finset.sum_le_sum fun i _ => hHb _
        _ = n * (B + |Γ|) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
      hSint ((ε * n) ^ 2)
    have hpos : 0 < (ε * n) ^ 2 := by positivity
    calc P.real {ω | ε < |Cited.doobAverage d f n ω - Γ|}
        ≤ P.real {ω | (ε * n) ^ 2 ≤ (∑ i ∈ Finset.range n, φ i ω) ^ 2} :=
          measureReal_mono hsub
      _ ≤ (∫ ω, (∑ i ∈ Finset.range n, φ i ω) ^ 2 ∂P) / (ε * n) ^ 2 := by
          rw [le_div_iff₀ hpos, mul_comm]; exact hmk
      _ ≤ (n * V) / (ε * n) ^ 2 := by gcongr; exact hvar n
      _ = V / (ε ^ 2 * n) := by field_simp
  have hlim : Tendsto (fun n : ℕ => V / (ε ^ 2 * n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (V / ε ^ 2))
    refine this.congr fun n => ?_
    rw [div_div]
  have hreal : Tendsto (fun n : ℕ => P.real {ω | ε < |Cited.doobAverage d f n ω - Γ|})
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => measureReal_nonneg) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hcheb n hn
  rw [← ENNReal.toReal_zero] at hreal
  exact (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) ENNReal.zero_ne_top).1 hreal

end QLLN

end

end ConditionedStableLaws.QProcessVariance
