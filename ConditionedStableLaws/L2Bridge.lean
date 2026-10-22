import ConditionedStableLaws.ConditionalCLTBounded

/-!
# `L²(μ)` estimates for the `L∞(ρ)` transition operator

The embedding `J : L∞(ρ) → L²(μ)` (`μ ≪ ρ`), the bounds `‖J(T₀ f)‖ ≤ C_op ‖J f‖` and `‖J(T₀ᵐ f)‖ ≤ L
κᵐ ‖J f‖` on `ker μ`, Cauchy–Schwarz, and the inverse bound `‖J y‖ ≤ C_inv ‖J (y - T₀ y)‖` on `ker
μ`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.L2Bridge

noncomputable section

open StandingHypothesis CanonicalChain TwistedOperators

/-! ### The abstract inverse bound -/

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem iterate_identity (T₀ : E →L[ℝ] E) {y z : E} (hyz : y - T₀ y = z) (N : ℕ) :
    y = ∑ k ∈ Finset.range N, (T₀ ^ k) z + (T₀ ^ N) y := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hy : y = z + T₀ y := by rw [← hyz]; abel
    rw [Finset.sum_range_succ, pow_succ, mul_apply_eq_comp]
    conv_lhs => rw [ih]
    nth_rewrite 1 [hy]
    rw [map_add]
    abel

/-- `‖J y‖ ≤ (1+L)/(1-κ) ‖J(y - T₀ y)‖` for `ℓ y = 0`. -/
theorem inverse_bound (T₀ : E →L[ℝ] E) (ℓ : E →L[ℝ] ℝ) (J : E →L[ℝ] F)
    (hℓT : ∀ w, ℓ (T₀ w) = ℓ w) {L κ : ℝ} (hL : 0 ≤ L) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hdec : ∀ f, ℓ f = 0 → ∀ m : ℕ, 1 ≤ m → ‖J ((T₀ ^ m) f)‖ ≤ L * κ ^ m * ‖J f‖)
    {y z : E} (hy : ℓ y = 0) (hyz : y - T₀ y = z) :
    ‖J y‖ ≤ (1 + L) / (1 - κ) * ‖J z‖ := by
  have hz : ℓ z = 0 := by rw [← hyz, map_sub, hℓT, hy, sub_zero]
  have hk : ∀ k : ℕ, ‖J ((T₀ ^ k) z)‖ ≤ (1 + L) * κ ^ k * ‖J z‖ := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [pow_zero, one_apply_eq_self, mul_one]
      nlinarith [norm_nonneg (J z)]
    · exact (hdec z hz k hk).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hκ0 k)) (norm_nonneg _))
  have hNb : ∀ N : ℕ, 1 ≤ N → ‖J y‖ ≤ (1 + L) / (1 - κ) * ‖J z‖ + L * κ ^ N * ‖J y‖ := by
    intro N hN1
    have hid := iterate_identity T₀ hyz N
    have h1 : ‖J y‖ ≤ ∑ k ∈ Finset.range N, ‖J ((T₀ ^ k) z)‖ + ‖J ((T₀ ^ N) y)‖ := by
      conv_lhs => rw [hid]
      rw [map_add, map_sum]
      exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    have h2 : ∑ k ∈ Finset.range N, ‖J ((T₀ ^ k) z)‖ ≤ (1 + L) / (1 - κ) * ‖J z‖ := by
      calc ∑ k ∈ Finset.range N, ‖J ((T₀ ^ k) z)‖
          ≤ ∑ k ∈ Finset.range N, (1 + L) * κ ^ k * ‖J z‖ := Finset.sum_le_sum fun k _ => hk k
        _ = (1 + L) * ‖J z‖ * ∑ k ∈ Finset.range N, κ ^ k := by
            rw [Finset.mul_sum]; congr 1; funext k; ring
        _ ≤ (1 + L) * ‖J z‖ * (1 - κ)⁻¹ :=
            mul_le_mul_of_nonneg_left (SecondMoment.geom_le hκ0 hκ1 N) (by positivity)
        _ = (1 + L) / (1 - κ) * ‖J z‖ := by ring
    linarith [hdec y hy N hN1]
  have ht : Tendsto (fun N : ℕ => (1 + L) / (1 - κ) * ‖J z‖ + L * κ ^ N * ‖J y‖) atTop
      (𝓝 ((1 + L) / (1 - κ) * ‖J z‖)) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul L).mul_const ‖J y‖
    simpa using (tendsto_const_nhds (x := (1 + L) / (1 - κ) * ‖J z‖)).add this
  exact ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun N hN => hNb N hN⟩)

end Abstract

/-! ### The concrete bridge -/

section Concrete

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem memLp_two_of_linfty [IsFiniteMeasure ρ] {μ : Measure M} [IsFiniteMeasure μ]
    (hμρ : μ ≪ ρ) (f : Lp ℝ ∞ ρ) : MemLp (f : M → ℝ) 2 μ :=
  (memLp_top_of_bound ((Lp.aestronglyMeasurable f).mono_ac hμρ) ‖f‖
    (hμρ.ae_le (ae_norm_le f))).mono_exponent le_top

/-- The embedding `L∞(ρ) → L²(μ)`. -/
def embed [IsFiniteMeasure ρ] (μ : Measure M) [IsProbabilityMeasure μ] (hμρ : μ ≪ ρ) :
    Lp ℝ ∞ ρ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_two_of_linfty hμρ f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_two_of_linfty hμρ (f + g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_two_of_linfty hμρ f).toLp _) ((memLp_two_of_linfty hμρ g).toLp _),
          (memLp_two_of_linfty hμρ f).coeFn_toLp, (memLp_two_of_linfty hμρ g).coeFn_toLp,
          hμρ.ae_le (Lp.coeFn_add f g)] with y h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
      map_smul' := fun a f => by
        apply Lp.ext
        filter_upwards [(memLp_two_of_linfty hμρ (a • f)).coeFn_toLp,
          Lp.coeFn_smul a ((memLp_two_of_linfty hμρ f).toLp _),
          (memLp_two_of_linfty hμρ f).coeFn_toLp, hμρ.ae_le (Lp.coeFn_smul a f)]
          with y h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply] }
    1 (fun f => by
      rw [one_mul]
      refine (Lp.norm_le_of_ae_bound (norm_nonneg f) ?_).trans_eq (by simp [measureUnivNNReal])
      filter_upwards [(memLp_two_of_linfty hμρ f).coeFn_toLp, hμρ.ae_le (ae_norm_le f)]
        with y h1 h2
      change ‖((memLp_two_of_linfty hμρ f).toLp _ : M → ℝ) y‖ ≤ _
      rw [h1]; exact h2)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem embed_ae [IsFiniteMeasure ρ] {μ : Measure M} [IsProbabilityMeasure μ] (hμρ : μ ≪ ρ)
    (f : Lp ℝ ∞ ρ) : (embed μ hμρ f : M → ℝ) =ᵐ[μ] f :=
  (memLp_two_of_linfty hμρ f).coeFn_toLp

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem norm_embed_le [IsFiniteMeasure ρ] {μ : Measure M} [IsProbabilityMeasure μ]
    (hμρ : μ ≪ ρ) (f : Lp ℝ ∞ ρ) : ‖embed μ hμρ f‖ ≤ ‖f‖ :=
  ((embed μ hμρ).le_opNorm f).trans (mul_le_of_le_one_left (norm_nonneg _)
    (LinearMap.mkContinuous_norm_le _ zero_le_one _))

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem norm_embed_sq [IsFiniteMeasure ρ] {μ : Measure M} [IsProbabilityMeasure μ]
    (hμρ : μ ≪ ρ) (f : Lp ℝ ∞ ρ) : ‖embed μ hμρ f‖ ^ 2 = ∫ y, f y ^ 2 ∂μ := by
  rw [SecondMoment.norm_sq_L2]
  exact integral_congr_ae (by filter_upwards [embed_ae hμρ f] with y hy; rw [hy])

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Cauchy–Schwarz against a bounded measurable function. -/
theorem abs_integral_mul_le [IsFiniteMeasure ρ] {μ : Measure M} [IsProbabilityMeasure μ]
    (hμρ : μ ≪ ρ) {q : M → ℝ} (hq : Measurable q) {B : ℝ} (hB : ∀ y, |q y| ≤ B)
    (f : Lp ℝ ∞ ρ) :
    |∫ y, q y * f y ∂μ| ≤ Real.sqrt (∫ y, q y ^ 2 ∂μ) * ‖embed μ hμρ f‖ := by
  have hmq : MemLp q 2 μ := MemLp.of_bound hq.aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  set Q : Lp ℝ 2 μ := hmq.toLp q
  have hinner : ∫ y, q y * f y ∂μ = @inner ℝ _ _ Q (embed μ hμρ f) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmq.coeFn_toLp, embed_ae hμρ f] with y h1 h2
    rw [h1, h2]; simp [mul_comm]
  have hQ : ‖Q‖ = Real.sqrt (∫ y, q y ^ 2 ∂μ) := by
    rw [← Real.sqrt_sq (norm_nonneg Q), SecondMoment.norm_sq_L2]
    congr 1
    exact integral_congr_ae (by filter_upwards [hmq.coeFn_toLp] with y hy; rw [hy])
  rw [hinner, ← hQ]
  exact abs_real_inner_le_norm _ _

variable [IsFiniteMeasure ρ]

/-- The `L²(μ)` bounds for the normalized transition operator on `L∞(ρ)`. -/
theorem l2_bridge (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (hμρ : μ ≪ ρ) (ℓ : Lp ℝ ∞ ρ →L[ℝ] ℝ)
    (hmean : ∀ f, ℓ f = ∫ y, f y ∂μ) :
    ∃ Cop L κ : ℝ, 0 ≤ Cop ∧ 0 ≤ L ∧ 0 ≤ κ ∧ κ < 1 ∧
      (∀ f, ‖embed μ hμρ (((d.rate.toReal)⁻¹ • h.transitionOperator) f)‖ ≤
        Cop * ‖embed μ hμρ f‖) ∧
      ∀ f, ℓ f = 0 → ∀ m : ℕ, 1 ≤ m →
        ‖embed μ hμρ ((((d.rate.toReal)⁻¹ • h.transitionOperator) ^ m) f)‖ ≤
          L * κ ^ m * ‖embed μ hμρ f‖ := by
  obtain ⟨-, -, P₂, R₂, hP₂, hR₂, L, κ, hL, hκ0, hκ1, hdec⟩ :=
    h.l2_extension_decay (K := C.toKilledKernel) d hc μ hleft hnorm
  set r := d.rate.toReal with hr_def
  set T₀ : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := r⁻¹ • h.transitionOperator with hT₀_def
  set J := embed μ hμρ
  -- Intertwining `J T₀ = P₂ J`.
  have hint : ∀ f, J (T₀ f) = P₂ (J f) := by
    intro f
    apply Lp.ext
    filter_upwards [embed_ae hμρ (T₀ f), hμρ.ae_le (Lp.coeFn_smul r⁻¹ (h.transitionOperator f)),
      hμρ.ae_le (h.transitionOperator_ae f), hP₂ (J f),
      KernelLp.kint_congr hleft (embed_ae hμρ f)] with y h1 h2 h3 h4 h5
    rw [h1, hT₀_def, smul_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
    have h5' : ∫ z, (J f) z ∂C.toKilledKernel.kernel y = ∫ z, f z ∂C.toKilledKernel.kernel y :=
      h5
    rw [h5']
    rfl
  have hintpow : ∀ m f, J ((T₀ ^ m) f) = (P₂ ^ m) (J f) := by
    intro m
    induction m with
    | zero => intro f; simp
    | succ m ih =>
      intro f
      rw [pow_succ', mul_apply_eq_comp, hint, ih, pow_succ',
        mul_apply_eq_comp]
  -- `P₂` preserves the mean and agrees with `R₂` on mean-zero functions.
  have hmeanP : ∀ g : Lp ℝ 2 μ, ∫ y, P₂ g y ∂μ = ∫ y, g y ∂μ := by
    intro g
    have hgi : Integrable (g : M → ℝ) μ := (Lp.memLp g).integrable (by norm_num)
    rw [integral_congr_ae (hP₂ g), integral_const_mul]
    have hk := KernelLp.integral_kint hleft d.rate_ne_top hgi
    have hk' : ∫ y, ∫ z, g z ∂C.toKilledKernel.kernel y ∂μ = r * ∫ y, g y ∂μ := hk
    rw [hk']
    have hr : r ≠ 0 := (ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top).ne'
    change r⁻¹ * (r * _) = _
    field_simp
  have hPR : ∀ g : Lp ℝ 2 μ, ∫ y, g y ∂μ = 0 → P₂ g = R₂ g := by
    intro g hg
    apply Lp.ext
    filter_upwards [hP₂ g, hR₂ g] with y h1 h2
    rw [h1, h2, hg, zero_mul, sub_zero]
  have hPRpow : ∀ m (g : Lp ℝ 2 μ), ∫ y, g y ∂μ = 0 → (P₂ ^ m) g = (R₂ ^ m) g := by
    intro m
    induction m with
    | zero => intro g _; simp
    | succ m ih =>
      intro g hg
      rw [pow_succ', mul_apply_eq_comp, ih g hg, pow_succ',
        mul_apply_eq_comp, hPR]
      have : ∀ k (u : Lp ℝ 2 μ), ∫ y, u y ∂μ = 0 → ∫ y, (R₂ ^ k) u y ∂μ = 0 := by
        intro k
        induction k with
        | zero => intro u hu; simpa using hu
        | succ k ihk =>
          intro u hu
          rw [pow_succ', mul_apply_eq_comp, ← hPR _ (ihk u hu), hmeanP]
          exact ihk u hu
      exact this m g hg
  refine ⟨‖P₂‖, L, κ, norm_nonneg _, hL.le, hκ0.le, hκ1, fun f => ?_, fun f hf m hm => ?_⟩
  · rw [hint]; exact P₂.le_opNorm _
  · rw [hintpow, hPRpow]
    · exact hdec m hm _
    · rw [integral_congr_ae (embed_ae hμρ f), ← hmean, hf]

end Concrete

end

end ConditionedStableLaws.L2Bridge
