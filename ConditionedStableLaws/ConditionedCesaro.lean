import ConditionedStableLaws.HypothesisSpectralGap
import ConditionedStableLaws.OperatorCesaro
import ConditionedStableLaws.ClusterMixing

/-! Canonical conditional Cesàro averages and the quasi-ergodic limit. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.CanonicalChain
noncomputable section
open StandingHypothesis ConditionalMixing PathMixing ClusterMixing
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  (C : CanonicalChain M) {ρ : Measure M}

/-- Exact single-time conditional expectation in normalized operator form,
including zero gaps on either side of the observation. -/
theorem integral_conditioned_unit_observable (h : HypothesisH ρ C.toKilledKernel)
    (c : ℝ) (hc : c ≠ 0) (one : Lp ℝ ∞ ρ)
    (hone : one =ᵐ[ρ] fun _ => (1 : ℝ)) (x : M)
    (F : M → ℝ≥0∞) (hFm : Measurable F) (hFb : ∀ y, F y ≤ 1)
    (g : Lp ℝ ∞ ρ) (hg : (fun y => (F y).toReal) =ᵐ[ρ] g) (i t : ℕ) :
    (∫ ω, zeroExtension (fun y => (F y).toReal) (ω (i+1))
      ∂C.conditionedMeasure x (i+t+1)) =
      h.stepEvaluation c x ((((c • h.transitionOperator)^i) * lpMultiplication ρ g *
        ((c • h.transitionOperator)^t)) one) /
      h.stepEvaluation c x (((c • h.transitionOperator)^(i+t)) one) := by
  have he := C.integral_conditioned_blocks_operator h c hc one hone x
    [(i, { first := g, internal := [] })] (fun _ => F)
    (fun _ _ => hFm) (fun _ _ => hFb) (by
      intro p hp
      simp [flatten] at hp
      subst p
      exact hg) t
  simp only [flatten, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    blockObservations, blockOperator, operatorWord, mul_one,
    liftObservations, pathProduct, ENNReal.toReal_mul] at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [C.ae_survival_conditionedMeasure x (i+t+1)] with ω hω
  have hs : ω 1 ≠ none := hω 1 (by omega)
  cases h1 : ω 1 with
  | none => exact False.elim (hs h1)
  | some y =>
    simp only [liveExtension, ENNReal.toReal_one, one_mul]
    rw [Nat.add_comm 1 i]
    cases ω (i+1) <;> rfl

/-- The conditional expectations averaged over times `1,…,n` converge to the rank-one coefficient,
including both temporal boundaries. -/
theorem tendsto_conditioned_unit_average (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.toKilledKernel.kernel) (s : SurvivalGapData h d)
    (x : M) (hx : x ∈ d.liveSet)
    (F : M → ℝ≥0∞) (hFm : Measurable F) (hFb : ∀ y, F y ≤ 1)
    (g : Lp ℝ ∞ ρ) (hg : (fun y => (F y).toReal) =ᵐ[ρ] g) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      ∫ ω, zeroExtension (fun y => (F y).toReal) (ω (i+1))
        ∂C.conditionedMeasure x n) atTop
      (𝓝 (s.mean (lpMultiplication ρ g s.eigenvector))) := by
  let Q := (d.rate.toReal)⁻¹ • h.transitionOperator
  let ev := h.stepEvaluation (d.rate.toReal)⁻¹ x
  have hr : d.rate.toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨d.rate_ne_zero, d.rate_ne_top⟩
  have he : ev s.eigenvector = (d.weight x).toReal := by
    rw [← h.smoothedOperator_apply]
    exact h.smoothed_eigenvector d s.eigenvector s.eigenvector_ae x
  have hpos : 0 < ev s.eigenvector := by
    rw [he]
    exact ENNReal.toReal_pos (by exact hx) (d.weight_ne_top x)
  have hl := OperatorCesaro.tendsto_conditional_average Q (lpMultiplication ρ g)
    s.mean ev s.eigenvector s.one s.mean_one hpos s.fullConstant_nonneg
    s.decay_nonneg s.decay_lt_one s.full_gap
  apply hl.congr' (eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  have hi (i : ℕ) (hin : i ∈ Finset.range n) :
      (∫ ω, zeroExtension (fun y => (F y).toReal) (ω (i+1))
        ∂C.conditionedMeasure x n) =
      ev ((Q^i * lpMultiplication ρ g * Q^(n-1-i)) s.one) /
        ev ((Q^(n-1)) s.one) := by
    have hit : i+(n-1-i) = n-1 := by
      have := Finset.mem_range.mp hin
      omega
    simpa only [hit, Nat.sub_add_cancel hn] using
      C.integral_conditioned_unit_observable h (d.rate.toReal)⁻¹ (inv_ne_zero hr)
        s.one s.one_ae x F hFm hFb g hg i (n-1-i)
  simp only [smul_apply, sum_apply,
    map_smul, map_sum, smul_eq_mul]
  rw [Finset.sum_congr rfl hi, ← Finset.sum_div]
  ring

/-- Identifying the rank-one coefficient with integration against `η μ`. -/
theorem tendsto_conditioned_unit_average_weighted
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.toKilledKernel.kernel) (s : SurvivalGapData h d)
    (μ : Measure M) (hleft : C.toKilledKernel.kernel ∘ₘ μ = d.rate • μ)
    (hmean : ∀ f : Lp ℝ ∞ ρ, s.mean f = ∫ y, f y ∂μ)
    (x : M) (hx : x ∈ d.liveSet)
    (F : M → ℝ≥0∞) (hFm : Measurable F) (hFb : ∀ y, F y ≤ 1) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      ∫ ω, zeroExtension (fun y => (F y).toReal) (ω (i+1))
        ∂C.conditionedMeasure x n) atTop
      (𝓝 (∫ y, (F y).toReal ∂μ.withDensity d.weight)) := by
  have hmem : MemLp (fun y => (F y).toReal) ∞ ρ :=
    memLp_top_of_bound hFm.ennreal_toReal.aestronglyMeasurable 1 (ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (ENNReal.toReal_mono (by simp) (hFb y)).trans_eq ENNReal.toReal_one))
  let g := hmem.toLp (fun y => (F y).toReal)
  have hg : (fun y => (F y).toReal) =ᵐ[ρ] g := hmem.coeFn_toLp.symm
  have hc := C.tendsto_conditioned_unit_average h d s x hx F hFm hFb g hg
  have hac := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  have heq : s.mean (lpMultiplication ρ g s.eigenvector) =
      ∫ y, (F y).toReal ∂μ.withDensity d.weight := by
    rw [hmean, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (ae_of_all _ (fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y)))]
    apply integral_congr_ae
    filter_upwards [hac.ae_eq (lpMultiplication_ae ρ g s.eigenvector),
      hac.ae_eq hg, hac.ae_eq s.eigenvector_ae] with y hy hgy hey
    rw [hy, ← hgy, hey, smul_eq_mul, mul_comm]
  rwa [heq] at hc

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Bounded measurable state observables are integrable on every finite path law. -/
theorem integrable_zeroExtension {f : M → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B)
    (P : Measure (Path M)) [IsFiniteMeasure P] (i : ℕ) :
    Integrable (fun ω => zeroExtension f (ω i)) P := by
  apply Integrable.of_bound ((measurable_zeroExtension hf).comp
    (measurable_pi_apply i)).aestronglyMeasurable B
  exact ae_of_all _ (fun ω => by
    cases hω : ω i with
    | none => simpa [hω, zeroExtension] using hB
    | some y => simpa [hω, zeroExtension] using hb y)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- On a survival-conditioned path, affine transformations of an observation
have the usual expectation formula, also at the first and last times. -/
theorem integral_conditioned_affine_unit (x : M)
    (hx : x ∈ survivingSet C.killedTransition) (n i : ℕ) (hi : i ≤ n)
    (F : M → ℝ≥0∞) (hFm : Measurable F) (hFb : ∀ y, F y ≤ 1)
    (f : M → ℝ) (a b : ℝ) (hf : ∀ y, f y = a*(F y).toReal+b) :
    (∫ ω, zeroExtension f (ω i) ∂C.conditionedMeasure x n) =
      a*(∫ ω, zeroExtension (fun y => (F y).toReal) (ω i)
        ∂C.conditionedMeasure x n)+b := by
  let := C.conditionedMeasure_isProbability_of_surviving x hx n
  have hFi : Integrable (fun ω => zeroExtension (fun y => (F y).toReal) (ω i))
      (C.conditionedMeasure x n) :=
    integrable_zeroExtension hFm.ennreal_toReal zero_le_one (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (ENNReal.toReal_mono (by simp) (hFb y)).trans_eq ENNReal.toReal_one) _ i
  have he : (fun ω => zeroExtension f (ω i)) =ᵐ[C.conditionedMeasure x n]
      (fun ω => a*zeroExtension (fun y => (F y).toReal) (ω i)+b) := by
    filter_upwards [C.ae_survival_conditionedMeasure x n] with ω hω
    cases hi' : ω i with
    | none => exact False.elim (hω i hi hi')
    | some y => exact hf y
  rw [integral_congr_ae he, integral_add (hFi.const_mul a) (integrable_const b),
    integral_const_mul]
  simp

/-- A bounded signed observable has the quasi-ergodic average limit. The time window here is
`1,…,n`; the following endpoint lemma returns to `0,…,n-1`. -/
theorem tendsto_conditioned_bounded_average_weighted
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.toKilledKernel.kernel) (s : SurvivalGapData h d)
    (μ : Measure M) (hleft : C.toKilledKernel.kernel ∘ₘ μ = d.rate • μ)
    (hmean : ∀ f : Lp ℝ ∞ ρ, s.mean f = ∫ y, f y ∂μ)
    (hnorm : ∫⁻ y, d.weight y ∂μ = 1) (hlive : d.liveSet = survivingSet C.killedTransition)
    (x : M) (hx : x ∈ d.liveSet)
    (f : M → ℝ) (hfm : Measurable f) {B : ℝ} (hB : 0 < B)
    (hfb : ∀ y, |f y| ≤ B) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      ∫ ω, zeroExtension f (ω (i+1)) ∂C.conditionedMeasure x n) atTop
      (𝓝 (∫ y, f y ∂μ.withDensity d.weight)) := by
  let F : M → ℝ≥0∞ := fun y => ENNReal.ofReal ((f y+B)/(2*B))
  have hnonneg (y : M) : 0 ≤ (f y+B)/(2*B) :=
    div_nonneg (by linarith [(abs_le.mp (hfb y)).1]) (by positivity)
  have hto (y : M) : (F y).toReal = (f y+B)/(2*B) := ENNReal.toReal_ofReal (hnonneg y)
  have hFm : Measurable F := (hfm.add_const B |>.div_const (2*B)).ennreal_ofReal
  have hFb (y : M) : F y ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    rw [div_le_iff₀ (by positivity : 0 < 2*B)]
    linarith [(abs_le.mp (hfb y)).2]
  have hf (y : M) : f y = (2*B)*(F y).toReal+(-B) := by
    rw [hto]
    field_simp
    ring
  let ν := μ.withDensity d.weight
  have : IsProbabilityMeasure ν := ⟨by
    change μ.withDensity d.weight univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa using hnorm⟩
  have hFi : Integrable (fun y => (F y).toReal) ν :=
    Integrable.of_bound hFm.ennreal_toReal.aestronglyMeasurable 1 (ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (ENNReal.toReal_mono (by simp) (hFb y)).trans_eq ENNReal.toReal_one))
  have hv : (∫ y, f y ∂ν) = (2*B)*(∫ y, (F y).toReal ∂ν)+(-B) := by
    conv_lhs => arg 2; ext y; rw [hf y]
    rw [integral_add (hFi.const_mul _) (integrable_const _), integral_const_mul]
    simp
  rw [show μ.withDensity d.weight = ν from rfl, hv]
  have hl := (C.tendsto_conditioned_unit_average_weighted h d s μ hleft hmean
    x hx F hFm hFb).const_mul (2*B) |>.add_const (-B)
  apply hl.congr' (eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  have hi (i : ℕ) (hin : i ∈ Finset.range n) :=
    C.integral_conditioned_affine_unit x (hlive ▸ hx) n (i+1)
      (by have := Finset.mem_range.mp hin; omega) F hFm hFb f (2*B) (-B) hf
  rw [Finset.sum_congr rfl hi]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- Uniformly bounded endpoints do not affect a Cesàro limit, even when
the entire array depends on the conditioning horizon. -/
theorem tendsto_average_of_shifted (u : ℕ → ℕ → ℝ) {B L : ℝ}
    (hb : ∀ n i, ‖u n i‖ ≤ B)
    (hl : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, u n (i+1))
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, u n i) atTop (𝓝 L) := by
  have herror : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (u n 0-u n n)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    have hbound (n : ℕ) : ‖(n : ℝ)⁻¹ * (u n 0-u n n)‖ ≤ (n : ℝ)⁻¹*(B+B) := by
      rw [norm_mul, norm_inv, Real.norm_natCast]
      exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hb n 0) (hb n n)))
        (by positivity)
    exact squeeze_zero (fun _ => norm_nonneg _) hbound (by
      simpa using ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
        (B+B) : Tendsto (fun n : ℕ => (n : ℝ)⁻¹*(B+B)) atTop (𝓝 (0*(B+B)))))
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, u n i) =
      (∑ i ∈ Finset.range n, u n (i+1))+u n 0-u n n := by
    have h1 := Finset.sum_range_succ (u n) n
    have h2 := Finset.sum_range_succ' (u n) n
    linarith
  have ht := hl.add herror
  simp only [add_zero] at ht
  convert! ht using 1
  funext n
  rw [hsum]
  ring

/-- The Birkhoff-average conditional expectation converges to integration against `η μ`, at every
nonescaping starting state. -/
theorem tendsto_conditioned_birkhoff_weighted
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.toKilledKernel.kernel) (s : SurvivalGapData h d)
    (μ : Measure M) (hleft : C.toKilledKernel.kernel ∘ₘ μ = d.rate • μ)
    (hmean : ∀ f : Lp ℝ ∞ ρ, s.mean f = ∫ y, f y ∂μ)
    (hnorm : ∫⁻ y, d.weight y ∂μ = 1) (hlive : d.liveSet = survivingSet C.killedTransition)
    (x : M) (hx : x ∈ d.liveSet)
    (f : M → ℝ) (hfm : Measurable f) {B : ℝ} (hB : 0 < B)
    (hfb : ∀ y, |f y| ≤ B) :
    Tendsto (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ * pathBirkhoffSum f n ω
      ∂C.conditionedMeasure x n) atTop
      (𝓝 (∫ y, f y ∂μ.withDensity d.weight)) := by
  have hprob (n : ℕ) := C.conditionedMeasure_isProbability_of_surviving x (hlive ▸ hx) n
  have hb (n i : ℕ) : ‖∫ ω, zeroExtension f (ω i) ∂C.conditionedMeasure x n‖ ≤ B := by
    let := hprob n
    have hbb : ∀ᵐ ω ∂C.conditionedMeasure x n, ‖zeroExtension f (ω i)‖ ≤ B :=
      ae_of_all _ (fun ω => by
        cases ω i with
        | none => simpa [zeroExtension] using hB.le
        | some y => simpa [zeroExtension, Real.norm_eq_abs] using hfb y)
    simpa using norm_integral_le_of_norm_le_const hbb
  have hl := tendsto_average_of_shifted _ hb
    (C.tendsto_conditioned_bounded_average_weighted h d s μ hleft hmean hnorm hlive
      x hx f hfm hB hfb)
  convert! hl using 1
  funext n
  let := hprob n
  rw [integral_const_mul]
  congr 1
  change (∫ ω, ∑ i ∈ Finset.range n, zeroExtension f (ω i) ∂C.conditionedMeasure x n) = _
  exact integral_finsetSum _ (fun i _ =>
    integrable_zeroExtension hfm hB.le (by simpa only [Real.norm_eq_abs] using hfb)
      (C.conditionedMeasure x n) i)

/-- Hypothesis H alone produces the weighted probability and the quasi-ergodic limit for every
bounded measurable observable and every nonescaping initial state. -/
theorem exists_pointwise_quasiErgodic_eigenData (h : HypothesisH ρ C.toKilledKernel) :
    ∃ d : DoobTransform.EigenData C.toKilledKernel.kernel,
      d.rate ≤ 1 ∧ Continuous d.weight ∧ d.liveSet = survivingSet C.killedTransition ∧
      ∃ μ : ProbabilityMeasure M,
        C.toKilledKernel.kernel ∘ₘ (μ : Measure M) = d.rate • (μ : Measure M) ∧
        (∫⁻ y, d.weight y ∂(μ : Measure M)) = 1 ∧
        ∀ x ∈ survivingSet C.killedTransition, ∀ f : M → ℝ, Measurable f →
          (∃ B : ℝ, ∀ y, |f y| ≤ B) →
          Tendsto (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ * pathBirkhoffSum f n ω
            ∂C.conditionedMeasure x n) atTop
            (𝓝 (∫ y, f y ∂(μ : Measure M).withDensity d.weight)) := by
  obtain ⟨d, hdr, hc, hlive, μ, hleft, hnorm⟩ := h.exists_normalized_eigenData
  obtain ⟨s, hs⟩ := h.exists_survivalGapData_with_mean d hc μ hleft hnorm
  refine ⟨d, hdr, hc, hlive, μ, hleft, hnorm, ?_⟩
  intro x hx f hfm hfb
  obtain ⟨B, hb⟩ := hfb
  exact C.tendsto_conditioned_birkhoff_weighted h d s μ hleft hs hnorm hlive x
    (hlive.symm ▸ hx) f hfm (lt_of_lt_of_le zero_lt_one (le_max_right B 1))
    (fun y => (hb y).trans (le_max_left B 1))

end
end ConditionedStableLaws.CanonicalChain
