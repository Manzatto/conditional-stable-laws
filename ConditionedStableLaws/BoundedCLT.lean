import ConditionedStableLaws.TriangularCLT
import ConditionedStableLaws.ConvergingTogether

/-!
# The conditional CLT for bounded observables

The theorem is the special case `g_n = ḡ`, `a_n = √n` of the conditional triangular-array CLT, for
which the three assumptions are immediate (`n σ_{g_n}²/a_n² = σ_g²`). Absolute convergence of the
correlation series follows from the pointwise decay of centred normalized iterates.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.ConditionalCLT

noncomputable section

open StandingHypothesis CanonicalChain

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The correlation series of a bounded observable converges absolutely. -/
theorem summable_abs_correlation (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) {g : M → ℝ} (hgm : Measurable g) {G : ℝ}
    (hgG : ∀ y, |g y| ≤ G) :
    Summable (fun m => |correlation C μ d g m|) := by
  have : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨D, hDr, hDη, -⟩ := SecondMoment.exists_data0 C h d s μ hleft hnorm 0 zero_lt_one
  set ν := μ.withDensity d.weight with hν_def
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  set gb := centered C μ d g with hgb_def
  set Gb := G + |∫ y, g y ∂ν| with hGb_def
  have hgbm : Measurable gb := hgm.sub measurable_const
  have hgb : ∀ y, |gb y| ≤ Gb := fun y =>
    (abs_sub _ _).trans (by simp only [hGb_def]; linarith [hgG y])
  have hGb0 : 0 ≤ Gb := (abs_nonneg _).trans (hgb (Classical.arbitrary M))
  set F : M → ℝ := fun z => (d.weight z).toReal * gb z with hF_def
  have hFm : Measurable F := d.measurable_weight.ennreal_toReal.mul hgbm
  have hFB : ∀ z, |F z| ≤ D.Bη * Gb := fun z => by
    rw [hF_def, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    have := D.η_le z; rw [hDη] at this
    exact mul_le_mul this (hgb z) (abs_nonneg _) D.Bη_nonneg
  have hF0 : ∫ z, F z ∂μ = 0 := by
    have e : ∫ z, F z ∂μ = ∫ z, gb z ∂ν := by
      rw [hν_def, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
        (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
      rfl
    rw [e, hgb_def]
    simp only [centered]
    rw [integral_sub (SecondMoment.integrable_of_bdd hgm hgG) (integrable_const _),
      integral_const, probReal_univ, one_smul, sub_self]
  have hbound : ∀ m, |correlation C μ d g m| ≤ Gb * (D.A * (D.Bη * Gb)) * D.θ ^ m := by
    intro m
    have hdec : ∀ z, |SecondMoment.nkp C D.r (m + 1) F z| ≤ D.A * D.θ ^ m * (D.Bη * Gb) :=
      fun z => by
        have := D.decay F hFm _ hFB m z
        rwa [hF0, zero_mul, sub_zero] at this
    have hpt : ∀ y, |gb y * SecondMoment.nkp C D.r (m + 1) F y| ≤
        Gb * (D.A * D.θ ^ m * (D.Bη * Gb)) := fun y => by
      rw [abs_mul]; exact mul_le_mul (hgb y) (hdec y) (abs_nonneg _) hGb0
    have e : correlation C μ d g m = ∫ y, gb y * SecondMoment.nkp C D.r (m + 1) F y ∂μ := by
      rw [hDr]; rfl
    rw [e]
    calc _ ≤ Gb * (D.A * D.θ ^ m * (D.Bη * Gb)) := SecondMoment.abs_integral_le_of_prob hpt
      _ = _ := by ring
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbound
    ((summable_geometric_of_lt_one D.θ_nonneg D.θ_lt_one).mul_left _)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem centered_centered (μ : Measure M) [IsProbabilityMeasure μ]
    (d : DoobTransform.EigenData C.killedTransition) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {g : M → ℝ} (hgm : Measurable g) {G : ℝ} (hgG : ∀ y, |g y| ≤ G) :
    centered C μ d (centered C μ d g) = centered C μ d g := by
  set ν := μ.withDensity d.weight with hν_def
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have h0 : ∫ y, centered C μ d g y ∂ν = 0 := by
    simp only [centered]
    rw [integral_sub (SecondMoment.integrable_of_bdd hgm hgG) (integrable_const _),
      integral_const, probReal_univ, one_smul, sub_self]
  funext y
  show centered C μ d g y - ∫ z, centered C μ d g z ∂ν = centered C μ d g y
  rw [h0, sub_zero]

/-- **Conditional CLT for bounded observables.** For bounded measurable `g` and every `x ∈ M \ Z`,
the correlation series converges absolutely, `σ_g² ≥ 0`, and under `ℙₓ(· | τ > n)`, `n^{-1/2}
∑_{j<n} ḡ(X_j) → 𝒩(0, σ_g²)` in distribution. -/
theorem conditional_clt_bounded (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) {g : M → ℝ} (hgm : Measurable g) {G : ℝ}
    (hgG : ∀ y, |g y| ≤ G) (x : d.State) :
    Summable (fun m => |correlation C μ d g m|) ∧ 0 ≤ asymptoticVariance C μ d g ∧
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ *
      pathBirkhoffSum (centered C μ d g) n ω)
      atTop id (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (gaussianReal 0 (asymptoticVariance C μ d g).toNNReal) := by
  set ν := μ.withDensity d.weight with hν_def
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  set gb := centered C μ d g with hgb_def
  set Gb := G + |∫ y, g y ∂ν| with hGb_def
  have hgbm : Measurable gb := hgm.sub measurable_const
  have hgb : ∀ y, |gb y| ≤ Gb := fun y =>
    (abs_sub _ _).trans (by simp only [hGb_def]; linarith [hgG y])
  have hcc : centered C μ d gb = gb := centered_centered C μ d hnorm hgm hgG
  have hgbν : ∫ y, gb y ∂ν = 0 := by
    have h0 := congrFun hcc x.val
    change gb x.val - ∫ z, gb z ∂ν = gb x.val at h0
    linarith
  have hvar : asymptoticVariance C μ d gb = asymptoticVariance C μ d g := by
    unfold asymptoticVariance correlation
    rw [hcc]
  set a : ℕ → ℝ := fun n => Real.sqrt (max (n : ℝ) 1) with ha_def
  have ha : ∀ n, 0 < a n := fun n =>
    Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  have ha_lim : Tendsto a atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_mono (fun n => le_max_left _ _)
      tendsto_natCast_atTop_atTop)
  have ha_sq : ∀ n, a n ^ 2 = max (n : ℝ) 1 := fun n =>
    Real.sq_sqrt (zero_le_one.trans (le_max_right _ _))
  have hi : Tendsto (fun n => Gb / a n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop ha_lim
  have hii : ∃ B : ℝ, ∀ n : ℕ, n * (∫ y, gb y ^ 2 ∂ν + ∫ y, gb y ^ 2 ∂μ) / a n ^ 2 ≤ B := by
    refine ⟨∫ y, gb y ^ 2 ∂ν + ∫ y, gb y ^ 2 ∂μ, fun n => ?_⟩
    have hS : 0 ≤ ∫ y, gb y ^ 2 ∂ν + ∫ y, gb y ^ 2 ∂μ :=
      add_nonneg (integral_nonneg fun y => sq_nonneg _) (integral_nonneg fun y => sq_nonneg _)
    rw [ha_sq, div_le_iff₀ (lt_of_lt_of_le one_pos (le_max_right _ _))]
    nlinarith [le_max_left (n : ℝ) 1]
  have hiii : Tendsto (fun n : ℕ => n * asymptoticVariance C μ d gb / a n ^ 2) atTop
      (𝓝 (asymptoticVariance C μ d gb)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [ha_sq, max_eq_left hn']
    field_simp
  obtain ⟨hσ, hY⟩ := TriangularCLT.conditional_triangular_clt C h d s hlive μ hleft hnorm
    (fun _ => gb) (fun _ => hgbm) (fun _ => Gb) (fun _ => hgb) (fun _ => hgbν) a ha ha_lim hi
    hii hiii x
  rw [hvar] at hσ hY
  refine ⟨summable_abs_correlation C h d s μ hleft hnorm hgm hgG, hσ, ?_⟩
  refine tendstoInDistribution_of_varying_probability_approximation
    (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
    (gaussianReal 0 (asymptoticVariance C μ d g).toNNReal) _
    (fun n ω => (a n)⁻¹ * pathBirkhoffSum gb n ω) id
    (fun n => (measurable_pathBirkhoffSum hgbm n).const_mul _)
    (fun n => (measurable_pathBirkhoffSum hgbm n).const_mul _) hY (fun ε hε => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : {ω | ε < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum gb n ω -
      (a n)⁻¹ * pathBirkhoffSum gb n ω|} = ∅ := by
    ext ω
    simp only [ha_def, max_eq_left hn', sub_self, abs_zero, Set.mem_ofPred_eq, mem_empty_iff_false,
      iff_false, not_lt]
    exact hε.le
  rw [this, measureReal_empty]

end

end ConditionedStableLaws.ConditionalCLT
