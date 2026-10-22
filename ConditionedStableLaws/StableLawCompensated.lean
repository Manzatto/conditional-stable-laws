import ConditionedStableLaws.SmallJumpMoment
import ConditionedStableLaws.CompensationAsymptotics
import ConditionedStableLaws.CompensatedPoissonLimits

/-!
# The conditional stable laws for `α = 1` and `1 < α < 2`

Under `ℙₓ(· | τ > n)`:

* (ii) if `α = 1`: `B_n⁻¹ (∑_{j<n} f_β(X_j) - A_n) → Z₁`, with `A_n = n ν(f_β 1_{f_β ≤ B_n})` and
  `Z₁ = lim_{ε→0} (∫_{(ε,∞]} y N(dy) - ∫_{(ε,1]} y υ_1(dy))`;
* (iii) if `1 < α < 2`: `f_β ∈ L¹(ν)` and `B_n⁻¹ (∑_{j<n} f_β(X_j) - n ν(f_β)) → Z_α`, with `Z_α =
  lim_{ε→0} (∫_{(ε,∞]} y N(dy) - ∫_{(ε,∞]} y υ_α(dy))`.

Middle jumps converge by the point-process theorem, together with the convergence of the
deterministic centring constants; the compensated small jumps are controlled in `L²` by the
conditional second-moment estimate and Chebyshev's inequality; large jumps by the point-process
count on `(R,∞]`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.StableLawCompensated

noncomputable section

open StandingHypothesis CanonicalChain NormalizationBridge StableLawSmall SmallJumpMoment
  AnnularPoissonClouds

/-! ### Exact pathwise decomposition -/

section Pathwise

variable {M : Type*} [MeasurableSpace M]

/-- On a surviving path, either some normalized observation exceeds `R`, or the
normalized sum minus its middle-jump part is exactly the normalized sum of the
small observations `f 1_{f ≤ εB}`. -/
theorem decomposition_eq {f : M → ℝ} (hm : Measurable f) (hf : ∀ x, 0 < f x) {n : ℕ} {B : ℝ}
    (hB : 0 < B) {ε R : ℝ≥0} (hε : 0 < ε) (hεR : ε ≤ R) {ω : Path M} (hω : ω ∈ survival n) :
    1 ≤ ((pathEmpirical f hm hf n B hB).toFun ω).countOn
        (Ioc (TruncatedPointIntegrals.endpoint R (hε.trans_le hεR)) ⊤) ∨
      B⁻¹ * pathBirkhoffSum f n ω -
          TruncatedPointIntegrals.truncatedIntegral (TruncatedPointIntegrals.endpoint ε hε)
            (TruncatedPointIntegrals.endpoint R (hε.trans_le hεR))
            ((pathEmpirical f hm hf n B hB).toFun ω) =
        B⁻¹ * pathBirkhoffSum (trunc f (ε * B)) n ω := by
  have hR : 0 < R := hε.trans_le hεR
  set y : Fin n → ℝ := fun i => positiveExtension f (ω i) / B
  have hy (i : Fin n) : 0 < y i := div_pos (positiveExtension_pos hf _) hB
  have hemp : (pathEmpirical f hm hf n B hB).toFun ω =
      LocallyFinitePointMeasure.empirical
        (fun i => ⟨ENNReal.ofReal (y i), ENNReal.ofReal_pos.2 (hy i)⟩) := rfl
  by_cases hlarge : ∃ i, (R : ℝ) < y i
  · obtain ⟨i, hi⟩ := hlarge
    left
    rw [hemp]
    exact one_le_countOn_empirical _ (measurableSet_Ioc_extreme _ _)
      (i := i) ((mem_Ioc_top hR (hy i)).2 hi)
  right
  push Not at hlarge
  have hpos (i : ℕ) (hi : i < n) : zeroExtension f (ω i) = positiveExtension f (ω i) :=
    (positiveExtension_eq_zeroExtension (hω i hi.le)).symm
  have hsum : B⁻¹ * pathBirkhoffSum f n ω = ∑ i, y i := by
    unfold pathBirkhoffSum birkhoffSum
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hpos i i.isLt]
    simp only [y]
    ring
  have hmid : TruncatedPointIntegrals.truncatedIntegral (TruncatedPointIntegrals.endpoint ε hε)
      (TruncatedPointIntegrals.endpoint R hR) ((pathEmpirical f hm hf n B hB).toFun ω) =
      ∑ i, if (ε : ℝ) < y i then y i else 0 := by
    rw [hemp, truncatedIntegral_empirical]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (ε : ℝ) < y i
    · rw [Set.indicator_of_mem ((mem_Ioc_endpoints hε hR (hy i)).2 ⟨hi, hlarge i⟩), ite_eq_left hi]
      exact ENNReal.toReal_ofReal (hy i).le
    · rw [Set.indicator_of_notMem (fun h => hi ((mem_Ioc_endpoints hε hR (hy i)).1 h).1),
        ite_eq_right hi]
  have hsmall : B⁻¹ * pathBirkhoffSum (trunc f (ε * B)) n ω =
      ∑ i, if y i ≤ ε then y i else 0 := by
    unfold trunc pathBirkhoffSum birkhoffSum
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (hω i i.isLt.le)
    have hyz : y i = f z / B := by simp only [y, hz, positiveExtension]
    simp only [hz, zeroExtension_some, hyz]
    by_cases hzi : f z ≤ ε * B
    · rw [Set.indicator_of_mem (show z ∈ {z | f z ≤ ε * B} from hzi),
        ite_eq_left ((div_le_iff₀ hB).2 hzi)]
      ring
    · rw [Set.indicator_of_notMem (show z ∉ {z | f z ≤ ε * B} from hzi),
        ite_eq_right (fun h => hzi ((div_le_iff₀ hB).1 h)), mul_zero]
  rw [hsum, hmid, hsmall, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (ε : ℝ) < y i
  · rw [ite_eq_left hi, ite_eq_right (not_le.2 hi), sub_self]
  · rw [ite_eq_right hi, ite_eq_left (not_lt.1 hi), sub_zero]

end Pathwise

/-! ### Compensated small jumps -/

section SmallJumps

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Chebyshev's inequality with the conditional second-moment estimate and the scaled truncated
second moment: eventually in `n`, `ℙ_{x,n}(|∫_{(0,ε]} y (N_n - υ_n)(dy)| > δ) ≤ K (ε^{2-α} +
ε²)/δ²`. -/
theorem compensated_small_jumps_eventually (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (x : d.State) {x₀ : M} {β Cc α : ℝ} (hβ : 0 < β)
    (hx₀ : d.weight x₀ ≠ 0) (hC : 0 < Cc) (hα : 0 < α) (hα2 : α < 2)
    (htail : Tendsto (fun t : ℝ => (μ.withDensity d.weight).real
      {z | t < singularObservable x₀ β z} / (Cc * t ^ (-α))) atTop (𝓝 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      (C.conditionedMeasure x.val n).real {ω | δ < |(positivePowerScale Cc α n)⁻¹ *
          pathBirkhoffSum (trunc (singularObservable x₀ β) (ε * positivePowerScale Cc α n)) n ω -
          n * (positivePowerScale Cc α n)⁻¹ * ∫ y, trunc (singularObservable x₀ β)
            (ε * positivePowerScale Cc α n) y ∂μ.withDensity d.weight|} ≤
        K * (ε ^ (2 - α) + ε ^ 2) / δ ^ 2 := by
  obtain ⟨Cx, hCx, o, ho, hmain⟩ := conditional_small_jump_second_moment_singular C h d s hlive
    μ hleft hnorm x hβ hx₀ hC hα hα2
  set f := singularObservable x₀ β with hf_def
  set ν := μ.withDensity d.weight with hν_def
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hfm : Measurable f := measurable_singularObservable x₀ β
  have hf0 : ∀ z, 0 ≤ f z := fun z => (singularObservable_pos x₀ β z).le
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  have h2α : 0 < 2 - α := sub_pos.2 hα2
  have ha0 : 0 ≤ α / (2 - α) := div_nonneg hα.le h2α.le
  refine ⟨(Cx + 1) * (α / (2 - α) + 1), by positivity, fun ε hε δ hδ => ?_⟩
  set B := positivePowerScale Cc α with hB_def
  have hεp : 0 < ε ^ (2 - α) := Real.rpow_pos_of_pos hε _
  have h2 := CompensationAsymptotics.scaled_second_moment (ν := ν) hfm hf0 hC hα hα2 htail hε
  have hev2 : ∀ᶠ n : ℕ in atTop, (n : ℝ) / B n ^ 2 *
      ∫ y, {y | f y ≤ ε * B n}.indicator (fun y => f y ^ 2) y ∂ν ≤
        α / (2 - α) * ε ^ (2 - α) + ε ^ (2 - α) :=
    h2.eventually (ge_mem_nhds (by linarith))
  have hevo : ∀ᶠ n : ℕ in atTop, o n ≤ ε ^ 2 := ho.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hev2, hevo] with n hn2 hno
  have := C.conditionedMeasure_isProbability_of_surviving x.val hx n
  set P := C.conditionedMeasure x.val n with hP_def
  have hB : 0 < B n := positivePowerScale_pos hC n
  set g := trunc f (ε * B n) with hg_def
  have hgm : Measurable g := measurable_trunc hfm _
  have hg0 : ∀ z, 0 ≤ g z := trunc_nonneg hf0 (ε * B n)
  have hgb : ∀ z, |g z| ≤ ε * B n := fun z => by
    rw [abs_of_nonneg (hg0 z)]; exact trunc_le (mul_pos hε hB).le z
  set c := ∫ y, g y ∂ν with hc_def
  set Y : Path M → ℝ := fun ω => (B n)⁻¹ * pathBirkhoffSum g n ω - n * (B n)⁻¹ * c with hY_def
  have hYm : Measurable Y := ((measurable_pathBirkhoffSum hgm n).const_mul _).sub_const _
  have hcb : |c| ≤ ε * B n := SecondMoment.abs_integral_le_of_prob hgb
  have hS : ∀ ω, |pathBirkhoffSum g n ω| ≤ n * (ε * B n) := by
    intro ω
    unfold pathBirkhoffSum birkhoffSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range n, |zeroExtension g (ω i)| ≤ ∑ _i ∈ Finset.range n, ε * B n :=
          Finset.sum_le_sum fun i _ =>
            SecondMoment.abs_zeroExtension_le (mul_pos hε hB).le hgb _
      _ = n * (ε * B n) := by simp
  have hYb : ∀ ω, |Y ω| ≤ 2 * n * ε := by
    intro ω
    have hBinv : 0 < (B n)⁻¹ := inv_pos.2 hB
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc |Y ω| ≤ |(B n)⁻¹ * pathBirkhoffSum g n ω| + |n * (B n)⁻¹ * c| := abs_sub _ _
      _ ≤ (B n)⁻¹ * (n * (ε * B n)) + n * (B n)⁻¹ * (ε * B n) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hBinv, Nat.abs_cast]
          exact add_le_add (mul_le_mul_of_nonneg_left (hS ω) hBinv.le)
            (mul_le_mul_of_nonneg_left hcb (mul_nonneg hn0 hBinv.le))
      _ = 2 * n * ε := by field_simp; ring
  have hY2int : Integrable (fun ω => Y ω ^ 2) P :=
    SecondMoment.integrable_of_bdd (hYm.pow_const 2) (SecondMoment.sq_bdd hYb)
  have hE : ∫ ω, Y ω ^ 2 ∂P ≤ (Cx + 1) * (α / (2 - α) + 1) * (ε ^ (2 - α) + ε ^ 2) := by
    have h1 := hmain ε hε n
    have hsq : ∫ y, g y ^ 2 ∂ν = ∫ y, {y | f y ≤ ε * B n}.indicator (fun y => f y ^ 2) y ∂ν := by
      congr 1; funext y
      simp only [hg_def, trunc, Set.indicator]
      split_ifs <;> simp
    rw [hsq] at h1
    have h3 : Cx * ((n : ℝ) / B n ^ 2) *
        ∫ y, {y | f y ≤ ε * B n}.indicator (fun y => f y ^ 2) y ∂ν ≤
        Cx * (α / (2 - α) * ε ^ (2 - α) + ε ^ (2 - α)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hn2 hCx
    have h4 : 0 ≤ Cx * (α / (2 - α)) * ε ^ 2 + (α / (2 - α) + 1) * ε ^ (2 - α) +
        α / (2 - α) * ε ^ 2 := by positivity
    calc ∫ ω, Y ω ^ 2 ∂P ≤ _ := h1
      _ ≤ Cx * (α / (2 - α) * ε ^ (2 - α) + ε ^ (2 - α)) + Cx * ε ^ 2 + ε ^ 2 := by linarith
      _ ≤ _ := by nlinarith
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg (Y ω)) hY2int
    (δ ^ 2)
  have hsub : {ω | δ < |Y ω|} ⊆ {ω | δ ^ 2 ≤ Y ω ^ 2} := fun ω hω => by
    have hω' : δ < |Y ω| := hω
    show δ ^ 2 ≤ Y ω ^ 2
    rw [← sq_abs (Y ω)]; exact pow_le_pow_left₀ hδ.le hω'.le 2
  have hmono : P.real {ω | δ < |Y ω|} ≤ P.real {ω | δ ^ 2 ≤ Y ω ^ 2} := measureReal_mono hsub
  change P.real {ω | δ < |Y ω|} ≤ _
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hmono, hmk, hE, sq_nonneg δ]

end SmallJumps

/-! ### The general compensated stable law -/

section Main

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The compensated stable law from the convergence of the centring
constants: if `B_n⁻¹ c_n = n B_n⁻¹ ν(f 1_{f ≤ εₖB_n}) + mₖ(n)` with
`mₖ(n) → mₖ`, and the cut compensated Poisson integrals
`∫_{(εₖ,Rₖ]} y N(dy) - mₖ` converge in distribution to `W`, then
`B_n⁻¹ (∑_{j<n} f_β(X_j) - c_n) → W` under `ℙₓ(· | τ > n)`. -/
theorem stable_law_of_compensation (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β α : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hαdef : dimension / β = α) (hα : 0 < α)
    (hα2 : α < 2) (c : ℕ → ℝ) (mk : ℕ → ℕ → ℝ) (mlim : ℕ → ℝ) (W : Sample → ℝ)
    (hc : ∀ k n, (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) α n)⁻¹ *
        c n = n * (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) α n)⁻¹ *
          ∫ y, trunc (singularObservable x₀ β) ((epsCut k : ℝ) *
            positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) α n) y
              ∂μ.withDensity d.weight + mk k n)
    (hmk : ∀ k, Tendsto (fun n => mk k n) atTop (𝓝 (mlim k)))
    (hZ : TendstoInDistribution (fun k ω => cutIntegral k (randomMeasure.toFun ω) - mlim k)
      atTop W (fun _ => powerLaw α hα) (powerLaw α hα)) :
    TendstoInDistribution
      (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) α n)⁻¹ *
        (pathBirkhoffSum (singularObservable x₀ β) n ω - c n)) atTop W
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw α hα) := by
  subst hαdef
  set α := dimension / β
  set Cc := volumeConstant * (d.weight x₀).toReal * m x₀
  have hC : 0 < Cc := mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _)))
    hadm.2.1
  set f := singularObservable x₀ β
  have hfm : Measurable f := measurable_singularObservable x₀ β
  have hfpos : ∀ z, 0 < f z := singularObservable_pos x₀ β
  set B := positivePowerScale Cc α
  have hB : ∀ n, 0 < B n := positivePowerScale_pos hC
  set P : ℕ → Measure (Path M) := fun n =>
    (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))
  set Q := powerLaw α hα
  set N : ℕ → RandomPointMeasure (Path M) := fun n => pathEmpirical f hfm hfpos n (B n) (hB n)
  have hcounts := fun (k : ℕ) (a b : Fin k → ExtremeState) (hab : ∀ j, a j < b j)
      (hdis : Pairwise fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) =>
    C.poisson_interval_counts_of_admissibility h d s.continuous_weight μ hleft hnorm m hm hm0 hμ x
      hadm hx₀ hβ k a b hab hdis
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  obtain ⟨K, hK, hsmall⟩ := compensated_small_jumps_eventually C h d s hlive μ hleft hnorm x hβ
    hx₀ hC hα hα2 htail
  refine tendstoInDistribution_of_double_probability_approximation P Q Q
    (fun n ω => (B n)⁻¹ * (pathBirkhoffSum f n ω - c n))
    (fun k n ω => cutIntegral k ((N n).toFun ω) - mk k n)
    (fun k ω => cutIntegral k (randomMeasure.toFun ω) - mlim k) W
    (fun n => ((measurable_pathBirkhoffSum hfm n).sub_const _).const_mul _)
    (fun k n => ((measurable_cutIntegral k).comp (N n).measurable).sub_const _)
    (fun k => ((measurable_cutIntegral k).comp randomMeasure.measurable).sub_const _)
    (fun k => ?_) hZ ?_
  · -- Middle jumps, with converging centring constants.
    have hmid := (TruncatedPointIntegrals.tendstoInDistribution_truncatedIntegral_of_disjoint_counts
      P Q N randomMeasure hcounts (epsCut k) (RCut k) (epsCut_pos k)
        (epsCut_le_RCut k)).continuous_comp (continuous_sub_right (mlim k))
    refine tendstoInDistribution_of_varying_probability_approximation P Q _
      (fun n ω => cutIntegral k ((N n).toFun ω) - mlim k) _
      (fun n => ((measurable_cutIntegral k).comp (N n).measurable).sub_const _)
      (fun n => ((measurable_cutIntegral k).comp (N n).measurable).sub_const _) hmid ?_
    intro ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(hmk k).eventually (Metric.ball_mem_nhds _ hε)] with n hn
    have hempty : {ω | ε < |cutIntegral k ((N n).toFun ω) - mk k n -
        (cutIntegral k ((N n).toFun ω) - mlim k)|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      rw [show cutIntegral k ((N n).toFun ω) - mk k n - (cutIntegral k ((N n).toFun ω) - mlim k)
        = -(mk k n - mlim k) by ring, abs_neg]
      exact (Metric.mem_ball.1 hn).le
    rw [hempty, measureReal_empty]
  · intro ε' δ hε' hδ
    have h2α : 0 < 2 - α := sub_pos.2 hα2
    set Sk : ℕ → ℝ := fun k => K * ((epsCut k : ℝ) ^ (2 - α) + (epsCut k : ℝ) ^ 2) / ε' ^ 2
    set Lk : ℕ → ℝ := fun k => (RCut k : ℝ) ^ (-α)
    have hSk : Tendsto Sk atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => (epsCut k : ℝ) ^ (2 - α)) atTop (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 (2 - α) (Or.inr h2α.le)).tendsto.comp
          CompensatedPoissonLimits.tendsto_epsCut
        rw [Real.zero_rpow h2α.ne'] at this
        exact this
      have h2 : Tendsto (fun k : ℕ => (epsCut k : ℝ) ^ 2) atTop (𝓝 0) := by
        simpa using CompensatedPoissonLimits.tendsto_epsCut.pow 2
      have := ((h1.add h2).const_mul K).div_const (ε' ^ 2)
      simpa [Sk] using this
    have hLk : Tendsto Lk atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hα).comp CompensatedPoissonLimits.tendsto_RCut
    have hev : ∀ᶠ k in atTop, Sk k + 2 * Lk k < δ := by
      have := hSk.add (hLk.const_mul 2)
      simp only [mul_zero, add_zero] at this
      exact this.eventually (gt_mem_nhds hδ)
    filter_upwards [hev] with k hk
    have hRk : 0 < RCut k := (epsCut_pos k).trans_le (epsCut_le_RCut k)
    set A : Set ExtremeState := Ioc (TruncatedPointIntegrals.endpoint (RCut k) hRk) ⊤
    have hAm : MeasurableSet A := measurableSet_Ioc
    have h1 := hsmall (epsCut k) (by exact_mod_cast epsCut_pos k) ε' hε'
    have hlt : TruncatedPointIntegrals.endpoint (RCut k) hRk < (⊤ : ExtremeState) := by
      refine lt_of_le_of_ne le_top fun heq => ?_
      have := congrArg Subtype.val heq
      exact ENNReal.coe_ne_top this
    have hc1 := hcounts 1 (fun _ => TruncatedPointIntegrals.endpoint (RCut k) hRk) (fun _ => ⊤)
      (fun _ => hlt) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    have hlim := tendsto_prob_of_tendstoInDistribution_nat hc1 {v | 1 ≤ v 0}
    have hQ : Q.real ((fun ω j => (randomMeasure.toFun ω).countOn
        (Ioc ((fun _ : Fin 1 => TruncatedPointIntegrals.endpoint (RCut k) hRk) j)
          ((fun _ : Fin 1 => (⊤ : ExtremeState)) j))) ⁻¹' {v | 1 ≤ v 0}) ≤ Lk k := by
      have hfinA : powerIntensity α A ≠ ∞ := by
        refine ne_top_of_le_ne_top (powerIntensity_tail_lt_top hα (RCut k) hRk).ne
          (measure_mono fun y hy => ?_)
        exact le_of_lt hy.1
      have := prob_count_pos_le (powerIntensity_tail_lt_top hα) hAm hfinA
      rw [NormalizationBridge.powerIntensity_real_Ioc_top hα _ ENNReal.coe_ne_top] at this
      exact this
    have h2 : ∀ᶠ n in atTop, (P n).real {ω | 1 ≤ ((N n).toFun ω).countOn A} < 2 * Lk k := by
      have hLpos : 0 < Lk k := Real.rpow_pos_of_pos (by exact_mod_cast hRk) _
      exact hlim.eventually (gt_mem_nhds (show Q.real _ < 2 * Lk k by linarith [hQ]))
    filter_upwards [h1, h2] with n hn1 hn2
    set Ys : Path M → ℝ := fun ω => (B n)⁻¹ * pathBirkhoffSum (trunc f ((epsCut k : ℝ) * B n)) n ω -
      n * (B n)⁻¹ * ∫ y, trunc f ((epsCut k : ℝ) * B n) y ∂μ.withDensity d.weight
    have hsub : {ω | ε' < |(B n)⁻¹ * (pathBirkhoffSum f n ω - c n) -
        (cutIntegral k ((N n).toFun ω) - mk k n)|} ≤ᵐ[P n]
        ({ω | ε' < |Ys ω|} ∪ {ω | 1 ≤ ((N n).toFun ω).countOn A} : Set (Path M)) := by
      filter_upwards [C.ae_survival_conditionedMeasure x.val n] with ω hω hmem
      rcases decomposition_eq hfm hfpos (hB n) (epsCut_pos k) (epsCut_le_RCut k) hω with
        hcount | heq
      · exact Or.inr hcount
      · left
        have hmem' : ε' < |(B n)⁻¹ * (pathBirkhoffSum f n ω - c n) -
            (cutIntegral k ((N n).toFun ω) - mk k n)| := hmem
        have hrw : (B n)⁻¹ * (pathBirkhoffSum f n ω - c n) -
            (cutIntegral k ((N n).toFun ω) - mk k n) =
            ((B n)⁻¹ * pathBirkhoffSum f n ω - cutIntegral k ((N n).toFun ω)) -
              ((B n)⁻¹ * c n - mk k n) := by ring
        rw [hrw, hc k n] at hmem'
        unfold cutIntegral at hmem'
        rw [heq] at hmem'
        show ε' < |Ys ω|
        simpa only [Ys, add_sub_cancel_right] using hmem'
    calc (P n).real {ω | ε' < |(B n)⁻¹ * (pathBirkhoffSum f n ω - c n) -
          (cutIntegral k ((N n).toFun ω) - mk k n)|}
        ≤ (P n).real ({ω | ε' < |Ys ω|} ∪ {ω | 1 ≤ ((N n).toFun ω).countOn A}) :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
      _ ≤ (P n).real {ω | ε' < |Ys ω|} + (P n).real {ω | 1 ≤ ((N n).toFun ω).countOn A} :=
          measureReal_union_le _ _
      _ < Sk k + 2 * Lk k := by
          have : (P n).real {ω | ε' < |Ys ω|} ≤ Sk k := hn1
          linarith
      _ < δ := hk

/-- **Stable law, α = 1.** If `α = d/β = 1`, then for every `x ∈ M \ Z`, under `ℙₓ(· | τ > n)`,
`B_n⁻¹ (∑_{j<n} f_β(X_j) - A_n) → Z₁` in distribution, where `B_n = C(x₀) n`, `A_n = n ν(f_β 1_{f_β
≤ B_n})` and `Z₁ = lim_{ε→0} (∫_{(ε,∞]} y N(dy) - ∫_{(ε,1]} y υ_1(dy))`. -/
theorem stable_law_one (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : dimension / β = 1) :
    TendstoInDistribution
      (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n)⁻¹ *
        (pathBirkhoffSum (singularObservable x₀ β) n ω - n * ∫ y,
          {y | singularObservable x₀ β y ≤
            positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀) 1 n}.indicator
            (singularObservable x₀ β) y ∂μ.withDensity d.weight)) atTop
      (unitCompensatedStable 1 one_pos)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw 1 one_pos) := by
  set Cc := volumeConstant * (d.weight x₀).toReal * m x₀
  have hC : 0 < Cc := mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _)))
    hadm.2.1
  set f := singularObservable x₀ β
  set ν := μ.withDensity d.weight
  have : IsFiniteMeasure ν :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
        exact ENNReal.one_lt_top⟩
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  rw [hα1] at htail
  set B := positivePowerScale Cc 1
  refine stable_law_of_compensation C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ hα1
    one_pos (by norm_num) _
    (fun k n => (n : ℝ) / B n * ((∫ y, {y | f y ≤ B n}.indicator f y ∂ν) -
      ∫ y, {y | f y ≤ (epsCut k : ℝ) * B n}.indicator f y ∂ν))
    (fun k => ∫ y, bandMark (epsCut k) y ∂powerIntensity 1) _ (fun k n => ?_) (fun k => ?_)
    (CompensatedPoissonLimits.cut_unitCompensated_tendstoInDistribution one_pos (by norm_num))
  · simp only [trunc]
    ring
  · rw [CompensatedPoissonLimits.bandMark_integral_one (by exact_mod_cast epsCut_pos k)
      (CompensatedPoissonLimits.epsCut_le_one k)]
    exact CompensationAsymptotics.scaled_band_mean (measurable_singularObservable x₀ β)
      (fun z => (singularObservable_pos x₀ β z).le) hC htail (by exact_mod_cast epsCut_pos k)
      (CompensatedPoissonLimits.epsCut_le_one k)

/-- **Stable law, 1 < α < 2.** If `1 < α = d/β < 2`, then `f_β ∈ L¹(ν)` and, for every `x ∈ M \ Z`,
under `ℙₓ(· | τ > n)`, `B_n⁻¹ (∑_{j<n} f_β(X_j) - n ν(f_β)) → Z_α` in distribution, where `B_n =
(C(x₀) n)^{1/α}` and `Z_α = lim_{ε→0} (∫_{(ε,∞]} y N(dy) - ∫_{(ε,∞]} y υ_α(dy))`. -/
theorem stable_law_mid (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : 1 < dimension / β) (hα2 : dimension / β < 2) :
    Integrable (singularObservable x₀ β) (μ.withDensity d.weight) ∧
    TendstoInDistribution
      (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
          (dimension / β) n)⁻¹ *
        (pathBirkhoffSum (singularObservable x₀ β) n ω -
          n * ∫ y, singularObservable x₀ β y ∂μ.withDensity d.weight)) atTop
      (fullyCompensatedStable (dimension / β) (zero_lt_one.trans hα1))
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw (dimension / β) (zero_lt_one.trans hα1)) := by
  set α := dimension / β
  have hα : 0 < α := zero_lt_one.trans hα1
  set Cc := volumeConstant * (d.weight x₀).toReal * m x₀
  have hC : 0 < Cc := mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _)))
    hadm.2.1
  set f := singularObservable x₀ β
  have hfm : Measurable f := measurable_singularObservable x₀ β
  have hf0 : ∀ z, 0 ≤ f z := fun z => (singularObservable_pos x₀ β z).le
  set ν := μ.withDensity d.weight
  have : IsFiniteMeasure ν :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
        exact ENNReal.one_lt_top⟩
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  refine ⟨integrable_of_power_tail_asymptotic ν f hfm hf0 Cc α hC hα1 htail, ?_⟩
  set B := positivePowerScale Cc α
  refine stable_law_of_compensation C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ rfl
    hα hα2 _
    (fun k n => (n : ℝ) / B n * ((∫ y, f y ∂ν) -
      ∫ y, {y | f y ≤ (epsCut k : ℝ) * B n}.indicator f y ∂ν))
    (fun k => ∫ y, tailMark (epsCut k) y ∂powerIntensity α) _ (fun k n => ?_) (fun k => ?_)
    (CompensatedPoissonLimits.cut_fullyCompensated_tendstoInDistribution hα hα1 hα2)
  · simp only [trunc]
    ring
  · rw [CompensatedPoissonLimits.tailMark_integral hα1 (by exact_mod_cast epsCut_pos k)]
    exact CompensationAsymptotics.scaled_tail_mean hfm hf0 hC hα1 htail
      (by exact_mod_cast epsCut_pos k)

end Main

end

end ConditionedStableLaws.StableLawCompensated
