import ConditionedStableLaws.ConditionedSingle
import ConditionedStableLaws.ChainPoissonProcess
import ConditionedStableLaws.TruncatedPointIntegrals
import ConditionedStableLaws.PositiveStableLaw
import ConditionedStableLaws.ConvergingTogether
import ConditionedStableLaws.FirstMoments

/-!
# The conditional stable law for `0 < α < 1`

Under `ℙₓ(· | τ > n)`, `B_n⁻¹ ∑_{j<n} f_β(X_j) → Z_α = ∫ y N(dy)`, where `N` is the Poisson random
measure with intensity `α y^{-α-1} dy`; the Laplace transform of `Z_α` is `exp(-Γ(1-α) t^α)`. Jumps
in `(ε, R]` converge by the point-process theorem; small jumps are controlled in mean by the
single-observation estimate and the truncated first moment; large jumps by the point-process limit
of the count on `(R, ∞]`; and the pieces are combined by the converging-together theorem.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.StableLawSmall

noncomputable section

open StandingHypothesis CanonicalChain NormalizationBridge

/-! ### Jump integrals of empirical point measures -/

section Empirical

theorem truncatedIntegral_empirical {n : ℕ} (a b : ExtremeState) (obs : Fin n → ExtremeState) :
    TruncatedPointIntegrals.truncatedIntegral a b (LocallyFinitePointMeasure.empirical obs) =
      ∑ i, (Ioc a b).indicator (fun y : ExtremeState => y.val.toReal) (obs i) := by
  unfold TruncatedPointIntegrals.truncatedIntegral
  rw [← integral_indicator measurableSet_Ioc]
  change ∫ y, (Ioc a b).indicator (fun y : ExtremeState => y.val.toReal) y
    ∂(Measure.sum fun i => Measure.dirac (obs i)) = _
  rw [Measure.sum_fintype, MeasureTheory.integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i _
    exact integrable_dirac (by simp)

theorem one_le_countOn_empirical {n : ℕ} {A : Set ExtremeState} (obs : Fin n → ExtremeState)
    (hA : MeasurableSet A) {i : Fin n} (hi : obs i ∈ A) :
    1 ≤ (LocallyFinitePointMeasure.empirical obs).countOn A := by
  have hle : (1 : ℝ≥0∞) ≤ (LocallyFinitePointMeasure.empirical obs).toMeasure A := by
    change 1 ≤ Measure.sum (fun j => Measure.dirac (obs j)) A
    calc (1 : ℝ≥0∞) = Measure.dirac (obs i) A := by rw [Measure.dirac_apply_of_mem hi]
      _ ≤ Measure.sum (fun j => Measure.dirac (obs j)) A := Measure.le_sum (fun j => Measure.dirac (obs j)) i A
  have hfin : (LocallyFinitePointMeasure.empirical obs).toMeasure A < ∞ := by
    change Measure.sum (fun j => Measure.dirac (obs j)) A < ∞
    rw [Measure.sum_apply _ hA, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun j _ => measure_lt_top _ _
  have h := LocallyFinitePointMeasure.countOn_eq_measure _ hA hfin
  rw [← h] at hle
  exact_mod_cast hle

end Empirical

/-! ### Pathwise decomposition into small, middle and large jumps -/

section Pathwise

variable {M : Type*} [MeasurableSpace M]

theorem mem_Ioc_endpoints {ε R : ℝ≥0} (hε : 0 < ε) (hR : 0 < R) {y : ℝ} (hy : 0 < y) :
    (⟨ENNReal.ofReal y, ENNReal.ofReal_pos.2 hy⟩ : ExtremeState) ∈
        Ioc (TruncatedPointIntegrals.endpoint ε hε) (TruncatedPointIntegrals.endpoint R hR) ↔
      (ε : ℝ) < y ∧ y ≤ R := by
  simp only [mem_Ioc, TruncatedPointIntegrals.endpoint, ← Subtype.coe_lt_coe,
    ← Subtype.coe_le_coe]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := R),
    ENNReal.ofReal_lt_ofReal_iff hy, ENNReal.ofReal_le_ofReal_iff R.coe_nonneg]

theorem mem_Ioc_top {R : ℝ≥0} (hR : 0 < R) {y : ℝ} (hy : 0 < y) :
    (⟨ENNReal.ofReal y, ENNReal.ofReal_pos.2 hy⟩ : ExtremeState) ∈
        Ioc (TruncatedPointIntegrals.endpoint R hR) ⊤ ↔ (R : ℝ) < y := by
  simp only [mem_Ioc, le_top, and_true, TruncatedPointIntegrals.endpoint, ← Subtype.coe_lt_coe]
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hy]

theorem measurableSet_Ioc_extreme (a b : ExtremeState) : MeasurableSet (Ioc a b) :=
  measurableSet_Ioc

/-- On a surviving path, if the normalized sum differs from its middle-jump
part by more than `δ`, then either the small jumps exceed `δ` or some
normalized observation exceeds `R`. -/
theorem decomposition {f : M → ℝ} (hm : Measurable f) (hf : ∀ x, 0 < f x) {n : ℕ} {B : ℝ}
    (hB : 0 < B) {ε R : ℝ≥0} (hε : 0 < ε) (hεR : ε ≤ R) {ω : Path M} (hω : ω ∈ survival n)
    {δ : ℝ} (hδ : δ < |B⁻¹ * pathBirkhoffSum f n ω -
      TruncatedPointIntegrals.truncatedIntegral (TruncatedPointIntegrals.endpoint ε hε)
        (TruncatedPointIntegrals.endpoint R (hε.trans_le hεR))
        ((pathEmpirical f hm hf n B hB).toFun ω)|) :
    δ < B⁻¹ * pathBirkhoffSum ({z | f z ≤ ε * B}.indicator f) n ω ∨
      1 ≤ ((pathEmpirical f hm hf n B hB).toFun ω).countOn
        (Ioc (TruncatedPointIntegrals.endpoint R (hε.trans_le hεR)) ⊤) := by
  have hR : 0 < R := hε.trans_le hεR
  set y : Fin n → ℝ := fun i => positiveExtension f (ω i) / B
  have hy (i : Fin n) : 0 < y i := div_pos (positiveExtension_pos hf _) hB
  have hemp : (pathEmpirical f hm hf n B hB).toFun ω =
      LocallyFinitePointMeasure.empirical (fun i => ⟨ENNReal.ofReal (y i), ENNReal.ofReal_pos.2 (hy i)⟩) :=
    rfl
  by_cases hlarge : ∃ i, (R : ℝ) < y i
  · obtain ⟨i, hi⟩ := hlarge
    right
    rw [hemp]
    exact one_le_countOn_empirical _ (measurableSet_Ioc_extreme _ _)
      (i := i) ((mem_Ioc_top hR (hy i)).2 hi)
  left
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
  have hsmall : B⁻¹ * pathBirkhoffSum ({z | f z ≤ ε * B}.indicator f) n ω =
      ∑ i, if y i ≤ ε then y i else 0 := by
    unfold pathBirkhoffSum birkhoffSum
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
  rw [hsum, hmid, ← Finset.sum_sub_distrib] at hδ
  rw [hsmall]
  have heq : (∑ i, (y i - if (ε : ℝ) < y i then y i else 0)) = ∑ i, if y i ≤ ε then y i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (ε : ℝ) < y i
    · rw [ite_eq_left hi, ite_eq_right (not_le.2 hi), sub_self]
    · rw [ite_eq_right hi, ite_eq_left (not_lt.1 hi), sub_zero]
  rw [heq, abs_of_nonneg (Finset.sum_nonneg fun i _ => by split_ifs <;> linarith [hy i])] at hδ
  exact hδ

end Pathwise

/-! ### Small jumps -/

section SmallJumps

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Small jumps**: there is `K ≥ 0` such that for every `ε, δ > 0`, eventually `ℙₓ,ₙ(B_n⁻¹ ∑
f(X_i) 1{f(X_i) ≤ ε B_n} > δ) ≤ (2 α/(1-α) ε^{1-α} + K ε)/δ`. -/
theorem small_jumps_eventually (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    (x : d.State) {f : M → ℝ} (hm : Measurable f) (hf : ∀ z, 0 < f z)
    {B : ℕ → ℝ} (hB : ∀ n, 0 < B n) (hBlim : Tendsto B atTop atTop) {α : ℝ}
    (hmom : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ) *
      (∫ y, {y | f y ≤ ε * B n}.indicator f y ∂μ.withDensity d.weight) / B n) atTop
      (𝓝 (α / (1 - α) * ε ^ (1 - α)))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      (C.conditionedMeasure x.val n).real
        {ω | δ < (B n)⁻¹ * pathBirkhoffSum ({z | f z ≤ ε * B n}.indicator f) n ω} ≤
        (2 * (α / (1 - α) * ε ^ (1 - α)) + K * ε) / δ := by
  obtain ⟨D, θ, hD, hθ0, hθ1, hapos, halim, hsingle⟩ :=
    ConditionedSingle.conditioned_single_le C h d s hlive μ hleft hnorm x
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  have := fun n => C.conditionedMeasure_isProbability_of_surviving x.val hx n
  set ηx := (d.weight x.val).toReal
  have hηx : 0 < ηx := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  refine ⟨3 + 2 * D / (1 - θ), by have := sub_pos.2 hθ1; positivity, fun ε hε δ hδ => ?_⟩
  set L := α / (1 - α) * ε ^ (1 - α)
  -- Eventual estimates for the three terms.
  have hratio : Tendsto (fun n => ηx / ConditionedSingle.normalizedMass C d n x.val) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := ηx)).div halim hηx.ne'
    rw [div_self hηx.ne'] at this
    exact this
  have h1 : ∀ᶠ n in atTop, ηx / ConditionedSingle.normalizedMass C d n x.val ≤ 2 :=
    hratio.eventually (ge_mem_nhds (by norm_num))
  have h2 : ∀ᶠ n : ℕ in atTop, (n : ℝ) *
      (∫ y, {y | f y ≤ ε * B n}.indicator f y ∂μ.withDensity d.weight) / B n ≤ L + ε / 2 :=
    (hmom ε hε).eventually (ge_mem_nhds (by linarith))
  have h3 : ∀ᶠ n : ℕ in atTop, f x.val / B n ≤ ε := by
    have : Tendsto (fun n => f x.val / B n) atTop (𝓝 0) := hBlim.const_div_atTop _
    exact this.eventually (ge_mem_nhds hε)
  filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
  set g : M → ℝ := {z | f z ≤ ε * B n}.indicator f
  have hgm : Measurable g := hm.indicator (measurableSet_le hm measurable_const)
  have hg0 (z : M) : 0 ≤ g z := Set.indicator_nonneg (fun z _ => (hf z).le) z
  have hgH (z : M) : g z ≤ ε * B n := by
    by_cases hz : f z ≤ ε * B n
    · simp only [g, Set.indicator_of_mem (show z ∈ {z | f z ≤ ε * B n} from hz)]; exact hz
    · simp only [g, Set.indicator_of_notMem (show z ∉ {z | f z ≤ ε * B n} from hz)]
      exact mul_nonneg hε.le (hB n).le
  have hgx : g x.val ≤ f x.val := by
    by_cases hz : f x.val ≤ ε * B n
    · simp only [g, Set.indicator_of_mem (show x.val ∈ {z | f z ≤ ε * B n} from hz), le_refl]
    · simp only [g, Set.indicator_of_notMem (show x.val ∉ {z | f z ≤ ε * B n} from hz)]
      exact (hf _).le
  set G : M → ℝ≥0∞ := fun z => ENNReal.ofReal (g z)
  set Sm : Path M → ℝ := fun ω => (B n)⁻¹ * pathBirkhoffSum g n ω
  have hSm0 (ω : Path M) : 0 ≤ Sm ω := by
    refine mul_nonneg (inv_nonneg.2 (hB n).le) ?_
    unfold pathBirkhoffSum birkhoffSum
    exact Finset.sum_nonneg fun i _ => by cases ω i <;> simp [zeroExtension, hg0]
  have hSmm : Measurable Sm := (measurable_pathBirkhoffSum hgm n).const_mul _
  have hSsum (ω : Path M) : pathBirkhoffSum g n ω ≤ n * (ε * B n) := by
    unfold pathBirkhoffSum birkhoffSum
    calc ∑ i ∈ Finset.range n, zeroExtension g (ω i) ≤ ∑ _i ∈ Finset.range n, ε * B n := by
          apply Finset.sum_le_sum
          intro i _
          cases ω i with
          | none => simp only [zeroExtension_none]; exact mul_nonneg hε.le (hB n).le
          | some z => rw [zeroExtension_some]; exact hgH z
      _ = n * (ε * B n) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSint : Integrable Sm (C.conditionedMeasure x.val n) :=
    Integrable.of_bound hSmm.aestronglyMeasurable (n * ε) (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hSm0 ω)]
      calc Sm ω = (B n)⁻¹ * pathBirkhoffSum g n ω := rfl
        _ ≤ (B n)⁻¹ * (n * (ε * B n)) := mul_le_mul_of_nonneg_left (hSsum ω) (inv_nonneg.2 (hB n).le)
        _ = n * ε := by
          rw [show (B n)⁻¹ * (↑n * (ε * B n)) = ↑n * ε * (B n * (B n)⁻¹) by ring,
            mul_inv_cancel₀ (hB n).ne', mul_one])
  -- Markov's inequality.
  have hmarkov : (C.conditionedMeasure x.val n).real {ω | δ < Sm ω} ≤
      (∫ ω, Sm ω ∂C.conditionedMeasure x.val n) / δ := by
    rw [le_div_iff₀ hδ, mul_comm]
    refine le_trans ?_ (mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hSm0) hSint δ)
    exact mul_le_mul_of_nonneg_left
      (measureReal_mono fun ω (hω : δ < Sm ω) => (le_of_lt hω : δ ≤ Sm ω)) hδ.le
  -- The expectation, term by term.
  have hzm (i : ℕ) : Measurable (fun ω : Path M => zeroExtension g (ω i)) :=
    (measurable_zeroExtension hgm).comp (measurable_pi_apply i)
  have hterm (i : ℕ) : ∫ ω, zeroExtension g (ω i) ∂C.conditionedMeasure x.val n =
      (∫⁻ ω, PathMixing.liveExtension G (ω i) ∂C.conditionedMeasure x.val n).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω : Path M => zeroExtension g (ω i))
      (Eventually.of_forall fun ω => by
        show 0 ≤ zeroExtension g (ω i)
        cases ω i <;> simp [zeroExtension, hg0]) (hzm i).aestronglyMeasurable]
    congr 1
    apply lintegral_congr
    intro ω
    exact RefinedLLN.ofReal_zeroExtension g (ω i)
  have hint_i (i : ℕ) : Integrable (fun ω : Path M => zeroExtension g (ω i))
      (C.conditionedMeasure x.val n) :=
    Integrable.of_bound (hzm i).aestronglyMeasurable
      (ε * B n) (Eventually.of_forall fun ω => by
        show ‖zeroExtension g (ω i)‖ ≤ ε * B n
        cases ω i with
        | none => simp only [zeroExtension_none, norm_zero]; exact mul_nonneg hε.le (hB n).le
        | some z => rw [zeroExtension_some, Real.norm_of_nonneg (hg0 z)]; exact hgH z)
  have hE : ∫ ω, Sm ω ∂C.conditionedMeasure x.val n =
      (B n)⁻¹ * ∑ i ∈ Finset.range n,
        (∫⁻ ω, PathMixing.liveExtension G (ω i) ∂C.conditionedMeasure x.val n).toReal := by
    simp only [Sm, pathBirkhoffSum, birkhoffSum]
    rw [integral_const_mul, MeasureTheory.integral_finsetSum _ fun i _ => hint_i i]
    simp_rw [hterm]
  have hzero : (∫⁻ ω, PathMixing.liveExtension G (ω 0) ∂C.conditionedMeasure x.val n).toReal =
      g x.val := by
    rw [RefinedLLN.lintegral_conditioned_single C x.val (Nat.zero_le n)
      (hgm.ennreal_ofReal : Measurable G)]
    have hK0 : (C.killedTransition ^ 0) x.val = Measure.dirac x.val := rfl
    have hmeas : Measurable (fun y => ENNReal.ofReal (g y) * (C.killedTransition ^ (n - 0)) y univ) :=
      hgm.ennreal_ofReal.mul ((C.killedTransition ^ (n - 0)).measurable_coe MeasurableSet.univ)
    rw [hK0, lintegral_dirac' _ hmeas, Nat.sub_zero]
    have hpos := C.pathMeasure_survival_pos x.val hx n
    rw [C.pathMeasure_survival] at hpos
    have hfin : (C.killedTransition ^ n) x.val univ ≠ ∞ :=
      ((C.killedTransition_pow_mass_le_one x.val n).trans_lt ENNReal.one_lt_top).ne
    rw [mul_comm (G x.val), ← mul_assoc, ENNReal.inv_mul_cancel hpos.ne' hfin, one_mul,
      ENNReal.toReal_ofReal (hg0 _)]
  set νg := ∫ y, g y ∂μ.withDensity d.weight
  have hνg0 : 0 ≤ νg := integral_nonneg hg0
  set a := ConditionedSingle.normalizedMass C d n x.val
  have hgeo (m : ℕ) : ∑ i ∈ Finset.range m, θ ^ i ≤ (1 - θ)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hθ0 hθ1]
    exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hθ0 j) (summable_geometric_of_lt_one hθ0 hθ1)
  have hsumE : ∑ i ∈ Finset.range n,
      (∫⁻ ω, PathMixing.liveExtension G (ω i) ∂C.conditionedMeasure x.val n).toReal ≤
      g x.val + n * (ηx / a * νg) + D * (ε * B n) * (2 * (1 - θ)⁻¹) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero]
      have h1 := hg0 x.val
      have h2 : 0 ≤ D * (ε * B 0) * (2 * (1 - θ)⁻¹) :=
        mul_nonneg (mul_nonneg hD (mul_nonneg hε.le (hB 0).le))
          (mul_nonneg zero_le_two (inv_nonneg.2 (sub_pos.2 hθ1).le))
      linarith
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hnpos
    simp only [zero_add] at *
    rw [Finset.sum_range_succ', hzero]
    have hb : ∀ i ∈ Finset.range m,
        (∫⁻ ω, PathMixing.liveExtension G (ω (i + 1)) ∂C.conditionedMeasure x.val (m + 1)).toReal ≤
        ηx / a * νg + D * (ε * B (m + 1)) * (θ ^ i + θ ^ (m - 1 - i)) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have h' := hsingle g hgm hg0 (ε * B (m + 1)) hgH (m + 1) (i + 1) (by omega) (by omega)
      have e1 : i + 1 - 1 = i := by omega
      have e2 : m + 1 - 1 - (i + 1) = m - 1 - i := by omega
      rw [e1, e2] at h'
      simp only [G, a, νg, zero_add]
      exact h'
    have hs := Finset.sum_le_sum hb
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib] at hs
    have hrefl : ∑ i ∈ Finset.range m, θ ^ (m - 1 - i) = ∑ i ∈ Finset.range m, θ ^ i :=
      Finset.sum_range_reflect (fun i => θ ^ i) m
    rw [hrefl] at hs
    have hDε : 0 ≤ D * (ε * B (m + 1)) := mul_nonneg hD (mul_nonneg hε.le (hB _).le)
    have hpart : D * (ε * B (m + 1)) * (∑ i ∈ Finset.range m, θ ^ i + ∑ i ∈ Finset.range m, θ ^ i) ≤
        D * (ε * B (m + 1)) * (2 * (1 - θ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hDε
      linarith [hgeo m]
    have hprod : 0 ≤ ηx / a * νg := mul_nonneg (div_nonneg hηx.le (hapos _).le) hνg0
    push_cast
    nlinarith [hs, hpart, hprod]
  -- Assemble the bound.
  rw [hE] at hmarkov
  refine hmarkov.trans ?_
  apply div_le_div_of_nonneg_right _ hδ.le
  have hBn := hB n
  have h2' : (n : ℝ) * νg / B n ≤ L + ε / 2 := hn2
  calc (B n)⁻¹ * ∑ i ∈ Finset.range n,
        (∫⁻ ω, PathMixing.liveExtension G (ω i) ∂C.conditionedMeasure x.val n).toReal
      ≤ (B n)⁻¹ * (g x.val + n * (ηx / a * νg) + D * (ε * B n) * (2 * (1 - θ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hsumE (inv_nonneg.2 hBn.le)
    _ = g x.val / B n + ηx / a * (n * νg / B n) + 2 * D * ε / (1 - θ) := by
        have h1 : B n ≠ 0 := hBn.ne'
        have h2 : a ≠ 0 := (hapos n).ne'
        have h3 : 1 - θ ≠ 0 := (sub_pos.2 hθ1).ne'
        field_simp
    _ ≤ ε + 2 * (L + ε / 2) + 2 * D * ε / (1 - θ) := by
        have hgB : g x.val / B n ≤ ε := (div_le_div_of_nonneg_right hgx hBn.le).trans hn3
        have hmid : ηx / a * (n * νg / B n) ≤ 2 * (L + ε / 2) := by
          have hnn : 0 ≤ (n : ℝ) * νg / B n := by positivity
          exact mul_le_mul hn1 h2' hnn (by norm_num)
        linarith
    _ ≤ 2 * L + (3 + 2 * D / (1 - θ)) * ε := by
        have : 2 * D * ε / (1 - θ) = 2 * D / (1 - θ) * ε := by ring
        nlinarith

end SmallJumps

/-!
### The truncated first moment at the stable scale
-/

section TruncatedMean

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `n ν(f 1{f ≤ ε Bₙ}) / Bₙ → α/(1-α) ε^{1-α}` for `0 < α < 1`, from the power tail. -/
theorem truncated_mean_scaled {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {Cc α : ℝ} (hC : 0 < Cc) (hα : 0 < α)
    (hα1 : α < 1)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (Cc * t ^ (-α))) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (∫ y, {y | f y ≤ ε * positivePowerScale Cc α n}.indicator f y ∂ν) /
        positivePowerScale Cc α n) atTop (𝓝 (α / (1 - α) * ε ^ (1 - α))) := by
  set B := positivePowerScale Cc α
  have hm := truncated_first_moment_div_rpow_tendsto (μ := ν) f hf hf0 Cc α hC hα1 htail
  have harg : Tendsto (fun n : ℕ => ε * B n) atTop atTop :=
    (positivePowerScale_tendsto_atTop hC hα).const_mul_atTop hε
  have hcomp := (hm.comp harg).mul_const (ε ^ (1 - α) / Cc)
  have hval : α * Cc / (1 - α) * (ε ^ (1 - α) / Cc) = α / (1 - α) * ε ^ (1 - α) := by
    field_simp
  rw [hval] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [positivePowerScale_eventually_eq Cc α, eventually_gt_atTop 0] with n hn hn0
  have hBpos : 0 < B n := positivePowerScale_pos hC n
  have hBα : B n ^ α = Cc * n := by
    simp only [B]
    rw [hn, powerScale_rpow hC.le hα.ne']
  set T := ∫ y, {y | f y ≤ ε * B n}.indicator f y ∂ν
  simp only [Function.comp_apply]
  have hpow : (ε * B n) ^ (1 - α) = ε ^ (1 - α) * (B n ^ α)⁻¹ * B n := by
    rw [Real.mul_rpow hε.le hBpos.le, Real.rpow_sub hBpos, Real.rpow_one, div_eq_mul_inv]
    ring
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hεp : ε ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hε _).ne'
  rw [hpow, hBα]
  field_simp
  rfl

end TruncatedMean

/-! ### Large jumps -/

section LargeJumps

/-- Convergence in distribution of natural count vectors gives convergence of
the probability of any event, since the count space is discrete. -/
theorem tendsto_prob_of_tendstoInDistribution_nat {k : ℕ}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {X : ∀ n, Ω n → (Fin k → ℕ)} {Y : Ω' → (Fin k → ℕ)}
    (h : TendstoInDistribution X atTop Y P Q) (S : Set (Fin k → ℕ)) :
    Tendsto (fun n => (P n).real (X n ⁻¹' S)) atTop (𝓝 (Q.real (Y ⁻¹' S))) := by
  have hS : frontier S = ∅ := (isClopen_discrete S).frontier_eq
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto
    (E := S) (by rw [hS, measure_empty])
  simp only [ProbabilityMeasure.coe_mk] at hlim
  rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit (DiscreteMeasurableSpace.forall_measurableSet S)] at hlim
  have hlim' := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim
  refine hlim'.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n)
    (DiscreteMeasurableSpace.forall_measurableSet S)]
  rfl

/-- A Poisson random measure charges a set of intensity `r` with probability at most `r`. -/
theorem prob_count_pos_le {υ : Measure ExtremeState} (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)
    {A : Set ExtremeState} (hA : MeasurableSet A) (hfin : υ A ≠ ∞) :
    (AnnularPoissonClouds.law υ hυ).real
      {ω | 1 ≤ (AnnularPoissonClouds.randomMeasure.toFun ω).countOn A} ≤ υ.real A := by
  set Q := AnnularPoissonClouds.law υ hυ
  have hsub : {ω | 1 ≤ (AnnularPoissonClouds.randomMeasure.toFun ω).countOn A} ⊆
      {ω | 1 ≤ (AnnularPoissonClouds.randomMeasure.toFun ω).toMeasure A} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, LocallyFinitePointMeasure.countOn] at hω ⊢
    have h1 : (1 : ℝ) ≤ (AnnularPoissonClouds.randomMeasure.toFun ω).toMeasure.real A := by
      have := Nat.le_floor_iff (measureReal_nonneg) |>.1 hω
      exact_mod_cast this
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((AnnularPoissonClouds.randomMeasure.toFun ω).toMeasure.real A) :=
          ENNReal.ofReal_le_ofReal h1
      _ ≤ _ := ENNReal.ofReal_toReal_le
  have hind : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have hmarkov := meas_ge_le_lintegral_div
    (AnnularPoissonClouds.aemeasurable_lintegral υ hυ _ hind)
    one_ne_zero ENNReal.one_ne_top (μ := Q)
  rw [AnnularPoissonClouds.campbell υ hυ _ hind, div_one] at hmarkov
  simp only [lintegral_indicator hA, lintegral_const, one_mul, Measure.restrict_apply_univ] at hmarkov
  exact ENNReal.toReal_mono hfin ((measure_mono hsub).trans hmarkov)

end LargeJumps

/-! ### The limit of the truncated Poisson integrals -/

section PoissonLimit

open AnnularPoissonClouds

/-- Cutoffs `εₖ = 1/(k+1)` and `Rₖ = k+1`. -/
def epsCut (k : ℕ) : ℝ≥0 := 1 / ((k : ℝ≥0) + 1)
def RCut (k : ℕ) : ℝ≥0 := (k : ℝ≥0) + 1

theorem epsCut_pos (k : ℕ) : 0 < epsCut k := by unfold epsCut; positivity
theorem epsCut_le_RCut (k : ℕ) : epsCut k ≤ RCut k := by
  unfold epsCut RCut
  have h1 : (1 : ℝ≥0) ≤ (k : ℝ≥0) + 1 := le_add_self
  exact (div_le_one_of_le₀ h1 (by positivity)).trans h1

/-- The truncated jump integral at cutoff level `k`. -/
def cutIntegral (k : ℕ) (ξ : LocallyFinitePointMeasure) : ℝ :=
  TruncatedPointIntegrals.truncatedIntegral (TruncatedPointIntegrals.endpoint (epsCut k) (epsCut_pos k))
    (TruncatedPointIntegrals.endpoint (RCut k) ((epsCut_pos k).trans_le (epsCut_le_RCut k))) ξ

theorem measurable_cutIntegral (k : ℕ) : Measurable (cutIntegral k) :=
  TruncatedPointIntegrals.measurable_truncatedIntegral _ _ (epsCut_pos k) (epsCut_le_RCut k)

theorem cutIntegral_tendsto {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∀ᵐ ω ∂powerLaw α hα, Tendsto (fun k => cutIntegral k (randomMeasure.toFun ω)) atTop
      (𝓝 (positiveIntegral ω)) := by
  filter_upwards [mark_integral_eq_ae hα, total_positiveMark_finite hα hα1] with ω heq hfin
  set ξ := (randomMeasure.toFun ω).toMeasure
  set I : ℕ → Set ExtremeState := fun k =>
    Ioc (TruncatedPointIntegrals.endpoint (epsCut k) (epsCut_pos k))
      (TruncatedPointIntegrals.endpoint (RCut k) ((epsCut_pos k).trans_le (epsCut_le_RCut k)))
  have hI (k : ℕ) : MeasurableSet (I k) := measurableSet_Ioc
  -- Each cut integral is the real part of a lintegral of the finite mark.
  have hcut (k : ℕ) : cutIntegral k (randomMeasure.toFun ω) =
      (∫⁻ y, (I k).indicator positiveMark y ∂ξ).toReal := by
    unfold cutIntegral TruncatedPointIntegrals.truncatedIntegral
    rw [← integral_indicator (hI k), integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y => Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) y)
      ((measurable_subtype_coe.ennreal_toReal.indicator (hI k)).aestronglyMeasurable)]
    congr 1
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ I k
    · simp [Set.indicator_of_mem hy, positiveMark]
    · simp [Set.indicator_of_notMem hy]
  have hmono : Monotone fun k => (I k).indicator positiveMark := by
    intro k l hkl y
    apply Set.indicator_le_indicator_of_subset _ (fun _ => bot_le)
    intro z hz
    simp only [I, mem_Ioc, TruncatedPointIntegrals.endpoint, ← Subtype.coe_lt_coe,
      ← Subtype.coe_le_coe] at hz ⊢
    constructor
    · refine lt_of_le_of_lt ?_ hz.1
      simp only [epsCut, ENNReal.coe_le_coe]
      gcongr
    · refine hz.2.trans ?_
      simp only [RCut, ENNReal.coe_le_coe]
      gcongr
  have hpt (y : ExtremeState) : Tendsto (fun k => (I k).indicator positiveMark y) atTop
      (𝓝 (positiveMark y)) := by
    by_cases htop : y.val = ⊤
    · have : positiveMark y = 0 := by simp [positiveMark, htop]
      rw [this]
      exact tendsto_const_nhds.congr fun k => by
        rw [Set.indicator_of_notMem]
        simp only [I, mem_Ioc, TruncatedPointIntegrals.endpoint, ← Subtype.coe_le_coe, htop,
          not_and, top_le_iff, ENNReal.coe_ne_top, not_false_eq_true, implies_true]
    · apply tendsto_const_nhds.congr'
      have hy0 : 0 < y.val.toReal := ENNReal.toReal_pos y.property.ne' htop
      have h1 : ∀ᶠ k : ℕ in atTop, (epsCut k : ℝ) < y.val.toReal := by
        have : Tendsto (fun k : ℕ => (epsCut k : ℝ)) atTop (𝓝 0) := by
          simp only [epsCut, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
          exact tendsto_one_div_add_atTop_nhds_zero_nat
        exact this.eventually (gt_mem_nhds hy0)
      have h2 : ∀ᶠ k : ℕ in atTop, y.val.toReal ≤ (RCut k : ℝ) := by
        have : Tendsto (fun k : ℕ => (RCut k : ℝ)) atTop atTop := by
          simp only [RCut, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
          exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        exact this.eventually (eventually_ge_atTop _)
      filter_upwards [h1, h2] with k hk1 hk2
      rw [Set.indicator_of_mem]
      simp only [I, mem_Ioc, TruncatedPointIntegrals.endpoint, ← Subtype.coe_lt_coe,
        ← Subtype.coe_le_coe]
      rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_coe_nnreal (p := RCut k)]
      exact ⟨(ENNReal.ofReal_lt_ofReal_iff hy0).2 hk1,
        ENNReal.ofReal_le_ofReal hk2⟩
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := ξ)
    (fun k => (measurable_positiveMark.indicator (hI k)).aemeasurable)
    (Eventually.of_forall fun y => fun k l hkl => hmono hkl y)
    (Eventually.of_forall hpt)
  have hreal := (ENNReal.tendsto_toReal hfin.ne).comp hlim
  have hpos : positiveIntegral ω = (∫⁻ y, positiveMark y ∂ξ).toReal := by
    unfold positiveIntegral
    rw [heq]
  rw [hpos]
  exact hreal.congr fun k => (hcut k).symm

end PoissonLimit

/-! ### The conditional stable law for `0 < α < 1` -/

section Main

open AnnularPoissonClouds

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Stable law, 0 < α < 1.** Under H and admissibility of `x₀`, if `α = d/β < 1` then for every `x
∈ M \ Z`, under `ℙₓ(· | τ > n)`, `B_n⁻¹ ∑_{j<n} f_β(X_j) → Z_α = ∫ y N(dy)` in distribution, with
`B_n = (C(x₀) n)^{1/α}` and `N` the Poisson random measure of intensity `α y^{-α-1} dy`. Its Laplace
transform is `exp(-Γ(1-α) t^α)`. -/
theorem stable_law_small (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : dimension / β < 1) :
    TendstoInDistribution
      (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
        (dimension / β) n)⁻¹ * pathBirkhoffSum (singularObservable x₀ β) n ω) atTop
      positiveIntegral
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw (dimension / β) (div_pos hadm.1.1 hβ)) := by
  set α := dimension / β
  have hα : 0 < α := div_pos hadm.1.1 hβ
  set Cc := volumeConstant * (d.weight x₀).toReal * m x₀
  have hC : 0 < Cc := mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _)))
    hadm.2.1
  set f := singularObservable x₀ β
  have hfm : Measurable f := measurable_singularObservable x₀ β
  have hfpos : ∀ z, 0 < f z := singularObservable_pos x₀ β
  set B := positivePowerScale Cc α
  have hB : ∀ n, 0 < B n := positivePowerScale_pos hC
  set P : ℕ → Measure (Path M) := fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))
  have hPeq (n : ℕ) : P n = C.conditionedMeasure x.val n := rfl
  set Q := powerLaw α hα
  set N : ℕ → RandomPointMeasure (Path M) := fun n => pathEmpirical f hfm hfpos n (B n) (hB n)
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  -- The point-process interval counts.
  have hcounts := fun (k : ℕ) (a b : Fin k → ExtremeState) (hab : ∀ j, a j < b j)
      (hdis : Pairwise fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) =>
    C.poisson_interval_counts_of_admissibility h d s.continuous_weight μ hleft hnorm m hm hm0 hμ x
      hadm hx₀ hβ k a b hab hdis
  -- The truncated moment hypothesis.
  have : IsFiniteMeasure (μ.withDensity d.weight) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
    exact ENNReal.one_lt_top
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  have hmom : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ) *
      (∫ y, {y | f y ≤ ε * B n}.indicator f y ∂μ.withDensity d.weight) / B n) atTop
      (𝓝 (α / (1 - α) * ε ^ (1 - α))) := fun ε hε =>
    truncated_mean_scaled hfm (fun z => (hfpos z).le) hC hα hα1 htail hε
  obtain ⟨K, hK, hsmall⟩ := small_jumps_eventually C h d s hlive μ hleft hnorm x hfm hfpos hB
    (positivePowerScale_tendsto_atTop hC hα) hmom
  refine tendstoInDistribution_of_double_probability_approximation P Q Q
    (fun n ω => (B n)⁻¹ * pathBirkhoffSum f n ω)
    (fun k n ω => cutIntegral k ((N n).toFun ω))
    (fun k ω => cutIntegral k (randomMeasure.toFun ω)) positiveIntegral
    (fun n => (measurable_pathBirkhoffSum hfm n).const_mul _)
    (fun k n => (measurable_cutIntegral k).comp (N n).measurable)
    (fun k => (measurable_cutIntegral k).comp randomMeasure.measurable)
    (fun k => TruncatedPointIntegrals.tendstoInDistribution_truncatedIntegral_of_disjoint_counts
      P Q N randomMeasure hcounts (epsCut k) (RCut k) (epsCut_pos k) (epsCut_le_RCut k))
    (tendstoInDistribution_of_ae_tendsto
      (fun k => ((measurable_cutIntegral k).comp randomMeasure.measurable).aemeasurable)
      (positiveIntegral_aemeasurable hα) (cutIntegral_tendsto hα hα1)) ?_
  intro ε' δ hε' hδ
  have hα1' : 0 < 1 - α := sub_pos.2 hα1
  -- Bounds that vanish as the cutoff level grows.
  set Sk : ℕ → ℝ := fun k => (2 * (α / (1 - α) * (epsCut k : ℝ) ^ (1 - α)) + K * epsCut k) / ε'
  set Lk : ℕ → ℝ := fun k => (RCut k : ℝ) ^ (-α)
  have heps : Tendsto (fun k : ℕ => (epsCut k : ℝ)) atTop (𝓝 0) := by
    simp only [epsCut, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hR : Tendsto (fun k : ℕ => (RCut k : ℝ)) atTop atTop := by
    simp only [RCut, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hSk : Tendsto Sk atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (epsCut k : ℝ) ^ (1 - α)) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (1 - α) (Or.inr hα1'.le)).tendsto.comp heps
      rw [Real.zero_rpow hα1'.ne'] at this
      exact this
    have := ((h1.const_mul (α / (1 - α))).const_mul 2).add (heps.const_mul K)
    simpa [Sk] using this.div_const ε'
  have hLk : Tendsto Lk atTop (𝓝 0) := (tendsto_rpow_neg_atTop hα).comp hR
  have hev : ∀ᶠ k in atTop, Sk k + 2 * Lk k < δ := by
    have := hSk.add (hLk.const_mul 2)
    simp only [mul_zero, add_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with k hk
  have hRk : 0 < RCut k := (epsCut_pos k).trans_le (epsCut_le_RCut k)
  set A : Set ExtremeState := Ioc (TruncatedPointIntegrals.endpoint (RCut k) hRk) ⊤
  have hAm : MeasurableSet A := measurableSet_Ioc
  -- Small jumps.
  have h1 := hsmall (epsCut k) (by exact_mod_cast epsCut_pos k) ε' hε'
  -- Large jumps: the count on `(Rₖ, ∞]` converges, and the limit is small.
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
    have := hlim.eventually (gt_mem_nhds (show Q.real _ < 2 * Lk k by linarith [hQ]))
    exact this
  filter_upwards [h1, h2] with n hn1 hn2
  -- The decomposition, almost surely on survival.
  have hsub : {ω | ε' < |(B n)⁻¹ * pathBirkhoffSum f n ω - cutIntegral k ((N n).toFun ω)|} ≤ᵐ[P n]
      ({ω | ε' < (B n)⁻¹ * pathBirkhoffSum ({z | f z ≤ (epsCut k : ℝ) * B n}.indicator f) n ω} ∪
        {ω | 1 ≤ ((N n).toFun ω).countOn A} : Set (Path M)) := by
    filter_upwards [C.ae_survival_conditionedMeasure x.val n] with ω hω hmem
    exact decomposition hfm hfpos (hB n) (epsCut_pos k) (epsCut_le_RCut k) hω hmem
  have := C.conditionedMeasure_isProbability_of_surviving x.val hx n
  calc (P n).real {ω | ε' < |(B n)⁻¹ * pathBirkhoffSum f n ω - cutIntegral k ((N n).toFun ω)|}
      ≤ (P n).real ({ω | ε' < (B n)⁻¹ * pathBirkhoffSum ({z | f z ≤ (epsCut k : ℝ) * B n}.indicator f) n ω} ∪
        {ω | 1 ≤ ((N n).toFun ω).countOn A}) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ (P n).real {ω | ε' < (B n)⁻¹ * pathBirkhoffSum ({z | f z ≤ (epsCut k : ℝ) * B n}.indicator f) n ω} +
        (P n).real {ω | 1 ≤ ((N n).toFun ω).countOn A} := measureReal_union_le _ _
    _ < Sk k + 2 * Lk k := by
        have : (P n).real {ω | ε' < (B n)⁻¹ *
            pathBirkhoffSum ({z | f z ≤ (epsCut k : ℝ) * B n}.indicator f) n ω} ≤ Sk k := hn1
        linarith
    _ < δ := hk


end Main

end

end ConditionedStableLaws.StableLawSmall
