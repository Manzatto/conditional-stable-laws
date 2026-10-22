import ConditionedStableLaws.SecondMoment
import ConditionedStableLaws.NormalizationBridge

/-!
# Conditional second moment of compensated small jumps

For `x ∈ M \ Z` there is `Cₓ`, independent of `n`, `ε` and the scale `B`, such that `E_x[(B⁻¹
∑_{i<n} h(Xᵢ) - n B⁻¹ ν(h))² | τ > n] ≤ Cₓ (n/B²) ν(h²) + Cₓ ε² + Cₓ n/B²`, where `h = f 1_{f ≤
εB}`. The left side is the second moment of `∫_{(0,ε]} y (N_n - υ_n)(dy)` for `B = B_n`. For `α <
2`, `n/B_n² → 0`, so the last term is `o(1)`. The comparison `μ(h²) ≤ η_*⁻¹ ν(h²) + C` follows from
`η ≥ η_*` on a set `V` and `f` bounded off `V`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.SmallJumpMoment

noncomputable section

open StandingHypothesis CanonicalChain SecondMoment

section Truncation

variable {M : Type*} [MeasurableSpace M]

/-- The truncated observable `f 1_{f ≤ a}`. -/
def trunc (f : M → ℝ) (a : ℝ) : M → ℝ := {z | f z ≤ a}.indicator f

theorem measurable_trunc {f : M → ℝ} (hf : Measurable f) (a : ℝ) : Measurable (trunc f a) :=
  hf.indicator (measurableSet_le hf measurable_const)

omit [MeasurableSpace M] in
theorem trunc_nonneg {f : M → ℝ} (hf0 : ∀ z, 0 ≤ f z) (a : ℝ) (z : M) : 0 ≤ trunc f a z := by
  unfold trunc
  by_cases hz : f z ≤ a
  · rw [indicator_of_mem (show z ∈ {z | f z ≤ a} from hz)]; exact hf0 z
  · rw [indicator_of_notMem (show z ∉ {z | f z ≤ a} from hz)]

omit [MeasurableSpace M] in
theorem trunc_le {f : M → ℝ} {a : ℝ} (ha : 0 ≤ a) (z : M) : trunc f a z ≤ a := by
  unfold trunc
  by_cases hz : f z ≤ a
  · rw [indicator_of_mem (show z ∈ {z | f z ≤ a} from hz)]; exact hz
  · rw [indicator_of_notMem (show z ∉ {z | f z ≤ a} from hz)]; exact ha

omit [MeasurableSpace M] in
theorem trunc_le_self {f : M → ℝ} (hf0 : ∀ z, 0 ≤ f z) (a : ℝ) (z : M) : trunc f a z ≤ f z := by
  unfold trunc
  by_cases hz : f z ≤ a
  · rw [indicator_of_mem (show z ∈ {z | f z ≤ a} from hz)]
  · rw [indicator_of_notMem (show z ∉ {z | f z ≤ a} from hz)]; exact hf0 z

omit [MeasurableSpace M] in
theorem pathBirkhoffSum_const_mul (a : ℝ) (g : M → ℝ) (n : ℕ) (ω : Path M) :
    pathBirkhoffSum (fun z => a * g z) n ω = a * pathBirkhoffSum g n ω := by
  unfold pathBirkhoffSum birkhoffSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show zeroExtension (fun z => a * g z) (ω i) = a * zeroExtension g (ω i)
  generalize ω i = w
  cases w <;> simp

omit [MeasurableSpace M] in
theorem pathBirkhoffSum_sub_const (g : M → ℝ) (c : ℝ) {n : ℕ} {ω : Path M}
    (hω : ω ∈ survival n) :
    pathBirkhoffSum (fun z => g z - c) n ω = pathBirkhoffSum g n ω - n * c := by
  unfold pathBirkhoffSum birkhoffSum
  rw [show (n : ℝ) * c = ∑ _i ∈ Finset.range n, c by simp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (hω i (Finset.mem_range.1 hi).le)
  simp [hz]

end Truncation

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Conditional second moment of small jumps.** Let `f ≥ 0` be measurable, `η ≥ η_* > 0` on `V`
and `f ≤ F` off `V`. For every `x ∈ M \ Z` there is `Cₓ` such that for all `ε, B > 0` and `n`, with
`h = f 1_{f ≤ εB}` and `ν = ημ`, `E_x[(B⁻¹ ∑_{i<n} h(Xᵢ) - n B⁻¹ ν(h))² | τ > n] ≤ Cₓ (n/B²) ν(h²) +
Cₓ ε² + Cₓ n/B²`. -/
theorem conditional_small_jump_second_moment (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (x : d.State) {f : M → ℝ} (hfm : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) {V : Set M} {ηs : ℝ} (hηs : 0 < ηs)
    (hηV : ∀ z ∈ V, ηs ≤ (d.weight z).toReal) {F : ℝ} (hF : ∀ z ∉ V, f z ≤ F) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧ ∀ ε B : ℝ, 0 < ε → 0 < B → ∀ n : ℕ,
      ∫ ω, (B⁻¹ * pathBirkhoffSum (trunc f (ε * B)) n ω -
          n * B⁻¹ * ∫ y, trunc f (ε * B) y ∂μ.withDensity d.weight) ^ 2
        ∂C.conditionedMeasure x.val n ≤
      Cx * (n / B ^ 2) * ∫ y, trunc f (ε * B) y ^ 2 ∂μ.withDensity d.weight +
        Cx * ε ^ 2 + Cx * (n / B ^ 2) := by
  obtain ⟨C0, hC0, hmain⟩ := conditional_sum_second_moment C h d s hlive μ hleft hnorm x
  set Fp := max F 0 with hFp_def
  refine ⟨C0 * (2 * (ηs⁻¹ + 1) + 1 + 2 * Fp ^ 2), by positivity, ?_⟩
  intro ε B hε hB n
  set ν := μ.withDensity d.weight with hν_def
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  set a := ε * B with ha_def
  have ha : 0 < a := mul_pos hε hB
  set hf := trunc f a with hhf_def
  have hhm : Measurable hf := measurable_trunc hfm a
  have hh0 : ∀ z, 0 ≤ hf z := trunc_nonneg hf0 a
  have hha : ∀ z, hf z ≤ a := trunc_le ha.le
  have hhb : ∀ z, |hf z| ≤ a := fun z => by rw [abs_of_nonneg (hh0 z)]; exact hha z
  set c := ∫ y, hf y ∂ν with hc_def
  have hc0 : 0 ≤ c := integral_nonneg hh0
  have hca : c ≤ a := (le_abs_self _).trans (abs_integral_le_of_prob (ν := ν) hhb)
  set g : M → ℝ := fun z => B⁻¹ * (hf z - c) with hg_def
  have hgm : Measurable g := measurable_const.mul (hhm.sub measurable_const)
  have hgb : ∀ z, |g z| ≤ ε := fun z => by
    simp only [hg_def]
    rw [abs_mul, abs_of_pos (inv_pos.2 hB)]
    have : |hf z - c| ≤ a := abs_sub_le_iff.2 ⟨by linarith [hha z], by linarith [hh0 z]⟩
    calc B⁻¹ * |hf z - c| ≤ B⁻¹ * a := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hB.le)
      _ = ε := by rw [ha_def]; field_simp
  have hgν : ∫ y, g y ∂ν = 0 := by
    simp only [hg_def]
    rw [integral_const_mul, integral_sub (integrable_of_bdd hhm hhb) (integrable_const c),
      integral_const, probReal_univ, one_smul, sub_self, mul_zero]
  -- The centred sum.
  have hid : ∫ ω, (B⁻¹ * pathBirkhoffSum hf n ω - n * B⁻¹ * c) ^ 2
      ∂C.conditionedMeasure x.val n = ∫ ω, pathBirkhoffSum g n ω ^ 2 ∂C.conditionedMeasure x.val n := by
    refine integral_congr_ae ?_
    filter_upwards [C.ae_survival_conditionedMeasure x.val n] with ω hω
    simp only [hg_def]
    rw [pathBirkhoffSum_const_mul, pathBirkhoffSum_sub_const hf c hω]
    ring
  rw [hid]
  refine (hmain g hgm ε hε.le hgb hgν n).trans ?_
  set νh := ∫ y, hf y ^ 2 ∂ν with hνh_def
  have hνh0 : 0 ≤ νh := integral_nonneg fun y => sq_nonneg _
  -- `ν(h)² ≤ ν(h²)`.
  have hc2 : c ^ 2 ≤ νh := by
    have := sq_integral_mul_le (ν := ν) (u := hf) (v := fun _ => 1) hhm measurable_const hhb
      (V := 1) (fun _ => by simp)
    simpa using this
  -- `μ(h²) ≤ η_*⁻¹ ν(h²) + F₊²`.
  obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d s.continuous_weight
  have hηb : ∀ y, |(d.weight y).toReal| ≤ Bη := fun y => by
    have := hBη y; rw [Real.norm_eq_abs] at this; exact this
  have hηm : Measurable fun y => (d.weight y).toReal := d.measurable_weight.ennreal_toReal
  have hμh : ∫ y, hf y ^ 2 ∂μ ≤ ηs⁻¹ * νh + Fp ^ 2 := by
    have hνeq : νh = ∫ y, hf y ^ 2 * (d.weight y).toReal ∂μ := by
      rw [hνh_def, hν_def, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
        (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
      congr 1; funext y; rw [smul_eq_mul, mul_comm]
    have hint1 : Integrable (fun y => ηs⁻¹ * (hf y ^ 2 * (d.weight y).toReal)) μ :=
      integrable_of_bdd (measurable_const.mul ((hhm.pow_const 2).mul hηm))
        (B := ηs⁻¹ * (a ^ 2 * Bη)) (fun y => by
          rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hηs)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (sq_bdd hhb y) (hηb y) (abs_nonneg _) (sq_nonneg _))
            (inv_nonneg.2 hηs.le))
    rw [hνeq]
    calc ∫ y, hf y ^ 2 ∂μ
        ≤ ∫ y, (ηs⁻¹ * (hf y ^ 2 * (d.weight y).toReal) + Fp ^ 2) ∂μ :=
          integral_mono (integrable_of_bdd (hhm.pow_const 2) (sq_bdd hhb))
            (hint1.add (integrable_const _)) (fun y => ?_)
      _ = ηs⁻¹ * ∫ y, hf y ^ 2 * (d.weight y).toReal ∂μ + Fp ^ 2 := by
          rw [integral_add hint1 (integrable_const _), integral_const_mul, integral_const,
            probReal_univ, one_smul]
    have hpos : 0 ≤ ηs⁻¹ * (hf y ^ 2 * (d.weight y).toReal) :=
      mul_nonneg (inv_nonneg.2 hηs.le) (mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)
    beta_reduce
    by_cases hy : y ∈ V
    · calc hf y ^ 2 = ηs⁻¹ * (hf y ^ 2 * ηs) := by field_simp
        _ ≤ ηs⁻¹ * (hf y ^ 2 * (d.weight y).toReal) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hηV y hy) (sq_nonneg _))
              (inv_nonneg.2 hηs.le)
        _ ≤ _ := le_add_of_nonneg_right (sq_nonneg _)
    · have h1 : hf y ≤ Fp := ((trunc_le_self hf0 a y).trans (hF y hy)).trans (le_max_left _ _)
      have h2 : hf y ^ 2 ≤ Fp ^ 2 := pow_le_pow_left₀ (hh0 y) h1 2
      linarith
  -- `μ(g²) ≤ 2B⁻²(μ(h²) + ν(h²))`.
  have hμg : ∫ y, g y ^ 2 ∂μ ≤ 2 * B⁻¹ ^ 2 * (∫ y, hf y ^ 2 ∂μ + νh) := by
    have hi1 : Integrable (fun y => 2 * B⁻¹ ^ 2 * hf y ^ 2) μ :=
      (integrable_of_bdd (hhm.pow_const 2) (sq_bdd hhb)).const_mul _
    calc ∫ y, g y ^ 2 ∂μ ≤ ∫ y, (2 * B⁻¹ ^ 2 * hf y ^ 2 + 2 * B⁻¹ ^ 2 * c ^ 2) ∂μ :=
          integral_mono (integrable_of_bdd (hgm.pow_const 2) (sq_bdd hgb))
            (hi1.add (integrable_const _)) (fun y => by
              simp only [hg_def]
              calc (B⁻¹ * (hf y - c)) ^ 2 = B⁻¹ ^ 2 * (hf y - c) ^ 2 := by ring
                _ ≤ B⁻¹ ^ 2 * (2 * hf y ^ 2 + 2 * c ^ 2) :=
                    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (hf y + c)])
                      (sq_nonneg _)
                _ = 2 * B⁻¹ ^ 2 * hf y ^ 2 + 2 * B⁻¹ ^ 2 * c ^ 2 := by ring)
      _ = 2 * B⁻¹ ^ 2 * ∫ y, hf y ^ 2 ∂μ + 2 * B⁻¹ ^ 2 * c ^ 2 := by
          rw [integral_add hi1 (integrable_const _), integral_const_mul, integral_const,
            probReal_univ, one_smul]
      _ ≤ 2 * B⁻¹ ^ 2 * (∫ y, hf y ^ 2 ∂μ + νh) := by
          have : 0 ≤ 2 * B⁻¹ ^ 2 := by positivity
          nlinarith
  -- Assembly.
  set t := (n : ℝ) / B ^ 2 with ht_def
  have ht : 0 ≤ t := by positivity
  have htn : (n : ℝ) * B⁻¹ ^ 2 = t := by rw [ht_def, inv_pow, div_eq_mul_inv]
  have hstep : (n : ℝ) * ∫ y, g y ^ 2 ∂μ ≤ 2 * t * ((ηs⁻¹ + 1) * νh + Fp ^ 2) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (n : ℝ) * ∫ y, g y ^ 2 ∂μ ≤ n * (2 * B⁻¹ ^ 2 * (∫ y, hf y ^ 2 ∂μ + νh)) :=
          mul_le_mul_of_nonneg_left hμg hn0
      _ ≤ n * (2 * B⁻¹ ^ 2 * ((ηs⁻¹ * νh + Fp ^ 2) + νh)) := by
          have : 0 ≤ (n : ℝ) * (2 * B⁻¹ ^ 2) := by positivity
          nlinarith
      _ = 2 * ((n : ℝ) * B⁻¹ ^ 2) * ((ηs⁻¹ + 1) * νh + Fp ^ 2) := by ring
      _ = 2 * t * ((ηs⁻¹ + 1) * νh + Fp ^ 2) := by rw [htn]
  have hηs' : 0 ≤ ηs⁻¹ := inv_nonneg.2 hηs.le
  have e1 : 0 ≤ C0 * (1 + 2 * Fp ^ 2) * t * νh := by positivity
  have e2 : 0 ≤ C0 * (2 * (ηs⁻¹ + 1) + 2 * Fp ^ 2) * ε ^ 2 := by positivity
  have e3 : 0 ≤ C0 * (2 * (ηs⁻¹ + 1) + 1) * t := by positivity
  have e4 := mul_le_mul_of_nonneg_left hstep hC0
  nlinarith [e1, e2, e3, e4]

open NormalizationBridge in
/-- **Conditional second moment of small jumps** for the singular observable `f_β = d(·, x₀)^{-β}`
and the scale `B_n = (C n)^{1/α}` with `α < 2`: there are `Cₓ`, independent of `n` and `ε`, and
`o(1)` terms with `E_{x,n}[(∫_{(0,ε]} y (N_n - υ_n)(dy))²] ≤ (Cₓ n / B_n²) ν(f_β² 1_{f_β ≤ εB_n}) +
Cₓ ε² + o(1)`. -/
theorem conditional_small_jump_second_moment_singular (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (x : d.State) {x₀ : M} {β Cc α : ℝ} (hβ : 0 < β)
    (hx₀ : d.weight x₀ ≠ 0) (hC : 0 < Cc) (hα : 0 < α) (hα2 : α < 2) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧ ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      ∫ ω, ((positivePowerScale Cc α n)⁻¹ *
          pathBirkhoffSum (trunc (singularObservable x₀ β) (ε * positivePowerScale Cc α n)) n ω -
          n * (positivePowerScale Cc α n)⁻¹ * ∫ y, trunc (singularObservable x₀ β)
            (ε * positivePowerScale Cc α n) y ∂μ.withDensity d.weight) ^ 2
        ∂C.conditionedMeasure x.val n ≤
      Cx * (n / positivePowerScale Cc α n ^ 2) * ∫ y, trunc (singularObservable x₀ β)
          (ε * positivePowerScale Cc α n) y ^ 2 ∂μ.withDensity d.weight +
        Cx * ε ^ 2 + o n := by
  set η0 := (d.weight x₀).toReal with hη0_def
  have hη0 : 0 < η0 := ENNReal.toReal_pos hx₀ (d.weight_ne_top _)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1
    ((s.continuous_weight_toReal.continuousAt (x := x₀)).eventually
      (lt_mem_nhds (half_lt_self hη0)))
  obtain ⟨Cx, hCx, hmain⟩ := conditional_small_jump_second_moment C h d s hlive μ hleft hnorm x
    (measurable_singularObservable x₀ β) (fun z => (singularObservable_pos x₀ β z).le)
    (V := Metric.ball x₀ r) (ηs := η0 / 2) (half_pos hη0)
    (fun z hz => (hball (Metric.mem_ball.1 hz)).le) (F := r ^ (-β)) (fun z hz => by
      have hle : r ≤ dist z x₀ := not_lt.1 (fun h' => hz (Metric.mem_ball.2 h'))
      have hne : z ≠ x₀ := fun h' => by rw [h', dist_self] at hle; linarith
      simp only [singularObservable, ite_eq_right hne]
      exact Real.rpow_le_rpow_of_nonpos hr hle (by linarith))
  refine ⟨Cx, hCx, fun n => Cx * (n / positivePowerScale Cc α n ^ 2), ?_,
    fun ε hε n => hmain ε _ hε (positivePowerScale_pos hC n) n⟩
  have := (nat_div_powerScale_sq_tendsto_zero hC hα hα2).const_mul Cx
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [positivePowerScale_eventually_eq Cc α] with n hn
  rw [hn]

end

end ConditionedStableLaws.SmallJumpMoment
