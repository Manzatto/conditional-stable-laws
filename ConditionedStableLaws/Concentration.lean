import ConditionedStableLaws.TwistedOperators
import ConditionedStableLaws.SmallJumpMoment
import ConditionedStableLaws.SourceSpectralGap

/-!
# Conditional exponential concentration

For bounded measurable `f` and `x ∈ M \ Z`, `ℙ_x(|n⁻¹ ∑_{j<n} f(X_j) - ν(f)| > ε | τ > n) ≤ Cₓ
e^{-γ(ε,f) n}`, with `γ(ε,f) = min{t_f/4, ε²/(16 K_f)}`.

The exponential moments are `E_x[e^{t S_n} | τ > n] = (g K)ⁿ 1 (x) / ℙ_x(τ > n)` with `g = e^{t(f -
ν(f))}` (Feynman–Kac); on `L∞(ρ)` the twisted operator `P̂ ∘ e^{t(f-ν(f))}` has, by the rank-one
perturbation theorem, a leading eigenvalue with `Λ'(0) = ν(f - ν(f)) = 0`, whence `E_x[e^{t S_n} | τ
> n] ≤ C e^{K n t²}` for `|t| ≤ t₀`; Markov's inequality concludes. The sums are taken over `0 ≤ j <
n` directly, so no boundary correction is needed.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.Concentration

noncomputable section

open StandingHypothesis CanonicalChain TwistedOperators FeynmanKac

/-! ### The twisted killed recursion -/

section Words

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- One step `u ↦ g · K u` of the twisted killed recursion. -/
def step (g : M → ℝ) (u : M → ℝ) : M → ℝ := fun y => g y * ∫ z, u z ∂C.killedTransition y

theorem killedWord_const (g : M → ℝ) (n : ℕ) :
    ∀ u, killedWord C (fun _ => g) n u = (step C g)^[n] u := by
  induction n with
  | zero => intro u; rfl
  | succ n ih =>
    intro u
    rw [Function.iterate_succ_apply]
    exact ih (step C g u)

/-- The Feynman–Kac representation of the conditioned exponential moments. -/
theorem integral_conditioned_exp {q : M → ℝ} (hq : Measurable q) {Q : ℝ} (_hQ0 : 0 ≤ Q)
    (hQ : ∀ y, |q y| ≤ Q) (t : ℝ) (x : M) (n : ℕ) :
    ∫ ω, Real.exp (t * pathBirkhoffSum q n ω) ∂C.conditionedMeasure x n =
      (C.pathMeasure x (survival n)).toReal⁻¹ *
        (step C (fun y => Real.exp (t * q y)))^[n] (fun _ => 1) x := by
  set g : M → ℝ := fun y => Real.exp (t * q y) with hg_def
  have hgm : Measurable g := (measurable_const.mul hq).exp
  have hgb : ∀ y, ‖g y‖ ≤ Real.exp (|t| * Q) := fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    calc t * q y ≤ |t * q y| := le_abs_self _
      _ = |t| * |q y| := abs_mul _ _
      _ ≤ |t| * Q := mul_le_mul_of_nonneg_left (hQ y) (abs_nonneg t)
  rw [conditionedMeasure, ProbabilityTheory.cond, integral_smul_measure,
    ← integral_indicator (measurableSet_survival n), smul_eq_mul, ENNReal.toReal_inv]
  congr 1
  rw [← killedWord_const, ← integral_prod_eq_killedWord C (fun _ => g) (fun _ => hgm)
    (Real.exp_pos _).le (fun _ y => hgb y) n measurable_const zero_le_one (fun _ => by simp) x]
  congr 1
  funext ω
  by_cases hω : ω ∈ survival n
  · rw [indicator_of_mem hω]
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (hω n le_rfl)
    rw [hz, ext_some, mul_one]
    unfold pathBirkhoffSum birkhoffSum
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hω i (Finset.mem_range.1 hi).le)
    rw [hy]
    simp [hg_def]
  · rw [indicator_of_notMem hω]
    have : ∃ k, k ≤ n ∧ ω k = none := by
      by_contra hc
      push Not at hc
      exact hω fun k hk => hc k hk
    obtain ⟨k, hk, hkn⟩ := this
    rcases lt_or_eq_of_le hk with hlt | rfl
    · rw [Finset.prod_eq_zero (Finset.mem_range.2 hlt) (by rw [hkn]; rfl), zero_mul]
    · rw [hkn, ext_none, mul_zero]

end Words

/-! ### The `L∞(ρ)` representation -/

section Linfty

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

theorem iterate_step_ae (h : HypothesisH ρ C.toKilledKernel) [IsFiniteMeasure ρ]
    (g : Multiplier M) (one : Lp ℝ ∞ ρ) (hone : (one : M → ℝ) =ᵐ[ρ] fun _ => 1) (m : ℕ) :
    ((((mulL g : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ) * h.transitionOperator) ^ m) one : M → ℝ) =ᵐ[ρ]
      (step C g.toFun)^[m] (fun _ => 1) := by
  induction m with
  | zero => simpa using hone
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp,
      Function.iterate_succ_apply']
    set w : Lp ℝ ∞ ρ := (((mulL g : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ) * h.transitionOperator) ^ m) one
    filter_upwards [mulL_ae g (h.transitionOperator w), h.transitionOperator_ae w] with y h1 h2
    rw [h1, h2]
    simp only [step]
    congr 1
    exact integral_congr_ae ((h.absolutelyContinuous y).ae_eq ih)

end Linfty

/-! ### Markov's inequality for exponential moments -/

theorem markov_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Z : Ω → ℝ} (hZ : Measurable Z) {b : ℝ} (hb : ∀ ω, |Z ω| ≤ b) {s : ℝ} (hs : 0 ≤ s) (a : ℝ) :
    P.real {ω | a < Z ω} ≤ Real.exp (-(s * a)) * ∫ ω, Real.exp (s * Z ω) ∂P := by
  have hint : Integrable (fun ω => Real.exp (s * Z ω)) P := by
    refine Integrable.of_bound (hZ.const_mul s).exp.aestronglyMeasurable (Real.exp (s * b))
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb ω)) hs
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos (s * Z ω)).le)
    hint (Real.exp (s * a))
  have hsub : {ω | a < Z ω} ⊆ {ω | Real.exp (s * a) ≤ Real.exp (s * Z ω)} := fun ω hω => by
    have : a < Z ω := hω
    show Real.exp (s * a) ≤ Real.exp (s * Z ω)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left this.le hs)
  have h1 := measureReal_mono (μ := P) hsub
  rw [Real.exp_neg]
  rw [le_inv_mul_iff₀ (Real.exp_pos _)]
  nlinarith [Real.exp_pos (s * a)]

/-! ### The concentration theorem -/

theorem rate_le {K t₀ ε : ℝ} (hK : 0 < K) (ht₀ : 0 < t₀) (hε : 0 < ε) :
    min (4 * K * t₀ ^ 2 / 4) (ε ^ 2 / (16 * K)) ≤ min t₀ (ε / (2 * K)) * ε / 2 := by
  rcases le_total t₀ (ε / (2 * K)) with hle | hle
  · rw [min_eq_left hle]
    refine (min_le_left _ _).trans ?_
    have : 2 * K * t₀ ≤ ε := by rw [le_div_iff₀ (by positivity)] at hle; linarith
    nlinarith
  · rw [min_eq_right hle]
    refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg ε, hK]

section Main

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

set_option maxHeartbeats 1000000 in
/-- **Conditional exponential concentration.** For bounded measurable `f` there are `t_f, K_f > 0`
such that for every `x ∈ M \ Z` there is `Cₓ > 0` with `ℙ_x(|n⁻¹ ∑_{j<n} f(X_j) - ν(f)| > ε | τ > n)
≤ Cₓ e^{-γ(ε,f) n}` for all `ε > 0` and `n ≥ 1`, where `γ(ε,f) = min{t_f/4, ε²/(16 K_f)}`. -/
theorem conditional_exponential_concentration (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) {f : M → ℝ} (hfm : Measurable f) {F : ℝ}
    (hF : ∀ y, |f y| ≤ F) :
    ∃ tf Kf : ℝ, 0 < tf ∧ 0 < Kf ∧ ∀ x : d.State, ∃ Cx : ℝ, 0 < Cx ∧
      ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
        (C.conditionedMeasure x.val n).real
          {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - ∫ y, f y ∂μ.withDensity d.weight|} ≤
        Cx * Real.exp (-(min (tf / 4) (ε ^ 2 / (16 * Kf))) * n) := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hKfin : IsFiniteKernel C.killedTransition := by
    simpa using killedKernel_power_isFinite C.toKilledKernel 1
  obtain ⟨s', hmean⟩ := h.exists_survivalGapData_with_mean d s.continuous_weight μ hleft hnorm
  set r := d.rate.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  set Top : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := h.transitionOperator with hTop_def
  set T₀ : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := r⁻¹ • Top with hT₀_def
  set ν := μ.withDensity d.weight with hν_def
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  set Fp := max F 0 with hFp_def
  have hFp0 : 0 ≤ Fp := le_max_right _ _
  have hfb : ∀ y, |f y| ≤ Fp := fun y => (hF y).trans (le_max_left _ _)
  set mf := ∫ y, f y ∂ν with hmf_def
  have hmf : |mf| ≤ Fp := SecondMoment.abs_integral_le_of_prob hfb
  set fbar : Multiplier M :=
    { toFun := fun y => f y - mf
      measurable := hfm.sub measurable_const
      bound := 2 * Fp
      bound_nonneg := by positivity
      le_bound := fun y => (abs_sub _ _).trans (by linarith [hfb y]) } with hfbar_def
  set H : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := mulL fbar with hH_def
  have hμρ : μ ≪ ρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  have hη : ∫ y, (d.weight y).toReal ∂μ = 1 :=
    L2Compactness.integral_eta (K := C.toKilledKernel) d μ hnorm
  set v := s'.eigenvector
  set ℓ := s'.mean
  have hℓv : ℓ v = 1 := by
    rw [hmean, integral_congr_ae (hμρ.ae_eq s'.eigenvector_ae)]; exact hη
  have hℓT : ∀ w, ℓ (T₀ w) = ℓ w := SurvivalGapData.mean_normalizedOperator h d s' μ hleft hmean
  have hTv : T₀ v = v := StandingHypothesis.SurvivalGapData.normalizedOperator_eigenvector h d s'
  have hT₀P : T₀ * ℓ.smulRight v = ℓ.smulRight v := by
    ext1 w
    simp only [mul_apply_eq_comp, ContinuousLinearMap.smulRight_apply, map_smul, hTv]
  have hPT₀ : ℓ.smulRight v * T₀ = ℓ.smulRight v := by
    ext1 w
    simp only [mul_apply_eq_comp, ContinuousLinearMap.smulRight_apply, hℓT]
  have hgap : ∀ n : ℕ, 1 ≤ n → ‖T₀ ^ n - ℓ.smulRight v‖ ≤ s'.constant * s'.decay ^ n :=
    fun n hn => s'.gap n hn
  have hHv : ℓ (H v) = 0 := by
    have hae : (H v : M → ℝ) =ᵐ[μ] fun y => (f y - mf) * (d.weight y).toReal :=
      hμρ.ae_eq ((mulL_ae fbar v).trans (by
        filter_upwards [s'.eigenvector_ae] with y hy
        show (f y - mf) * v y = _
        rw [hy]))
    have hηint : Integrable (fun y => (d.weight y).toReal) μ := by
      obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d s.continuous_weight
      exact Integrable.of_bound d.measurable_weight.ennreal_toReal.aestronglyMeasurable Bη
        (Eventually.of_forall hBη)
    have hfη : ∫ y, f y * (d.weight y).toReal ∂μ = mf := by
      rw [hmf_def, hν_def, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
        (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
      congr 1; funext y; rw [smul_eq_mul, mul_comm]
    have hfηi : Integrable (fun y => f y * (d.weight y).toReal) μ := by
      refine (hηint.const_mul Fp).mono' (hfm.mul d.measurable_weight.ennreal_toReal).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (ENNReal.toReal_nonneg)]
      exact mul_le_mul_of_nonneg_right (hfb y) ENNReal.toReal_nonneg
    rw [hmean, integral_congr_ae hae]
    simp only [sub_mul]
    rw [integral_sub hfηi (hηint.const_mul mf), integral_const_mul, hfη, hη, mul_one, sub_self]
  obtain ⟨t₀, ht₀, K, hK, B, hB, hbound⟩ := twisted_power_bound T₀ H v ℓ hℓv hℓT hT₀P hPT₀
    s'.decay_nonneg s'.decay_lt_one hgap hHv
  refine ⟨4 * K * t₀ ^ 2, K, by positivity, hK, fun x => ?_⟩
  -- A lower bound for the normalized survival mass at `x`.
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  set a : ℕ → ℝ := fun n => r⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ with ha_def
  have ha_pos : ∀ n, 0 < a n := fun n => by
    refine mul_pos (pow_pos (inv_pos.2 hr) _) ?_
    have hp := C.pathMeasure_survival_pos x.val hx n
    rw [C.pathMeasure_survival] at hp
    have : IsFiniteKernel (C.killedTransition ^ n) := killedKernel_power_isFinite C.toKilledKernel n
    exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have ha_lim : Tendsto a atTop (𝓝 (d.weight x.val).toReal) := by
    have := s.normalized_survival_tendstoUniformly.tendsto_at x.val
    exact this.congr fun n => normalized_survival_toReal (K := C.toKilledKernel) d n x.val
  obtain ⟨c, hc, hca⟩ := SecondMoment.exists_pos_lower ha_pos
    (ENNReal.toReal_pos x.property (d.weight_ne_top _)) ha_lim
  -- The exponential moment bound.
  set A0 := Real.exp (t₀ * (2 * Fp)) with hA0_def
  have hA0 : 0 < A0 := Real.exp_pos _
  set M1 := max 1 (A0 * B * ‖T₀‖) with hM1_def
  set Bx := A0 * M1 / (r * c) with hBx_def
  have hBx : 0 < Bx := by positivity
  have hmgf : ∀ t, |t| ≤ t₀ → ∀ n, 1 ≤ n →
      ∫ ω, Real.exp (t * pathBirkhoffSum fbar.toFun n ω) ∂C.conditionedMeasure x.val n ≤
        Bx * Real.exp (K * n * t ^ 2) := by
    intro t ht n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [integral_conditioned_exp C fbar.measurable fbar.bound_nonneg fbar.le_bound]
    set g := expMultiplier fbar t with hg_def
    have hgA : g.bound ≤ A0 := by
      simp only [hg_def, expMultiplier, hA0_def, Real.exp_le_exp, fbar]
      exact mul_le_mul_of_nonneg_right ht (by positivity)
    have hA : NormedSpace.exp (t • H) = mulL g := exp_smul_mulL fbar t
    set A : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := mulL g with hA_def
    have hAn : ‖A‖ ≤ A0 := (norm_mulL_le g).trans hgA
    -- `(A ∘ T₀)ᵐ` is bounded through the twisted family `T₀ ∘ A`.
    have hpow : ∀ k : ℕ, ‖(A * T₀) ^ k‖ ≤ M1 * Real.exp (K * k * t ^ 2) := by
      intro k
      rcases k with _ | k
      · simp only [pow_zero, CharP.cast_eq_zero, mul_zero, zero_mul, Real.exp_zero, mul_one]
        exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)
      · rw [mul_pow_succ_eq]
        have h1 := hbound t ht k
        rw [hA] at h1
        calc ‖A * (T₀ * A) ^ k * T₀‖ ≤ ‖A‖ * ‖(T₀ * A) ^ k‖ * ‖T₀‖ :=
              (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _))
          _ ≤ A0 * (B * Real.exp (K * k * t ^ 2)) * ‖T₀‖ := by gcongr
          _ = A0 * B * ‖T₀‖ * Real.exp (K * k * t ^ 2) := by ring
          _ ≤ M1 * Real.exp (K * ↑(k + 1) * t ^ 2) := by
              apply mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
                (le_max_left _ _ |>.trans' zero_le_one)
              push_cast
              nlinarith [sq_nonneg t]
    -- The class of the constant one.
    set one : Lp ℝ ∞ ρ := (memLp_top_const (μ := ρ) (1 : ℝ)).toLp _ with hone_def
    have hone : (one : M → ℝ) =ᵐ[ρ] fun _ => 1 := (memLp_top_const (1 : ℝ)).coeFn_toLp
    have hone_n : ‖one‖ ≤ 1 := by
      refine (Lp.norm_le_of_ae_bound zero_le_one ?_).trans_eq (by simp)
      filter_upwards [hone] with y hy
      rw [hy]; simp
    have hrepr := iterate_step_ae C h g one hone m
    set w := ((A * Top) ^ m) one with hw_def
    have hATop : ∀ k : ℕ, (A * Top) ^ k = r ^ k • (A * T₀) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ (A * Top), ih, pow_succ (A * T₀), pow_succ r]
        ext1 u
        simp only [mul_apply_eq_comp, smul_apply, hT₀_def,
          map_smul, smul_smul]
        congr 1
        field_simp
    have hw : ‖w‖ ≤ r ^ m * (M1 * Real.exp (K * m * t ^ 2)) := by
      rw [hw_def, hATop]
      calc ‖(r ^ m • (A * T₀) ^ m) one‖ ≤ ‖r ^ m • (A * T₀) ^ m‖ * ‖one‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖r ^ m • (A * T₀) ^ m‖ * 1 := mul_le_mul_of_nonneg_left hone_n (norm_nonneg _)
        _ = r ^ m * ‖(A * T₀) ^ m‖ := by
            rw [mul_one, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr m)]
        _ ≤ r ^ m * (M1 * Real.exp (K * m * t ^ 2)) :=
            mul_le_mul_of_nonneg_left (hpow m) (pow_pos hr m).le
    have hU : (step C g.toFun)^[m + 1] (fun _ => 1) x.val ≤
        A0 * (r ^ m * (M1 * Real.exp (K * m * t ^ 2))) := by
      rw [Function.iterate_succ_apply']
      simp only [step]
      have hint : ∫ z, (step C g.toFun)^[m] (fun _ => 1) z ∂C.killedTransition x.val =
          ∫ z, w z ∂C.killedTransition x.val :=
        integral_congr_ae ((h.absolutelyContinuous x.val).ae_eq hrepr.symm)
      rw [hint]
      have hk := h.kernel_integral_norm_le w x.val
      have hgx : g.toFun x.val ≤ A0 := (le_abs_self _).trans ((g.le_bound _).trans hgA)
      have hgx0 : 0 ≤ g.toFun x.val := (Real.exp_pos _).le
      calc g.toFun x.val * ∫ z, w z ∂C.killedTransition x.val
          ≤ g.toFun x.val * ‖w‖ :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans (by simpa using hk)) hgx0
        _ ≤ A0 * (r ^ m * (M1 * Real.exp (K * m * t ^ 2))) :=
            mul_le_mul hgx hw (norm_nonneg _) hA0.le
    have hden : (C.pathMeasure x.val (survival (m + 1))).toReal = r ^ (m + 1) * a (m + 1) := by
      rw [C.pathMeasure_survival, ha_def]
      simp only
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul]
      rfl
    rw [hden]
    have han := hca (m + 1)
    have hden_pos : 0 < r ^ (m + 1) * a (m + 1) := mul_pos (pow_pos hr _) (ha_pos _)
    rw [← div_eq_inv_mul, div_le_iff₀ hden_pos]
    calc (step C g.toFun)^[m + 1] (fun _ => 1) x.val
        ≤ A0 * (r ^ m * (M1 * Real.exp (K * m * t ^ 2))) := hU
      _ ≤ Bx * Real.exp (K * ↑(m + 1) * t ^ 2) * (r ^ (m + 1) * a (m + 1)) := by
        have he : Real.exp (K * m * t ^ 2) ≤ Real.exp (K * ↑(m + 1) * t ^ 2) := by
          apply Real.exp_le_exp.2; push_cast; nlinarith [sq_nonneg t]
        rw [hBx_def, pow_succ r m]
        have hM1 : 0 < M1 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        have hrm : 0 < r ^ m := pow_pos hr m
        rw [show A0 * M1 / (r * c) * Real.exp (K * ↑(m + 1) * t ^ 2) * (r ^ m * r * a (m + 1))
          = A0 * M1 * Real.exp (K * ↑(m + 1) * t ^ 2) * r ^ m * (a (m + 1) / c) by
            field_simp]
        have hac : 1 ≤ a (m + 1) / c := by rw [le_div_iff₀ hc]; linarith
        calc A0 * (r ^ m * (M1 * Real.exp (K * m * t ^ 2)))
            ≤ A0 * M1 * Real.exp (K * ↑(m + 1) * t ^ 2) * r ^ m * 1 := by
              rw [mul_one]
              have := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ A0 * M1 * r ^ m)
              nlinarith [this]
          _ ≤ _ := mul_le_mul_of_nonneg_left hac (by positivity)
  -- Markov's inequality on both tails.
  refine ⟨max (2 * Bx) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun ε hε n hn => ?_⟩
  set sε := min t₀ (ε / (2 * K)) with hsε_def
  have hs0 : 0 < sε := lt_min ht₀ (by positivity)
  have hst : |sε| ≤ t₀ := by rw [abs_of_pos hs0]; exact min_le_left _ _
  have hst' : |-sε| ≤ t₀ := by rw [abs_neg]; exact hst
  have hsK : K * sε ≤ ε / 2 := by
    have := min_le_right t₀ (ε / (2 * K))
    calc K * sε ≤ K * (ε / (2 * K)) := mul_le_mul_of_nonneg_left this hK.le
      _ = ε / 2 := by field_simp
  have hx' := C.conditionedMeasure_isProbability_of_surviving x.val hx n
  set P := C.conditionedMeasure x.val n with hP_def
  set Sbar : Path M → ℝ := fun ω => pathBirkhoffSum fbar.toFun n ω with hSbar_def
  have hSm : Measurable Sbar := measurable_pathBirkhoffSum fbar.measurable n
  have hSb : ∀ ω, |Sbar ω| ≤ n * (2 * Fp) := by
    intro ω
    simp only [hSbar_def]
    unfold pathBirkhoffSum birkhoffSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range n, |zeroExtension fbar.toFun (ω i)| ≤ ∑ _i ∈ Finset.range n, 2 * Fp :=
          Finset.sum_le_sum fun i _ =>
            SecondMoment.abs_zeroExtension_le fbar.bound_nonneg fbar.le_bound _
      _ = n * (2 * Fp) := by simp
  have hnSb : ∀ ω, |-Sbar ω| ≤ n * (2 * Fp) := fun ω => by rw [abs_neg]; exact hSb ω
  have hup := markov_exp (P := P) hSm hSb hs0.le (n * ε)
  have hlow := markov_exp (P := P) hSm.neg hnSb hs0.le (n * ε)
  have hm1 := hmgf sε hst n hn
  have hm2 := hmgf (-sε) hst' n hn
  have e2 : ∫ ω, Real.exp (sε * (-Sbar) ω) ∂P = ∫ ω, Real.exp (-sε * Sbar ω) ∂P := by
    congr 1; funext ω; simp only [Pi.neg_apply]; ring_nf
  -- The event is contained in the two tails.
  have hsub : {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - mf|} ≤ᵐ[P]
      ({ω | n * ε < Sbar ω} ∪ {ω | n * ε < (-Sbar) ω} : Set (Path M)) := by
    filter_upwards [C.ae_survival_conditionedMeasure x.val n] with ω hω hmem
    have hmem' : ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - mf| := hmem
    have hS : Sbar ω = pathBirkhoffSum f n ω - n * mf :=
      SmallJumpMoment.pathBirkhoffSum_sub_const f mf hω
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have heq : (n : ℝ)⁻¹ * pathBirkhoffSum f n ω - mf = (n : ℝ)⁻¹ * Sbar ω := by
      rw [hS]; field_simp
    rw [heq, abs_mul, abs_of_pos (inv_pos.2 hn0), inv_mul_eq_div, lt_div_iff₀ hn0] at hmem'
    rcases lt_abs.1 (by linarith : n * ε < |Sbar ω|) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by simpa using h1)
  have hγ : min (4 * K * t₀ ^ 2 / 4) (ε ^ 2 / (16 * K)) ≤ sε * ε / 2 :=
    rate_le hK ht₀ hε
  have hexp : Real.exp (-(sε * (n * ε))) * (Bx * Real.exp (K * n * sε ^ 2)) ≤
      Bx * Real.exp (-(min (4 * K * t₀ ^ 2 / 4) (ε ^ 2 / (16 * K))) * n) := by
    rw [mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hBx.le
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : K * n * sε ^ 2 ≤ n * sε * (ε / 2) := by
      have := mul_le_mul_of_nonneg_left hsK (by positivity : 0 ≤ n * sε)
      nlinarith [this]
    nlinarith [mul_le_mul_of_nonneg_right hγ hn0]
  calc P.real {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - ∫ y, f y ∂μ.withDensity d.weight|}
      ≤ P.real ({ω | n * ε < Sbar ω} ∪ {ω | n * ε < (-Sbar) ω}) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ P.real {ω | n * ε < Sbar ω} + P.real {ω | n * ε < (-Sbar) ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-(sε * (n * ε))) * (Bx * Real.exp (K * n * sε ^ 2)) +
        Real.exp (-(sε * (n * ε))) * (Bx * Real.exp (K * n * (-sε) ^ 2)) := by
        refine add_le_add (hup.trans (mul_le_mul_of_nonneg_left hm1 (Real.exp_pos _).le))
          (hlow.trans ?_)
        rw [e2]
        exact mul_le_mul_of_nonneg_left hm2 (Real.exp_pos _).le
    _ = 2 * (Real.exp (-(sε * (n * ε))) * (Bx * Real.exp (K * n * sε ^ 2))) := by
        rw [neg_sq]; ring
    _ ≤ 2 * (Bx * Real.exp (-(min (4 * K * t₀ ^ 2 / 4) (ε ^ 2 / (16 * K))) * n)) :=
        mul_le_mul_of_nonneg_left hexp zero_le_two
    _ ≤ max (2 * Bx) 1 * Real.exp (-(min (4 * K * t₀ ^ 2 / 4) (ε ^ 2 / (16 * K))) * n) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- **Theorem D.** For bounded measurable `h` there is `a_h > 0` such that every `x ∈ M \ Z` has
`C_x > 0` with `ℙ_x(|n⁻¹ ∑_{j<n} h(X_j) - ν(h)| > ε | τ > n) ≤ C_x e^{-a_h ε² n}` for every `ε > 0`
and `n ≥ 1`. It follows from the rate `min{t_h/4, ε²/(16K_h)}`: for `ε > 2‖h‖_∞` the event is empty,
and otherwise the rate is at least `a_h ε²`. -/
theorem conditional_exponential_concentration_sq (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) {f : M → ℝ} (hfm : Measurable f) {F : ℝ}
    (hF : ∀ y, |f y| ≤ F) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : d.State, ∃ Cx : ℝ, 0 < Cx ∧
      ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
        (C.conditionedMeasure x.val n).real
          {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - ∫ y, f y ∂μ.withDensity d.weight|} ≤
        Cx * Real.exp (-(a * ε ^ 2 * n)) := by
  obtain ⟨tf, Kf, htf, hKf, hmain⟩ :=
    conditional_exponential_concentration C h d s hlive μ hleft hnorm hfm hF
  set Fp := max F 0 with hFp_def
  have hFp0 : 0 ≤ Fp := le_max_right _ _
  have hfFp : ∀ y, |f y| ≤ Fp := fun y => (hF y).trans (le_max_left _ _)
  set B := 2 * Fp + 1 with hB_def
  have hB : 0 < B := by positivity
  set a := min (tf / (4 * B ^ 2)) (1 / (16 * Kf)) with ha_def
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  set ν := μ.withDensity d.weight with hν_def
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hνF : |∫ y, f y ∂ν| ≤ Fp := SecondMoment.abs_integral_le_of_prob hfFp
  refine ⟨a, ha, fun x => ?_⟩
  obtain ⟨Cx, hCx, hx⟩ := hmain x
  refine ⟨Cx, hCx, fun ε hε n hn => ?_⟩
  by_cases hεB : ε ≤ B
  · refine (hx ε hε n hn).trans (mul_le_mul_of_nonneg_left ?_ hCx.le)
    rw [Real.exp_le_exp, neg_mul, neg_le_neg_iff]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine mul_le_mul_of_nonneg_right ?_ hn0
    apply le_min
    · have hε2 : ε ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hε.le hεB 2
      calc a * ε ^ 2 ≤ tf / (4 * B ^ 2) * ε ^ 2 :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
        _ ≤ tf / (4 * B ^ 2) * B ^ 2 := mul_le_mul_of_nonneg_left hε2 (by positivity)
        _ = tf / 4 := by field_simp
    · calc a * ε ^ 2 ≤ 1 / (16 * Kf) * ε ^ 2 :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
        _ = ε ^ 2 / (16 * Kf) := by ring
  · have hempty : {ω : Path M | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - ∫ y, f y ∂ν|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      have hsum : |pathBirkhoffSum f n ω| ≤ n * Fp := by
        unfold pathBirkhoffSum birkhoffSum
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i ∈ Finset.range n, |zeroExtension f (ω i)| ≤ ∑ _i ∈ Finset.range n, Fp :=
              Finset.sum_le_sum fun i _ => by
                cases ω i with
                | none => simp [zeroExtension_none, hFp0]
                | some y => simpa [zeroExtension_some] using hfFp y
          _ = n * Fp := by simp
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have havg : |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω| ≤ Fp := by
        rw [abs_mul, abs_of_pos (inv_pos.2 hn'), inv_mul_le_iff₀ hn']
        exact hsum
      calc |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - ∫ y, f y ∂ν|
          ≤ |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω| + |∫ y, f y ∂ν| := abs_sub _ _
        _ ≤ ε := by linarith
    rw [hempty, measureReal_empty]
    positivity

end Main

end

end ConditionedStableLaws.Concentration
