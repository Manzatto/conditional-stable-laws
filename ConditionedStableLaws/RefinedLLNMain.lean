import ConditionedStableLaws.QProcessVariance
import ConditionedStableLaws.RefinedLLNMean
import ConditionedStableLaws.RefinedLLNProbability
import ConditionedStableLaws.Concentration

/-!
# Refined conditional laws of large numbers: (i) and (ii)

Part (i): bounded observables, every initial state in `M \ Z`. Part (ii): `h ∈ L¹(μ)` vanishing on
`Z`, `ν`-a.e. initial state.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.RefinedLLN

noncomputable section

open StandingHypothesis CanonicalChain

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-! ### Time spent in `Z` -/

/-- `E_x[n⁻¹ ∑_{i<n} g(Xᵢ) | τ > n] → 0` for bounded `g ≥ 0` supported in `Z`. -/
theorem conditioned_average_Z_tendsto_zero (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (x : d.State)
    {g : M → ℝ} (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) {B : ℝ} (hgB : ∀ y, g y ≤ B)
    (hgZ : ∀ y, y ∈ survivingSet C.killedTransition → g y = 0) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ * pathBirkhoffSum g n ω)
      ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  set r := d.rate.toReal
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  set S := s.survivalConstant
  set θ := s.decay
  set Bs := s.survivalBound
  have hB0 : 0 ≤ B := (hg0 x.val).trans (hgB _)
  -- `ℙₓ(τ > n) ≥ c λⁿ`.
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ n,
      c ≤ ((d.rate⁻¹) ^ n * (C.toKilledKernel.kernel ^ n) x.val univ).toReal := by
    apply ConditionalTransfer.exists_pos_lower_bound _
      (ENNReal.toReal_pos x.property (d.weight_ne_top _))
      (s.normalized_survival_tendstoUniformly.tendsto_at x.val)
    intro n
    have hpos := C.pathMeasure_survival_pos x.val hx n
    rw [C.pathMeasure_survival] at hpos
    apply ENNReal.toReal_pos
    · exact mul_ne_zero (pow_ne_zero _ (ENNReal.inv_ne_zero.2 d.rate_ne_top)) hpos.ne'
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 d.rate_ne_zero))
        ((C.killedTransition_pow_mass_le_one x.val n).trans_lt ENNReal.one_lt_top).ne
  have hreal (k : ℕ) (y : M) : ((d.rate⁻¹) ^ k * (C.toKilledKernel.kernel ^ k) y univ).toReal =
      r⁻¹ ^ k * ((C.killedTransition ^ k) y).real univ :=
    normalized_survival_toReal (K := C.toKilledKernel) d k y
  have hKn (n : ℕ) : c * r ^ n ≤ ((C.killedTransition ^ n) x.val).real univ := by
    have := hcle n
    rw [hreal, inv_pow, inv_mul_eq_div, le_div_iff₀ (pow_pos hr n)] at this
    exact this
  have hKi (i : ℕ) : ((C.killedTransition ^ i) x.val).real univ ≤ r ^ i * Bs := by
    have := s.normalized_survival_real_le i x.val
    rw [hreal, inv_pow, inv_mul_le_iff₀ (pow_pos hr _)] at this
    exact this
  -- Survival from `Z` decays like `(λθ)ᵏ`.
  have hZsurv (k : ℕ) (y : M) (hy : y ∉ survivingSet C.killedTransition) :
      ((C.killedTransition ^ (k + 1)) y).real univ ≤ r ^ (k + 1) * (S * θ ^ k) := by
    have he := s.normalized_survival_error k y
    have hw : d.weight y = 0 := by
      rw [← hlive] at hy
      exact not_not.1 hy
    rw [hreal, hw, ENNReal.toReal_zero, sub_zero, abs_of_nonneg (mul_nonneg
      (pow_nonneg (inv_nonneg.2 hr.le) _) measureReal_nonneg), inv_pow,
      inv_mul_le_iff₀ (pow_pos hr _)] at he
    exact he
  have hfin (i : ℕ) : ∫⁻ y, ENNReal.ofReal (g y) ∂(C.killedTransition ^ i) x.val ≠ ∞ := by
    have : IsFiniteKernel (C.killedTransition ^ i) := killedKernel_power_isFinite C.toKilledKernel i
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B))
      (measure_ne_top ((C.killedTransition ^ i) x.val) univ)) ?_
    rw [← lintegral_const]
    exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hgB y)
  -- The real form of the conditioned mean is `O(1/n)`.
  set D := B * S * Bs / c
  have hD : 0 ≤ D := by
    have := s.survivalConstant_nonneg; have := s.survivalBound_nonneg; positivity
  have hbound (n : ℕ) : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      (((C.killedTransition ^ n) x.val).real univ)⁻¹ *
        ∫ y, g y * ((C.killedTransition ^ (n - i)) y).real univ ∂(C.killedTransition ^ i) x.val ≤
      (n : ℝ)⁻¹ * (D * (1 - θ)⁻¹) := by
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg n))
    have hpos : 0 < c * r ^ n := mul_pos hc (pow_pos hr n)
    calc ∑ i ∈ Finset.range n, (((C.killedTransition ^ n) x.val).real univ)⁻¹ *
          ∫ y, g y * ((C.killedTransition ^ (n - i)) y).real univ ∂(C.killedTransition ^ i) x.val
        ≤ ∑ i ∈ Finset.range n, D * θ ^ (n - 1 - i) := by
          apply Finset.sum_le_sum
          intro i hi
          have hin := Finset.mem_range.1 hi
          have hk : n - i = (n - 1 - i) + 1 := by omega
          have : IsFiniteKernel (C.killedTransition ^ i) :=
            killedKernel_power_isFinite C.toKilledKernel i
          have hpt (y : M) : g y * ((C.killedTransition ^ (n - i)) y).real univ ≤
              B * (r ^ (n - i) * (S * θ ^ (n - 1 - i))) := by
            by_cases hy : y ∈ survivingSet C.killedTransition
            · rw [hgZ y hy, zero_mul]
              exact mul_nonneg hB0 (mul_nonneg (pow_nonneg hr.le _)
                (mul_nonneg s.survivalConstant_nonneg (pow_nonneg s.decay_nonneg _)))
            · rw [hk]
              exact mul_le_mul (hgB y) (hZsurv _ y hy) measureReal_nonneg hB0
          have hint := norm_integral_le_of_norm_le_const (μ := (C.killedTransition ^ i) x.val)
            (C := B * (r ^ (n - i) * (S * θ ^ (n - 1 - i))))
            (Eventually.of_forall fun y => by
              rw [Real.norm_of_nonneg (mul_nonneg (hg0 y) measureReal_nonneg)]
              exact hpt y)
          rw [Real.norm_eq_abs] at hint
          have hI := (le_abs_self _).trans hint
          have hθ : 0 ≤ θ ^ (n - 1 - i) := pow_nonneg s.decay_nonneg _
          have hS := s.survivalConstant_nonneg
          calc (((C.killedTransition ^ n) x.val).real univ)⁻¹ *
                ∫ y, g y * ((C.killedTransition ^ (n - i)) y).real univ ∂(C.killedTransition ^ i) x.val
              ≤ (c * r ^ n)⁻¹ * (B * (r ^ (n - i) * (S * θ ^ (n - 1 - i))) *
                  ((C.killedTransition ^ i) x.val).real univ) := by
                apply mul_le_mul (inv_anti₀ hpos (hKn n)) hI
                  (integral_nonneg fun y => mul_nonneg (hg0 y) measureReal_nonneg)
                  (inv_nonneg.2 hpos.le)
            _ ≤ (c * r ^ n)⁻¹ * (B * (r ^ (n - i) * (S * θ ^ (n - 1 - i))) * (r ^ i * Bs)) := by
                gcongr
                exact hKi i
            _ = D * θ ^ (n - 1 - i) := by
                have hrn : r ^ n = r ^ i * r ^ (n - i) := by
                  rw [← pow_add, Nat.add_sub_cancel' hin.le]
                simp only [D]
                rw [hrn]
                field_simp
      _ = D * ∑ j ∈ Finset.range n, θ ^ j := by
          rw [← Finset.mul_sum, Finset.sum_range_reflect (fun j => θ ^ j) n]
      _ ≤ D * (1 - θ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ hD
          rw [← tsum_geometric_of_lt_one s.decay_nonneg s.decay_lt_one]
          exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg s.decay_nonneg j)
            (summable_geometric_of_lt_one s.decay_nonneg s.decay_lt_one)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (D * (1 - θ)⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
      (D * (1 - θ)⁻¹)
  rw [← ENNReal.ofReal_zero]
  refine (ENNReal.tendsto_ofReal (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hlim (fun n => ?_) hbound)).congr fun n => ?_
  · exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (inv_nonneg.2 measureReal_nonneg)
        (integral_nonneg fun y => mul_nonneg (hg0 y) measureReal_nonneg))
  · exact (conditioned_average_eq_ofReal C x.val hx n hg hg0 hfin).symm

/-! ### Part (i): bounded observables, every initial state -/

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem abs_avg_le {g : M → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hgB : ∀ y, |g y| ≤ B) (n : ℕ)
    (ω : Path M) : |(n : ℝ)⁻¹ * pathBirkhoffSum g n ω| ≤ B := by
  have hsum : |pathBirkhoffSum g n ω| ≤ n * B := by
    unfold pathBirkhoffSum birkhoffSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range n, |zeroExtension g (ω i)| ≤ ∑ _i ∈ Finset.range n, B := by
          apply Finset.sum_le_sum
          intro i _
          cases hω : ω i with
          | none => simp [zeroExtension_none, hB0]
          | some y => rw [zeroExtension_some]; exact hgB y
      _ = n * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn, hB0]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_mul, abs_inv, Nat.abs_cast, inv_mul_le_iff₀ hn']
    exact hsum

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurable_avg {g : M → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (fun ω : Path M => (n : ℝ)⁻¹ * pathBirkhoffSum g n ω) :=
  (measurable_pathBirkhoffSum hg n).const_mul _

/-- **Refined conditional LLN (i).** For every bounded measurable `h` and every `x ∈ M \ Z`,
`E_x[|Γₙ - ν(h)| | τ > n] → 0`. -/
theorem lln_bounded (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {f : M → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : d.State) :
    Tendsto (fun n : ℕ => ∫ ω, |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω -
      ∫ y, f y ∂μ.withDensity d.weight| ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
  have hx : x.val ∈ survivingSet C.killedTransition := by
    rw [← hlive]
    exact x.property
  let Γ := ∫ y, f y ∂μ.withDensity d.weight
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x.val)
  let : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) :=
    fun n ↦ C.conditionedMeasure_isProbability_of_surviving x.val hx n
  obtain ⟨a, ha, hmain⟩ :=
    Concentration.conditional_exponential_concentration_sq C h d s hlive μ hleft hnorm hf hB
  obtain ⟨K, _hK, hKbound⟩ := hmain x
  apply BoundedConvergence.tendsto_integral_abs_of_bounded_in_probability
    (fun n ↦ C.conditionedMeasure x.val n)
    (fun n ω ↦ (n : ℝ)⁻¹ * pathBirkhoffSum f n ω - Γ)
    (fun n ↦ (measurable_avg hf n).sub_const Γ) (B + |Γ|)
  · intro n
    exact Eventually.of_forall fun ω ↦
      (abs_sub _ _).trans (add_le_add (abs_avg_le hB0 hB n ω) le_rfl)
  · apply BoundedConvergence.tendsto_in_probability_of_exponential_bound _ _ ha
    intro ε hε
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hKbound ε hε n hn

/-! ### Part (ii): `h ∈ L¹(μ)` vanishing on `Z`, `ν`-a.e. initial state -/

omit [MeasurableSpace M] in
omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem pathBirkhoffSum_add (g₁ g₂ : M → ℝ) (n : ℕ) (ω : Path M) :
    pathBirkhoffSum (g₁ + g₂) n ω = pathBirkhoffSum g₁ n ω + pathBirkhoffSum g₂ n ω := by
  unfold pathBirkhoffSum birkhoffSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  cases ω i <;> simp [zeroExtension]

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem abs_pathBirkhoffSum_le (g : M → ℝ) (n : ℕ) (ω : Path M) :
    |pathBirkhoffSum g n ω| ≤ pathBirkhoffSum (fun y => |g y|) n ω := by
  unfold pathBirkhoffSum birkhoffSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  cases ω i <;> simp [zeroExtension]

/-- **Refined conditional LLN (ii).** For measurable `h` vanishing on `Z` with `h ∈ L¹(μ)`, for
`ν`-almost every `x ∈ M \ Z`, `E_x[|Γₙ - ν(h)| | τ > n] → 0`. -/
theorem lln_L1 (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {f : M → ℝ} (hf : Measurable f) (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0)
    (hfi : Integrable f μ) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M),
      Tendsto (fun n : ℕ => ∫ ω, |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω -
        ∫ y, f y ∂μ.withDensity d.weight| ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
  set μ' := μ.withDensity d.weight
  set Γ := ∫ y, f y ∂μ'
  -- `f ∈ L¹(ν)` since `η` is bounded.
  obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d s.continuous_weight
  have hwle (y : M) : d.weight y ≤ ENNReal.ofReal Bη := by
    rw [← ENNReal.ofReal_toReal (d.weight_ne_top y)]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hBη y))
  have hfi' : Integrable f μ' :=
    integrable_weighted_of_integrable ENNReal.ofReal_ne_top (ae_of_all _ hwle) hfi
  -- Truncations.
  set hK : ℕ → M → ℝ := fun K => {y | |f y| ≤ K}.indicator f
  set gK : ℕ → M → ℝ := fun K => {y | |f y| ≤ K}ᶜ.indicator f
  set tK : ℕ → M → ℝ := fun K => {y | |f y| ≤ K}ᶜ.indicator fun y => |f y|
  have hSm (K : ℕ) : MeasurableSet {y | |f y| ≤ (K : ℝ)} :=
    measurableSet_le (continuous_abs.measurable.comp hf) measurable_const
  have hhKm (K : ℕ) : Measurable (hK K) := hf.indicator (hSm K)
  have hgKm (K : ℕ) : Measurable (gK K) := hf.indicator (hSm K).compl
  have htKm (K : ℕ) : Measurable (tK K) :=
    (continuous_abs.measurable.comp hf).indicator (hSm K).compl
  have hsplit (K : ℕ) : f = hK K + gK K := (Set.indicator_self_add_compl _ f).symm
  have hhKb (K : ℕ) (y : M) : |hK K y| ≤ K := by
    by_cases hy : y ∈ {y | |f y| ≤ (K : ℝ)}
    · simp only [hK, Set.indicator_of_mem hy]; exact hy
    · simp only [hK, Set.indicator_of_notMem hy, abs_zero]; exact Nat.cast_nonneg K
  have habs (K : ℕ) : (fun y => |gK K y|) = tK K := by
    funext y
    simp only [gK, tK]
    by_cases hy : y ∈ {y | |f y| ≤ (K : ℝ)}ᶜ
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have htK0 (K : ℕ) (y : M) : 0 ≤ tK K y := Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
  have htKZ (K : ℕ) : ∀ z ∈ escapingSet C.killedTransition, tK K z = 0 := by
    intro z hz
    simp only [tK]
    by_cases h' : z ∈ {y | |f y| ≤ (K : ℝ)}ᶜ
    · rw [Set.indicator_of_mem h', hZ z hz, abs_zero]
    · rw [Set.indicator_of_notMem h']
  have htKi (K : ℕ) : Integrable (tK K) μ := by
    rw [← habs K]
    exact (hfi.indicator (hSm K).compl).abs
  -- Step 3 for every tail, simultaneously.
  have hstep3 : ∀ᵐ x ∂(μ'.comap (Subtype.val : d.State → M)), ∀ K : ℕ,
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ * pathBirkhoffSum (tK K) n ω)
        ∂C.conditionedMeasure x.val n) atTop (𝓝 (ENNReal.ofReal (∫ y, tK K y ∂μ'))) :=
    ae_all_iff.2 fun K => lln_mean_nonneg C h d s hlive μ hleft hnorm (htKm K) (htK0 K)
      (htKZ K) (htKi K)
  -- The tails vanish in `L¹(ν)`.
  have htail : Tendsto (fun K : ℕ => ∫ y, tK K y ∂μ') atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ') (F := fun K => tK K)
      (f := fun _ => (0 : ℝ)) (fun y => |f y|) (fun K => (htKm K).aestronglyMeasurable)
      hfi'.abs (fun K => Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (htK0 K y), ← habs K]
        simp only [gK]
        by_cases hy : y ∈ {y | |f y| ≤ (K : ℝ)}ᶜ
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy])
      (Eventually.of_forall fun y => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈|f y|⌉₊] with K hK
        simp only [tK]
        rw [Set.indicator_of_notMem]
        simp only [mem_compl_iff, Set.mem_ofPred_eq, not_not]
        exact (Nat.le_ceil _).trans (by exact_mod_cast hK))
    simpa using this
  filter_upwards [hstep3] with x hx3
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  have := fun n => C.conditionedMeasure_isProbability_of_surviving x.val hx n
  -- Notation for the averages.
  set A : (M → ℝ) → ℕ → Path M → ℝ := fun g n ω => (n : ℝ)⁻¹ * pathBirkhoffSum g n ω
  have hAm (g : M → ℝ) (hg : Measurable g) (n : ℕ) : Measurable (A g n) :=
    measurable_avg hg n
  set L : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal |A f n ω - Γ| ∂C.conditionedMeasure x.val n
  -- Pointwise truncation inequality.
  have hpt (K n : ℕ) (ω : Path M) :
      |A f n ω - Γ| ≤ |A (hK K) n ω - ∫ y, hK K y ∂μ'| + A (tK K) n ω + ∫ y, tK K y ∂μ' := by
    have hΓ : Γ = ∫ y, hK K y ∂μ' + ∫ y, gK K y ∂μ' := by
      simp only [Γ]
      conv_lhs => rw [hsplit K]
      exact integral_add ((hfi'.indicator (hSm K))) (hfi'.indicator (hSm K).compl)
    have hA : A f n ω = A (hK K) n ω + A (gK K) n ω := by
      simp only [A]
      conv_lhs => rw [hsplit K]
      rw [pathBirkhoffSum_add, mul_add]
    have h1 : |A (gK K) n ω| ≤ A (tK K) n ω := by
      simp only [A]
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)⁻¹ from inv_nonneg.2 (Nat.cast_nonneg n)),
        ← habs K]
      exact mul_le_mul_of_nonneg_left (abs_pathBirkhoffSum_le _ n ω)
        (inv_nonneg.2 (Nat.cast_nonneg n))
    have h2 : |∫ y, gK K y ∂μ'| ≤ ∫ y, tK K y ∂μ' := by
      rw [← habs K]; exact abs_integral_le_integral_abs
    rw [hA, hΓ]
    calc |A (hK K) n ω + A (gK K) n ω - (∫ y, hK K y ∂μ' + ∫ y, gK K y ∂μ')|
        = |(A (hK K) n ω - ∫ y, hK K y ∂μ') + A (gK K) n ω - ∫ y, gK K y ∂μ'| := by ring_nf
      _ ≤ |A (hK K) n ω - ∫ y, hK K y ∂μ'| + |A (gK K) n ω| + |∫ y, gK K y ∂μ'| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by gcongr
  -- The bounded part tends to zero (part (i)), in lintegral form.
  have hbdd (K : ℕ) : Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |A (hK K) n ω -
      ∫ y, hK K y ∂μ'| ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
    have h1 := lln_bounded C h d s hlive μ hleft hnorm (hhKm K) (hhKb K) x
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.tendsto_ofReal h1).congr fun n => ?_
    refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun ω => abs_nonneg _))
    exact Integrable.of_bound
      ((continuous_abs.measurable.comp ((hAm _ (hhKm K) n).sub_const _)).aestronglyMeasurable)
      (K + |∫ y, hK K y ∂μ'|) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (add_le_add (abs_avg_le (Nat.cast_nonneg K) (hhKb K) n ω) le_rfl))
  -- Lintegral form of the truncation inequality.
  have hLle (K n : ℕ) : L n ≤ ∫⁻ ω, ENNReal.ofReal |A (hK K) n ω - ∫ y, hK K y ∂μ'|
      ∂C.conditionedMeasure x.val n +
      ∫⁻ ω, ENNReal.ofReal (A (tK K) n ω) ∂C.conditionedMeasure x.val n +
      ENNReal.ofReal (∫ y, tK K y ∂μ') := by
    have htA (ω : Path M) : 0 ≤ A (tK K) n ω := by
      refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) ?_
      unfold pathBirkhoffSum birkhoffSum
      exact Finset.sum_nonneg fun i _ => by cases ω i <;> simp [zeroExtension, htK0]
    have hν0 : 0 ≤ ∫ y, tK K y ∂μ' := integral_nonneg (htK0 K)
    calc L n ≤ ∫⁻ ω, (ENNReal.ofReal |A (hK K) n ω - ∫ y, hK K y ∂μ'| +
          ENNReal.ofReal (A (tK K) n ω) + ENNReal.ofReal (∫ y, tK K y ∂μ'))
          ∂C.conditionedMeasure x.val n := by
          apply lintegral_mono
          intro ω
          simp only
          rw [← ENNReal.ofReal_add (abs_nonneg _) (htA ω),
            ← ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (htA ω)) hν0]
          exact ENNReal.ofReal_le_ofReal (hpt K n ω)
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_right _
            ((hAm _ (htKm K) n).ennreal_ofReal), lintegral_const, measure_univ, mul_one]
  -- `L n → 0`.
  have hL : Tendsto L atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hεt : ε = ∞
    · exact Eventually.of_forall fun n => by rw [hεt]; exact le_top
    have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
    have htailE : Tendsto (fun K : ℕ => ENNReal.ofReal (∫ y, tK K y ∂μ')) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal htail
    obtain ⟨K, hKε⟩ := ((ENNReal.tendsto_nhds_zero.1 htailE) (ε / 4) hε4).exists
    have h1 := (ENNReal.tendsto_nhds_zero.1 (hbdd K)) (ε / 4) hε4
    have h2 : ∀ᶠ n in atTop, ∫⁻ ω, ENNReal.ofReal (A (tK K) n ω) ∂C.conditionedMeasure x.val n ≤
        ENNReal.ofReal (∫ y, tK K y ∂μ') + ε / 4 :=
      (hx3 K).eventually (Iic_mem_nhds (ENNReal.lt_add_right ENNReal.ofReal_ne_top hε4.ne'))
    filter_upwards [h1, h2] with n hn1 hn2
    calc L n ≤ ε / 4 + (ENNReal.ofReal (∫ y, tK K y ∂μ') + ε / 4) +
          ENNReal.ofReal (∫ y, tK K y ∂μ') :=
          (hLle K n).trans (add_le_add (add_le_add hn1 hn2) le_rfl)
      _ ≤ ε / 4 + (ε / 4 + ε / 4) + ε / 4 := by gcongr
      _ = ε := by
          rw [show ε / 4 + (ε / 4 + ε / 4) + ε / 4 = ε / 4 * 4 by ring]
          exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  -- Back to the Bochner integral.
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL
  rw [ENNReal.toReal_zero] at h1
  refine h1.congr fun n => ?_
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => abs_nonneg _)
    (continuous_abs.measurable.comp ((hAm f hf n).sub_const Γ)).aestronglyMeasurable).symm

end

end ConditionedStableLaws.RefinedLLN
