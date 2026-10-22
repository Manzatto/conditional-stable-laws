import ConditionedStableLaws.QProcessCesaro

/-!
# Conditional means of nonnegative integrable observables

The nonnegative mean step for Theorem F(ii). The pointwise Cesàro inputs come from the Doob-kernel
maximal argument.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.RefinedLLN

noncomputable section

open StandingHypothesis CanonicalChain

section Step3Main

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- **Step 3**, for nonnegative observables. For measurable `h ≥ 0` vanishing on `Z` with `h ∈
L¹(μ)`, for `ν`-almost every `x ∈ M \ Z`, `E_x[Γₙ | τ > n] → ν(h)`. -/
theorem lln_mean_nonneg (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    {g : M → ℝ} (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (hZ : ∀ z ∈ escapingSet C.killedTransition, g z = 0) (hgi : Integrable g μ) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M),
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ * pathBirkhoffSum g n ω)
        ∂C.conditionedMeasure x.val n) atTop
        (𝓝 (ENNReal.ofReal (∫ y, g y ∂μ.withDensity d.weight))) := by
  set ν := (μ.withDensity d.weight).comap (Subtype.val : d.State → M)
  set Γ := ∫ y, g y ∂μ.withDensity d.weight
  have : IsProbabilityMeasure ν := d.isProbabilityMeasure_weightedMeasure μ hnorm
  -- The eigenfunction is bounded.
  obtain ⟨Bη, hBη⟩ : ∃ B : ℝ, ∀ y, (d.weight y).toReal ≤ B := by
    let f : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨_, s.continuous_weight_toReal⟩
    exact ⟨‖f‖, fun y => (le_abs_self _).trans (f.norm_coe_le_norm y)⟩
  have hwle (y : M) : d.weight y ≤ ENNReal.ofReal Bη := by
    rw [← ENNReal.ofReal_toReal (d.weight_ne_top y)]
    exact ENNReal.ofReal_le_ofReal (hBη y)
  have hgν : Integrable (fun x : d.State => g x.val) ν :=
    integrable_live d μ (integrable_weighted_of_integrable ENNReal.ofReal_ne_top
      (ae_of_all _ hwle) hgi)
  -- `u = h/η`, extended by zero.
  set u : M → ℝ := fun y => g y / (d.weight y).toReal
  have hu0 (y : M) : 0 ≤ u y := div_nonneg (hg0 y) ENNReal.toReal_nonneg
  have hum : Measurable u := hg.div d.measurable_weight.ennreal_toReal
  have hgZ (y : M) (hy : d.weight y = 0) : g y = 0 := by
    apply hZ
    have : y ∉ d.liveSet := fun h' => h' hy
    rw [hlive] at this
    simpa [survivingSet] using this
  have hug (y : M) : u y * (d.weight y).toReal = g y := by
    by_cases hy : d.weight y = 0
    · simp [u, hy, hgZ y hy]
    · exact div_mul_cancel₀ _ (ENNReal.toReal_ne_zero.2 ⟨hy, d.weight_ne_top y⟩)
  have hugE (y : M) : d.weight y * ENNReal.ofReal (u y) = ENNReal.ofReal (g y) := by
    rw [← hug y, ENNReal.ofReal_mul (hu0 y), ENNReal.ofReal_toReal (d.weight_ne_top y),
      mul_comm]
  have hgfin : ∫⁻ y, ENNReal.ofReal (g y) ∂μ ≠ ∞ := hgi.lintegral_lt_top.ne
  have huν : Integrable (fun x : d.State => u x.val) ν := by
    apply integrable_live d μ
    refine integrable_of_lintegral_ne_top hum hu0 ?_
    rw [lintegral_withDensity_eq_lintegral_mul _ d.measurable_weight hum.ennreal_ofReal]
    simp only [Pi.mul_apply, hugE]
    exact hgfin
  have hB := QProcessCesaro.nonneg_kernel_cesaro h d s.continuous_weight μ hleft hnorm
    (g := fun y : d.State => g y.val)
    (hg.comp measurable_subtype_coe) hgν (fun y => hg0 y.val)
  have hC := QProcessCesaro.nonneg_kernel_cesaro h d s.continuous_weight μ hleft hnorm
    (g := fun y : d.State => u y.val)
    (hum.comp measurable_subtype_coe) huν (fun y => hu0 y.val)
  have hfinν := ae_live_of_ae d μ
    (ae_lintegral_kernel_pow_ne_top hleft d.rate_ne_top hg.ennreal_ofReal hgfin)
  filter_upwards [hB, hC, hfinν] with x hBx hCx hfx
  -- Notation at the fixed initial state.
  set r := d.rate.toReal
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  set ηx := (d.weight x.val).toReal
  have hηx : 0 < ηx := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  set S := s.survivalConstant
  set θ := s.decay
  have hgK (i : ℕ) : Integrable g ((C.killedTransition ^ i) x.val) :=
    integrable_of_lintegral_ne_top hg hg0 (hfx i)
  set q : ℕ → ℝ := fun i => ∫ y, g y.val ∂(d.kernel ^ i) x
  set q' : ℕ → ℝ := fun i => ∫ y, u y.val ∂(d.kernel ^ i) x
  change Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q i)
    atTop (𝓝 (∫ y, g y.val ∂ν)) at hBx
  change Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q' i)
    atTop (𝓝 (∫ y, u y.val ∂ν)) at hCx
  have hfinw (i : ℕ) {F : M → ℝ} (hF0 : ∀ y, 0 ≤ F y) {B' : ℝ} (hB' : 0 ≤ B')
      (hFle : ∀ y, F y * (d.weight y).toReal ≤ B' * g y) :
      ∫⁻ y, ENNReal.ofReal (F y) * d.weight y ∂(C.killedTransition ^ i) x.val ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B')) (hfx i)) ?_
    rw [← lintegral_const_mul _ hg.ennreal_ofReal]
    apply lintegral_mono
    intro y
    simp only
    rw [← ENNReal.ofReal_toReal (d.weight_ne_top y), ← ENNReal.ofReal_mul (hF0 y),
      ← ENNReal.ofReal_mul hB']
    exact ENNReal.ofReal_le_ofReal (hFle y)
  have hBη0 : 0 ≤ Bη := ENNReal.toReal_nonneg.trans (hBη x.val)
  have hD1 (i : ℕ) : ηx * q i =
      r⁻¹ ^ i * ∫ y, g y * (d.weight y).toReal ∂(C.killedTransition ^ i) x.val :=
    doob_pow_integral d i x hg hg0 (hfinw i hg0 hBη0 fun y => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hBη y) (hg0 y))
  have hD2 (i : ℕ) : ηx * q' i = r⁻¹ ^ i * ∫ y, g y ∂(C.killedTransition ^ i) x.val := by
    have := doob_pow_integral d i x hum hu0 (hfinw i hu0 zero_le_one fun y => by
      rw [hug y, one_mul])
    simpa only [hug] using this
  -- Normalized survival masses.
  set e : ℕ → M → ℝ := fun k y => r⁻¹ ^ k * ((C.killedTransition ^ k) y).real univ
  have he_err (k : ℕ) (y : M) : |e (k + 1) y - (d.weight y).toReal| ≤ S * θ ^ k := by
    have := s.normalized_survival_error k y
    rw [normalized_survival_toReal (K := C.toKilledKernel) d (k + 1) y] at this
    exact this
  have he_meas (k : ℕ) : Measurable (e k) :=
    measurable_const.mul ((Kernel.measurable_coe _ MeasurableSet.univ).ennreal_toReal)
  have he_bd (k : ℕ) (y : M) : ‖e k y‖ ≤ s.survivalBound := by
    have := s.normalized_survival_real_le k y
    rw [normalized_survival_toReal (K := C.toKilledKernel) d k y] at this
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.2 hr.le) _) measureReal_nonneg)]
    exact this
  have ha : Tendsto (fun n => e n x.val) atTop (𝓝 ηx) := by
    have := s.normalized_survival_tendstoUniformly.tendsto_at x.val
    exact this.congr fun n => normalized_survival_toReal (K := C.toKilledKernel) d n x.val
  -- The exact formula and its decomposition.
  set D : ℕ → ℕ → ℝ := fun n i => r⁻¹ ^ i *
    ∫ y, g y * (e (n - i) y - (d.weight y).toReal) ∂(C.killedTransition ^ i) x.val
  have hpowe (k : ℕ) (y : M) : ((C.killedTransition ^ k) y).real univ = r ^ k * e k y := by
    simp only [e]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul]
  have hηbd (y : M) : ‖(d.weight y).toReal‖ ≤ Bη := by
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]; exact hBη y
  have hint1 (i k : ℕ) : Integrable (fun y => g y * e k y) ((C.killedTransition ^ i) x.val) :=
    (hgK i).mul_bdd (he_meas k).aestronglyMeasurable (Eventually.of_forall (he_bd k))
  have hint2 (i : ℕ) : Integrable (fun y => g y * (d.weight y).toReal)
      ((C.killedTransition ^ i) x.val) :=
    (hgK i).mul_bdd d.measurable_weight.ennreal_toReal.aestronglyMeasurable
      (Eventually.of_forall hηbd)
  have hterm (n i : ℕ) (hi : i < n) :
      (((C.killedTransition ^ n) x.val).real univ)⁻¹ *
        ∫ y, g y * ((C.killedTransition ^ (n - i)) y).real univ ∂(C.killedTransition ^ i) x.val =
      (e n x.val)⁻¹ * (ηx * q i + D n i) := by
    simp_rw [hpowe]
    have hsplit : ∫ y, g y * e (n - i) y ∂(C.killedTransition ^ i) x.val =
        ∫ y, g y * (d.weight y).toReal ∂(C.killedTransition ^ i) x.val +
          ∫ y, g y * (e (n - i) y - (d.weight y).toReal) ∂(C.killedTransition ^ i) x.val := by
      have h3 : Integrable (fun y => g y * (e (n - i) y - (d.weight y).toReal))
          ((C.killedTransition ^ i) x.val) := by
        have := (hint1 i (n - i)).sub (hint2 i)
        simp only [mul_sub]
        exact this
      rw [← integral_add (hint2 i) h3]
      congr 1
      funext y
      ring
    have hcomm : (fun y => g y * (r ^ (n - i) * e (n - i) y)) =
        fun y => r ^ (n - i) * (g y * e (n - i) y) := by
      funext y; ring
    rw [hcomm, integral_const_mul, hsplit, hD1 i]
    simp only [D]
    have hrn : r ^ n = r ^ i * r ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi.le]
    rw [hrn]
    have hri : r ^ i ≠ 0 := pow_ne_zero _ hr.ne'
    have hrni : r ^ (n - i) ≠ 0 := pow_ne_zero _ hr.ne'
    rw [inv_pow]
    field_simp
  have hDb (n i : ℕ) (hi : i < n) : |D n i| ≤ S * ηx * (θ ^ (n - 1 - i) * q' i) := by
    have hk : n - i = (n - 1 - i) + 1 := by omega
    have hb : ∀ y, ‖g y * (e (n - i) y - (d.weight y).toReal)‖ ≤
        S * θ ^ (n - 1 - i) * g y := by
      intro y
      rw [norm_mul, Real.norm_of_nonneg (hg0 y), Real.norm_eq_abs, hk, mul_comm]
      exact mul_le_mul_of_nonneg_right (he_err _ y) (hg0 y)
    have hle := norm_integral_le_of_norm_le ((hgK i).const_mul (S * θ ^ (n - 1 - i)))
      (Eventually.of_forall hb)
    rw [integral_const_mul] at hle
    simp only [D]
    rw [abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.2 hr.le) _)]
    calc r⁻¹ ^ i * |∫ y, g y * (e (n - i) y - (d.weight y).toReal) ∂(C.killedTransition ^ i) x.val|
        ≤ r⁻¹ ^ i * (S * θ ^ (n - 1 - i) * ∫ y, g y ∂(C.killedTransition ^ i) x.val) :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg (inv_nonneg.2 hr.le) _)
      _ = S * θ ^ (n - 1 - i) * (r⁻¹ ^ i * ∫ y, g y ∂(C.killedTransition ^ i) x.val) := by ring
      _ = S * ηx * (θ ^ (n - 1 - i) * q' i) := by rw [← hD2 i]; ring
  -- Limits.
  have hq'0 (i : ℕ) : 0 ≤ q' i := integral_nonneg fun y => hu0 _
  have hDlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, D n i) atTop (𝓝 0) := by
    have hgeo := geometric_cesaro_tendsto_zero hCx s.decay_nonneg s.decay_lt_one
    have hbound : Tendsto (fun n : ℕ => S * ηx *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, θ ^ (n - 1 - i) * q' i)) atTop (𝓝 0) := by
      simpa only [θ, mul_zero] using hgeo.const_mul (S * ηx)
    refine squeeze_zero_norm (fun n => ?_) hbound
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)), mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg n))
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [Real.norm_eq_abs]
    exact hDb n i (Finset.mem_range.1 hi)
  have hΓ : ∫ y, g y.val ∂ν = Γ := integral_live d μ g
  have hlim : Tendsto (fun n : ℕ => (e n x.val)⁻¹ *
      (ηx * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q i) +
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, D n i)) atTop (𝓝 Γ) := by
    have := (ha.inv₀ hηx.ne').mul ((hBx.const_mul ηx).add hDlim)
    rw [hΓ, add_zero, ← mul_assoc, inv_mul_cancel₀ hηx.ne', one_mul] at this
    exact this
  refine (ENNReal.tendsto_ofReal hlim).congr fun n => ?_
  rw [conditioned_average_eq_ofReal C x.val hx n hg hg0 hfx]
  congr 1
  rw [Finset.sum_congr rfl fun i hi => hterm n i (Finset.mem_range.1 hi), ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Step3Main

end

end ConditionedStableLaws.RefinedLLN
