import ConditionedStableLaws.RefinedLLNMain

/-!
# Single-observation conditioned expectations

A quantitative form of the one-observation case of mixing of all orders: for bounded measurable `g ≥
0` and `1 ≤ i < n`, `E_x[g(Xᵢ) | τ > n] ≤ (η(x)/aₙ) ν(g) + D ‖g‖∞ (θ^{i-1} + θ^{n-1-i})`, where `aₙ
= λ⁻ⁿ Kⁿ(x, M) → η(x)`. The constant `D` does not depend on `g`, `i` or `n`. This is used for the
small-jump estimates of the stable laws.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.ConditionedSingle

noncomputable section

open StandingHypothesis CanonicalChain RefinedLLN

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Normalized survival mass `aₙ(x) = λ⁻ⁿ Kⁿ(x, M)`. -/
def normalizedMass (d : DoobTransform.EigenData C.killedTransition) (n : ℕ) (x : M) : ℝ :=
  (d.rate.toReal)⁻¹ ^ n * ((C.killedTransition ^ n) x).real univ

theorem conditioned_single_le (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    (x : d.State) :
    ∃ D θ : ℝ, 0 ≤ D ∧ 0 ≤ θ ∧ θ < 1 ∧
      (∀ n, 0 < normalizedMass C d n x.val) ∧
      Tendsto (fun n => normalizedMass C d n x.val) atTop (𝓝 (d.weight x.val).toReal) ∧
      ∀ (g : M → ℝ), Measurable g → (∀ y, 0 ≤ g y) → ∀ H : ℝ, (∀ y, g y ≤ H) →
        ∀ n i : ℕ, 1 ≤ i → i < n →
          (∫⁻ ω, PathMixing.liveExtension (fun y => ENNReal.ofReal (g y)) (ω i)
            ∂C.conditionedMeasure x.val n).toReal ≤
          (d.weight x.val).toReal / normalizedMass C d n x.val *
              ∫ y, g y ∂μ.withDensity d.weight +
            D * H * (θ ^ (i - 1) + θ ^ (n - 1 - i)) := by
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  obtain ⟨A, θ₁, hA, hθ₁0, hθ₁1, hdecay⟩ :=
    h.exists_pointwise_decay (K := C.toKilledKernel) d s.continuous_weight μ hleft hnorm
  set θ₂ := s.decay
  set θ := max θ₁ θ₂
  have hθ0 : 0 ≤ θ := le_max_of_le_left hθ₁0
  have hθ1 : θ < 1 := max_lt hθ₁1 s.decay_lt_one
  set r := d.rate.toReal
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  set S := s.survivalConstant
  have hS := s.survivalConstant_nonneg
  set Bs := s.survivalBound
  have hBs := s.survivalBound_nonneg
  obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d s.continuous_weight
  have hBη' (y : M) : (d.weight y).toReal ≤ Bη := (le_abs_self _).trans (hBη y)
  have hBη0 : 0 ≤ Bη := ENNReal.toReal_nonneg.trans (hBη' x.val)
  set ηx := (d.weight x.val).toReal
  have hreal (k : ℕ) (y : M) : ((d.rate⁻¹) ^ k * (C.toKilledKernel.kernel ^ k) y univ).toReal =
      r⁻¹ ^ k * ((C.killedTransition ^ k) y).real univ :=
    normalized_survival_toReal (K := C.toKilledKernel) d k y
  have hapos (n : ℕ) : 0 < normalizedMass C d n x.val := by
    have hpos := C.pathMeasure_survival_pos x.val hx n
    rw [C.pathMeasure_survival] at hpos
    exact mul_pos (pow_pos (inv_pos.2 hr) _) (ENNReal.toReal_pos hpos.ne'
      ((C.killedTransition_pow_mass_le_one x.val n).trans_lt ENNReal.one_lt_top).ne)
  have halim : Tendsto (fun n => normalizedMass C d n x.val) atTop (𝓝 ηx) :=
    (s.normalized_survival_tendstoUniformly.tendsto_at x.val).congr fun n => hreal n x.val
  obtain ⟨c, hc, hcle⟩ := ConditionalTransfer.exists_pos_lower_bound hapos
    (ENNReal.toReal_pos x.property (d.weight_ne_top _)) halim
  set D' := S + A * (Bη + 1) + S * Bs
  have hD' : 0 ≤ D' := by positivity
  refine ⟨D' / c, θ, div_nonneg hD' hc.le, hθ0, hθ1, hapos, halim,
    fun g hg hg0 H hgH n i hi hin => ?_⟩
  have hH0 : 0 ≤ H := (hg0 x.val).trans (hgH _)
  have : IsFiniteKernel (C.killedTransition ^ i) := killedKernel_power_isFinite C.toKilledKernel i
  set a := normalizedMass C d n x.val
  set e : ℕ → M → ℝ := fun k y => r⁻¹ ^ k * ((C.killedTransition ^ k) y).real univ
  have hk (k : ℕ) (y : M) : ((C.killedTransition ^ k) y univ) ≠ ∞ :=
    ((C.killedTransition_pow_mass_le_one y k).trans_lt ENNReal.one_lt_top).ne
  have hpowe (k : ℕ) (y : M) : ((C.killedTransition ^ k) y).real univ = r ^ k * e k y := by
    simp only [e]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul]
  have he_meas (k : ℕ) : Measurable (e k) :=
    measurable_const.mul ((Kernel.measurable_coe _ MeasurableSet.univ).ennreal_toReal)
  have he_err (k : ℕ) (y : M) : |e (k + 1) y - (d.weight y).toReal| ≤ S * θ₂ ^ k := by
    have := s.normalized_survival_error k y
    rw [hreal] at this
    exact this
  have he0 (k : ℕ) (y : M) : 0 ≤ e k y :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 hr.le) _) measureReal_nonneg
  have hebd (k : ℕ) (y : M) : e k y ≤ Bs := by
    have := s.normalized_survival_real_le k y
    rw [hreal] at this
    exact this
  -- The exact formula in real form.
  have hgi : Integrable g ((C.killedTransition ^ i) x.val) :=
    Integrable.of_bound hg.aestronglyMeasurable H (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (hg0 y)]; exact hgH y)
  have hge (k : ℕ) : Integrable (fun y => g y * e k y) ((C.killedTransition ^ i) x.val) :=
    hgi.mul_bdd (he_meas k).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (he0 k y)]; exact hebd k y)
  have hformula : (∫⁻ ω, PathMixing.liveExtension (fun y => ENNReal.ofReal (g y)) (ω i)
      ∂C.conditionedMeasure x.val n).toReal =
      a⁻¹ * (r⁻¹ ^ i * ∫ y, g y * e (n - i) y ∂(C.killedTransition ^ i) x.val) := by
    rw [lintegral_conditioned_single C x.val hin.le hg.ennreal_ofReal, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    have hint : (∫⁻ y, ENNReal.ofReal (g y) * (C.killedTransition ^ (n - i)) y univ
        ∂(C.killedTransition ^ i) x.val).toReal =
        ∫ y, g y * ((C.killedTransition ^ (n - i)) y).real univ ∂(C.killedTransition ^ i) x.val := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y =>
          mul_nonneg (hg0 y) measureReal_nonneg)
        (hg.mul ((Kernel.measurable_coe _ MeasurableSet.univ).ennreal_toReal)).aestronglyMeasurable]
      congr 1
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_mul (hg0 y), Measure.real, ENNReal.ofReal_toReal (hk _ y)]
    rw [hint]
    change (((C.killedTransition ^ n) x.val).real univ)⁻¹ * _ = _
    simp_rw [hpowe]
    have hcomm : (fun y => g y * (r ^ (n - i) * e (n - i) y)) =
        fun y => r ^ (n - i) * (g y * e (n - i) y) := by funext y; ring
    rw [hcomm, integral_const_mul]
    change (r ^ n * e n x.val)⁻¹ * _ = (e n x.val)⁻¹ * _
    have hrn : r ^ n = r ^ i * r ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hin.le]
    have hri : r ^ i ≠ 0 := pow_ne_zero _ hr.ne'
    have hrni : r ^ (n - i) ≠ 0 := pow_ne_zero _ hr.ne'
    have hen : e n x.val ≠ 0 := (hapos n).ne'
    rw [hrn, inv_pow]
    field_simp
  -- Bound the integral.
  have hmid : r⁻¹ ^ i * ∫ y, g y * e (n - i) y ∂(C.killedTransition ^ i) x.val ≤
      (∫ y, g y ∂μ.withDensity d.weight) * ηx + H * D' * (θ ^ (i - 1) + θ ^ (n - 1 - i)) := by
    set νg := ∫ y, g y ∂μ.withDensity d.weight
    have hμ' : IsProbabilityMeasure (μ.withDensity d.weight) := by
      constructor
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
    have hνg0 : 0 ≤ νg := integral_nonneg hg0
    have hνgH : νg ≤ H := by
      have := integral_mono_of_nonneg (μ := μ.withDensity d.weight)
        (Eventually.of_forall hg0) (integrable_const H) (Eventually.of_forall hgH)
      simpa using this
    have hsplit : ∫ y, g y * e (n - i) y ∂(C.killedTransition ^ i) x.val ≤
        ∫ y, g y * (d.weight y).toReal ∂(C.killedTransition ^ i) x.val +
          H * (S * θ₂ ^ (n - 1 - i)) * ((C.killedTransition ^ i) x.val).real univ := by
      have hk' : n - i = (n - 1 - i) + 1 := by omega
      have hη_int : Integrable (fun y => g y * (d.weight y).toReal)
          ((C.killedTransition ^ i) x.val) :=
        hgi.mul_bdd d.measurable_weight.ennreal_toReal.aestronglyMeasurable
          (Eventually.of_forall fun y => by
            rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]; exact hBη' y)
      set cst := H * (S * θ₂ ^ (n - 1 - i))
      have hle := integral_mono (hge (n - i)) (hη_int.add (integrable_const cst)) (fun y => by
        have h1 := he_err (n - 1 - i) y
        rw [← hk'] at h1
        have h2 : e (n - i) y ≤ (d.weight y).toReal + S * θ₂ ^ (n - 1 - i) := by
          linarith [le_abs_self (e (n - i) y - (d.weight y).toReal)]
        simp only [Pi.add_apply]
        calc g y * e (n - i) y ≤ g y * ((d.weight y).toReal + S * θ₂ ^ (n - 1 - i)) :=
              mul_le_mul_of_nonneg_left h2 (hg0 y)
          _ = g y * (d.weight y).toReal + g y * (S * θ₂ ^ (n - 1 - i)) := by ring
          _ ≤ g y * (d.weight y).toReal + cst := by
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hgH y)
                (mul_nonneg hS (pow_nonneg s.decay_nonneg _))))
      simp only [Pi.add_apply] at hle
      rw [integral_add hη_int (integrable_const cst), integral_const, smul_eq_mul] at hle
      linarith [mul_comm cst (((C.killedTransition ^ i) x.val).real univ)]
    -- The weighted integral through the pointwise decay.
    set F : M → ℝ := fun y => (d.weight y).toReal * g y - νg
    have hwg : Measurable (fun y => (d.weight y).toReal * g y) :=
      d.measurable_weight.ennreal_toReal.mul hg
    have hwgb (y : M) : ‖(d.weight y).toReal * g y‖ ≤ Bη * H := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg (hg0 y)]
      exact mul_le_mul (hBη' y) (hgH y) (hg0 y) hBη0
    have hFm : Measurable F := hwg.sub measurable_const
    have hFb (y : M) : |F y| ≤ Bη * H + H := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg (hg0 y)]
        exact mul_le_mul (hBη' y) (hgH y) (hg0 y) hBη0
      · rw [abs_of_nonneg hνg0]; exact hνgH
    have hηg : Integrable (fun y => (d.weight y).toReal * g y) μ :=
      Integrable.of_bound hwg.aestronglyMeasurable (Bη * H) (Eventually.of_forall hwgb)
    have hF0 : ∫ y, F y ∂μ = 0 := by
      simp only [F]
      rw [integral_sub hηg (integrable_const _), integral_const, probReal_univ, one_smul]
      have : ∫ y, (d.weight y).toReal * g y ∂μ = νg := by
        simp only [νg]
        rw [integral_withDensity_eq_integral_toReal_smul d.measurable_weight
          (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
        rfl
      rw [this, sub_self]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
    have hdec : |r⁻¹ ^ (j + 1) * ∫ y, F y ∂(C.killedTransition ^ (j + 1)) x.val| ≤
        A * θ₁ ^ j * (Bη * H + H) := hdecay F hFm _ hFb hF0 j x.val
    have hint2 : ∫ y, g y * (d.weight y).toReal ∂(C.killedTransition ^ (j + 1)) x.val =
        ∫ y, F y ∂(C.killedTransition ^ (j + 1)) x.val +
          νg * ((C.killedTransition ^ (j + 1)) x.val).real univ := by
      simp only [F]
      rw [integral_sub (Integrable.of_bound hwg.aestronglyMeasurable (Bη * H)
          (Eventually.of_forall hwgb)) (integrable_const _), integral_const, smul_eq_mul]
      simp only [mul_comm (g _)]
      ring
    have hei := he_err j x.val
    have he1 : e (j + 1) x.val ≤ ηx + S * θ₂ ^ j := by
      linarith [le_abs_self (e (j + 1) x.val - ηx)]
    have hθj₁ : θ₁ ^ j ≤ θ ^ j := pow_le_pow_left₀ hθ₁0 (le_max_left _ _) j
    have hθj₂ : θ₂ ^ j ≤ θ ^ j := pow_le_pow_left₀ s.decay_nonneg (le_max_right _ _) j
    have hθk₂ : θ₂ ^ (n - 1 - (j + 1)) ≤ θ ^ (n - 1 - (j + 1)) :=
      pow_le_pow_left₀ s.decay_nonneg (le_max_right _ _) _
    simp only [Nat.add_sub_cancel]
    have hmass : r⁻¹ ^ (j + 1) * ((C.killedTransition ^ (j + 1)) x.val).real univ ≤ Bs :=
      hebd (j + 1) x.val
    calc r⁻¹ ^ (j + 1) * ∫ y, g y * e (n - (j + 1)) y ∂(C.killedTransition ^ (j + 1)) x.val
        ≤ r⁻¹ ^ (j + 1) * (∫ y, g y * (d.weight y).toReal ∂(C.killedTransition ^ (j + 1)) x.val +
          H * (S * θ₂ ^ (n - 1 - (j + 1))) * ((C.killedTransition ^ (j + 1)) x.val).real univ) :=
          mul_le_mul_of_nonneg_left hsplit (pow_nonneg (inv_nonneg.2 hr.le) _)
      _ = r⁻¹ ^ (j + 1) * ∫ y, F y ∂(C.killedTransition ^ (j + 1)) x.val + νg * e (j + 1) x.val +
          H * (S * θ₂ ^ (n - 1 - (j + 1))) * e (j + 1) x.val := by
          rw [hint2]; simp only [e]; ring
      _ ≤ A * θ₁ ^ j * (Bη * H + H) + νg * (ηx + S * θ₂ ^ j) +
          H * (S * θ₂ ^ (n - 1 - (j + 1))) * Bs := by
          refine add_le_add (add_le_add ((le_abs_self _).trans hdec)
            (mul_le_mul_of_nonneg_left he1 hνg0)) ?_
          exact mul_le_mul_of_nonneg_left (hebd (j + 1) x.val)
            (mul_nonneg hH0 (mul_nonneg hS (pow_nonneg s.decay_nonneg _)))
      _ ≤ νg * ηx + H * D' * (θ ^ j + θ ^ (n - 1 - (j + 1))) := by
          have h1 : A * θ₁ ^ j * (Bη * H + H) ≤ H * (A * (Bη + 1)) * θ ^ j := by
            calc A * θ₁ ^ j * (Bη * H + H) = (H * (A * (Bη + 1))) * θ₁ ^ j := by ring
              _ ≤ (H * (A * (Bη + 1))) * θ ^ j :=
                  mul_le_mul_of_nonneg_left hθj₁ (by positivity)
          have h2 : νg * (S * θ₂ ^ j) ≤ H * S * θ ^ j := by
            calc νg * (S * θ₂ ^ j) ≤ H * (S * θ ^ j) :=
                  mul_le_mul hνgH (mul_le_mul_of_nonneg_left hθj₂ hS)
                    (mul_nonneg hS (pow_nonneg s.decay_nonneg _)) hH0
              _ = H * S * θ ^ j := by ring
          have h3 : H * (S * θ₂ ^ (n - 1 - (j + 1))) * Bs ≤
              H * (S * Bs) * θ ^ (n - 1 - (j + 1)) := by
            calc H * (S * θ₂ ^ (n - 1 - (j + 1))) * Bs = (H * (S * Bs)) * θ₂ ^ (n - 1 - (j + 1)) := by
                  ring
              _ ≤ (H * (S * Bs)) * θ ^ (n - 1 - (j + 1)) :=
                  mul_le_mul_of_nonneg_left hθk₂ (by positivity)
          have hp1 : 0 ≤ θ ^ j := pow_nonneg hθ0 _
          have hp2 : 0 ≤ θ ^ (n - 1 - (j + 1)) := pow_nonneg hθ0 _
          have hextra : 0 ≤ H * (S * Bs) * θ ^ j + H * S * θ ^ (n - 1 - (j + 1)) +
              H * (A * (Bη + 1)) * θ ^ (n - 1 - (j + 1)) := by positivity
          calc A * θ₁ ^ j * (Bη * H + H) + νg * (ηx + S * θ₂ ^ j) +
                H * (S * θ₂ ^ (n - 1 - (j + 1))) * Bs
              = A * θ₁ ^ j * (Bη * H + H) + νg * (S * θ₂ ^ j) + νg * ηx +
                H * (S * θ₂ ^ (n - 1 - (j + 1))) * Bs := by ring
            _ ≤ H * (A * (Bη + 1)) * θ ^ j + H * S * θ ^ j + νg * ηx +
                H * (S * Bs) * θ ^ (n - 1 - (j + 1)) := by linarith
            _ ≤ νg * ηx + H * D' * (θ ^ j + θ ^ (n - 1 - (j + 1))) := by
                simp only [D']; nlinarith
  have ha := hapos n
  have hac : c ≤ a := hcle n
  have hp : 0 ≤ H * D' * (θ ^ (i - 1) + θ ^ (n - 1 - i)) := by positivity
  calc (∫⁻ ω, PathMixing.liveExtension (fun y => ENNReal.ofReal (g y)) (ω i)
        ∂C.conditionedMeasure x.val n).toReal
      = a⁻¹ * (r⁻¹ ^ i * ∫ y, g y * e (n - i) y ∂(C.killedTransition ^ i) x.val) := hformula
    _ ≤ a⁻¹ * ((∫ y, g y ∂μ.withDensity d.weight) * ηx +
          H * D' * (θ ^ (i - 1) + θ ^ (n - 1 - i))) :=
        mul_le_mul_of_nonneg_left hmid (inv_nonneg.2 ha.le)
    _ = ηx / a * (∫ y, g y ∂μ.withDensity d.weight) +
          a⁻¹ * (H * D' * (θ ^ (i - 1) + θ ^ (n - 1 - i))) := by ring
    _ ≤ ηx / a * (∫ y, g y ∂μ.withDensity d.weight) +
          c⁻¹ * (H * D' * (θ ^ (i - 1) + θ ^ (n - 1 - i))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (inv_anti₀ hc hac) hp)
    _ = ηx / a * (∫ y, g y ∂μ.withDensity d.weight) +
          D' / c * H * (θ ^ (i - 1) + θ ^ (n - 1 - i)) := by ring

end

end ConditionedStableLaws.ConditionedSingle
