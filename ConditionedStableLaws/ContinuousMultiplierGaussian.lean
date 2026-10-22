import ConditionedStableLaws.ContinuousMultiplierTruncation
import ConditionedStableLaws.ContinuousMultiplierMomentComparison
import ConditionedStableLaws.GaussianBoundary

/-! Continuous multiplier residuals on the Gaussian boundary scale. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
noncomputable section
namespace ConditionedStableLaws.ContinuousMultiplier
open GaussianBoundary CanonicalChain StandingHypothesis SmallJumpMoment SecondMoment

/-- Positive totalization of the Gaussian scale; it equals B_n for all large n. -/
def gaussianScale (c : ℝ) (n : ℕ) : ℝ := max (bScale c n) 1

theorem gaussianScale_pos (c : ℝ) (n : ℕ) : 0 < gaussianScale c n :=
  lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem gaussianScale_eventually_eq {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, gaussianScale c n = bScale c n :=
  ((bScale_tendsto hc).eventually_ge_atTop 1).mono fun _ hn => max_eq_left hn

theorem gaussianScale_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (gaussianScale c) atTop atTop :=
  tendsto_atTop_mono (fun _ => le_max_left _ _) (bScale_tendsto hc)

theorem nat_div_gaussianScale_sq {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) / gaussianScale c n ^ 2) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => c⁻¹ * (Real.log n)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_log_nat.inv_tendsto_atTop.const_mul c⁻¹
  apply ht.congr'
  filter_upwards [gaussianScale_eventually_eq hc, eventually_one_le_log,
    eventually_gt_atTop (0 : ℕ)] with n hn hl hn0
  rw [hn, bScale, Real.sq_sqrt (by positivity)]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hl' : Real.log n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hl)
  field_simp

section Moments
variable {M : Type*} [MeasurableSpace M]

theorem gaussian_original_second_moment
    (ν : Measure M) [IsProbabilityMeasure ν] {f : M → ℝ} (hfm : Measurable f)
    (hf : ∀ y, 0 ≤ f y) {c : ℝ} (hc : 0 < c)
    (htail : Tendsto (fun t : ℝ => ν.real {y | t < f y} / (c * t ^ (-2 : ℝ)))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) / gaussianScale c n ^ 2 *
      ∫ y, trunc f (uScale c n) y ^ 2 ∂ν) atTop (𝓝 1) := by
  have ht := (trunc_sq_div_log_tendsto hfm hf hc htail).const_mul c⁻¹
  rw [inv_mul_cancel₀ hc.ne'] at ht
  apply ht.congr'
  filter_upwards [gaussianScale_eventually_eq hc, eventually_one_le_log,
    eventually_gt_atTop (0 : ℕ)] with n hn hl hn0
  have hi : (∫ y, {y | f y ≤ uScale c n}.indicator (fun y => f y ^ 2) y ∂ν) =
      ∫ y, trunc f (uScale c n) y ^ 2 ∂ν := by
    apply integral_congr_ae
    apply ae_of_all
    intro y
    by_cases hy : f y ≤ uScale c n <;> simp [trunc, hy]
  rw [hi, hn, bScale, Real.sq_sqrt (by positivity)]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hl' : Real.log n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hl)
  field_simp

end Moments
section Chain
variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The Gaussian truncated multiplier error has negligible centered sums. -/
theorem gaussian_cut_residual_negligible
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {f r : M → ℝ} (hfm : Measurable f) (hrm : Measurable r)
    (hf : ∀ y, 0 ≤ f y)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |r y| ≤ η * f y + K)
    {T a c : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hc : 0 < c)
    (hlower : ∀ y, T < f y → a ≤ (d.weight y).toReal)
    (htail : Tendsto (fun t : ℝ => (μ.withDensity d.weight).real {y | t < f y} /
      (c * t ^ (-2 : ℝ))) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (C.conditionedMeasure x.val n).real
      {ω | ε < |(gaussianScale c n)⁻¹ *
        (pathBirkhoffSum (cut f r (uScale c n)) n ω -
          n * ∫ y, cut f r (uScale c n) y ∂μ.withDensity d.weight)|}) atTop (𝓝 0) := by
  let ν := μ.withDensity d.weight
  have : IsProbabilityMeasure ν :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hu0 (n : ℕ) : 0 ≤ uScale c n := by
    unfold uScale
    positivity
  have hν2 := gaussian_original_second_moment ν hfm hf hc htail
  have hν2b : ∀ᶠ n : ℕ in atTop, (n : ℝ) / gaussianScale c n ^ 2 *
      ∫ y, trunc f (uScale c n) y ^ 2 ∂ν ≤ 2 :=
    (hν2.eventually_lt_const (by norm_num : (1 : ℝ) < 2)).mono fun _ hn => hn.le
  have hnb := nat_div_gaussianScale_sq hc
  have hμ2b : ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / gaussianScale c n ^ 2 * ∫ y, trunc f (uScale c n) y ^ 2 ∂μ ≤ L := by
    refine ⟨a⁻¹ * 2 + T ^ 2, by positivity, ?_⟩
    filter_upwards [hν2b, hnb.eventually_lt_const zero_lt_one] with n hn hnbn
    have hb := trunc_second_moment_mu_le (K := C.toKilledKernel) d s.continuous_weight μ hfm hf hT ha hlower
      (uScale c n) (hu0 n)
    have hnb0 : 0 ≤ (n : ℝ) / gaussianScale c n ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hb hnb0
    have h2 := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ha.le)
    have h3 := mul_le_mul_of_nonneg_right hnbn.le (sq_nonneg T)
    nlinarith
  have hμr := scaled_residual_second_moment_zero μ hfm hrm hf hr (uScale c) hu0 hnb hμ2b
  have hνr := scaled_residual_second_moment_zero ν hfm hrm hf hr (uScale c) hu0 hnb
    ⟨2, by norm_num, hν2b⟩
  let q : ℕ → M → ℝ := fun n y => (gaussianScale c n)⁻¹ * cut f r (uScale c n) y
  have hqm (n : ℕ) : Measurable (q n) := (measurable_cut hfm hrm _).const_mul _
  obtain ⟨K, hK, hKr⟩ := hr 1 zero_lt_one
  let G : ℕ → ℝ := fun n => (uScale c n + K) / gaussianScale c n
  have hG0 (n : ℕ) : 0 ≤ G n := div_nonneg (add_nonneg (hu0 n) hK) (gaussianScale_pos c n).le
  have hqG (n : ℕ) (y : M) : |q n y| ≤ G n := by
    dsimp [q, G]
    rw [abs_mul, abs_of_pos (inv_pos.mpr (gaussianScale_pos c n))]
    have hb := abs_cut_le (show (0 : ℝ) ≤ 1 by norm_num) hK (hu0 n) hKr y
    simpa only [one_mul, div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (gaussianScale_pos c n).le)
  have hG : Tendsto G atTop (𝓝 0) := by
    have ht := (uScale_div_bScale_tendsto hc).add
      ((tendsto_const_nhds (x := K)).div_atTop (bScale_tendsto hc))
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [gaussianScale_eventually_eq hc] with n hn
    simp only [G, hn, add_div]
  have heq (κ : Measure M) (n : ℕ) : (n : ℝ) * ∫ y, q n y ^ 2 ∂κ =
      (n : ℝ) / gaussianScale c n ^ 2 * ∫ y, cut f r (uScale c n) y ^ 2 ∂κ := by
    simp only [q, mul_pow, integral_const_mul]
    rw [inv_pow, div_eq_mul_inv, mul_assoc]
  have hnear := centered_array_negligible C h d s hlive μ hleft hnorm x q hqm G hG0 hqG hG
    (hμr.congr fun n => (heq μ n).symm) (hνr.congr fun n => (heq ν n).symm)
  intro ε hε
  apply (hnear ε hε).congr
  intro n
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, q, pathBirkhoffSum_const_mul, integral_const_mul]
  have he : (gaussianScale c n)⁻¹ * pathBirkhoffSum (cut f r (uScale c n)) n ω -
      n * ((gaussianScale c n)⁻¹ * ∫ y, cut f r (uScale c n) y ∂ν) =
      (gaussianScale c n)⁻¹ * (pathBirkhoffSum (cut f r (uScale c n)) n ω -
        n * ∫ y, cut f r (uScale c n) y ∂ν) := by ring
  rw [he]


/-- Truncation can be removed for the Gaussian multiplier residual: both its moments and the
exceptional paths are estimated. -/
theorem gaussian_full_residual_negligible
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) {f r : M → ℝ} (hfm : Measurable f) (hrm : Measurable r)
    (hf : ∀ y, 0 ≤ f y)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |r y| ≤ η * f y + K)
    {T a c : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hc : 0 < c)
    (hlower : ∀ y, T < f y → a ≤ (d.weight y).toReal)
    (htail : Tendsto (fun t : ℝ => (μ.withDensity d.weight).real {y | t < f y} /
      (c * t ^ (-2 : ℝ))) atTop (𝓝 1)) :
    Integrable r (μ.withDensity d.weight) ∧
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (C.conditionedMeasure x.val n).real
      {ω | ε < |(bScale c n)⁻¹ *
        (pathBirkhoffSum r n ω - n * ∫ y, r y ∂μ.withDensity d.weight)|}) atTop (𝓝 0) := by
  let ν := μ.withDensity d.weight
  have : IsProbabilityMeasure ν :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have := h.reference_probability
  have hνeq (k : M → ℝ) : ∫ y, k y ∂ν = ∫ y, (d.weight y).toReal * k y ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (ae_of_all _ fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y))]
    rfl
  have hfi : Integrable f ν :=
    integrable_of_power_tail_asymptotic ν f hfm hf c 2 hc one_lt_two htail
  obtain ⟨K, hK, hKr⟩ := hr 1 zero_lt_one
  have hri : Integrable r ν := (hfi.add (integrable_const K)).mono'
    hrm.aestronglyMeasurable (ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs, Pi.add_apply, one_mul] using hKr y)
  refine ⟨hri, ?_⟩
  let U : ℕ → Set M := fun n => {y | uScale c n < f y}
  have hU (n : ℕ) : MeasurableSet (U n) := measurableSet_lt measurable_const hfm
  have hρU : Tendsto (fun n => ρ (U n)) atTop (𝓝 0) :=
    (GaussianBoundary.tendsto_measure_gt_zero ρ hfm).comp (uScale_tendsto hc)
  have hνU := nat_mul_tail_tendsto (ν := ν) hc htail
  have hμU : Tendsto (fun n : ℕ => (n : ℝ) * μ.real (U n)) atTop (𝓝 0) := by
    have hlim := hνU.const_mul a⁻¹
    simp only [mul_zero] at hlim
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hlim
    filter_upwards [(uScale_tendsto hc).eventually_ge_atTop T] with n hn
    have hcomp : μ.real (U n) ≤ a⁻¹ * ν.real (U n) := by
      obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d s.continuous_weight
      have hwi : Integrable (fun y => (d.weight y).toReal * (U n).indicator (fun _ => (1 : ℝ)) y) μ :=
        ((integrable_const (1 : ℝ)).indicator (hU n)).bdd_mul (c := Bη)
          d.measurable_weight.ennreal_toReal.aestronglyMeasurable (ae_of_all _ hBη)
      rw [← integral_indicator_one (hU n), ← integral_indicator_one (hU n), hνeq,
        ← integral_const_mul]
      apply integral_mono ((integrable_const (1 : ℝ)).indicator (hU n)) (hwi.const_mul _)
      intro y
      by_cases hy : y ∈ U n
      · have hl := hlower y (lt_of_le_of_lt hn hy)
        simp only [indicator_of_mem hy, mul_one]
        rw [inv_mul_eq_div, le_div_iff₀ ha, one_mul]
        exact hl
      · simp only [indicator_of_notMem hy, mul_zero, le_refl]
    have hh := mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simpa only [mul_assoc, mul_left_comm (n : ℝ) a⁻¹] using hh
  have hxU : ∀ᶠ n in atTop, x.val ∉ U n :=
    ((uScale_tendsto hc).eventually_ge_atTop (f x.val)).mono fun _ hn hx => not_lt.mpr hn hx
  have hsum := L2Variance.sum_targets_tendsto_zero C h d s hlive μ hleft hnorm x U hU hρU hμU hxU
  have htailmean := tail_mean_tendsto (ν := ν) hfm hf hc htail
  have htailprob : Tendsto (fun n : ℕ => (n : ℝ) / bScale c n * (K * ν.real (U n)))
      atTop (𝓝 0) := by
    have ht := (hνU.mul ((bScale_tendsto hc).inv_tendsto_atTop)).const_mul K
    simp only [mul_zero] at ht
    apply ht.congr
    intro n
    dsimp [U]
    ring
  have hmean_bound (n : ℕ) :
      |(∫ y, r y ∂ν) - ∫ y, cut f r (uScale c n) y ∂ν| ≤
        (∫ y, (U n).indicator f y ∂ν) + K * ν.real (U n) := by
    have hcut : Integrable (cut f r (uScale c n)) ν :=
      hri.indicator (measurableSet_le hfm measurable_const)
    have heq : (∫ y, r y ∂ν) - ∫ y, cut f r (uScale c n) y ∂ν =
        ∫ y, (U n).indicator r y ∂ν := by
      rw [eq_comm, eq_sub_iff_add_eq, ← integral_add (hri.indicator (hU n)) hcut]
      apply integral_congr_ae
      apply ae_of_all
      intro y
      by_cases hy : f y ≤ uScale c n <;> simp [U, cut, hy, not_lt, lt_of_not_ge]
    rw [heq]
    calc
      _ ≤ ∫ y, |(U n).indicator r y| ∂ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm ((U n).indicator r)
      _ ≤ ∫ y, ((U n).indicator f y + (U n).indicator (fun _ => K) y) ∂ν := by
        apply integral_mono (hri.indicator (hU n)).abs
          ((hfi.indicator (hU n)).add ((integrable_const K).indicator (hU n)))
        intro y
        change |(U n).indicator r y| ≤ (U n).indicator f y + (U n).indicator (fun _ => K) y
        by_cases hy : y ∈ U n
        · simp only [indicator_of_mem hy]
          simpa only [one_mul] using hKr y
        · simp only [indicator_of_notMem hy, abs_zero, add_zero, le_refl]
      _ = _ := by
        rw [integral_add (hfi.indicator (hU n)) ((integrable_const K).indicator (hU n)),
          integral_indicator_const _ (hU n), smul_eq_mul, mul_comm (ν.real (U n)) K]
  have hmean : Tendsto (fun n : ℕ => (n : ℝ) / bScale c n *
      |(∫ y, r y ∂ν) - ∫ y, cut f r (uScale c n) y ∂ν|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg
      (div_nonneg (Nat.cast_nonneg n) (show 0 ≤ bScale c n from Real.sqrt_nonneg _)) (abs_nonneg _))
      (fun n => ?_) (show Tendsto
        (fun n : ℕ => (n : ℝ) / bScale c n * ∫ y, (U n).indicator f y ∂ν +
          (n : ℝ) / bScale c n * (K * ν.real (U n))) atTop (𝓝 0) from by
            simpa only [add_zero] using htailmean.add htailprob)
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (hmean_bound n)
      (div_nonneg (Nat.cast_nonneg n) (show 0 ≤ bScale c n from Real.sqrt_nonneg _))
  have hcutnear := gaussian_cut_residual_negligible C h d s hlive μ hleft hnorm x
    hfm hrm hf hr hT ha hc hlower htail
  intro ε hε
  have hcutε := hcutnear (ε / 2) (half_pos hε)
  have hlim := hcutε.add hsum
  simp only [add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hlim
  filter_upwards [gaussianScale_eventually_eq hc,
    hmean.eventually_lt_const (half_pos hε)] with n hbn hmn
  have : IsProbabilityMeasure (C.conditionedMeasure x.val n) :=
    C.conditionedMeasure_isProbability_of_surviving x.val
      (d.liveSet_subset_survivingSet x.property) n
  let A : Set (Path M) := {ω | ε / 2 < |(gaussianScale c n)⁻¹ *
    (pathBirkhoffSum (cut f r (uScale c n)) n ω - n * ∫ y, cut f r (uScale c n) y ∂ν)|}
  let E : Set (Path M) := ⋃ i ∈ Finset.range n, {ω | ω i ∈ Option.some '' U n}
  have hsub : {ω | ε < |(bScale c n)⁻¹ *
      (pathBirkhoffSum r n ω - n * ∫ y, r y ∂ν)|} ⊆ A ∪ E := by
    intro ω hω
    by_cases he : ω ∈ E
    · exact Or.inr he
    apply Or.inl
    have hpath : pathBirkhoffSum r n ω = pathBirkhoffSum (cut f r (uScale c n)) n ω := by
      unfold pathBirkhoffSum birkhoffSum
      apply Finset.sum_congr rfl
      intro i hi
      cases hωi : ω i with
      | none => simp only [hωi, zeroExtension_none]
      | some y =>
        have hy : f y ≤ uScale c n := by
          by_contra hgt
          apply he
          refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
          change ω i ∈ Option.some '' U n
          rw [hωi]
          exact Set.mem_image_of_mem _ (show y ∈ U n from lt_of_not_ge hgt)
        simp [hωi, cut, hy]
    have hsplit : (bScale c n)⁻¹ * (pathBirkhoffSum r n ω - n * ∫ y, r y ∂ν) =
        (bScale c n)⁻¹ * (pathBirkhoffSum (cut f r (uScale c n)) n ω -
          n * ∫ y, cut f r (uScale c n) y ∂ν) -
        (n : ℝ) / bScale c n * ((∫ y, r y ∂ν) - ∫ y, cut f r (uScale c n) y ∂ν) := by
      rw [hpath]
      ring
    have hb := abs_sub
      ((bScale c n)⁻¹ * (pathBirkhoffSum (cut f r (uScale c n)) n ω -
        n * ∫ y, cut f r (uScale c n) y ∂ν))
      ((n : ℝ) / bScale c n * ((∫ y, r y ∂ν) - ∫ y, cut f r (uScale c n) y ∂ν))
    have habs : |(n : ℝ) / bScale c n * ((∫ y, r y ∂ν) -
      ∫ y, cut f r (uScale c n) y ∂ν)| = (n : ℝ) / bScale c n *
      |(∫ y, r y ∂ν) - ∫ y, cut f r (uScale c n) y ∂ν| := by
        rw [abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (show 0 ≤ bScale c n from Real.sqrt_nonneg _))]
    rw [habs] at hb
    change ε < _ at hω
    rw [hsplit] at hω
    change ε / 2 < _
    rw [hbn]
    linarith
  calc
    _ ≤ (C.conditionedMeasure x.val n).real (A ∪ E) := measureReal_mono hsub
    _ ≤ (C.conditionedMeasure x.val n).real A + (C.conditionedMeasure x.val n).real E :=
      measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (measureReal_biUnion_finset_le _ _)

/-- Continuous multipliers on the Gaussian boundary: the centered observable `f_β g`, divided by the
original `B_n`, converges to `g(x₀) Z`. -/
theorem stable_law_boundary_multiplier
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα : dimension / β = 2)
    {g : M → ℝ} (hg : Continuous g) :
    Integrable (observable x₀ β g) (μ.withDensity d.weight) ∧
    TendstoInDistribution
      (fun n ω => (bScale (volumeConstant * (d.weight x₀).toReal * m x₀) n)⁻¹ *
        (pathBirkhoffSum (observable x₀ β g) n ω -
          n * ∫ y, observable x₀ β g y ∂μ.withDensity d.weight)) atTop
      (fun z : ℝ => g x₀ * z)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (gaussianReal 0 1) := by
  obtain ⟨hfi, hbase⟩ := GaussianBoundary.stable_law_boundary C h d s hlive μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ hα
  let c := volumeConstant * (d.weight x₀).toReal * m x₀
  have hc : 0 < c := mul_pos (mul_pos hadm.1.2.1
    (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  have htail := C.admissible_weighted_tail h d s.continuous_weight μ m hm hm0 hμ hadm hx₀ hβ
  rw [hα] at htail
  obtain ⟨T, hT, a, ha, hlower⟩ := exists_weight_lower C d s.continuous_weight hx₀ hβ
  obtain ⟨hri, hnear⟩ := gaussian_full_residual_negligible C h d s hlive μ hleft hnorm x
    (measurable_singularObservable x₀ β) (measurable_residual x₀ β hg)
    (fun y => (singularObservable_pos x₀ β y).le)
    (fun _ hε => residual_bound hβ hg hε) hT.le ha hc hlower htail
  have hgfi : Integrable (observable x₀ β g) (μ.withDensity d.weight) := by
    apply ((hfi.const_mul (g x₀)).add hri).congr
    apply ae_of_all
    intro y
    dsimp [observable, residual]
    ring
  refine ⟨hgfi, ?_⟩
  have hir : (∫ y, residual x₀ β g y ∂μ.withDensity d.weight) =
      (∫ y, observable x₀ β g y ∂μ.withDensity d.weight) -
        g x₀ * ∫ y, singularObservable x₀ β y ∂μ.withDensity d.weight := by
    rw [← integral_const_mul, ← integral_sub hgfi (hfi.const_mul (g x₀))]
    apply integral_congr_ae
    exact ae_of_all _ fun y => (observable_sub_center x₀ β g y).symm
  let X : ℕ → Path M → ℝ := fun n ω => (bScale c n)⁻¹ *
    (pathBirkhoffSum (observable x₀ β g) n ω -
      n * ∫ y, observable x₀ β g y ∂μ.withDensity d.weight)
  let Y : ℕ → Path M → ℝ := fun n ω => g x₀ * ((bScale c n)⁻¹ *
    (pathBirkhoffSum (singularObservable x₀ β) n ω -
      n * ∫ y, singularObservable x₀ β y ∂μ.withDensity d.weight))
  have hXm (n : ℕ) : Measurable (X n) :=
    ((measurable_pathBirkhoffSum (measurable_observable x₀ β hg) n).sub
      measurable_const).const_mul _
  have hYm (n : ℕ) : Measurable (Y n) :=
    (((measurable_pathBirkhoffSum (measurable_singularObservable x₀ β) n).sub
      measurable_const).const_mul _).const_mul _
  have hscaled := hbase.continuous_comp (g := fun z : ℝ => g x₀ * z)
    (continuous_const.mul continuous_id)
  apply tendstoInDistribution_of_varying_probability_approximation
    (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
    (gaussianReal 0 1) X Y (fun z : ℝ => g x₀ * z) hXm hYm hscaled
  intro ε hε
  apply (hnear ε hε).congr
  intro n
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  have he : X n ω - Y n ω = (bScale c n)⁻¹ *
      (pathBirkhoffSum (residual x₀ β g) n ω -
        n * ∫ y, residual x₀ β g y ∂μ.withDensity d.weight) := by
    rw [path_residual_eq, hir]
    dsimp [X, Y]
    ring
  rw [he]

end Chain
end ConditionedStableLaws.ContinuousMultiplier
