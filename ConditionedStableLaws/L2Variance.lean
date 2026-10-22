import ConditionedStableLaws.CovarianceSeries
import ConditionedStableLaws.TriangularCLT
import ConditionedStableLaws.BoundedCLT
import ConditionedStableLaws.ConvergingTogether
import ConditionedStableLaws.SecondMoment
import ConditionedStableLaws.EndpointChainBounds
import ConditionedStableLaws.SingularChainTargets
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The asymptotic variance for `L²(μ)` observables

The covariance-series estimates for bounded observables extend to `L²(μ)` representatives. The
interpolated remainder operator is the normalized killed-kernel operator on representatives.
Consequently the covariance terms are inner products in `L²(μ)` and inherit the exponential operator
bound.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace ConditionedStableLaws.L2Variance

noncomputable section

open StandingHypothesis CanonicalChain ConditionalCLT

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {rho : Measure M} (C : CanonicalChain M)

/-! ### Bounded truncations in `L²` -/

/-- A finite-valued bounded truncation.  Using zero outside the truncation
set (instead of clipping at the two endpoints) makes the domination argument
particularly transparent; both choices have the same `L²` limit. -/
def truncation (k : ℕ) (g : M → ℝ) : M → ℝ :=
  fun y => if |g y| ≤ (k : ℝ) then g y else 0

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurable_truncation {g : M → ℝ} (hg : Measurable g) (k : ℕ) :
    Measurable (truncation (M := M) k g) := by
  exact hg.ite (measurableSet_le hg.norm measurable_const) measurable_const

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem abs_truncation_le (g : M → ℝ) (k : ℕ) (y : M) :
    |truncation k g y| ≤ (k : ℝ) := by
  simp only [truncation]
  split_ifs with h
  · exact h
  · simp

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem memLp_truncation {mu : Measure M} [IsFiniteMeasure mu] {g : M → ℝ}
    (hg : Measurable g) (k : ℕ) : MemLp (truncation k g) 2 mu := by
  apply MemLp.of_bound (measurable_truncation hg k).aestronglyMeasurable (k : ℝ)
  exact Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact abs_truncation_le g k y

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The bounded truncations converge to the original finite-valued
representative in `L²(μ)`. -/
theorem truncation_tendsto_L2 {mu : Measure M} [IsFiniteMeasure mu] {g : M → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 mu) :
    Tendsto (fun k => (memLp_truncation hg k).toLp (truncation k g)) atTop
      (nhds (hg2.toLp g)) := by
  let F : ℕ → M → ℝ := fun k y => (truncation k g y - g y) ^ 2
  have hFmeas : ∀ k, AEStronglyMeasurable (F k) mu := fun k =>
    (((measurable_truncation hg k).sub hg).pow_const 2).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ y ∂mu, ‖F k y‖ ≤ g y ^ 2 := by
    intro k
    exact Eventually.of_forall fun y => by
      simp only [F, Real.norm_eq_abs, abs_sq]
      simp only [truncation]
      split_ifs with h
      · simpa using sq_nonneg (g y)
      · simp
  have hlim : ∀ᵐ y ∂mu, Tendsto (fun k => F k y) atTop (nhds 0) := by
    refine Eventually.of_forall fun y => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt |g y|
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro k hk
    have hle : |g y| ≤ (k : ℝ) := hN.le.trans (by exact_mod_cast hk)
    simp [F, truncation, hle]
  have hsq : Tendsto (fun k => ∫ y, F k y ∂mu) atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun y => g y ^ 2)
      hFmeas hg2.integrable_sq hbound hlim
    simpa using h
  have hnorm : Tendsto (fun k =>
      ‖(memLp_truncation hg k).toLp (truncation k g) - hg2.toLp g‖) atTop
      (nhds 0) := by
    have hsqrt := hsq.sqrt
    simpa only [Real.sqrt_zero] using hsqrt.congr' (Eventually.of_forall fun k => by
      rw [← Real.sqrt_sq (norm_nonneg
        ((memLp_truncation hg k).toLp (truncation k g) - hg2.toLp g)),
        SecondMoment.norm_sq_L2]
      congr 1
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((memLp_truncation hg k).toLp (truncation k g))
          (hg2.toLp g), (memLp_truncation hg k).coeFn_toLp, hg2.coeFn_toLp]
        with y hsub htr hg'
      rw [hsub, Pi.sub_apply, htr, hg'])
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The square integral of the part removed by the bounded truncation tends to zero. -/
theorem integral_sq_sub_truncation_tendsto_zero
    {mu : Measure M} [IsFiniteMeasure mu] {g : M → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 mu) :
    Tendsto (fun k => ∫ y, (g y - truncation k g y) ^ 2 ∂mu) atTop (nhds 0) := by
  let F : ℕ → M → ℝ := fun k y => (g y - truncation k g y) ^ 2
  have hFm : ∀ k, AEStronglyMeasurable (F k) mu := fun k =>
    ((hg.sub (measurable_truncation hg k)).pow_const 2).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ y ∂mu, ‖F k y‖ ≤ g y ^ 2 := by
    intro k
    exact Eventually.of_forall fun y => by
      simp only [F, Real.norm_eq_abs, abs_sq, truncation]
      split_ifs with h
      · simpa using sq_nonneg (g y)
      · simp
  have hlim : ∀ᵐ y ∂mu, Tendsto (fun k => F k y) atTop (nhds 0) := by
    refine Eventually.of_forall fun y => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt |g y|
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro k hk
    have hle : |g y| ≤ (k : ℝ) := hN.le.trans (by exact_mod_cast hk)
    simp [F, truncation, hle]
  simpa using tendsto_integral_of_dominated_convergence (fun y => g y ^ 2)
    hFm hg2.integrable_sq hbound hlim

/-- The part of `g-gₖ` below the CLT scale `ε√n`. -/
def doubleTruncation (k n : ℕ) (ε : ℝ) (g : M → ℝ) : M → ℝ :=
  fun y => if |g y| ≤ ε * Real.sqrt n then g y - truncation k g y else 0

/-- The complementary part removed by the moving cutoff. -/
def movingTail (k n : ℕ) (ε : ℝ) (g : M → ℝ) : M → ℝ :=
  fun y => if ε * Real.sqrt n < |g y| then g y - truncation k g y else 0

/-- The square of `g` above the moving cutoff. -/
def movingSquareTail (n : ℕ) (ε : ℝ) (g : M → ℝ) : M → ℝ :=
  fun y => if ε * Real.sqrt n < |g y| then g y ^ 2 else 0

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem sub_truncation_eq_doubleTruncation_add_movingTail
    (k n : ℕ) (ε : ℝ) (g : M → ℝ) (y : M) :
    g y - truncation k g y =
      doubleTruncation k n ε g y + movingTail k n ε g y := by
  simp only [doubleTruncation, movingTail]
  by_cases hy : |g y| ≤ ε * Real.sqrt n
  · rw [ite_eq_left hy, ite_eq_right (not_lt.mpr hy)]
    ring
  · rw [ite_eq_right hy, ite_eq_left (lt_of_not_ge hy)]
    ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurable_doubleTruncation {g : M → ℝ} (hg : Measurable g)
    (k n : ℕ) (ε : ℝ) : Measurable (doubleTruncation k n ε g) := by
  exact (hg.sub (measurable_truncation hg k)).ite
    (measurableSet_le hg.norm measurable_const) measurable_const

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurable_movingTail {g : M → ℝ} (hg : Measurable g)
    (k n : ℕ) (ε : ℝ) : Measurable (movingTail k n ε g) := by
  exact (hg.sub (measurable_truncation hg k)).ite
    (measurableSet_lt measurable_const hg.norm) measurable_const

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurable_movingSquareTail {g : M → ℝ} (hg : Measurable g)
    (n : ℕ) (ε : ℝ) : Measurable (movingSquareTail n ε g) := by
  exact (hg.pow_const 2).ite (measurableSet_lt measurable_const hg.norm) measurable_const

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem abs_doubleTruncation_le {g : M → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (k n : ℕ) (y : M) :
    |doubleTruncation k n ε g y| ≤ ε * Real.sqrt n := by
  simp only [doubleTruncation]
  split_ifs with hcut
  · simp only [truncation]
    split_ifs with hk
    · simpa using mul_nonneg hε (Real.sqrt_nonneg (n : ℝ))
    · simpa using hcut
  · exact abs_zero.trans_le (mul_nonneg hε (Real.sqrt_nonneg _))

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem doubleTruncation_sq_le (k n : ℕ) (ε : ℝ) (g : M → ℝ) (y : M) :
    doubleTruncation k n ε g y ^ 2 ≤ (g y - truncation k g y) ^ 2 := by
  simp only [doubleTruncation]
  split_ifs with hcut
  · exact le_rfl
  · simpa using sq_nonneg (g y - truncation k g y)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Square-integrable functions have vanishing square mass above the moving
level `ε√n`. -/
theorem movingSquareTail_integral_tendsto_zero
    {mu : Measure M} [IsFiniteMeasure mu] {g : M → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 mu) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ∫ y, movingSquareTail n ε g y ∂mu) atTop (nhds 0) := by
  have hcut : Tendsto (fun n : ℕ => ε * Real.sqrt (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hmeas : ∀ n, AEStronglyMeasurable (movingSquareTail n ε g) mu := fun n =>
    (measurable_movingSquareTail hg n ε).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ y ∂mu, ‖movingSquareTail n ε g y‖ ≤ g y ^ 2 := by
    intro n
    exact ae_of_all _ fun y => by
      simp only [movingSquareTail]
      split_ifs
      · rw [Real.norm_eq_abs, abs_sq]
      · simpa using sq_nonneg (g y)
  have hpoint : ∀ᵐ y ∂mu,
      Tendsto (fun n => movingSquareTail n ε g y) atTop (nhds 0) := by
    refine ae_of_all _ fun y => ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [hcut.eventually (eventually_gt_atTop |g y|)] with n hn
    simp [movingSquareTail, not_lt.mpr hn.le]
  simpa using tendsto_integral_of_dominated_convergence (fun y => g y ^ 2)
    hmeas hg2.integrable_sq hbound hpoint

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The deterministic centring contributed by the moving tail is negligible
on the `√n` scale. -/
theorem movingTail_mean_sqrt_tendsto_zero
    {mu : Measure M} [IsProbabilityMeasure mu] {g : M → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 mu) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * |∫ y, movingTail k n ε g y ∂mu|)
      atTop (nhds 0) := by
  have hcut : Tendsto (fun n : ℕ => ε * Real.sqrt (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsquare := movingSquareTail_integral_tendsto_zero hg hg2 hε
  have hupper : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (n : ℝ) * |∫ y, movingTail k n ε g y ∂mu| ≤
        ε⁻¹ * ∫ y, movingSquareTail n ε g y ∂mu := by
    filter_upwards [hcut.eventually (eventually_gt_atTop (k : ℝ))] with n hnk
    have htm : Measurable (movingTail k n ε g) := measurable_movingTail hg k n ε
    have hdiff2 : MemLp (fun y => g y - truncation k g y) 2 mu :=
      hg2.sub (memLp_truncation hg k)
    have htint : Integrable (movingTail k n ε g) mu := by
      apply (hdiff2.integrable (by norm_num)).abs.mono' htm.aestronglyMeasurable
      exact ae_of_all _ fun y => by
        simp only [movingTail]
        split_ifs
        · simp only [Real.norm_eq_abs]
          exact le_rfl
        · simp
    have hsqint : Integrable (movingSquareTail n ε g) mu := by
      apply hg2.integrable_sq.mono' (measurable_movingSquareTail hg n ε).aestronglyMeasurable
      exact ae_of_all _ fun y => by
        simp only [movingSquareTail, Real.norm_eq_abs]
        split_ifs
        · exact (abs_of_nonneg (sq_nonneg _)).le
        · simpa using sq_nonneg (g y)
    calc
      Real.sqrt (n : ℝ) * |∫ y, movingTail k n ε g y ∂mu|
          ≤ Real.sqrt (n : ℝ) * ∫ y, |movingTail k n ε g y| ∂mu := by
            gcongr
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
              (f := movingTail k n ε g) (μ := mu)
      _ = ∫ y, Real.sqrt (n : ℝ) * |movingTail k n ε g y| ∂mu := by
        rw [integral_const_mul]
      _ ≤ ∫ y, ε⁻¹ * movingSquareTail n ε g y ∂mu := by
        apply integral_mono
        · exact htint.abs.const_mul _
        · exact hsqint.const_mul _
        · intro y
          simp only [movingTail, movingSquareTail]
          split_ifs with hy
          · have hkg : (k : ℝ) < |g y| := hnk.trans hy
            have htr : truncation k g y = 0 := by
              simp [truncation, not_le.mpr hkg]
            rw [htr, sub_zero]
            have hy' : ε * Real.sqrt (n : ℝ) ≤ |g y| := hy.le
            rw [inv_mul_eq_div]
            apply (le_div_iff₀ hε).2
            rw [← sq_abs (g y)]
            nlinarith [mul_le_mul_of_nonneg_right hy' (abs_nonneg (g y))]
          · simp
      _ = ε⁻¹ * ∫ y, movingSquareTail n ε g y ∂mu := by
        rw [integral_const_mul]
  apply squeeze_zero' (Eventually.of_forall fun n =>
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hupper
  simpa using hsquare.const_mul ε⁻¹

/-- The event that one of the first `n` observations exceeds the moving
CLT-scale cutoff.  The zero extension makes the definition valid on all
paths; under the conditioned law paths survive through time `n`. -/
def largeObservationEvent (g : M → ℝ) (ε : ℝ) (n : ℕ) : Set (CanonicalChain.Path M) :=
  {omega | ∃ i ∈ Finset.range n,
    ε * Real.sqrt n < |zeroExtension g (omega i)|}

/-- The state-space target corresponding to an observation above the CLT
scale. -/
def largeObservationTarget (g : M → ℝ) (ε : ℝ) (n : ℕ) : Set M :=
  {y | ε * Real.sqrt n < |g y|}

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurableSet_largeObservationTarget {g : M → ℝ} (hg : Measurable g)
    (ε : ℝ) (n : ℕ) : MeasurableSet (largeObservationTarget g ε n) :=
  measurableSet_lt measurable_const hg.norm

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The usual `L²` tail estimate
`n μ(|g| > ε√n) → 0`. -/
theorem scaled_largeObservationTarget_tendsto_zero
    {mu : Measure M} [IsFiniteMeasure mu] {g : M → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 mu) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) * mu.real (largeObservationTarget g ε n))
      atTop (nhds 0) := by
  have htail := movingSquareTail_integral_tendsto_zero hg hg2 hε
  have hupper : ∀ n : ℕ,
      (n : ℝ) * mu.real (largeObservationTarget g ε n) ≤
        ε⁻¹ ^ 2 * ∫ y, movingSquareTail n ε g y ∂mu := by
    intro n
    have hU := measurableSet_largeObservationTarget hg ε n
    have hleft : Integrable
        ((largeObservationTarget g ε n).indicator (fun _ => (n : ℝ))) mu :=
      (integrable_const (n : ℝ)).indicator hU
    have hright : Integrable (fun y => ε⁻¹ ^ 2 * movingSquareTail n ε g y) mu := by
      apply Integrable.const_mul
      apply hg2.integrable_sq.mono'
        (measurable_movingSquareTail hg n ε).aestronglyMeasurable
      exact ae_of_all _ fun y => by
        simp only [movingSquareTail, Real.norm_eq_abs]
        split_ifs
        · rw [abs_sq]
        · simpa using sq_nonneg (g y)
    have hpoint (y : M) :
        (largeObservationTarget g ε n).indicator (fun _ => (n : ℝ)) y ≤
          ε⁻¹ ^ 2 * movingSquareTail n ε g y := by
      by_cases hy : y ∈ largeObservationTarget g ε n
      · rw [Set.indicator_of_mem hy]
        change ε * Real.sqrt (n : ℝ) < |g y| at hy
        rw [movingSquareTail, ite_eq_left hy]
        have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = n :=
          Real.sq_sqrt (Nat.cast_nonneg n)
        have hsq : (ε * Real.sqrt (n : ℝ)) ^ 2 < |g y| ^ 2 := by
          exact (sq_lt_sq₀ (mul_nonneg hε.le (Real.sqrt_nonneg _))
            (abs_nonneg _)).2 hy
        rw [sq_abs] at hsq
        field_simp [hε.ne']
        rw [mul_pow, hsqrt] at hsq
        nlinarith
      · rw [Set.indicator_of_notMem hy]
        exact mul_nonneg (sq_nonneg _) (by
          simp only [movingSquareTail]
          split_ifs <;> positivity)
    calc
      (n : ℝ) * mu.real (largeObservationTarget g ε n) =
          ∫ y, (largeObservationTarget g ε n).indicator (fun _ => (n : ℝ)) y ∂mu := by
            rw [integral_indicator hU, integral_const, smul_eq_mul]
            rw [measureReal_restrict_apply_univ]
            ring
      _ ≤ ∫ y, ε⁻¹ ^ 2 * movingSquareTail n ε g y ∂mu :=
        integral_mono hleft hright hpoint
      _ = ε⁻¹ ^ 2 * ∫ y, movingSquareTail n ε g y ∂mu := by
        rw [integral_const_mul]
  apply squeeze_zero' (Eventually.of_forall fun n =>
    mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)
    (Eventually.of_forall hupper)
  convert htail.const_mul (ε⁻¹ ^ 2) using 1; ring_nf

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem largeObservationTarget_measureReal_tendsto_zero
    {mu : Measure M} [IsFiniteMeasure mu] {g : M → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 mu) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => mu.real (largeObservationTarget g ε n))
      atTop (nhds 0) := by
  have hle : ∀ᶠ n : ℕ in atTop,
      mu.real (largeObservationTarget g ε n) ≤
        (n : ℝ) * mu.real (largeObservationTarget g ε n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [measureReal_nonneg (μ := mu) (s := largeObservationTarget g ε n)]
  exact squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) hle
    (scaled_largeObservationTarget_tendsto_zero hg hg2 hε)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem largeObservationTarget_measure_tendsto_zero
    {mu : Measure M} [IsFiniteMeasure mu] {g : M → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 mu) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => mu (largeObservationTarget g ε n))
      atTop (nhds 0) := by
  rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top mu _)]
  exact largeObservationTarget_measureReal_tendsto_zero hg hg2 hε

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measure_tendsto_zero_of_subset
    {mu : Measure M} [IsFiniteMeasure mu] {U V : ℕ → Set M}
    (hsub : ∀ n, V n ⊆ U n)
    (hU : Tendsto (fun n => mu (U n)) atTop (nhds 0)) :
    Tendsto (fun n => mu (V n)) atTop (nhds 0) := by
  rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top mu _)]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => ENNReal.toReal_mono (measure_ne_top mu _) (measure_mono (hsub n)))
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hU

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- A large observation is bounded by the sum of its one-time conditioned
marginals. -/
theorem largeObservation_probability_le_sum
    {g : M → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) (x : M) :
    (C.conditionedMeasure x n).real (largeObservationEvent g ε n) ≤
      ∑ i ∈ Finset.range n, (C.conditionedMeasure x n).real
        {omega | omega i ∈ Option.some '' largeObservationTarget g ε n} := by
  have he : largeObservationEvent g ε n =
      ⋃ i ∈ Finset.range n,
        {omega : CanonicalChain.Path M |
          omega i ∈ Option.some '' largeObservationTarget g ε n} := by
    ext omega
    constructor
    · rintro ⟨i, hi, hgi⟩
      apply Set.mem_iUnion.2
      refine ⟨i, Set.mem_iUnion.2 ⟨hi, ?_⟩⟩
      cases hwi : omega i with
      | none =>
          simp only [hwi, zeroExtension_none, abs_zero] at hgi
          exact False.elim (not_lt_of_ge (mul_nonneg hε (Real.sqrt_nonneg _)) hgi)
      | some y =>
          have hy : y ∈ largeObservationTarget g ε n := by
            simpa [largeObservationTarget, hwi] using hgi
          exact ⟨y, hy, hwi.symm⟩
    · intro homega
      obtain ⟨i, homega⟩ := Set.mem_iUnion.1 homega
      obtain ⟨hi, homega⟩ := Set.mem_iUnion.1 homega
      obtain ⟨y, hy, hiy⟩ := homega
      refine ⟨i, hi, ?_⟩
      rw [← hiy, zeroExtension_some]
      exact hy
  rw [he]
  exact measureReal_biUnion_finset_le _ _

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The exact one-time marginal written with normalized killed-kernel
iterates. -/
theorem conditioned_target_real_eq_nkp
    (r : ℝ) (hr : 0 < r) (x : M) {i n : ℕ} (hin : i ≤ n)
    (U : Set M) (hU : MeasurableSet U)
    (hpos : 0 < ((C.killedTransition ^ n) x).real univ) :
    (C.conditionedMeasure x n).real {omega | omega i ∈ Option.some '' U} =
      SecondMoment.nkp C r i
          (U.indicator (SecondMoment.nkp C r (n - i) (fun _ => 1))) x /
        SecondMoment.nkp C r n (fun _ => 1) x := by
  have hn : i + (n - i) = n := Nat.add_sub_of_le hin
  conv_lhs => rw [← hn]
  rw [C.conditioned_target_real x i (n - i) U hU]
  unfold SecondMoment.nkp SecondMoment.kpow
  simp only [integral_const, smul_eq_mul, mul_one]
  rw [integral_indicator hU, integral_const_mul]
  have hr0 : r ≠ 0 := hr.ne'
  rw [hn]
  field_simp [hr0, hpos.ne']
  have hp : (1 / r) ^ n = (1 / r) ^ i * (1 / r) ^ (n - i) := by
    rw [← pow_add, hn]
  rw [hp]
  ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Pulling one kernel step out of a normalized iterate. -/
theorem nkp_succ_eq_nkp_nkp_one
    (r : ℝ) (k : ℕ) {F : M → ℝ} (hF : Measurable F)
    {B : ℝ} (hB : ∀ y, |F y| ≤ B) (x : M) :
    SecondMoment.nkp C r (k + 1) F x =
      SecondMoment.nkp C r k (SecondMoment.nkp C r 1 F) x := by
  unfold SecondMoment.nkp
  rw [show (fun y => r⁻¹ ^ 1 * SecondMoment.kpow C 1 F y) =
      fun y => r⁻¹ * SecondMoment.kpow C 1 F y by
        funext y; rw [pow_one],
    SecondMoment.kpow_const_mul]
  have hone : SecondMoment.kpow C 1 F =
      fun z => ∫ w, F w ∂C.killedTransition z := by
    funext z
    simp [SecondMoment.kpow]
  have hs := SecondMoment.kpow_succ' C k hF hB x
  rw [hone, hs, pow_succ]
  ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem nkp_mono_of_bdd
    {r : ℝ} (hr : 0 ≤ r) (k : ℕ) {F G : M → ℝ}
    (hF : Measurable F) (hG : Measurable G) {B : ℝ}
    (hFB : ∀ y, |F y| ≤ B) (hGB : ∀ y, |G y| ≤ B)
    (hFG : ∀ y, F y ≤ G y) (x : M) :
    SecondMoment.nkp C r k F x ≤ SecondMoment.nkp C r k G x := by
  unfold SecondMoment.nkp
  exact mul_le_mul_of_nonneg_left
    (SecondMoment.kpow_mono C k hF hG hFB hGB hFG x)
    (pow_nonneg (inv_nonneg.2 hr) _)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- A one-time marginal bound obtained by mixing across the initial gap.
This is the estimate used for the second half of the trajectory. -/
theorem conditioned_target_late_le
    {mu : Measure M} [IsProbabilityMeasure mu]
    (D : SecondMoment.Data0 C mu) (x : M) {i n : ℕ}
    (hi : 1 ≤ i) (hin : i < n) (U : Set M) (hU : MeasurableSet U)
    {c : ℝ} (hc : 0 < c)
    (hden : c ≤ SecondMoment.nkp C D.r n (fun _ => 1) x) :
    (C.conditionedMeasure x n).real {omega | omega i ∈ Option.some '' U} ≤
      (D.E * ((mu.real U) * D.η x + D.A * D.θ ^ (i - 1))) / c := by
  have hxden : c ≤ SecondMoment.nkp C D.r n (fun _ => 1) x := hden
  have hpath : 0 < ((C.killedTransition ^ n) x).real univ := by
    have hnkp : 0 < SecondMoment.nkp C D.r n (fun _ => 1) x := hc.trans_le hxden
    unfold SecondMoment.nkp SecondMoment.kpow at hnkp
    simpa only [integral_const, smul_eq_mul, mul_one] using
      (pos_of_mul_pos_right hnkp (pow_nonneg (inv_nonneg.2 D.r_pos.le) _))
  let e := SecondMoment.nkp C D.r (n - i) (fun _ => 1)
  let F := U.indicator e
  let G := U.indicator (fun _ => D.E)
  have he0 (y : M) : 0 ≤ e y :=
    SecondMoment.nkp_nonneg C D.r_pos.le _ (fun _ => zero_le_one) y
  have heE (y : M) : e y ≤ D.E := D.mass_le _ y
  have hEm : 0 ≤ D.E := D.E_nonneg
  have hemeas : Measurable e := SecondMoment.measurable_nkp C _ _ measurable_const
  have hFm : Measurable F := hemeas.indicator hU
  have hGm : Measurable G := measurable_const.indicator hU
  have hFB (y : M) : |F y| ≤ D.E := by
    by_cases hy : y ∈ U
    · simp only [F, Set.indicator_of_mem hy, abs_of_nonneg (he0 y)]
      exact heE y
    · simp [F, hy, hEm]
  have hGB (y : M) : |G y| ≤ D.E := by
    by_cases hy : y ∈ U <;> simp [G, hy, abs_of_nonneg hEm, hEm]
  have hFG (y : M) : F y ≤ G y := by
    by_cases hy : y ∈ U <;> simp [F, G, hy, heE y]
  have hnmono : SecondMoment.nkp C D.r i F x ≤ SecondMoment.nkp C D.r i G x :=
    nkp_mono_of_bdd C D.r_pos.le i hFm hGm hFB hGB hFG x
  have hGint : ∫ y, G y ∂mu = D.E * mu.real U := by
    simp only [G]
    rw [integral_indicator hU, integral_const, smul_eq_mul,
      measureReal_restrict_apply_univ]
    ring
  have hdec := D.decay G hGm D.E hGB (i - 1) x
  rw [Nat.sub_add_cancel hi] at hdec
  have hnupper : SecondMoment.nkp C D.r i F x ≤
      D.E * ((mu.real U) * D.η x + D.A * D.θ ^ (i - 1)) := by
    calc
      _ ≤ SecondMoment.nkp C D.r i G x := hnmono
      _ ≤ (∫ y, G y ∂mu) * D.η x + D.A * D.θ ^ (i - 1) * D.E := by
        linarith [le_abs_self (SecondMoment.nkp C D.r i G x -
          (∫ y, G y ∂mu) * D.η x)]
      _ = _ := by rw [hGint]; ring
  have hn0 : 0 ≤ SecondMoment.nkp C D.r i F x :=
    SecondMoment.nkp_nonneg C D.r_pos.le i
      (fun y => Set.indicator_nonneg (fun z _ => he0 z) y) x
  rw [conditioned_target_real_eq_nkp C D.r D.r_pos x hin.le U hU hpath]
  calc
    SecondMoment.nkp C D.r i F x / SecondMoment.nkp C D.r n (fun _ => 1) x
        ≤ SecondMoment.nkp C D.r i F x / c := by
          exact div_le_div_of_nonneg_left hn0 hc hxden
    _ ≤ (D.E * ((mu.real U) * D.η x + D.A * D.θ ^ (i - 1))) / c := by
      exact div_le_div_of_nonneg_right hnupper hc.le

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- A one-time marginal bound obtained by mixing after the first kernel step. Its geometric error
carries the small one-step target factor; this is the estimate used for the first half of the
trajectory. -/
theorem conditioned_target_early_le
    {mu : Measure M} [IsProbabilityMeasure mu]
    (D : SecondMoment.Data0 C mu) (x : M) {i n : ℕ}
    (hi : 1 ≤ i) (hin : i < n) (U : Set M) (hU : MeasurableSet U)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hden : c ≤ SecondMoment.nkp C D.r n (fun _ => 1) x)
    (hsmall : ∀ y,
      SecondMoment.nkp C D.r 1 (U.indicator D.η) y ≤ δ) :
    (C.conditionedMeasure x n).real {omega | omega i ∈ Option.some '' U} ≤
      ((∫ y, U.indicator D.η y ∂mu) * D.η x +
          (D.A + 1) * D.θ ^ (i - 2) * δ +
          D.E * (D.S * D.θ ^ (n - i - 1))) / c := by
  have : Nonempty M := ⟨x⟩
  have hxden : c ≤ SecondMoment.nkp C D.r n (fun _ => 1) x := hden
  have hpath : 0 < ((C.killedTransition ^ n) x).real univ := by
    have hnkp : 0 < SecondMoment.nkp C D.r n (fun _ => 1) x := hc.trans_le hxden
    unfold SecondMoment.nkp SecondMoment.kpow at hnkp
    simpa only [integral_const, smul_eq_mul, mul_one] using
      (pos_of_mul_pos_right hnkp (pow_nonneg (inv_nonneg.2 D.r_pos.le) _))
  let e := SecondMoment.nkp C D.r (n - i) (fun _ => 1)
  let W := U.indicator D.η
  let H := SecondMoment.nkp C D.r 1 W
  let tail := D.S * D.θ ^ (n - i - 1)
  let F := U.indicator e
  have hBη : 0 ≤ D.Bη := D.Bη_nonneg
  have htail0 : 0 ≤ tail := mul_nonneg D.S_nonneg (pow_nonneg D.θ_nonneg _)
  have he0 (y : M) : 0 ≤ e y :=
    SecondMoment.nkp_nonneg C D.r_pos.le _ (fun _ => zero_le_one) y
  have hW0 (y : M) : 0 ≤ W y :=
    Set.indicator_nonneg (fun z _ => D.η_nonneg z) y
  have hWm : Measurable W := D.measurable_η.indicator hU
  have hWB (y : M) : |W y| ≤ D.Bη := by
    by_cases hy : y ∈ U
    · simp only [W, Set.indicator_of_mem hy, abs_of_nonneg (D.η_nonneg y)]
      exact D.η_le y
    · simp [W, hy, hBη]
  have hHm : Measurable H := SecondMoment.measurable_nkp C _ _ hWm
  have hH0 (y : M) : 0 ≤ H y :=
    SecondMoment.nkp_nonneg C D.r_pos.le _ hW0 y
  have hHB (y : M) : |H y| ≤ δ := by
    rw [abs_of_nonneg (hH0 y)]
    exact hsmall y
  have hHint : ∫ y, H y ∂mu = ∫ y, W y ∂mu := by
    exact D.invariant 1 W hWm D.Bη hWB
  have hmain : SecondMoment.nkp C D.r i W x ≤
      (∫ y, W y ∂mu) * D.η x + (D.A + 1) * D.θ ^ (i - 2) * δ := by
    rcases hi.eq_or_lt with rfl | hi2
    · have heq := nkp_succ_eq_nkp_nkp_one C D.r 0 hWm hWB x
      rw [Nat.zero_add, SecondMoment.nkp_zero C D.r hHm] at heq
      rw [heq]
      have hlead : 0 ≤ (∫ y, W y ∂mu) * D.η x :=
        mul_nonneg (integral_nonneg hW0) (D.η_nonneg x)
      have herr : δ ≤ (D.A + 1) * D.θ ^ (1 - 2) * δ := by
        norm_num
        nlinarith [D.A_nonneg, hδ]
      exact (hsmall x).trans (by linarith)
    · obtain ⟨k, hk⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      subst i
      have heq := nkp_succ_eq_nkp_nkp_one C D.r (k + 1) hWm hWB x
      have hdec := D.decay H hHm δ hHB k x
      rw [hHint] at hdec
      rw [heq]
      have hupper : SecondMoment.nkp C D.r (k + 1) H x ≤
          (∫ y, W y ∂mu) * D.η x + D.A * D.θ ^ k * δ := by
        linarith [le_abs_self (SecondMoment.nkp C D.r (k + 1) H x -
          (∫ y, W y ∂mu) * D.η x)]
      have hcoef : D.A * D.θ ^ k * δ ≤ (D.A + 1) * D.θ ^ k * δ := by
        exact mul_le_mul_of_nonneg_right (by
          exact mul_le_mul_of_nonneg_right (by linarith [D.A_nonneg])
            (pow_nonneg D.θ_nonneg k)) hδ
      simpa only [Nat.add_sub_cancel] using hupper.trans (add_le_add le_rfl hcoef)
  have ht : 1 ≤ n - i := Nat.sub_pos_of_lt hin
  have hemass := D.mass_sub (n - i) x ht
  have heupper (y : M) : e y ≤ D.η y + tail := by
    have hh := D.mass_sub (n - i) y ht
    dsimp only [e, tail]
    linarith [le_abs_self (SecondMoment.nkp C D.r (n - i) (fun _ => 1) y - D.η y)]
  let G : M → ℝ := fun y => W y + tail
  have hFm : Measurable F := (SecondMoment.measurable_nkp C _ _ measurable_const).indicator hU
  have hGm : Measurable G := hWm.add measurable_const
  have hcommon : 0 ≤ D.Bη + tail := add_nonneg hBη htail0
  have hFB (y : M) : |F y| ≤ D.Bη + tail := by
    by_cases hy : y ∈ U
    · simp only [F, Set.indicator_of_mem hy, abs_of_nonneg (he0 y)]
      exact (heupper y).trans (by linarith [D.η_le y])
    · simp [F, hy, hcommon]
  have hGB (y : M) : |G y| ≤ D.Bη + tail := by
    rw [abs_of_nonneg (add_nonneg (hW0 y) htail0)]
    exact add_le_add (D.η_le y |>.trans' (by
      by_cases hy : y ∈ U <;> simp [W, hy, D.η_nonneg y])) le_rfl
  have hFG (y : M) : F y ≤ G y := by
    by_cases hy : y ∈ U
    · simp only [F, W, G, Set.indicator_of_mem hy]
      exact heupper y
    · simp only [F, G, W, Set.indicator_of_notMem hy, zero_add]
      exact htail0
  have hnmono : SecondMoment.nkp C D.r i F x ≤ SecondMoment.nkp C D.r i G x :=
    nkp_mono_of_bdd C D.r_pos.le i hFm hGm hFB hGB hFG x
  have hadd : SecondMoment.nkp C D.r i G x =
      SecondMoment.nkp C D.r i W x +
        SecondMoment.nkp C D.r i (fun _ => tail) x := by
    exact SecondMoment.nkp_add C D.r i hWm measurable_const
      (fun y => hWB y |>.trans (le_add_of_nonneg_right htail0))
      (fun _ => by rw [abs_of_nonneg htail0]; exact le_add_of_nonneg_left hBη) x
  have hconst : SecondMoment.nkp C D.r i (fun _ => tail) x ≤ D.E * tail := by
    exact (le_abs_self _).trans (D.nkp_abs_le i measurable_const htail0
      (fun _ => by rw [abs_of_nonneg htail0]) x)
  have hnupper : SecondMoment.nkp C D.r i F x ≤
      (∫ y, W y ∂mu) * D.η x + (D.A + 1) * D.θ ^ (i - 2) * δ + D.E * tail := by
    rw [hadd] at hnmono
    linarith
  have hn0 : 0 ≤ SecondMoment.nkp C D.r i F x :=
    SecondMoment.nkp_nonneg C D.r_pos.le i
      (fun y => Set.indicator_nonneg (fun z _ => he0 z) y) x
  rw [conditioned_target_real_eq_nkp C D.r D.r_pos x hin.le U hU hpath]
  calc
    SecondMoment.nkp C D.r i F x / SecondMoment.nkp C D.r n (fun _ => 1) x
        ≤ SecondMoment.nkp C D.r i F x / c :=
          div_le_div_of_nonneg_left hn0 hc hxden
    _ ≤ ((∫ y, U.indicator D.η y ∂mu) * D.η x +
          (D.A + 1) * D.θ ^ (i - 2) * δ +
          D.E * (D.S * D.θ ^ (n - i - 1))) / c := by
      exact div_le_div_of_nonneg_right (by simpa [W, tail] using hnupper) hc.le

theorem reverse_geometric_tail_le
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    {m n : ℕ} (hmn : m < n) :
    (∑ j ∈ Finset.range m, θ ^ (n - (j + 1) - 1)) ≤
      θ ^ (n - m - 1) / (1 - θ) := by
  rw [← Finset.sum_range_reflect (fun j => θ ^ (n - (j + 1) - 1)) m]
  have heq : (∑ j ∈ Finset.range m, θ ^ (n - (m - 1 - j + 1) - 1)) =
      θ ^ (n - m - 1) * ∑ j ∈ Finset.range m, θ ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_add]
    congr 1
    have hjm := Finset.mem_range.1 hj
    omega
  rw [heq, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (SecondMoment.geom_le hθ0 hθ1 m) (pow_nonneg hθ0 _)

theorem forward_geometric_tail_le
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (m l : ℕ) :
    (∑ j ∈ Finset.range l, θ ^ (m + 1 + j - 1)) ≤
      θ ^ m / (1 - θ) := by
  have heq : (∑ j ∈ Finset.range l, θ ^ (m + 1 + j - 1)) =
      θ ^ m * ∑ j ∈ Finset.range l, θ ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_add]
    congr 1
    omega
  rw [heq, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (SecondMoment.geom_le hθ0 hθ1 l) (pow_nonneg hθ0 _)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurableSet_largeObservationEvent {g : M → ℝ} (hg : Measurable g)
    (ε : ℝ) (n : ℕ) : MeasurableSet (largeObservationEvent g ε n) := by
  have hi (i : ℕ) : MeasurableSet
      {omega : CanonicalChain.Path M |
        ε * Real.sqrt n < |zeroExtension g (omega i)|} :=
    measurableSet_lt measurable_const
      ((measurable_zeroExtension hg).comp (measurable_pi_apply i)).norm
  have he : largeObservationEvent g ε n =
      ⋃ i ∈ Finset.range n,
        {omega : CanonicalChain.Path M |
          ε * Real.sqrt n < |zeroExtension g (omega i)|} := by
    ext omega
    simp [largeObservationEvent]
  rw [he]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun i _ => hi i

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Multiplication by a uniformly bounded measurable function preserves `L²` convergence. -/
theorem mul_tendsto_L2 {mu : Measure M} {a : M → ℝ} {B : ℝ}
    (haB : ∀ y, |a y| ≤ B) (f : ℕ → M → ℝ) (f₀ : M → ℝ)
    (hf : ∀ n, MemLp (f n) 2 mu) (hf₀ : MemLp f₀ 2 mu)
    (haf : ∀ n, MemLp (fun y => a y * f n y) 2 mu)
    (haf₀ : MemLp (fun y => a y * f₀ y) 2 mu)
    (ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (nhds (hf₀.toLp f₀))) :
    Tendsto (fun n => (haf n).toLp (fun y => a y * f n y)) atTop
      (nhds (haf₀.toLp (fun y => a y * f₀ y))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsub : Tendsto (fun n => (hf n).toLp (f n) - hf₀.toLp f₀) atTop (nhds 0) := by
    simpa using ht.sub (tendsto_const_nhds (x := hf₀.toLp f₀))
  apply squeeze_zero' (Eventually.of_forall fun n =>
    show 0 ≤ ‖(haf n).toLp (fun y => a y * f n y) -
      haf₀.toLp (fun y => a y * f₀ y)‖ from norm_nonneg _)
  · exact Eventually.of_forall fun n => by
      show ‖(haf n).toLp (fun y => a y * f n y) -
        haf₀.toLp (fun y => a y * f₀ y)‖ ≤
          B * ‖(hf n).toLp (f n) - hf₀.toLp f₀‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub ((haf n).toLp (fun y => a y * f n y))
          (haf₀.toLp (fun y => a y * f₀ y)), (haf n).coeFn_toLp,
          haf₀.coeFn_toLp, Lp.coeFn_sub ((hf n).toLp (f n)) (hf₀.toLp f₀),
          (hf n).coeFn_toLp, hf₀.coeFn_toLp] with y hwsub hw hw₀ hfsub hfn hf0
      rw [hwsub, Pi.sub_apply, hw, hw₀, hfsub, Pi.sub_apply, hfn, hf0,
        Real.norm_eq_abs, Real.norm_eq_abs]
      rw [show a y * f n y - a y * f₀ y = a y * (f n y - f₀ y) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_right (haB y) (abs_nonneg _)
  · simpa using hsub.norm.const_mul B

/-- Centred Gaussian laws depend continuously on their (nonnegative) real
variance parameter, including at variance zero. -/
theorem tendstoInDistribution_gaussian_variance {v : ℕ → ℝ} {v₀ : ℝ}
    (hv : Tendsto v atTop (nhds v₀)) (hvn : ∀ n, 0 ≤ v n) (hv₀ : 0 ≤ v₀) :
    TendstoInDistribution (fun _ : ℕ => id) atTop id
      (fun n => gaussianReal 0 (v n).toNNReal) (gaussianReal 0 v₀.toNNReal) := by
  refine ⟨fun _ => measurable_id.aemeasurable, measurable_id.aemeasurable, ?_⟩
  simp only [Measure.map_id]
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
  intro t
  have hc : Tendsto (fun n => ((v n : ℝ) : ℂ)) atTop (nhds ((v₀ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.tendsto v₀ |>.comp hv
  have he := Complex.continuous_exp.tendsto _ |>.comp
    ((hc.mul_const ((t : ℂ) ^ 2)).div_const 2).neg
  change Tendsto (fun n => Complex.exp (-(((v n : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)))
    atTop (nhds (Complex.exp (-(((v₀ : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)))) at he
  simpa [charFun_gaussianReal, Real.toNNReal_of_nonneg, hvn, hv₀] using he

/-- The bilinear `L²` form underlying the asymptotic variance. -/
def operatorVariance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E →L[ℝ] E) (u v : E) : ℝ :=
  ⟪u, v⟫_ℝ + 2 * ∑' m : ℕ, ⟪u, (R ^ (m + 1)) v⟫_ℝ

/-- Continuity of the variance form under norm convergence, using the
uniform geometric bound on powers of the spectral remainder. -/
theorem operatorVariance_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (R : E →L[ℝ] E) {L kappa : ℝ} (hL : 0 ≤ L) (hk0 : 0 ≤ kappa)
    (hk1 : kappa < 1)
    (hdec : ∀ m : ℕ, 1 ≤ m → ∀ w, ‖(R ^ m) w‖ ≤ L * kappa ^ m * ‖w‖)
    (u v : ℕ → E) (u0 v0 : E) (hu : Tendsto u atTop (nhds u0))
    (hv : Tendsto v atTop (nhds v0)) :
    Tendsto (fun n => operatorVariance R (u n) (v n)) atTop
      (nhds (operatorVariance R u0 v0)) := by
  obtain ⟨U, hU⟩ := (Metric.isBounded_range_of_tendsto u hu).exists_norm_le
  obtain ⟨V, hV⟩ := (Metric.isBounded_range_of_tendsto v hv).exists_norm_le
  have hUn : ∀ n, ‖u n‖ ≤ U := fun n => hU (u n) ⟨n, rfl⟩
  have hVn : ∀ n, ‖v n‖ ≤ V := fun n => hV (v n) ⟨n, rfl⟩
  have hU0 : 0 ≤ U := (norm_nonneg (u 0)).trans (hUn 0)
  have hV0 : 0 ≤ V := (norm_nonneg (v 0)).trans (hVn 0)
  have hsum : Summable (fun m : ℕ => U * (L * kappa ^ (m + 1) * V)) := by
    have hk := (summable_geometric_of_lt_one hk0 hk1).mul_left (U * L * V * kappa)
    convert hk using 1
    funext m
    rw [pow_succ]
    ring
  have hterm (m : ℕ) : Tendsto (fun n => ⟪u n, (R ^ (m + 1)) (v n)⟫_ℝ)
      atTop (nhds ⟪u0, (R ^ (m + 1)) v0⟫_ℝ) := by
    have hvR : Tendsto (fun n => (R ^ (m + 1)) (v n)) atTop
        (nhds ((R ^ (m + 1)) v0)) :=
      Filter.Tendsto.comp (R ^ (m + 1)).continuous.continuousAt hv
    exact hu.inner hvR
  have hdom : ∀ n m, ‖⟪u n, (R ^ (m + 1)) (v n)⟫_ℝ‖ ≤
      U * (L * kappa ^ (m + 1) * V) := by
    intro n m
    calc
      ‖⟪u n, (R ^ (m + 1)) (v n)⟫_ℝ‖ ≤ ‖u n‖ * ‖(R ^ (m + 1)) (v n)‖ :=
        norm_inner_le_norm _ _
      _ ≤ U * (L * kappa ^ (m + 1) * V) := by
        apply mul_le_mul (hUn n) ((hdec (m + 1) (by omega) (v n)).trans
          (mul_le_mul_of_nonneg_left (hVn n)
            (mul_nonneg hL (pow_nonneg hk0 _)))) (norm_nonneg _) hU0
  have hseries := tendsto_tsum_of_dominated_convergence hsum hterm
    (Eventually.of_forall hdom)
  unfold operatorVariance
  exact (hu.inner hv).add (hseries.const_mul 2)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
private theorem integrable_kint_of_memLp_two
    {K : Kernel M M} {mu : Measure M} [IsFiniteMeasure mu] {c : ENNReal}
    (hK : K ∘ₘ mu = c • mu) (hc : c ≠ ∞) {f : M → ℝ}
    (hf : MemLp f 2 mu) : Integrable (KernelLp.kint K f) mu := by
  have hf1 : MemLp f 1 mu := hf.mono_exponent (by norm_num)
  let f1 : Lp ℝ 1 mu := hf1.toLp f
  have hk : MemLp (KernelLp.kint K f1) 1 mu := KernelLp.memLp_one_kint hK hc f1
  refine (hk.integrable le_rfl).congr ?_
  exact KernelLp.kint_congr hK hf1.coeFn_toLp

omit [BorelSpace M] in
/-- The `L²` remainder has zero `μ`-mean. -/
theorem integral_remainder_eq_zero
    {K : KilledKernel M} (d : DoobTransform.EigenData K.kernel)
    (hc : Continuous d.weight)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : K.kernel ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ x, d.weight x ∂mu = 1)
    (R2 : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (hR2 : ∀ f, R2 f =ᵐ[mu] fun x => (d.rate.toReal)⁻¹ * ∫ y, f y ∂K.kernel x -
      (∫ y, f y ∂mu) * L2Compactness.eta d x)
    (f : Lp ℝ 2 mu) : ∫ x, R2 f x ∂mu = 0 := by
  have hfint : Integrable (f : M → ℝ) mu := (Lp.memLp f).integrable (by norm_num)
  have hkint : Integrable (KernelLp.kint K.kernel f) mu :=
    integrable_kint_of_memLp_two hleft d.rate_ne_top (Lp.memLp f)
  have heta : Integrable (L2Compactness.eta d) mu :=
    (L2Compactness.memLp_eta d mu hc).integrable le_top
  rw [integral_congr_ae (hR2 f)]
  change (∫ x, d.rate.toReal⁻¹ * KernelLp.kint K.kernel f x -
    (∫ y, f y ∂mu) * L2Compactness.eta d x ∂mu) = 0
  rw [integral_sub (hkint.const_mul _) (heta.const_mul _),
    integral_const_mul, integral_const_mul,
    KernelLp.integral_kint hleft d.rate_ne_top hfint,
    L2Compactness.integral_eta d mu hnorm]
  have hr : d.rate.toReal ≠ 0 := (L2Compactness.rate_pos d).ne'
  field_simp
  ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The normalized one-step integral of a normalized `k`-step integral is the normalized
`(k+1)`-step integral, almost everywhere, for `L²(μ)` functions. -/
theorem normalized_kpow_succ_ae
    (d : DoobTransform.EigenData C.killedTransition)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    {F : M → ℝ} (hF : Measurable F) (hF2 : MemLp F 2 mu) (k : ℕ) :
    (fun x => (d.rate.toReal)⁻¹ * ∫ y, SecondMoment.nkp C d.rate.toReal k F y
      ∂C.killedTransition x) =ᵐ[mu]
      SecondMoment.nkp C d.rate.toReal (k + 1) F := by
  have hFi : Integrable F mu := hF2.integrable (by norm_num)
  have hpow := RefinedLLN.kernel_pow_comp hleft (k + 1)
  have hae := KernelLp.ae_integrable_kernel hpow (ENNReal.pow_ne_top d.rate_ne_top)
    hF.stronglyMeasurable hFi
  filter_upwards [hae] with x hx
  unfold SecondMoment.nkp SecondMoment.kpow
  rw [integral_const_mul]
  have hi : (∫ a, ∫ z, F z ∂(C.killedTransition ^ k) a ∂C.killedTransition x) =
      ∫ z, F z ∂(C.killedTransition ^ (k + 1)) x := by
    rw [show C.killedTransition ^ (k + 1) =
      (C.killedTransition ^ k) * C.killedTransition from pow_succ _ _]
    exact (Kernel.integral_comp (η := C.killedTransition ^ k)
      (κ := C.killedTransition) (a := x) (f := F) hx).symm
  rw [hi, pow_succ]
  ring

omit [BorelSpace M] in
set_option maxHeartbeats 1000000 in
/-- Powers of the interpolated `L²` remainder are precisely normalized
killed-kernel powers on a centred `L²` representative. -/
theorem remainder_pow_ae_nkp
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ x, d.weight x ∂mu = 1)
    (R2 : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (hR2 : ∀ f, R2 f =ᵐ[mu] fun x => (d.rate.toReal)⁻¹ *
      (∫ y, f y ∂C.killedTransition x) -
        (∫ y, f y ∂mu) * L2Compactness.eta (K := C.toKilledKernel) d x)
    {F : M → ℝ} (hF : Measurable F) (hF2 : MemLp F 2 mu)
    (hF0 : ∫ y, F y ∂mu = 0) (k : ℕ) :
    ((R2 ^ k) (hF2.toLp F) : M → ℝ) =ᵐ[mu]
      SecondMoment.nkp C d.rate.toReal k F := by
  have hmain : ∀ k : ℕ,
      ((R2 ^ k) (hF2.toLp F) : M → ℝ) =ᵐ[mu]
        SecondMoment.nkp C d.rate.toReal k F ∧
      ∫ y, (R2 ^ k) (hF2.toLp F) y ∂mu = 0 := by
    intro k
    induction k with
    | zero =>
        constructor
        · rw [pow_zero, one_apply_eq_self]
          exact hF2.coeFn_toLp.trans (Eventually.of_forall fun y =>
            (SecondMoment.nkp_zero C d.rate.toReal hF y).symm)
        · rw [pow_zero, one_apply_eq_self,
            integral_congr_ae hF2.coeFn_toLp, hF0]
    | succ k ih =>
        have hsucc := normalized_kpow_succ_ae C d mu hleft hF hF2 k
        constructor
        · rw [pow_succ', mul_apply_eq_comp]
          filter_upwards [hR2 ((R2 ^ k) (hF2.toLp F)),
            KernelLp.kint_congr hleft ih.1, hsucc] with y h1 h2 h3
          rw [h1, ih.2, zero_mul, sub_zero]
          change d.rate.toReal⁻¹ * KernelLp.kint C.killedTransition
            ((R2 ^ k) (hF2.toLp F)) y = _
          rw [h2]
          exact h3
        · rw [pow_succ', mul_apply_eq_comp]
          exact integral_remainder_eq_zero (K := C.toKilledKernel)
            d hc mu hleft hnorm R2 hR2 _
  exact (hmain k).1

omit [BorelSpace M] in
set_option maxHeartbeats 1000000 in
/-- Identification of the asymptotic variance with the bilinear `L²` operator form. -/
theorem asymptoticVariance_eq_operatorVariance
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ x, d.weight x ∂mu = 1)
    (R2 : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (hR2 : ∀ f, R2 f =ᵐ[mu] fun x => (d.rate.toReal)⁻¹ *
      (∫ y, f y ∂C.killedTransition x) -
        (∫ y, f y ∂mu) * L2Compactness.eta (K := C.toKilledKernel) d x)
    (q : M → ℝ) (hqm : Measurable q)
    (hc2 : MemLp (centered C mu d q) 2 mu)
    (hw2 : MemLp (fun y => (d.weight y).toReal * centered C mu d q y) 2 mu)
    (hw0 : ∫ y, (d.weight y).toReal * centered C mu d q y ∂mu = 0) :
    asymptoticVariance C mu d q = operatorVariance R2
      (hc2.toLp (centered C mu d q))
      (hw2.toLp (fun y => (d.weight y).toReal * centered C mu d q y)) := by
  let cq := centered C mu d q
  let wq : M → ℝ := fun y => (d.weight y).toReal * cq y
  let u : Lp ℝ 2 mu := hc2.toLp cq
  let v : Lp ℝ 2 mu := hw2.toLp wq
  have hcqm : Measurable cq := hqm.sub measurable_const
  have hwqm : Measurable wq := d.measurable_weight.ennreal_toReal.mul hcqm
  have hpow (m : ℕ) : ((R2 ^ (m + 1)) v : M → ℝ) =ᵐ[mu]
      SecondMoment.nkp C d.rate.toReal (m + 1) wq := by
    exact remainder_pow_ae_nkp C d hc mu hleft hnorm R2 hR2 hwqm hw2 hw0 (m + 1)
  have hcorr (m : ℕ) : correlation C mu d q m = ⟪u, (R2 ^ (m + 1)) v⟫_ℝ := by
    rw [correlation, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hc2.coeFn_toLp, hpow m] with y hu hv
    simp only [u, v, cq, wq, Real.inner_apply]
    rw [hu, hv]
    rfl
  have hdiag : ∫ y, centered C mu d q y ^ 2 ∂mu.withDensity d.weight = ⟪u, v⟫_ℝ := by
    rw [integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y)),
      MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hc2.coeFn_toLp, hw2.coeFn_toLp] with y hu hv
    simp only [u, v, cq, wq, Real.inner_apply]
    rw [hu, hv, smul_eq_mul]
    ring
  rw [asymptoticVariance, operatorVariance, hdiag]
  congr 2
  exact tsum_congr hcorr

/-- Continuity of the asymptotic variance once the centred observables and their
eigenfunction-weighted versions converge in `L²(μ)`. -/
theorem asymptoticVariance_tendsto_of_centered_L2
    (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ x, d.weight x ∂mu = 1)
    (q : ℕ → M → ℝ) (g : M → ℝ) (hqm : ∀ n, Measurable (q n))
    (hgm : Measurable g)
    (hcq : ∀ n, MemLp (centered C mu d (q n)) 2 mu)
    (hcg : MemLp (centered C mu d g) 2 mu)
    (hwq : ∀ n, MemLp (fun y => (d.weight y).toReal * centered C mu d (q n) y) 2 mu)
    (hwg : MemLp (fun y => (d.weight y).toReal * centered C mu d g y) 2 mu)
    (hwq0 : ∀ n, ∫ y, (d.weight y).toReal * centered C mu d (q n) y ∂mu = 0)
    (hwg0 : ∫ y, (d.weight y).toReal * centered C mu d g y ∂mu = 0)
    (hu : Tendsto (fun n => (hcq n).toLp (centered C mu d (q n))) atTop
      (nhds (hcg.toLp (centered C mu d g))))
    (hv : Tendsto (fun n => (hwq n).toLp
      (fun y => (d.weight y).toReal * centered C mu d (q n) y)) atTop
      (nhds (hwg.toLp (fun y => (d.weight y).toReal * centered C mu d g y)))) :
    Tendsto (fun n => asymptoticVariance C mu d (q n)) atTop
      (nhds (asymptoticVariance C mu d g)) := by
  obtain ⟨-, -, P2, R2, _hP2, hR2, L, kappa, hL, hk0, hk1, hdec⟩ :=
    h.l2_extension_decay (K := C.toKilledKernel) d s.continuous_weight mu hleft hnorm
  have heq (f : M → ℝ) (hfm : Measurable f)
      (hcf : MemLp (centered C mu d f) 2 mu)
      (hwf : MemLp (fun y => (d.weight y).toReal * centered C mu d f y) 2 mu)
      (hwf0 : ∫ y, (d.weight y).toReal * centered C mu d f y ∂mu = 0) :
      asymptoticVariance C mu d f = operatorVariance R2
        (hcf.toLp (centered C mu d f))
        (hwf.toLp (fun y => (d.weight y).toReal * centered C mu d f y)) :=
    asymptoticVariance_eq_operatorVariance C d s.continuous_weight mu hleft hnorm R2 hR2
      f hfm hcf hwf hwf0
  have ht := operatorVariance_tendsto R2 hL.le hk0.le hk1 hdec
    (fun n => (hcq n).toLp (centered C mu d (q n)))
    (fun n => (hwq n).toLp (fun y => (d.weight y).toReal * centered C mu d (q n) y))
    (hcg.toLp (centered C mu d g))
    (hwg.toLp (fun y => (d.weight y).toReal * centered C mu d g y)) hu hv
  rw [heq g hgm hcg hwg hwg0]
  refine ht.congr' ?_
  exact Eventually.of_forall fun n => (heq (q n) (hqm n) (hcq n) (hwq n) (hwq0 n)).symm

set_option maxHeartbeats 2000000 in
/-- The asymptotic variances of the bounded truncations converge to the
variance of an arbitrary finite-valued `L²(μ)` observable. -/
theorem asymptoticVariance_truncation_tendsto
    (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ x, d.weight x ∂mu = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 mu) :
    Tendsto (fun k => asymptoticVariance C mu d (truncation k g)) atTop
      (nhds (asymptoticVariance C mu d g)) := by
  let eta : M → ℝ := fun y => (d.weight y).toReal
  have hetam : Measurable eta := d.measurable_weight.ennreal_toReal
  obtain ⟨B₀, hB₀⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel)
    d s.continuous_weight
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hetaB : ∀ y, |eta y| ≤ B := fun y => by
    have hy := hB₀ y
    rw [Real.norm_eq_abs] at hy
    exact hy.trans (le_max_left _ _)
  have heta2 : MemLp eta 2 mu := MemLp.of_bound hetam.aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hetaB y)
  let eta₂ : Lp ℝ 2 mu := heta2.toLp eta
  let one₂ : Lp ℝ 2 mu := (memLp_const (1 : ℝ)).toLp (fun _ : M => 1)
  let nu := mu.withDensity d.weight
  have hnu : IsProbabilityMeasure nu := by
    refine ⟨?_⟩
    change mu.withDensity d.weight Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  let : IsProbabilityMeasure nu := hnu
  have hq2 : ∀ k, MemLp (truncation k g) 2 mu := fun k => memLp_truncation hgm k
  have hraw : Tendsto (fun k => (hq2 k).toLp (truncation k g)) atTop
      (nhds (hg2.toLp g)) := truncation_tendsto_L2 hgm hg2
  have hmean_eq {f : M → ℝ} (hfm : Measurable f) (hf2 : MemLp f 2 mu) :
      ∫ y, f y ∂nu = @inner ℝ (Lp ℝ 2 mu) _ (hf2.toLp f) eta₂ := by
    rw [show nu = mu.withDensity d.weight from rfl,
      integral_withDensity_eq_integral_toReal_smul d.measurable_weight
        (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y)),
      MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp, heta2.coeFn_toLp] with y hf heta'
    simp only [eta₂, eta, Real.inner_apply]
    rw [hf, heta', smul_eq_mul]
    ring
  have hmean : Tendsto (fun k => ∫ y, truncation k g y ∂nu) atTop
      (nhds (∫ y, g y ∂nu)) := by
    have heta_const : Tendsto (fun _ : ℕ => eta₂) atTop (nhds eta₂) := tendsto_const_nhds
    have hi : Tendsto
        (fun k => inner ℝ ((hq2 k).toLp (truncation k g)) eta₂) atTop
        (nhds (inner ℝ (hg2.toLp g) eta₂)) := hraw.inner heta_const
    convert hi using 1
    · funext k
      exact hmean_eq (measurable_truncation hgm k) (hq2 k)
    · exact congrArg nhds (hmean_eq hgm hg2)
  have hcq : ∀ k, MemLp (centered C mu d (truncation k g)) 2 mu := fun k =>
    (hq2 k).sub (memLp_const (∫ y, truncation k g y ∂nu))
  have hcg : MemLp (centered C mu d g) 2 mu :=
    hg2.sub (memLp_const (∫ y, g y ∂nu))
  have hcenter_toLp {f : M → ℝ} (hf2 : MemLp f 2 mu) :
      (hf2.sub (memLp_const (∫ y, f y ∂nu))).toLp (centered C mu d f) =
        hf2.toLp f - (∫ y, f y ∂nu) • one₂ := by
    change (hf2.sub (memLp_const (∫ y, f y ∂nu))).toLp
      (f - fun _ => ∫ z, f z ∂nu) = _
    apply Lp.ext
    filter_upwards [(hf2.sub (memLp_const (∫ y, f y ∂nu))).coeFn_toLp,
      hf2.coeFn_toLp, Lp.coeFn_sub (hf2.toLp f) ((∫ y, f y ∂nu) • one₂),
      Lp.coeFn_smul (∫ y, f y ∂nu) one₂,
      (memLp_const (1 : ℝ)).coeFn_toLp] with y hc hf hsub hsmul hone
    rw [hc, hsub]
    change f y - (∫ z, f z ∂nu) =
      (hf2.toLp f : M → ℝ) y - (((∫ z, f z ∂nu) • one₂ : Lp ℝ 2 mu) : M → ℝ) y
    rw [hf, hsmul, Pi.smul_apply]
    change f y - (∫ z, f z ∂nu) =
      f y - (∫ z, f z ∂nu) * ((one₂ : Lp ℝ 2 mu) : M → ℝ) y
    rw [show ((one₂ : Lp ℝ 2 mu) : M → ℝ) y = 1 by exact hone]
    ring
  have hcenter : Tendsto
      (fun k => (hcq k).toLp (centered C mu d (truncation k g))) atTop
      (nhds (hcg.toLp (centered C mu d g))) := by
    have hs := hmean.smul_const one₂
    have ht := hraw.sub hs
    rw [hcenter_toLp hg2]
    refine ht.congr' (Eventually.of_forall fun k => ?_)
    exact (hcenter_toLp (hq2 k)).symm
  have hwq : ∀ k,
      MemLp (fun y => eta y * centered C mu d (truncation k g) y) 2 mu := fun k =>
    (hcq k).of_le_mul (hetam.mul ((measurable_truncation hgm k).sub measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hetaB y) (norm_nonneg _))
  have hwg : MemLp (fun y => eta y * centered C mu d g y) 2 mu :=
    hcg.of_le_mul (hetam.mul (hgm.sub measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hetaB y) (norm_nonneg _))
  have hweighted : Tendsto
      (fun k => (hwq k).toLp (fun y => eta y * centered C mu d (truncation k g) y)) atTop
      (nhds (hwg.toLp (fun y => eta y * centered C mu d g y))) :=
    mul_tendsto_L2 hetaB
      (fun k => centered C mu d (truncation k g)) (centered C mu d g)
      hcq hcg hwq hwg hcenter
  have hzero {f : M → ℝ} (hfm : Measurable f)
      (hw : MemLp (fun y => eta y * centered C mu d f y) 2 mu) :
      ∫ y, eta y * centered C mu d f y ∂mu = 0 := by
    have hcint : Integrable (centered C mu d f) nu := by
      rw [show nu = mu.withDensity d.weight from rfl,
        integrable_withDensity_iff d.measurable_weight
          (Eventually.of_forall fun y => (d.weight_ne_top y).lt_top)]
      simpa only [smul_eq_mul, eta, mul_comm] using hw.integrable (by norm_num)
    have hfint : Integrable f nu := by
      change Integrable (fun y => f y - ∫ z, f z ∂nu) nu at hcint
      have hi := hcint.add (integrable_const (∫ y, f y ∂nu))
      convert hi using 1
      funext y
      change f y = (f y - ∫ z, f z ∂nu) + ∫ z, f z ∂nu
      ring
    have hc₀ : ∫ y, centered C mu d f y ∂nu = 0 := by
      rw [show centered C mu d f = fun y => f y - ∫ z, f z ∂nu from rfl,
        integral_sub hfint (integrable_const _), integral_const, probReal_univ, one_smul,
        sub_self]
    rw [show nu = mu.withDensity d.weight from rfl,
      integral_withDensity_eq_integral_toReal_smul d.measurable_weight
        (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))] at hc₀
    simpa only [smul_eq_mul, eta] using hc₀
  exact asymptoticVariance_tendsto_of_centered_L2 C h d s mu hleft hnorm
    (fun k => truncation k g) g (fun k => measurable_truncation hgm k) hgm
    hcq hcg hwq hwg (fun k => hzero (measurable_truncation hgm k) (hwq k))
    (hzero hgm hwg) hcenter hweighted


set_option maxHeartbeats 2000000 in
/-- For an `L²(μ)` observable, the covariance series defining `σ²` converges absolutely. -/
theorem summable_abs_correlation_l2
    (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ x, d.weight x ∂mu = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 mu) :
    Summable (fun m => |correlation C mu d g m|) := by
  have hc := s.continuous_weight
  obtain ⟨B0, hB0⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d hc
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hetaB : ∀ y, |L2Compactness.eta (K := C.toKilledKernel) d y| ≤ B := fun y => by
    change |(d.weight y).toReal| ≤ B
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    have hy := hB0 y
    change ‖(d.weight y).toReal‖ ≤ B0 at hy
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hy
    exact hy.trans (le_max_left _ _)
  let nu := mu.withDensity d.weight
  have hnu : IsProbabilityMeasure nu := by
    refine ⟨?_⟩
    change mu.withDensity d.weight Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  let : IsProbabilityMeasure nu := hnu
  let mg := ∫ y, g y ∂nu
  let gb : M → ℝ := fun y => g y - mg
  have hgbm : Measurable gb := hgm.sub measurable_const
  have hgb2 : MemLp gb 2 mu := hg2.sub (memLp_const mg)
  have hetam : Measurable (L2Compactness.eta (K := C.toKilledKernel) d) :=
    L2Compactness.measurable_eta (K := C.toKilledKernel) d
  let F : M → ℝ := fun y => L2Compactness.eta (K := C.toKilledKernel) d y * gb y
  have hFm : Measurable F := hetam.mul hgbm
  have hF2 : MemLp F 2 mu := hgb2.of_le_mul hFm.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      simp only [F, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hetaB y) (norm_nonneg (gb y)))
  have hgintnu : Integrable g nu := by
    change Integrable g (mu.withDensity d.weight)
    rw [integrable_withDensity_iff d.measurable_weight
      (Eventually.of_forall fun y => (d.weight_ne_top y).lt_top)]
    have hgi : Integrable g mu := hg2.integrable (by norm_num)
    exact hgi.mul_bdd hetam.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact hetaB y)
  have hgb0nu : ∫ y, gb y ∂nu = 0 := by
    rw [show gb = fun y => g y - mg from rfl,
      integral_sub hgintnu (integrable_const mg), integral_const, probReal_univ]
    simp [mg]
  have hF0 : ∫ y, F y ∂mu = 0 := by
    have hdens : ∫ y, gb y ∂nu = ∫ y, gb y * L2Compactness.eta
        (K := C.toKilledKernel) d y ∂mu := by
      change (∫ y, gb y ∂mu.withDensity d.weight) = _
      rw [integral_withDensity_eq_integral_toReal_smul d.measurable_weight
        (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
      congr 1
      funext y
      rw [smul_eq_mul]
      change (d.weight y).toReal * gb y = gb y * (d.weight y).toReal
      ring
    rw [hgb0nu] at hdens
    rw [show F = fun y => gb y * L2Compactness.eta
      (K := C.toKilledKernel) d y by funext y; simp only [F]; ring]
    exact hdens.symm
  obtain ⟨-, -, P2, R2, _hP2, hR2, L, kappa, hL, hk0, hk1, hdec⟩ :=
    h.l2_extension_decay (K := C.toKilledKernel) d hc mu hleft hnorm
  let u : Lp ℝ 2 mu := hgb2.toLp gb
  let v : Lp ℝ 2 mu := hF2.toLp F
  have hcent : centered C mu d g = gb := by
    rfl
  have hFeq : (fun z => (d.weight z).toReal * gb z) = F := by
    rfl
  have hpow (m : ℕ) : ((R2 ^ (m + 1)) v : M → ℝ) =ᵐ[mu]
      SecondMoment.nkp C d.rate.toReal (m + 1) F := by
    exact remainder_pow_ae_nkp C d hc mu hleft hnorm R2 hR2 hFm hF2 hF0 (m + 1)
  have hcorr (m : ℕ) : correlation C mu d g m = ⟪u, (R2 ^ (m + 1)) v⟫_ℝ := by
    rw [correlation, hcent, hFeq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgb2.coeFn_toLp, hpow m] with y hu hv
    simp only [u, v, Real.inner_apply]
    rw [hu, hv]
    rfl
  have hmajor : Summable (fun m : ℕ => ‖u‖ * (L * kappa ^ (m + 1) * ‖v‖)) := by
    have hk := (summable_geometric_of_lt_one hk0.le hk1).mul_left
      (‖u‖ * L * ‖v‖ * kappa)
    convert hk using 1
    funext m
    rw [pow_succ]
    ring
  refine hmajor.of_nonneg_of_le (fun _ => abs_nonneg _) fun m => ?_
  rw [hcorr]
  calc
    |⟪u, (R2 ^ (m + 1)) v⟫_ℝ| ≤ ‖u‖ * ‖(R2 ^ (m + 1)) v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * (L * kappa ^ (m + 1) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hdec (m + 1) (by omega) v) (norm_nonneg u)


/-! ### The double-truncation estimate -/

/-- The centred part of `g-gₖ` below the moving level `ε√n` satisfies a uniform second-moment
estimate. The constant is independent of `k`, `n`, and `ε`. -/
theorem doubleTruncation_second_moment
    (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ y, d.weight y ∂mu = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 mu) (x : d.State) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k n : ℕ, ∀ ε : ℝ, 0 ≤ ε →
      let nu := mu.withDensity d.weight
      let q := doubleTruncation k n ε g
      let qbar := fun y => q y - ∫ z, q z ∂nu
      ∫ omega, pathBirkhoffSum qbar n omega ^ 2
          ∂C.conditionedMeasure x.val n ≤
        A * n * ((∫ y, (g y - truncation k g y) ^ 2 ∂mu) + ε ^ 2) := by
  obtain ⟨Cx, hCx, hsecond⟩ :=
    SecondMoment.conditional_sum_second_moment C h d s hlive mu hleft hnorm x
  obtain ⟨B0, hB0⟩ := L2Compactness.exists_eta_bound
    (K := C.toKilledKernel) d s.continuous_weight
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hetaB (y : M) : (d.weight y).toReal ≤ B := by
    have hy := hB0 y
    change ‖(d.weight y).toReal‖ ≤ B0 at hy
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hy
    exact hy.trans (le_max_left _ _)
  let nu := mu.withDensity d.weight
  have hnu : IsProbabilityMeasure nu := by
    refine ⟨?_⟩
    change mu.withDensity d.weight univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  let : IsProbabilityMeasure nu := hnu
  let K0 := 2 * (1 + B)
  let A := Cx * (K0 + 4)
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  refine ⟨A, mul_nonneg hCx (by dsimp [K0]; positivity), ?_⟩
  intro k n ε hε
  dsimp only
  let q := doubleTruncation k n ε g
  let c := ∫ z, q z ∂nu
  let qbar : M → ℝ := fun y => q y - c
  let tailSq := ∫ y, (g y - truncation k g y) ^ 2 ∂mu
  have hqm : Measurable q := measurable_doubleTruncation hgm k n ε
  have hqb (y : M) : |q y| ≤ ε * Real.sqrt n :=
    abs_doubleTruncation_le hε k n y
  have hqint : Integrable q nu := SecondMoment.integrable_of_bdd hqm hqb
  have hc : |c| ≤ ε * Real.sqrt n := SecondMoment.abs_integral_le_of_prob hqb
  have hqbarm : Measurable qbar := hqm.sub measurable_const
  have hqbarb (y : M) : |qbar y| ≤ 2 * ε * Real.sqrt n := by
    dsimp only [qbar]
    calc
      |q y - c| ≤ |q y| + |c| := abs_sub _ _
      _ ≤ ε * Real.sqrt n + ε * Real.sqrt n := add_le_add (hqb y) hc
      _ = 2 * ε * Real.sqrt n := by ring
  have hqbar0 : ∫ y, qbar y ∂nu = 0 := by
    dsimp only [qbar, c]
    rw [integral_sub hqint (integrable_const _), integral_const, probReal_univ,
      one_smul, sub_self]
  have htail0 : 0 ≤ tailSq := integral_nonneg fun y => sq_nonneg _
  have hdiff2 : MemLp (fun y => g y - truncation k g y) 2 mu :=
    hg2.sub (memLp_truncation hgm k)
  have htailint : Integrable (fun y => (g y - truncation k g y) ^ 2) mu :=
    hdiff2.integrable_sq
  have hq2nu : ∫ y, q y ^ 2 ∂nu ≤ B * tailSq := by
    rw [show nu = mu.withDensity d.weight from rfl,
      integral_withDensity_eq_integral_toReal_smul d.measurable_weight
        (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
    have hleftint : Integrable
        (fun y => (d.weight y).toReal • q y ^ 2) mu := by
      apply SecondMoment.integrable_of_bdd
      · exact d.measurable_weight.ennreal_toReal.smul (hqm.pow_const 2)
      · intro y
        rw [smul_eq_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_pow]
        exact mul_le_mul (hetaB y) (pow_le_pow_left₀ (abs_nonneg _) (hqb y) 2)
          (sq_nonneg _) hB
    calc
      ∫ y, (d.weight y).toReal • q y ^ 2 ∂mu
          ≤ ∫ y, B * (g y - truncation k g y) ^ 2 ∂mu := by
            apply integral_mono
            · exact hleftint
            · exact htailint.const_mul B
            · intro y
              change (d.weight y).toReal * q y ^ 2 ≤
                B * (g y - truncation k g y) ^ 2
              have hqtail := doubleTruncation_sq_le k n ε g y
              exact mul_le_mul (hetaB y) hqtail (sq_nonneg _) hB
      _ = B * tailSq := by rw [integral_const_mul]
  have hc2 : c ^ 2 ≤ B * tailSq := by
    have hcs := SecondMoment.sq_integral_mul_le (ν := nu) (u := q) (v := fun _ => 1)
      hqm measurable_const hqb (V := 1) (fun _ => by simp)
    have hone : ∫ _y : M, (1 : ℝ) ^ 2 ∂nu = 1 := by simp
    rw [hone, mul_one] at hcs
    have hcs' : c ^ 2 ≤ ∫ y, q y ^ 2 ∂nu := by
      simpa only [mul_one, c] using hcs
    exact hcs'.trans hq2nu
  have hqbar2 : ∫ y, qbar y ^ 2 ∂mu ≤ K0 * tailSq := by
    have hqbarint : Integrable (fun y => qbar y ^ 2) mu :=
      SecondMoment.integrable_of_bdd (hqbarm.pow_const 2) (SecondMoment.sq_bdd hqbarb)
    have hqintmu : Integrable (fun y => q y ^ 2) mu :=
      SecondMoment.integrable_of_bdd (hqm.pow_const 2) (SecondMoment.sq_bdd hqb)
    have hcint : Integrable (fun _y : M => (2 : ℝ) * c ^ 2) mu := integrable_const _
    calc
      ∫ y, qbar y ^ 2 ∂mu ≤ ∫ y, 2 * q y ^ 2 + 2 * c ^ 2 ∂mu := by
        apply integral_mono hqbarint (hqintmu.const_mul 2 |>.add hcint)
        intro y
        dsimp only [qbar]
        change (q y - c) ^ 2 ≤ 2 * q y ^ 2 + 2 * c ^ 2
        nlinarith [sq_nonneg (q y + c)]
      _ = 2 * ∫ y, q y ^ 2 ∂mu + 2 * c ^ 2 := by
        rw [integral_add (hqintmu.const_mul 2) hcint, integral_const_mul,
          integral_const, probReal_univ, one_smul]
      _ ≤ 2 * tailSq + 2 * (B * tailSq) := by
        gcongr
        apply integral_mono hqintmu
        · exact htailint
        · exact doubleTruncation_sq_le k n ε g
      _ = K0 * tailSq := by dsimp [K0]; ring
  have hmain := hsecond qbar hqbarm (2 * ε * Real.sqrt n) (by positivity) hqbarb hqbar0 n
  refine hmain.trans ?_
  have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  calc
    Cx * (↑n * ∫ y, qbar y ^ 2 ∂mu + (2 * ε * Real.sqrt n) ^ 2)
        ≤ Cx * (↑n * (K0 * tailSq) + 4 * ε ^ 2 * n) := by
          apply mul_le_mul_of_nonneg_left _ hCx
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hqbar2 (Nat.cast_nonneg n)
          · calc
              (2 * ε * Real.sqrt n) ^ 2 = 4 * ε ^ 2 * (Real.sqrt n) ^ 2 := by ring
              _ = 4 * ε ^ 2 * n := by rw [hsqrt]
              _ ≤ 4 * ε ^ 2 * n := le_rfl
    _ ≤ Cx * (K0 + 4) * n * (tailSq + ε ^ 2) := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have he2 : 0 ≤ ε ^ 2 := sq_nonneg ε
      calc
        _ = Cx * n * (K0 * tailSq + 4 * ε ^ 2) := by ring
        _ ≤ Cx * n * ((K0 + 4) * (tailSq + ε ^ 2)) := by
          gcongr
          nlinarith [mul_nonneg hK0 he2,
            mul_nonneg (show 0 ≤ (4 : ℝ) by norm_num) htail0]
        _ = _ := by ring
    _ = A * n * (tailSq + ε ^ 2) := rfl

/-- Chebyshev's inequality applied to the double-truncation second-moment bound. -/
theorem doubleTruncation_probability
    (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ y, d.weight y ∂mu = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 mu) (x : d.State) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k n : ℕ, 1 ≤ n → ∀ ε δ : ℝ, 0 ≤ ε → 0 < δ →
      let nu := mu.withDensity d.weight
      let q := doubleTruncation k n ε g
      let qbar := fun y => q y - ∫ z, q z ∂nu
      (C.conditionedMeasure x.val n).real {omega |
          δ < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum qbar n omega|} ≤
        A * ((∫ y, (g y - truncation k g y) ^ 2 ∂mu) + ε ^ 2) / δ ^ 2 := by
  obtain ⟨A, hA, hmoment⟩ :=
    doubleTruncation_second_moment C h d s hlive mu hleft hnorm hgm hg2 x
  refine ⟨A, hA, ?_⟩
  intro k n hn ε δ hε hδ
  dsimp only
  have hxsurv : x.val ∈ survivingSet C.killedTransition := by
    rw [← hlive]
    exact x.property
  let : IsProbabilityMeasure (C.conditionedMeasure x.val n) :=
    C.conditionedMeasure_isProbability_of_surviving x.val hxsurv n
  let nu := mu.withDensity d.weight
  let q := doubleTruncation k n ε g
  let qbar : M → ℝ := fun y => q y - ∫ z, q z ∂nu
  let Y : CanonicalChain.Path M → ℝ := fun omega =>
    (Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum qbar n omega
  have hqm : Measurable q := measurable_doubleTruncation hgm k n ε
  have hqbarm : Measurable qbar := hqm.sub measurable_const
  have hYm : Measurable Y := (measurable_pathBirkhoffSum hqbarm n).const_mul _
  have hYb (omega : CanonicalChain.Path M) :
      |Y omega| ≤ 2 * ε * n := by
    have hqbarb (y : M) : |qbar y| ≤ 2 * ε * Real.sqrt n := by
      have hqb := abs_doubleTruncation_le (g := g) hε k n y
      have hnu : IsProbabilityMeasure nu := by
        refine ⟨?_⟩
        change mu.withDensity d.weight univ = 1
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
      let : IsProbabilityMeasure nu := hnu
      have hc := SecondMoment.abs_integral_le_of_prob
        (ν := nu) (f := q) (fun z => abs_doubleTruncation_le (g := g) hε k n z)
      dsimp only [qbar]
      exact (abs_sub _ _).trans (by linarith)
    unfold Y pathBirkhoffSum birkhoffSum
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans ?_
    calc
      |(Real.sqrt (n : ℝ))⁻¹| * ∑ i ∈ Finset.range n,
          |zeroExtension qbar (omega i)|
          ≤ |(Real.sqrt (n : ℝ))⁻¹| * ∑ _i ∈ Finset.range n,
              (2 * ε * Real.sqrt n) := by
                gcongr with i hi
                cases omega i with
                | none =>
                    simp only [zeroExtension_none, abs_zero]
                    positivity
                | some y => simpa using hqbarb y
      _ = 2 * ε * n := by
        have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          abs_of_pos (inv_pos.2 hsqrt)]
        field_simp
  have hY2int : Integrable (fun omega => Y omega ^ 2)
      (C.conditionedMeasure x.val n) :=
    SecondMoment.integrable_of_bdd (hYm.pow_const 2) (SecondMoment.sq_bdd hYb)
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun omega => sq_nonneg (Y omega)) hY2int (δ ^ 2)
  have hsub : {omega | δ < |Y omega|} ⊆ {omega | δ ^ 2 ≤ Y omega ^ 2} := by
    intro omega homega
    change δ < |Y omega| at homega
    change δ ^ 2 ≤ Y omega ^ 2
    rw [← sq_abs (Y omega)]
    exact pow_le_pow_left₀ hδ.le homega.le 2
  have hmono : (C.conditionedMeasure x.val n).real {omega | δ < |Y omega|} ≤
      (C.conditionedMeasure x.val n).real {omega | δ ^ 2 ≤ Y omega ^ 2} :=
    measureReal_mono hsub
  have hm := hmoment k n ε hε
  change (C.conditionedMeasure x.val n).real {omega | δ < |Y omega|} ≤ _
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt2 : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hnreal.le
  have hYeq : ∫ omega, Y omega ^ 2 ∂C.conditionedMeasure x.val n =
      (n : ℝ)⁻¹ * ∫ omega, pathBirkhoffSum qbar n omega ^ 2
        ∂C.conditionedMeasure x.val n := by
    unfold Y
    rw [← integral_const_mul]
    congr 1
    funext omega
    rw [mul_pow]
    field_simp [hnreal.ne']
    rw [hsqrt2]
    ring
  rw [le_div_iff₀ (sq_pos_of_pos hδ)]
  calc
    (C.conditionedMeasure x.val n).real {omega | δ < |Y omega|} * δ ^ 2
        ≤ (C.conditionedMeasure x.val n).real {omega | δ ^ 2 ≤ Y omega ^ 2} * δ ^ 2 :=
          mul_le_mul_of_nonneg_right hmono (sq_nonneg δ)
    _ ≤ ∫ omega, Y omega ^ 2 ∂C.conditionedMeasure x.val n := by
      rw [mul_comm]
      exact hmk
    _ ≤ A * ((∫ y, (g y - truncation k g y) ^ 2 ∂mu) + ε ^ 2) := by
      rw [hYeq]
      calc
        (n : ℝ)⁻¹ * ∫ omega, pathBirkhoffSum qbar n omega ^ 2
            ∂C.conditionedMeasure x.val n
            ≤ (n : ℝ)⁻¹ *
              (A * n * ((∫ y, (g y - truncation k g y) ^ 2 ∂mu) + ε ^ 2)) :=
                mul_le_mul_of_nonneg_left hm (inv_nonneg.2 hnreal.le)
        _ = _ := by field_simp

set_option maxHeartbeats 2000000 in
/-- The double-truncation argument: once CLT-scale observations are unlikely,
the bounded truncations approximate the original centred sums in conditioned
probability, uniformly for all sufficiently large truncation levels. -/
theorem truncation_negligible_of_large_observations
    (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ y, d.weight y ∂mu = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 mu) (x : d.State)
    (hlarge : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (C.conditionedMeasure x.val n).real
        (largeObservationEvent g ε n)) atTop (nhds 0)) :
    ∀ a b : ℝ, 0 < a → 0 < b → ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      (C.conditionedMeasure x.val n).real {omega |
        a < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum (centered C mu d g) n omega -
          (Real.sqrt (n : ℝ))⁻¹ *
            pathBirkhoffSum (centered C mu d (truncation k g)) n omega|} < b := by
  intro a b ha hb
  let nu := mu.withDensity d.weight
  have hnu : IsProbabilityMeasure nu := by
    refine ⟨?_⟩
    change mu.withDensity d.weight univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  let : IsProbabilityMeasure nu := hnu
  obtain ⟨B0, hB0⟩ := L2Compactness.exists_eta_bound
    (K := C.toKilledKernel) d s.continuous_weight
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hweight (y : M) : d.weight y ≤ ENNReal.ofReal B := by
    have hy := hB0 y
    change ‖(d.weight y).toReal‖ ≤ B0 at hy
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hy
    have hyr : (d.weight y).toReal ≤ B := hy.trans (le_max_left _ _)
    rw [← ENNReal.ofReal_toReal (d.weight_ne_top y)]
    exact ENNReal.ofReal_le_ofReal hyr
  have hg2nu : MemLp g 2 nu := by
    exact memLp_weighted_of_memLp ENNReal.ofReal_ne_top
      (ae_of_all _ hweight) hg2
  obtain ⟨A, hA, hprob⟩ :=
    doubleTruncation_probability C h d s hlive mu hleft hnorm hgm hg2 x
  let den := (a / 2) ^ 2
  have hden : 0 < den := sq_pos_of_pos (half_pos ha)
  have htarget : 0 < (b / 4) * den := mul_pos (by positivity) hden
  obtain ⟨c, hc, hAc⟩ := exists_pos_mul_lt htarget A
  let ε := min c 1
  have hε : 0 < ε := lt_min hc zero_lt_one
  have hεsq : ε ^ 2 ≤ c := by
    change (min c 1) ^ 2 ≤ c
    by_cases hc1 : c ≤ 1
    · rw [min_eq_left hc1]
      nlinarith
    · rw [min_eq_right (le_of_not_ge hc1)]
      nlinarith
  have hbase : A * ε ^ 2 / den < b / 4 := by
    apply (div_lt_iff₀ hden).2
    calc
      A * ε ^ 2 ≤ A * c := mul_le_mul_of_nonneg_left hεsq hA
      _ < (b / 4) * den := hAc
  have htail := integral_sq_sub_truncation_tendsto_zero hgm hg2
  have hboundlim : Tendsto (fun k =>
      A * ((∫ y, (g y - truncation k g y) ^ 2 ∂mu) + ε ^ 2) / den)
      atTop (nhds (A * ε ^ 2 / den)) := by
    convert ((htail.add_const (ε ^ 2)).const_mul A).div_const den using 1; ring_nf
  have hkbound : ∀ᶠ k in atTop,
      A * ((∫ y, (g y - truncation k g y) ^ 2 ∂mu) + ε ^ 2) / den < b / 2 :=
    hboundlim.eventually (gt_mem_nhds (hbase.trans (by linarith)))
  filter_upwards [hkbound] with k hk
  have hmean := movingTail_mean_sqrt_tendsto_zero hgm hg2nu k hε
  have hnmean : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (n : ℝ) * |∫ y, movingTail k n ε g y ∂nu| < a / 2 :=
    hmean.eventually (gt_mem_nhds (half_pos ha))
  have hnlarge : ∀ᶠ n in atTop,
      (C.conditionedMeasure x.val n).real (largeObservationEvent g ε n) < b / 2 :=
    (hlarge ε hε).eventually (gt_mem_nhds (half_pos hb))
  filter_upwards [hnmean, hnlarge, eventually_ge_atTop 1] with n hnmean hnlarge hn
  have hxsurv : x.val ∈ survivingSet C.killedTransition := by
    rw [← hlive]
    exact x.property
  let : IsProbabilityMeasure (C.conditionedMeasure x.val n) :=
    C.conditionedMeasure_isProbability_of_surviving x.val hxsurv n
  let q := doubleTruncation k n ε g
  let t := movingTail k n ε g
  let cq := ∫ y, q y ∂nu
  let ct := ∫ y, t y ∂nu
  let qbar : M → ℝ := fun y => q y - cq
  have hqevent := hprob k n hn ε (a / 2) hε.le (half_pos ha)
  have hqsmall : (C.conditionedMeasure x.val n).real {omega |
      a / 2 < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum qbar n omega|} < b / 2 :=
    hqevent.trans_lt (by simpa only [den, q, cq, qbar, nu] using hk)
  have hsub : {omega |
      a < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum (centered C mu d g) n omega -
        (Real.sqrt (n : ℝ))⁻¹ *
          pathBirkhoffSum (centered C mu d (truncation k g)) n omega|} ≤ᵐ[C.conditionedMeasure x.val n]
      (largeObservationEvent g ε n ∪
        {omega | a / 2 < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum qbar n omega|}) := by
    filter_upwards [C.ae_survival_conditionedMeasure x.val n] with omega homega hbad
    by_cases hbig : omega ∈ largeObservationEvent g ε n
    · exact Or.inl hbig
    · right
      have htzero : pathBirkhoffSum t n omega = 0 := by
        unfold pathBirkhoffSum birkhoffSum
        apply Finset.sum_eq_zero
        intro i hi
        have hnot : ¬ ε * Real.sqrt n < |zeroExtension g (omega i)| := by
          intro hgi
          exact hbig ⟨i, hi, hgi⟩
        cases hwi : omega i with
        | none => simp [t]
        | some y =>
            simp only [t, zeroExtension_some, movingTail]
            rw [ite_eq_right]
            simpa [hwi] using hnot
      have hdecomp (y : M) : g y - truncation k g y = q y + t y :=
        sub_truncation_eq_doubleTruncation_add_movingTail k n ε g y
      have hqint : Integrable q nu :=
        SecondMoment.integrable_of_bdd (measurable_doubleTruncation hgm k n ε)
          (abs_doubleTruncation_le hε.le k n)
      have htint : Integrable t nu := by
        have hd2 : MemLp (fun y => g y - truncation k g y) 2 nu :=
          hg2nu.sub (memLp_truncation (mu := nu) hgm k)
        have hi := (hd2.integrable (by norm_num)).sub hqint
        apply hi.congr
        exact ae_of_all _ fun y => by
          simp only [Pi.sub_apply]
          linarith [hdecomp y]
      have hmeanadd : ∫ y, (g y - truncation k g y) ∂nu = cq + ct := by
        calc
          ∫ y, (g y - truncation k g y) ∂nu = ∫ y, q y + t y ∂nu :=
            integral_congr_ae (ae_of_all _ hdecomp)
          _ = cq + ct := by rw [integral_add hqint htint]
      have hgint : Integrable g nu := hg2nu.integrable (by norm_num)
      have hgkint : Integrable (truncation k g) nu :=
        (memLp_truncation (mu := nu) hgm k).integrable (by norm_num)
      have hmeansub : (∫ y, g y ∂nu) - ∫ y, truncation k g y ∂nu = cq + ct := by
        rw [← integral_sub hgint hgkint]
        exact hmeanadd
      have hdiff :
          (Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum (centered C mu d g) n omega -
            (Real.sqrt (n : ℝ))⁻¹ *
              pathBirkhoffSum (centered C mu d (truncation k g)) n omega =
          (Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum qbar n omega -
            Real.sqrt (n : ℝ) * ct := by
        have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
        have hpointsum :
            pathBirkhoffSum (centered C mu d g) n omega -
                pathBirkhoffSum (centered C mu d (truncation k g)) n omega =
              pathBirkhoffSum qbar n omega +
                pathBirkhoffSum (fun y => t y - ct) n omega := by
          unfold pathBirkhoffSum birkhoffSum
          rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (homega i (Finset.mem_range.1 hi).le)
          simp only [hy, centered, qbar, cq, ct, zeroExtension_some]
          linarith [hdecomp y, hmeansub]
        calc
          _ = (Real.sqrt (n : ℝ))⁻¹ *
              (pathBirkhoffSum (centered C mu d g) n omega -
                pathBirkhoffSum (centered C mu d (truncation k g)) n omega) := by ring
          _ = (Real.sqrt (n : ℝ))⁻¹ *
              (pathBirkhoffSum qbar n omega +
                pathBirkhoffSum (fun y => t y - ct) n omega) := by rw [hpointsum]
          _ = _ := by
            rw [SmallJumpMoment.pathBirkhoffSum_sub_const t ct homega, htzero]
            have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = n :=
              Real.sq_sqrt (Nat.cast_nonneg n)
            field_simp [hsqrt.ne']
            rw [hsqrt_sq]
            ring
      rw [hdiff] at hbad
      have hct : |Real.sqrt (n : ℝ) * ct| < a / 2 := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact hnmean
      by_contra hqbad
      have hqle : |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum qbar n omega| ≤ a / 2 :=
        not_lt.mp hqbad
      exact (not_lt_of_ge ((abs_sub _ _).trans (by linarith))) hbad
  calc
    (C.conditionedMeasure x.val n).real {omega |
        a < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum (centered C mu d g) n omega -
          (Real.sqrt (n : ℝ))⁻¹ *
            pathBirkhoffSum (centered C mu d (truncation k g)) n omega|}
        ≤ (C.conditionedMeasure x.val n).real
          (largeObservationEvent g ε n ∪
            {omega | a / 2 < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum qbar n omega|}) :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ (C.conditionedMeasure x.val n).real (largeObservationEvent g ε n) +
          (C.conditionedMeasure x.val n).real
            {omega | a / 2 < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum qbar n omega|} :=
          measureReal_union_le _ _
    _ < b := by linarith


set_option maxHeartbeats 2000000 in
/-- The final converging-together step for the `L²` conditional CLT, given the double-truncation
negligibility estimate. -/
theorem conditional_clt_l2_of_truncation_negligible
    (h : HypothesisH rho C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (mu : Measure M) [IsProbabilityMeasure mu]
    (hleft : C.killedTransition ∘ₘ mu = d.rate • mu)
    (hnorm : ∫⁻ y, d.weight y ∂mu = 1)
    {g : M → ℝ} (hgm : Measurable g) (hg2 : MemLp g 2 mu) (x : d.State)
    (hnear : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      (C.conditionedMeasure x.val n).real {omega |
        ε < |(Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum (centered C mu d g) n omega -
          (Real.sqrt (n : ℝ))⁻¹ *
            pathBirkhoffSum (centered C mu d (truncation k g)) n omega|} < δ) :
    Summable (fun m => |correlation C mu d g m|) ∧
      0 ≤ asymptoticVariance C mu d g ∧
      TendstoInDistribution
        (fun (n : ℕ) omega => (Real.sqrt (n : ℝ))⁻¹ *
          pathBirkhoffSum (centered C mu d g) n omega)
        atTop id (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
        (gaussianReal 0 (asymptoticVariance C mu d g).toNNReal) := by
  let variance : ℕ → ℝ := fun k => asymptoticVariance C mu d (truncation k g)
  let variance₀ : ℝ := asymptoticVariance C mu d g
  have hbounded (k : ℕ) := ConditionalCLT.conditional_clt_bounded C h d s hlive mu hleft hnorm
    (measurable_truncation hgm k) (abs_truncation_le g k) x
  have hvn : ∀ k, 0 ≤ variance k := fun k => (hbounded k).2.1
  have hv : Tendsto variance atTop (nhds variance₀) :=
    asymptoticVariance_truncation_tendsto C h d s mu hleft hnorm hgm hg2
  have hv₀ : 0 ≤ variance₀ := ge_of_tendsto hv (Eventually.of_forall hvn)
  refine ⟨summable_abs_correlation_l2 C h d s mu hleft hnorm hgm hg2, hv₀, ?_⟩
  let P : ℕ → Measure (Path M) := fun n =>
    (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))
  let hP (n : ℕ) : IsProbabilityMeasure (P n) := by
    dsimp only [P]
    infer_instance
  let Q : Measure ℝ := gaussianReal 0 1
  let X : ℕ → Path M → ℝ := fun n omega => (Real.sqrt (n : ℝ))⁻¹ *
    pathBirkhoffSum (centered C mu d g) n omega
  let Y : ℕ → ℕ → Path M → ℝ := fun k n omega =>
    (Real.sqrt (n : ℝ))⁻¹ * pathBirkhoffSum (centered C mu d (truncation k g)) n omega
  let Z : ℕ → ℝ → ℝ := fun k z => Real.sqrt (variance k) * z
  let W : ℝ → ℝ := fun z => Real.sqrt variance₀ * z
  have hX : ∀ n, Measurable (X n) := fun n =>
    (measurable_pathBirkhoffSum (hgm.sub measurable_const) n).const_mul _
  have hY : ∀ k n, Measurable (Y k n) := fun k n =>
    (measurable_pathBirkhoffSum ((measurable_truncation hgm k).sub measurable_const) n).const_mul _
  have hZ : ∀ k, Measurable (Z k) := fun k => measurable_id.const_mul _
  have hYZ : ∀ k, TendstoInDistribution (Y k) atTop (Z k) P Q := by
    intro k
    have hb := (hbounded k).2.2
    refine ⟨hb.forall_aemeasurable, (hZ k).aemeasurable, ?_⟩
    have hmap : Q.map (Z k) = gaussianReal 0 (variance k).toNNReal := by
      change (gaussianReal 0 1).map (fun z => Real.sqrt (variance k) * z) = _
      rw [gaussianReal_map_const_mul]
      simp only [mul_zero]
      congr 1
      apply NNReal.eq
      simp only [NNReal.coe_mk, mul_one,
        Real.sq_sqrt (hvn k), Real.coe_toNNReal _ (hvn k)]
    have hlim := hb.tendsto
    simpa only [Measure.map_id, hmap] using hlim
  have hZW : TendstoInDistribution Z atTop W (fun _ => Q) Q := by
    apply tendstoInDistribution_of_ae_tendsto
    · exact fun k => (hZ k).aemeasurable
    · exact measurable_id.const_mul _ |>.aemeasurable
    · apply ae_of_all
      intro z
      exact hv.sqrt.mul_const z
  have hfinal := tendstoInDistribution_of_double_probability_approximation P Q Q
    X Y Z W hX hY hZ hYZ hZW (by
      intro ε δ hε hδ
      simpa only [P, X, Y, CanonicalChain.liveConditionedProbabilityMeasure,
        ProbabilityMeasure.coe_mk] using hnear ε δ hε hδ)
  refine ⟨hfinal.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  have hmap₀ : Q.map W = gaussianReal 0 variance₀.toNNReal := by
    change (gaussianReal 0 1).map (fun z => Real.sqrt variance₀ * z) = _
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mk, mul_one,
      Real.sq_sqrt hv₀, Real.coe_toNNReal _ hv₀]
  have ht := hfinal.tendsto
  simpa only [Measure.map_id, hmap₀] using ht


end

end ConditionedStableLaws.L2Variance
