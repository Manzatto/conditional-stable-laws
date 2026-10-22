import ConditionedStableLaws.EndpointTrimming
import ConditionedStableLaws.ClusterProbabilities

/-!
# One-time conditioned bounds for removing endpoint strips

A uniform normalized-survival bound dominates a conditioned target marginal by the Doob return
probability. Together with the refined return estimate, this retains summable geometric errors near
the initial endpoint.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
namespace ConditionedStableLaws.CanonicalChain
open PathMixing StandingHypothesis
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)
local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

/-- Exact one-time marginal of the conditioned path law. -/
theorem conditioned_target_real (x : M) (i t : ℕ) (U : Set M) (hU : MeasurableSet U) :
    (C.conditionedMeasure x (i + t)).real {ω | ω i ∈ Option.some '' U} =
      (∫ y in U, ((C.killedTransition ^ t) y).real univ ∂(C.killedTransition ^ i) x) /
        ((C.killedTransition ^ (i + t)) x).real univ := by
  have hp := C.conditioned_multitime_event x [(i, U)] (by simpa) t
  have he : pathEvent [(i, U)] = {ω : ℕ → Option M | ω i ∈ Option.some '' U} := by
    ext ω
    simp [pathEvent]
  simp only [totalTime, indicatorObservations, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, he, PathMixing.kernelWord] at hp
  have hi : (fun y => U.indicator (fun _ => (1 : ℝ≥0∞)) y * (C.killedTransition ^ t) y univ) =
      U.indicator (fun y => (C.killedTransition ^ t) y univ) := by
    funext y
    by_cases hy : y ∈ U <;> simp [hy]
  rw [hi, lintegral_indicator hU] at hp
  have hr := congrArg ENNReal.toReal hp
  have : IsFiniteKernel (C.killedTransition ^ t) := killedKernel_power_isFinite C.toKilledKernel t
  have hm : Measurable (fun y => (C.killedTransition ^ t) y univ) :=
    (C.killedTransition ^ t).measurable_coe MeasurableSet.univ
  have hc := integral_toReal (μ := ((C.killedTransition ^ i) x).restrict U)
    hm.aemeasurable (Eventually.of_forall (fun y => (measure_ne_top _ _).lt_top))
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_inv, ← hc,
    div_eq_mul_inv, mul_comm] using hr

/-- Real form of the exact ambient Doob target formula, with its live-subtype probability. -/
theorem doob_target_real (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) (i : ℕ) (U : Set M) (hU : MeasurableSet U) :
    ((d.kernel ^ i) x).real (Subtype.val ⁻¹' U) =
      (d.rate.toReal)⁻¹ ^ i * (d.weight x.val).toReal⁻¹ *
        ∫ y in U, (d.weight y).toReal ∂(C.killedTransition ^ i) x.val := by
  have hd := d.lintegral_power_ambient i x
    (U.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hU)
  have hlive : (fun y : d.State => U.indicator (fun _ => (1 : ℝ≥0∞)) y.val) =
      (Subtype.val ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) := rfl
  have hind : (fun y => d.weight y * U.indicator (fun _ => (1 : ℝ≥0∞)) y) =
      U.indicator d.weight := by
    funext y
    by_cases hy : y ∈ U <;> simp [hy]
  rw [hlive, lintegral_indicator (hU.preimage measurable_subtype_coe), lintegral_one,
    Measure.restrict_apply_univ, hind, lintegral_indicator hU] at hd
  have hc := integral_toReal (μ := ((C.killedTransition ^ i) x.val).restrict U)
    d.measurable_weight.aemeasurable
    (Eventually.of_forall (fun y => (d.weight_ne_top y).lt_top))
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ← hc]
    using congrArg ENNReal.toReal hd


/-- Once normalized survival at the starting state is at least half its limit, a conditioned target
marginal is bounded by a fixed multiple of the Doob return. The remaining survival gap can be
arbitrarily short. -/
theorem conditioned_target_le_doob (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) (i t : ℕ) (U : Set M) (hU : MeasurableSet U)
    (B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a)
    (hlower : ∀ y ∈ U, a ≤ (d.weight y).toReal)
    (hupper : ∀ y, (d.rate.toReal)⁻¹ ^ t * ((C.killedTransition ^ t) y).real univ ≤ B)
    (hden : (d.weight x.val).toReal / 2 ≤
      (d.rate.toReal)⁻¹ ^ (i + t) * ((C.killedTransition ^ (i + t)) x.val).real univ) :
    (C.conditionedMeasure x.val (i + t)).real {ω | ω i ∈ Option.some '' U} ≤
      (2 * B / a) * ((d.kernel ^ i) x).real (Subtype.val ⁻¹' U) := by
  let c := (d.rate.toReal)⁻¹
  have hc : 0 < c := inv_pos.mpr (ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top)
  have hx : 0 < (d.weight x.val).toReal := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  have hwint : Integrable (fun y => (d.weight y).toReal) ((C.killedTransition ^ i) x.val) := by
    apply integrable_toReal_of_lintegral_ne_top d.measurable_weight.aemeasurable
    rw [d.right_eigen_power]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top d.rate_ne_top) (d.weight_ne_top _)
  have hi : (∫ y in U, c ^ t * ((C.killedTransition ^ t) y).real univ
      ∂(C.killedTransition ^ i) x.val) ≤
      ∫ y in U, (B / a) * (d.weight y).toReal ∂(C.killedTransition ^ i) x.val := by
    apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => by positivity))
      ((hwint.const_mul (B / a)).integrableOn)
    filter_upwards [ae_restrict_mem hU] with y hy
    exact (hupper y).trans (by
      have hh := mul_le_mul_of_nonneg_left (hlower y hy) (div_nonneg hB ha.le)
      simpa [div_mul_cancel₀ _ ha.ne'] using hh)
  simp only [integral_const_mul] at hi
  have hq : c^i * (∫ y in U, (d.weight y).toReal ∂(C.killedTransition ^ i) x.val) =
      (d.weight x.val).toReal * ((d.kernel ^ i) x).real (Subtype.val ⁻¹' U) := by
    rw [C.doob_target_real d x i U hU]
    dsimp [c]
    field_simp
  have hZ : 0 < ((C.killedTransition ^ (i + t)) x.val).real univ := by
    have hh : 0 < c^(i+t) * ((C.killedTransition ^ (i+t)) x.val).real univ :=
      (half_pos hx).trans_le hden
    exact (mul_pos_iff_of_pos_left (pow_pos hc _)).mp hh
  have he : (C.conditionedMeasure x.val (i+t)).real {ω | ω i ∈ Option.some '' U} *
      (c^(i+t) * ((C.killedTransition ^ (i+t)) x.val).real univ) =
      c^i * (∫ y in U, c^t * ((C.killedTransition ^ t) y).real univ
        ∂(C.killedTransition ^ i) x.val) := by
    rw [C.conditioned_target_real x.val i t U hU, integral_const_mul,
      show c^(i+t) = c^i*c^t from pow_add c i t]
    field_simp [hZ.ne']
  have hn : (C.conditionedMeasure x.val (i+t)).real {ω | ω i ∈ Option.some '' U} *
      (c^(i+t) * ((C.killedTransition ^ (i+t)) x.val).real univ) ≤
      (B/a) * ((d.weight x.val).toReal * ((d.kernel ^ i) x).real (Subtype.val ⁻¹' U)) := by
    rw [he, ← hq, integral_const_mul]
    calc
      _ ≤ c^i * ((B/a) * ∫ y in U, (d.weight y).toReal ∂(C.killedTransition ^ i) x.val) :=
        mul_le_mul_of_nonneg_left hi (pow_nonneg hc.le _)
      _ = _ := by ring
  have hd := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ (C.conditionedMeasure x.val (i+t)).real {ω | ω i ∈ Option.some '' U} from measureReal_nonneg)
  apply (mul_le_mul_iff_right₀ hx).mp
  dsimp [c] at hn
  simp only [div_eq_mul_inv] at hn hd ⊢
  nlinarith

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.EndpointTrimming

/-- The geometric error along any set of positive times is summable, so both
endpoint strips together cost only one geometric-series constant. -/
theorem sum_boundary_geometric_le (n L : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (∑ t ∈ boundaryTimes n L, if t.val = 0 then (0 : ℝ) else θ^(t.val - 1)) ≤
      1 / (1 - θ) := by
  have hall : (∑ t : Fin n, if t.val = 0 then (0 : ℝ) else θ^(t.val - 1)) ≤
      1 / (1 - θ) := by
    cases n with
    | zero =>
        simpa using (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (sub_nonneg.mpr hθ1.le))
    | succ n =>
        simpa [Fin.sum_univ_succ] using ClusterGapSums.geometric_sum_le n hθ0 hθ1
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun t _ _ => by split <;> positivity)).trans hall

/-- A quantitative endpoint bound from marginal estimates retaining their
geometric small-target error. Time zero is handled separately. -/
theorem sum_boundary_marginals_le (n L : ℕ) (v : Fin n → ℝ)
    (p D C θ δ : ℝ) (hp : 0 ≤ p) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (hzero : ∀ t : Fin n, t.val = 0 → v t = 0)
    (hv : ∀ t : Fin n, 0 < t.val → v t ≤ D * (p + C * θ^(t.val - 1) * δ)) :
    (∑ t ∈ boundaryTimes n L, v t) ≤
      D * (2 * (L : ℝ) * p + C * δ / (1 - θ)) := by
  have hpoint (t : Fin n) : v t ≤ D*p + D*C*δ*(if t.val = 0 then 0 else θ^(t.val - 1)) := by
    by_cases ht : t.val = 0
    · rw [hzero t ht]
      simp only [ht, ↓reduceIte, mul_zero, add_zero]
      positivity
    · have hh := hv t (Nat.pos_of_ne_zero ht)
      simp only [ht, ↓reduceIte]
      nlinarith [hh]
  calc
    _ ≤ ∑ t ∈ boundaryTimes n L, (D*p + D*C*δ*(if t.val = 0 then 0 else θ^(t.val - 1))) :=
      Finset.sum_le_sum (fun t _ => hpoint t)
    _ = ((boundaryTimes n L).card : ℝ)*(D*p) + D*C*δ*
        ∑ t ∈ boundaryTimes n L, (if t.val = 0 then 0 else θ^(t.val - 1)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (2*(L : ℝ))*(D*p) + D*C*δ*(1/(1-θ)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hD hp)
        exact_mod_cast card_boundaryTimes_le n L
      · exact mul_le_mul_of_nonneg_left (sum_boundary_geometric_le n L hθ0 hθ1)
          (by positivity)
    _ = _ := by ring

/-- The endpoint probability bound vanishes under precisely the first-order small-target scalings.
-/
theorem boundary_marginal_bound_tendsto_zero (L : ℕ → ℕ) (p δ : ℕ → ℝ)
    (D C θ rate : ℝ)
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 rate))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => D * (2 * (L n : ℝ) * p n + C * δ n / (1 - θ))) atTop (𝓝 0) := by
  have hLp : Tendsto (fun n => (L n : ℝ)*p n) atTop (𝓝 0) := by
    have hh := hL.mul hp
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  have hh := ((hLp.const_mul 2).add ((hδ.const_mul C).div_const (1-θ))).const_mul D
  simpa [mul_assoc] using hh

end ConditionedStableLaws.EndpointTrimming


namespace ConditionedStableLaws.CanonicalChain
open PathMixing StandingHypothesis EndpointTrimming ConditionalMixing
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)
local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

/-- The zero-time endpoint is absent whenever the fixed starting state is
outside the target, independently of the conditioning horizon. -/
theorem conditioned_target_zero [MeasurableSingletonClass M]
    (x : M) (n : ℕ) (U : Set M) (hU : MeasurableSet U) (hx : x ∉ U) :
    (C.conditionedMeasure x n).real {ω | ω 0 ∈ Option.some '' U} = 0 := by
  have he := C.conditioned_target_real x 0 n U hU
  simp only [zero_add] at he
  rw [he]
  change (∫ y in U, ((C.killedTransition ^ n) y).real univ ∂Measure.dirac x) / _ = 0
  rw [← integral_indicator hU, integral_dirac, indicator_of_notMem hx, zero_div]

variable [MetricSpace M] [CompactSpace M] [BorelSpace M] {ρ : Measure M}

/-- The first-order endpoint-strip estimate of PPP Step 3, derived from the operator gap, uniform
normalized survival, and the one-step small mass. All finite-time marginal probabilities are those
of the canonical conditioned path measure. -/
theorem conditioned_endpoint_sum_tendsto_zero
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (μ : Measure M) (hμρ : μ ≪ ρ)
    (hmean : ∀ v, s.mean v = ∫ y, v y ∂μ)
    (hleft : ∀ v, s.mean (((d.rate.toReal)⁻¹ • h.transitionOperator) v) = s.mean v)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, a ≤ (d.weight y).toReal)
    (hxU : ∀ᶠ n in atTop, x.val ∉ U n)
    (δ : ℕ → ℝ) (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hsmall : ∀ᶠ n in atTop, ∀ y, (C.killedTransition y).real (U n) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (L : ℕ → ℕ) (rate : ℝ)
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (μ.withDensity d.weight).real (U n))
      atTop (𝓝 rate)) :
    Tendsto (fun n => ∑ i ∈ boundaryTimes n (L n),
      (C.conditionedMeasure x.val n).real {ω | ω i.val ∈ Option.some '' U n}) atTop (𝓝 0) := by
  obtain ⟨R, _hR0, hRt, hR⟩ := h.weight_bounded d s.eigenvector s.eigenvector_ae
  have hweight : ∀ y, (d.weight y).toReal ≤ R.toReal := fun y => ENNReal.toReal_mono hRt (hR y)
  have hx : 0 < (d.weight x.val).toReal := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  let D := 2 * s.survivalBound / a
  let Cx := max s.constant ‖1 - rankOne s.mean s.eigenvector‖ *
    (d.rate.toReal)⁻¹ * R.toReal / (d.weight x.val).toReal
  have hD : 0 ≤ D := by dsimp [D]; exact div_nonneg (by nlinarith [s.survivalBound_nonneg]) ha.le
  have hCx : 0 ≤ Cx := by dsimp [Cx]; positivity
  have hden : ∀ᶠ n in atTop, (d.weight x.val).toReal / 2 ≤
      (d.rate.toReal)⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ := by
    have hh := (tendsto_order.mp (s.normalized_survival_tendstoUniformly.tendsto_at x.val)).1
      _ (half_lt_self hx)
    filter_upwards [hh] with n hn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, Measure.real, toKilledKernel_kernel] using hn.le
  have hlim := boundary_marginal_bound_tendsto_zero L
    (fun n => (μ.withDensity d.weight).real (U n)) δ D Cx s.decay rate hL hp hδ
  apply squeeze_zero' (Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => measureReal_nonneg))) _ hlim
  filter_upwards [hlower, hxU, hδ0, hsmall, hden] with n hlow hxUn hδn hsmalln hdenn
  apply sum_boundary_marginals_le n (L n) _ _ D Cx s.decay (δ n)
    measureReal_nonneg hD hCx s.decay_nonneg s.decay_lt_one hδn
  · intro i hi
    rw [hi]
    exact C.conditioned_target_zero x.val n (U n) (hU n) hxUn
  · intro i hi
    have hit : i.val + (n - i.val) = n := Nat.add_sub_of_le i.isLt.le
    have hupper (y : M) : (d.rate.toReal)⁻¹ ^ (n - i.val) *
        ((C.killedTransition ^ (n - i.val)) y).real univ ≤ s.survivalBound := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, Measure.real, toKilledKernel_kernel] using s.normalized_survival_real_le (n - i.val) y
    have hdom := C.conditioned_target_le_doob d x i.val (n - i.val) (U n) (hU n)
      s.survivalBound a s.survivalBound_nonneg ha hlow hupper (by simpa only [hit] using hdenn)
    rw [hit] at hdom
    have hret := h.doob_short_return d μ hμρ s.mean hmean s.eigenvector s.eigenvector_ae
      (U n) (hU n) (weightedTargetVector s.eigenvector (U n) (hU n))
      (weightedTargetVector_ae s.eigenvector (U n) (hU n) _ s.eigenvector_ae) (hleft _)
      R.toReal (δ n) (d.weight x.val).toReal s.constant s.decay ENNReal.toReal_nonneg hδn hx
      s.constant_nonneg s.decay_nonneg hweight hsmalln s.gap (i.val - 1) x le_rfl
    rw [Nat.sub_add_cancel hi] at hret
    exact hdom.trans (mul_le_mul_of_nonneg_left hret hD)

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.CanonicalChain
open StandingHypothesis EndpointTrimming
variable {M J : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  [Fintype J] {ρ : Measure M} (C : CanonicalChain M)
local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] [Fintype J] in
/-- The conditioned probability law at a live starting state. -/
def liveConditionedProbabilityMeasure (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) (n : ℕ) : ProbabilityMeasure (Path M) :=
  ⟨C.conditionedMeasure x.val n,
    C.conditionedMeasure_isProbability_of_surviving x.val (d.liveSet_subset_survivingSet x.property) n⟩

/-- Under the spectral and small-target hypotheses, a trimmed count limit is a limit for the
original canonical conditioned count vector. The boundary-hit probability is proved through one-time
chain estimates. -/
theorem conditioned_count_law_transfer_of_small_targets
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (μ : Measure M) (hμρ : μ ≪ ρ)
    (hmean : ∀ v, s.mean v = ∫ y, v y ∂μ)
    (hleft : ∀ v, s.mean (((d.rate.toReal)⁻¹ • h.transitionOperator) v) = s.mean v)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, a ≤ (d.weight y).toReal)
    (hxU : ∀ᶠ n in atTop, x.val ∉ U n)
    (δ : ℕ → ℝ) (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hsmall : ∀ᶠ n in atTop, ∀ y, (C.killedTransition y).real (U n) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (L : ℕ → ℕ) (rate : ℝ)
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (μ.withDensity d.weight).real (U n))
      atTop (𝓝 rate))
    (targets : ℕ → J → Set M) (hTargets : ∀ n j, MeasurableSet (targets n j))
    (hTargetsU : ∀ n j, targets n j ⊆ U n)
    (ν : ProbabilityMeasure (J → ℕ))
    (htrim : Tendsto (fun n => ProbabilityMeasure.map (C.liveConditionedProbabilityMeasure d x n)
      (visitCountVector (trimmedObservations (L n) (fun i : Fin n => fun ω : Path M => ω i.val))
        (liftedTargets (fun j => Option.some '' targets n j)))) atTop (𝓝 ν)) :
    Tendsto (fun n => ProbabilityMeasure.map (C.liveConditionedProbabilityMeasure d x n)
      (visitCountVector (fun i : Fin n => fun ω : Path M => ω i.val)
        (fun j => Option.some '' targets n j))) atTop (𝓝 ν) := by
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val (d.liveSet_subset_survivingSet x.property) n
  apply count_law_transfer_of_boundaryHit (fun n => C.conditionedMeasure x.val n)
    (fun n i ω => ω i.val) (fun _ _ => measurable_pi_apply _)
    (fun n j => Option.some '' targets n j)
    (fun n j => measurableEmbedding_some_state.measurableSet_image' (hTargets n j)) L _ ν htrim
  apply boundaryHit_tendsto_zero_of_common_target_sum (fun n => C.conditionedMeasure x.val n)
    (fun n i ω => ω i.val) (fun n j => Option.some '' targets n j)
    (fun n => Option.some '' U n) (fun n j => Set.image_mono (hTargetsU n j)) L
  exact C.conditioned_endpoint_sum_tendsto_zero h d s μ hμρ hmean hleft x U hU a ha hlower hxU
    δ hδ0 hsmall hδ L rate hL hp

end ConditionedStableLaws.CanonicalChain
