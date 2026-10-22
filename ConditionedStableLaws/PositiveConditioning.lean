import ConditionedStableLaws.EndpointChainBounds

/-!
# Positive conditioned words and Doob probabilities

For target events, positivity gives a multiplicative domination by the Doob law. This gives upper
bounds on excluded configurations.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
noncomputable section
namespace ConditionedStableLaws.PositiveConditioning
open PathMixing StationaryClusters
variable {M : Type*} [MeasurableSpace M]

/-- A terminal comparison on the common target propagates through every
nonnegative target word when it is evaluated inside that target. -/
theorem kernelWord_terminal_le_on (K : Kernel M M) (U : Set M)
    (w : List (ℕ × Set M)) (hsub : ∀ p ∈ w, p.2 ⊆ U)
    (g h : M → ℝ≥0∞) (hgh : ∀ y ∈ U, g y ≤ h y)
    (x : M) (hx : x ∈ U) :
    PathMixing.kernelWord K (indicatorObservations w) g x ≤
      PathMixing.kernelWord K (indicatorObservations w) h x := by
  induction w generalizing x with
  | nil => exact hgh x hx
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ A
      · simp only [indicator_of_mem hy, one_mul]
        exact ih (fun p hp => hsub p (by simp [hp])) y (hsub (n, A) (by simp) hy)
      · simp [hy]

/-- A nonempty target word needs a terminal comparison only on its last
target, rather than on every point of the ambient state space. -/
theorem kernelWord_terminal_le (K : Kernel M M) (U : Set M)
    (w : List (ℕ × Set M)) (hne : w ≠ []) (hsub : ∀ p ∈ w, p.2 ⊆ U)
    (g h : M → ℝ≥0∞) (hgh : ∀ y ∈ U, g y ≤ h y) (x : M) :
    PathMixing.kernelWord K (indicatorObservations w) g x ≤
      PathMixing.kernelWord K (indicatorObservations w) h x := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons p w =>
      rcases p with ⟨n, A⟩
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ A
      · simp only [indicator_of_mem hy, one_mul]
        exact kernelWord_terminal_le_on K U w (fun p hp => hsub p (by simp [hp]))
          g h hgh y (hsub (n, A) (by simp) hy)
      · simp [hy]

/-- The live-state event attached to an ambient list of target sets. -/
def doobEvent {K : Kernel M M} (d : DoobTransform.EigenData K) (w : List (ℕ × Set M)) :
    Set (ℕ → d.State) :=
  targetEvent (w.map (fun p => (p.1, (Subtype.val : d.State → M) ⁻¹' p.2)))

/-- The probability of a deterministic-start Doob target event is its kernel word. -/
theorem doob_multitime_event {K : Kernel M M} [IsSFiniteKernel K]
    (d : DoobTransform.EigenData K) (x : d.State)
    (w : List (ℕ × Set M)) (hw : ∀ p ∈ w, MeasurableSet p.2) :
    QProcessLimit.pathMeasure d.kernel x (doobEvent d w) =
      PathMixing.kernelWord d.kernel (d.liveObservations (indicatorObservations w)) (fun _ => 1) x := by
  let v := w.map (fun p => (p.1, (Subtype.val : d.State → M) ⁻¹' p.2))
  have hv : ∀ p ∈ v, MeasurableSet p.2 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (hw q hq).preimage measurable_subtype_coe
  have he : d.liveObservations (indicatorObservations w) = indicatorObservations v := by
    simp only [DoobTransform.EigenData.liveObservations, indicatorObservations, v,
      List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p _
    congr 1
  rw [he]
  have hi := lintegral_pathProduct d.kernel x (indicatorObservations v)
    (measurable_indicatorObservations v hv) (fun _ => 1) measurable_const
  simp only [mul_one] at hi
  simp_rw [pathProduct_target_indicators] at hi
  rw [lintegral_indicator (measurableSet_targetEvent v hv), lintegral_one,
    Measure.restrict_apply_univ] at hi
  exact hi


/-- A word of observations bounded by one preserves the eigenfunction bound.
This proves finiteness of the weighted word without a global positive lower
bound on the eigenfunction. -/
theorem kernelWord_weight_le {K : Kernel M M} [IsSFiniteKernel K]
    (d : DoobTransform.EigenData K) (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, ∀ y, p.2 y ≤ 1) (x : M) :
    PathMixing.kernelWord K w d.weight x ≤ d.rate ^ totalTime w * d.weight x := by
  induction w generalizing x with
  | nil => simp [PathMixing.kernelWord, totalTime]
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      calc
        _ ≤ ∫⁻ y, d.rate ^ totalTime w * d.weight y ∂(K ^ n) x := by
          apply lintegral_mono
          intro y
          exact (mul_le_mul' (hw (n, f) (by simp) y)
            (ih (fun p hp => hw p (by simp [hp])) y)).trans_eq (one_mul _)
        _ = d.rate ^ totalTime w * (d.rate ^ n * d.weight x) := by
          rw [lintegral_const_mul _ d.measurable_weight, d.right_eigen_power]
        _ = _ := by
          simp only [totalTime, List.map_cons, List.sum_cons, pow_add]
          ac_rfl

end ConditionedStableLaws.PositiveConditioning


namespace ConditionedStableLaws.CanonicalChain
open PathMixing StandingHypothesis StationaryClusters PositiveConditioning
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)
local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

/-- Positive multitime target events are dominated by their Doob probabilities. This gives upper
bounds for excluded configurations. -/
theorem conditioned_targets_le_doob (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) (U : Set M) (w : List (ℕ × Set M)) (hw : ∀ p ∈ w, MeasurableSet p.2)
    (hne : w ≠ []) (hsub : ∀ p ∈ w, p.2 ⊆ U) (t : ℕ)
    (B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a)
    (hlower : ∀ y ∈ U, a ≤ (d.weight y).toReal)
    (hupper : ∀ y, (d.rate.toReal)⁻¹ ^ t * ((C.killedTransition ^ t) y).real univ ≤ B)
    (hden : (d.weight x.val).toReal / 2 ≤
      (d.rate.toReal)⁻¹ ^ (totalTime (indicatorObservations w) + t) *
        ((C.killedTransition ^ (totalTime (indicatorObservations w) + t)) x.val).real univ) :
    (C.conditionedMeasure x.val (totalTime (indicatorObservations w) + t)).real (pathEvent w) ≤
      (2 * B / a) * (QProcessLimit.pathMeasure d.kernel x).real (doobEvent d w) := by
  let v := indicatorObservations w
  let N := totalTime v
  let c := (d.rate.toReal)⁻¹
  have hc : 0 < c := inv_pos.mpr (ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top)
  have hx : 0 < (d.weight x.val).toReal := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  have hBa : 0 ≤ B/a := div_nonneg hB ha.le
  have hv : ∀ p ∈ v, Measurable p.2 := measurable_indicatorObservations w hw
  have hvb : ∀ p ∈ v, ∀ y, p.2 y ≤ 1 := by
    intro p hp y
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    by_cases hy : y ∈ q.2 <;> simp [hy]
  have hg : Measurable (fun y => (C.killedTransition ^ t) y univ) :=
    (C.killedTransition ^ t).measurable_coe MeasurableSet.univ
  have hterm (y : M) (hy : y ∈ U) :
      (d.rate⁻¹)^t * (C.killedTransition ^ t) y univ ≤ ENNReal.ofReal (B/a) * d.weight y := by
    have : IsFiniteKernel (C.killedTransition ^ t) := killedKernel_power_isFinite C.toKilledKernel t
    rw [← ENNReal.ofReal_toReal (d.weight_ne_top y), ← ENNReal.ofReal_mul hBa]
    apply (ENNReal.le_ofReal_iff_toReal_le
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr d.rate_ne_zero))
        (measure_ne_top _ _)) (mul_nonneg hBa ENNReal.toReal_nonneg)).mpr
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    exact (hupper y).trans (by
      have hh := mul_le_mul_of_nonneg_left (hlower y hy) hBa
      simpa [div_mul_cancel₀ _ ha.ne'] using hh)
  have hn := kernelWord_terminal_le C.killedTransition U w hne hsub
    (fun y => (d.rate⁻¹)^t * (C.killedTransition ^ t) y univ)
    (fun y => ENNReal.ofReal (B/a) * d.weight y) hterm x.val
  rw [kernelWord_const_mul C.killedTransition v hv _ _ hg,
    kernelWord_const_mul C.killedTransition v hv _ _ d.measurable_weight] at hn
  have hfin : PathMixing.kernelWord C.killedTransition v d.weight x.val ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top d.rate_ne_top) (d.weight_ne_top _))
      (kernelWord_weight_le d v hvb x.val)
  have hnr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hn
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hBa] at hnr
  have hQ : (QProcessLimit.pathMeasure d.kernel x).real (doobEvent d w) =
      c^N * (d.weight x.val).toReal⁻¹ * (PathMixing.kernelWord C.killedTransition v d.weight x.val).toReal := by
    unfold Measure.real
    rw [doob_multitime_event d x w hw, d.kernelWord_doob v hv]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    rfl
  have hP : (C.conditionedMeasure x.val (N+t)).real (pathEvent w) =
      (PathMixing.kernelWord C.killedTransition v (fun y => (C.killedTransition ^ t) y univ) x.val).toReal /
        ((C.killedTransition ^ (N+t)) x.val).real univ := by
    unfold Measure.real
    rw [C.conditioned_multitime_event x.val w hw t]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
    rfl
  have hZ : 0 < ((C.killedTransition ^ (N+t)) x.val).real univ := by
    have hh : 0 < c^(N+t) * ((C.killedTransition ^ (N+t)) x.val).real univ :=
      (half_pos hx).trans_le hden
    exact (mul_pos_iff_of_pos_left (pow_pos hc _)).mp hh
  have hq : c^N * (PathMixing.kernelWord C.killedTransition v d.weight x.val).toReal =
      (d.weight x.val).toReal * (QProcessLimit.pathMeasure d.kernel x).real (doobEvent d w) := by
    rw [hQ]
    field_simp
  have hp : (C.conditionedMeasure x.val (N+t)).real (pathEvent w) *
      (c^(N+t) * ((C.killedTransition ^ (N+t)) x.val).real univ) =
      c^N * (c^t * (PathMixing.kernelWord C.killedTransition v
        (fun y => (C.killedTransition ^ t) y univ) x.val).toReal) := by
    rw [hP, show c^(N+t) = c^N*c^t from pow_add c N t]
    field_simp [hZ.ne']
  have hnreal : (C.conditionedMeasure x.val (N+t)).real (pathEvent w) *
      (c^(N+t) * ((C.killedTransition ^ (N+t)) x.val).real univ) ≤
      (B/a) * ((d.weight x.val).toReal * (QProcessLimit.pathMeasure d.kernel x).real (doobEvent d w)) := by
    rw [hp, ← hq]
    exact (mul_le_mul_of_nonneg_left hnr (pow_nonneg hc.le N)).trans_eq (by ring)
  have hd := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ (C.conditionedMeasure x.val (N+t)).real (pathEvent w) from measureReal_nonneg)
  apply (mul_le_mul_iff_right₀ hx).mp
  change _ ≤ (d.weight x.val).toReal * ((2*B/a) * (QProcessLimit.pathMeasure d.kernel x).real (doobEvent d w))
  dsimp [N, c, v] at hnreal
  simp only [div_eq_mul_inv] at hnreal hd ⊢
  nlinarith

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.PositiveConditioning
open PathMixing StationaryClusters ClusterProbabilities
variable {M : Type*} [MeasurableSpace M]

/-- Moving the first observation gap into the initial measure is an exact identity of Markov target
probabilities. -/
theorem kernelWord_first_eq_initial (K : Kernel M M) [IsMarkovKernel K]
    (x : M) (i : ℕ) (A : Set M) (hA : MeasurableSet A)
    (w : List (ℕ × Set M)) (hw : ∀ p ∈ w, MeasurableSet p.2) :
    PathMixing.kernelWord K (indicatorObservations ((i, A) :: w)) (fun _ => 1) x =
      initialPathMeasure K ((K ^ i) x) (targetEvent ((0, A) :: w)) := by
  have hwm : ∀ p ∈ (0, A) :: w, MeasurableSet p.2 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hA
    · exact hw p hp
  have hp := lintegral_initial_pathProduct K ((K ^ i) x)
    (indicatorObservations ((0, A) :: w)) (measurable_indicatorObservations _ hwm)
  simp_rw [pathProduct_target_indicators] at hp
  rw [lintegral_indicator (measurableSet_targetEvent _ hwm), lintegral_one,
    Measure.restrict_apply_univ] at hp
  rw [hp]
  change (∫⁻ y, A.indicator (fun _ => 1) y *
    PathMixing.kernelWord K (indicatorObservations w) (fun _ => 1) y ∂(K ^ i) x) = _
  apply lintegral_congr
  intro y
  change _ = ∫⁻ z, A.indicator (fun _ => 1) z *
    PathMixing.kernelWord K (indicatorObservations w) (fun _ => 1) z ∂Measure.dirac y
  exact (lintegral_dirac' y ((measurable_const.indicator hA).mul
    (measurable_kernelWord K _ (measurable_indicatorObservations _ hw) _ measurable_const))).symm

/-- Deterministic-start Doob event probabilities retain one factor for the
first hit and one return factor for each subsequent positive time gap. -/
theorem doob_event_product_le {K : Kernel M M} [IsSFiniteKernel K]
    (d : DoobTransform.EigenData K) (x : d.State) (U A : Set M)
    (hA : MeasurableSet A) (hAU : A ⊆ U) (i : ℕ)
    (w : List (ℕ × Set M)) (hw : ∀ p ∈ w, MeasurableSet p.2)
    (hsub : ∀ p ∈ w, p.2 ⊆ U)
    (p₀ : ℝ) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hfirst : ((d.kernel ^ i) x).real (Subtype.val ⁻¹' U) ≤ p₀)
    (hreturn : ∀ p ∈ w, ∀ y : d.State, y.val ∈ U →
      ((d.kernel ^ p.1) y).real (Subtype.val ⁻¹' U) ≤ b p.1) :
    (QProcessLimit.pathMeasure d.kernel x).real (doobEvent d ((i, A) :: w)) ≤
      p₀ * (w.map (fun p => b p.1)).prod := by
  let v := w.map (fun p => (p.1, (Subtype.val : d.State → M) ⁻¹' p.2))
  have hv : ∀ p ∈ v, MeasurableSet p.2 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (hw q hq).preimage measurable_subtype_coe
  have hvs : ∀ p ∈ v, p.2 ⊆ (Subtype.val : d.State → M) ⁻¹' U := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact preimage_mono (hsub q hq)
  have hvr : ∀ p ∈ v, ∀ y ∈ (Subtype.val : d.State → M) ⁻¹' U,
      ((d.kernel ^ p.1) y).real (Subtype.val ⁻¹' U) ≤ b p.1 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact hreturn q hq
  have : IsMarkovKernel (d.kernel ^ i) := markov_power d.kernel i
  have hh := initial_cluster_real_le d.kernel ((d.kernel ^ i) x) (Subtype.val ⁻¹' U)
    (Subtype.val ⁻¹' A) (hA.preimage measurable_subtype_coe) (preimage_mono hAU)
    v hv hvs b hb hvr
  simp only [Measure.real] at hh
  rw [← kernelWord_first_eq_initial d.kernel x i (Subtype.val ⁻¹' A)
    (hA.preimage measurable_subtype_coe) v hv] at hh
  have he : d.liveObservations (indicatorObservations ((i, A) :: w)) =
      indicatorObservations ((i, (Subtype.val : d.State → M) ⁻¹' A) :: v) := by
    simp only [DoobTransform.EigenData.liveObservations, indicatorObservations, v,
      List.map_cons, List.map_map, Function.comp_def]
    congr 1
  have hwm : ∀ p ∈ (i, A) :: w, MeasurableSet p.2 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hA
    · exact hw p hp
  have hev := congrArg ENNReal.toReal (doob_multitime_event d x ((i, A) :: w) hwm)
  rw [he] at hev
  rw [show (QProcessLimit.pathMeasure d.kernel x).real (doobEvent d ((i, A) :: w)) =
    (PathMixing.kernelWord d.kernel (indicatorObservations ((i, Subtype.val ⁻¹' A) :: v))
      (fun _ => 1) x).toReal from hev]
  have hprod : 0 ≤ (w.map (fun p => b p.1)).prod := by
    apply List.prod_nonneg
    intro a ha
    rcases List.mem_map.mp ha with ⟨q, hq, rfl⟩
    exact hb q.1
  have hh' : (PathMixing.kernelWord d.kernel
      (indicatorObservations ((i, Subtype.val ⁻¹' A) :: v)) (fun _ => 1) x).toReal ≤
      ((d.kernel ^ i) x).real (Subtype.val ⁻¹' U) * (w.map (fun p => b p.1)).prod := by
    simpa only [Measure.real, v, List.map_map, Function.comp_def] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_right hfirst hprod)

end ConditionedStableLaws.PositiveConditioning
