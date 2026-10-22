import ConditionedStableLaws.PoissonTargetStart
import ConditionedStableLaws.ConvergingTogether
import ConditionedStableLaws.MultiplierReflection

/-!
# Arbitrary finite values at the singularity

Under H, a reference-null set is never visited at positive times. Changing an
observable on such a set changes a conditioned Birkhoff sum only at time zero.
Consequently every diverging normalization preserves its distributional limit.
Regularity makes the singularity a null singleton, and the quasi-ergodic
integral, including the absolute truncation at exponent one, is unchanged.
-/

open MeasureTheory ProbabilityTheory Filter Set
open Classical
open scoped Topology ENNReal

noncomputable section
namespace ConditionedStableLaws.CanonicalChain
open StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- No positive-time observation lies in a reference-null measurable set. -/
theorem ae_positive_time_avoids_null (h : HypothesisH ρ C.toKilledKernel)
    {N : Set M} (hN : MeasurableSet N) (hnull : ρ N = 0) (x : M) (n : ℕ) :
    ∀ᵐ ω ∂C.conditionedMeasure x n, ∀ k : ℕ, 0 < k → ω k ∉ Option.some '' N := by
  apply ProbabilityTheory.cond_absolutelyContinuous.ae_le
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k = 0
  · subst k
    exact ae_of_all _ fun _ h => (Nat.lt_irrefl _ h).elim
  · have hz : C.pathMeasure x {ω | ω k ∈ Option.some '' N} = 0 := by
      rw [← C.killedTransition_pow_apply x k N hN]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hN]
      apply lintegral_eq_zero_of_ae_eq_zero
      exact ae_of_all _ fun y => h.absolutelyContinuous y hnull
    have ha : ∀ᵐ ω ∂C.pathMeasure x, ω k ∉ Option.some '' N := by
      apply ae_iff.mpr
      simpa only [not_not] using hz
    exact ha.mono fun _ hω _ => hω

/-- Equality off a null set gives an exact finite-time sum identity. -/
theorem ae_path_sum_sub_of_eq_off_null (h : HypothesisH ρ C.toKilledKernel)
    {N : Set M} (hN : MeasurableSet N) (hnull : ρ N = 0)
    {f g : M → ℝ} (hfg : ∀ y ∉ N, f y = g y) (x : M) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂C.conditionedMeasure x n,
      pathBirkhoffSum f n ω - pathBirkhoffSum g n ω = f x - g x := by
  filter_upwards [C.ae_positive_time_avoids_null h hN hnull x n,
    C.ae_initial_conditionedMeasure x n] with ω hω hzero
  unfold pathBirkhoffSum birkhoffSum
  rw [← Finset.sum_sub_distrib]
  have he : ∑ j ∈ Finset.range n, (zeroExtension f (ω j) - zeroExtension g (ω j)) =
      zeroExtension f (ω 0) - zeroExtension g (ω 0) := by
    apply Finset.sum_eq_single 0
    · intro j hj hj0
      have havoid := hω j (Nat.pos_of_ne_zero hj0)
      cases he : ω j with
      | none => simp [zeroExtension]
      | some y =>
        have hy : y ∉ N := fun hy => havoid (he ▸ Set.mem_image_of_mem Option.some hy)
        simp [zeroExtension, hfg y hy]
    · intro hbad
      exact (hbad (Finset.mem_range.mpr hn)).elim
  rw [he, hzero]
  rfl

/-- A finite change on a null set preserves any centered limit on a diverging scale. -/
theorem limit_of_eq_off_null
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State)
    {N : Set M} (hN : MeasurableSet N) (hnull : ρ N = 0)
    {f g : M → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ y ∉ N, f y = g y) (A B : ℕ → ℝ)
    (hB : Tendsto B atTop atTop) {Z : Ω → ℝ}
    (hlim : TendstoInDistribution
      (fun n ω => (B n)⁻¹ * (pathBirkhoffSum g n ω - A n)) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q) :
    TendstoInDistribution
      (fun n ω => (B n)⁻¹ * (pathBirkhoffSum f n ω - A n)) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q := by
  apply tendstoInDistribution_of_varying_probability_approximation _ Q _ _ Z
    (fun n => ((measurable_pathBirkhoffSum hf n).sub_const _).const_mul _)
    (fun n => ((measurable_pathBirkhoffSum hg n).sub_const _).const_mul _) hlim
  intro ε hε
  have he := (constant_div_tendsto_zero (f x.val - g x.val) hB).abs
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    he.eventually_lt_const (by simpa using hε)] with n hn hsmall
  have hae := C.ae_path_sum_sub_of_eq_off_null h hN hnull hfg x.val hn
  have hz : {ω | ε < |(B n)⁻¹ * (pathBirkhoffSum f n ω - A n) -
      (B n)⁻¹ * (pathBirkhoffSum g n ω - A n)|}
      =ᵐ[C.conditionedMeasure x.val n] (∅ : Set (Path M)) := by
    filter_upwards [hae] with ω hω
    apply propext
    change (ε < |(B n)⁻¹ * (pathBirkhoffSum f n ω - A n) -
      (B n)⁻¹ * (pathBirkhoffSum g n ω - A n)|) ↔ False
    rw [iff_false, not_lt]
    have halg : (B n)⁻¹ * (pathBirkhoffSum f n ω - A n) -
        (B n)⁻¹ * (pathBirkhoffSum g n ω - A n) = (f x.val - g x.val) / B n := by
      rw [← mul_sub, sub_sub_sub_cancel_right, hω, div_eq_mul_inv, mul_comm]
    rw [halg]
    exact hsmall.le
  change 0 = (C.conditionedMeasure x.val n).real _
  rw [measureReal_congr hz, measureReal_empty]

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws

/-- Assign a specified finite value at the singularity. -/
def setCenterValue {M : Type*} (f : M → ℝ) (x₀ : M) (v : ℝ) : M → ℝ :=
  fun y => if y = x₀ then v else f y

theorem measurable_setCenterValue {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] {f : M → ℝ} (hf : Measurable f) (x₀ : M) (v : ℝ) :
    Measurable (setCenterValue f x₀ v) :=
  Measurable.ite (measurableSet_singleton x₀) measurable_const hf

theorem setCenterValue_ae_eq {M : Type*} [MeasurableSpace M]
    {ν : Measure M} (f : M → ℝ) {x₀ : M} (hnull : ν {x₀} = 0) (v : ℝ) :
    setCenterValue f x₀ v =ᵐ[ν] f := by
  have havoid : ∀ᵐ y ∂ν, y ≠ x₀ := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using hnull
  filter_upwards [havoid] with y hy
  exact ite_eq_right hy

/-- Changing the finite convention does not change the mean centering. -/
theorem integral_setCenterValue {M : Type*} [MeasurableSpace M]
    {ν : Measure M} (f : M → ℝ) {x₀ : M} (hnull : ν {x₀} = 0) (v : ℝ) :
    (∫ y, setCenterValue f x₀ v y ∂ν) = ∫ y, f y ∂ν :=
  integral_congr_ae (setCenterValue_ae_eq f hnull v)

/-- The signed, absolute-truncation centering at α=1 is unchanged as well. -/
theorem integral_absTrunc_setCenterValue {M : Type*} [MeasurableSpace M]
    {ν : Measure M} (f : M → ℝ) {x₀ : M} (hnull : ν {x₀} = 0) (v B : ℝ) :
    (∫ y, MultiplierReflection.absTrunc (setCenterValue f x₀ v) B y ∂ν) =
      ∫ y, MultiplierReflection.absTrunc f B y ∂ν := by
  apply integral_congr_ae
  filter_upwards [setCenterValue_ae_eq f hnull v] with y hy
  simp only [MultiplierReflection.absTrunc, Set.indicator_apply,
    Set.mem_ofPred_eq, hy]

namespace CanonicalChain
open StandingHypothesis
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Every admissible-centre limit allows any fixed finite centre value. -/
theorem limit_setCenterValue
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State)
    {x₀ : M} {dimension volumeConstant : ℝ}
    (hreg : IsRegularAt ρ x₀ dimension volumeConstant)
    {f : M → ℝ} (hf : Measurable f) (v : ℝ) (A B : ℕ → ℝ)
    (hB : Tendsto B atTop atTop) {Z : Ω → ℝ}
    (hlim : TendstoInDistribution
      (fun n ω => (B n)⁻¹ * (pathBirkhoffSum f n ω - A n)) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q) :
    TendstoInDistribution
      (fun n ω => (B n)⁻¹ * (pathBirkhoffSum (setCenterValue f x₀ v) n ω - A n)) atTop Z
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M))) Q := by
  let := h.reference_probability
  exact C.limit_of_eq_off_null Q h d x (measurableSet_singleton x₀)
    hreg.measure_singleton_eq_zero (measurable_setCenterValue hf x₀ v) hf
    (fun y hy => ite_eq_right hy) A B hB hlim

/-- The quasi-ergodic law gives the admissible centre zero mass. -/
theorem quasiErgodic_center_null (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (μ : Measure M)
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    {x₀ : M} {dimension volumeConstant : ℝ}
    (hreg : IsRegularAt ρ x₀ dimension volumeConstant) :
    (μ.withDensity d.weight) {x₀} = 0 := by
  let := h.reference_probability
  exact withDensity_absolutelyContinuous μ d.weight
    (h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft hreg.measure_singleton_eq_zero)

end CanonicalChain
end ConditionedStableLaws
