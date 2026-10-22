import ConditionedStableLaws.KernelSmallTargets
import ConditionedStableLaws.QuasiStationary
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Support

/-!
# Small targets for the eigenfunction-weighted measure

Uniform smallness of one-step transitions to sets small for the quasi-ergodic measure, with the
spectral data as hypotheses.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace ConditionedStableLaws

noncomputable section

/-- Absolute continuity of a finite measure implies continuity on sets of
vanishing reference measure, by the Radon–Nikodym representation. -/
theorem tendsto_measureReal_zero_of_absolutelyContinuous
    {Y : Type*} [MeasurableSpace Y] {μ ν : Measure Y}
    [IsFiniteMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (U : ℕ → Set Y) (hU : Tendsto (fun n => ν (U n)) atTop (𝓝 0)) :
    Tendsto (fun n => (μ (U n)).toReal) atTop (𝓝 0) := by
  have hi : Integrable (fun y => (μ.rnDeriv ν y).toReal) ν := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := ν)
        (measure_ne_top μ univ))
  simpa only [Measure.setIntegral_toReal_rnDeriv hμν, measureReal_def] using
    hi.tendsto_setIntegral_nhds_zero hU

/-- A compact L¹ family converts pointwise smallness of its set integrals
into uniform smallness. This isolates the finite-net step from the measure
used to establish pointwise convergence. -/
theorem uniform_small_sets_of_pointwise_L1
    {Y : Type*} [MeasurableSpace Y] {ρ : Measure Y}
    {F : Set (Lp ℝ 1 ρ)} (hF : IsCompact F) (U : ℕ → Set Y)
    (hpoint : ∀ f ∈ F,
      Tendsto (fun n => ∫ y in U n, f y ∂ρ) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ f ∈ F, |∫ y in U n, f y ∂ρ| < ε := by
  intro ε hε
  obtain ⟨t, htF, ht, hcover⟩ := hF.finite_cover_balls (half_pos hε)
  have hcenters : ∀ g ∈ t, ∀ᶠ n in atTop,
      |∫ y in U n, g y ∂ρ| < ε / 2 := by
    intro g hg
    exact (hpoint g (htF hg)).abs.eventually_lt_const (by simpa using half_pos hε)
  filter_upwards [(Filter.eventually_all_finite ht).2 hcenters] with n hn f hf
  obtain ⟨g, hgt, hfg⟩ := Set.mem_iUnion₂.mp (hcover hf)
  have hdist : dist f g < ε / 2 := hfg
  calc
    |∫ y in U n, f y ∂ρ|
        ≤ |(∫ y in U n, f y ∂ρ) - ∫ y in U n, g y ∂ρ|
          + |∫ y in U n, g y ∂ρ| := by
            simpa only [sub_add_cancel] using
              abs_add_le ((∫ y in U n, f y ∂ρ) - ∫ y in U n, g y ∂ρ)
                (∫ y in U n, g y ∂ρ)
    _ ≤ dist f g + |∫ y in U n, g y ∂ρ| :=
      add_le_add (abs_setIntegral_sub_le_L1_dist f g (U n)) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hdist (hn g hgt)
    _ = ε := add_halves ε

/-- Continuity in L¹ implies continuity of every set integral. -/
theorem continuous_setIntegral_of_continuous_L1
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace Y] {ρ : Measure Y}
    {κ : X → Lp ℝ 1 ρ} (hκ : Continuous κ) (A : Set Y) :
    Continuous (fun x => ∫ y in A, κ x y ∂ρ) := by
  have hLip : LipschitzWith 1 (fun f : Lp ℝ 1 ρ => ∫ y in A, f y ∂ρ) := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
      abs_setIntegral_sub_le_L1_dist f g A
  exact hLip.continuous.comp hκ

/-- A continuous transition probability vanishes on the support of an
eigenmeasure whenever the target is null for that eigenmeasure. -/
theorem kernel_null_on_support_of_eigenmeasure
    {M : Type*} [MeasurableSpace M] [TopologicalSpace M]
    (K : Kernel M M) [IsFiniteKernel K] (μ : Measure M) {rate : ℝ≥0∞}
    (heigen : K ∘ₘ μ = rate • μ) {A : Set M} (hA : MeasurableSet A)
    (hcont : Continuous (fun x => (K x A).toReal)) (hμA : μ A = 0)
    {x : M} (hx : x ∈ μ.support) : K x A = 0 := by
  have hint : ∫⁻ z, K z A ∂μ = 0 := by
    rw [← Measure.bind_apply hA K.aemeasurable, heigen]
    simp [hμA]
  have hae := (lintegral_eq_zero_iff (K.measurable_coe hA)).mp hint
  have hzero : ∀ᵐ z ∂μ, (K z A).toReal = 0 := by
    filter_upwards [hae] with z hz
    simp [hz]
  have hxs : (K x A).toReal = 0 :=
    μ.support_subset_of_isClosed (isClosed_eq hcont continuous_const) hzero hx
  exact (ENNReal.toReal_eq_zero_iff _).mp hxs |>.resolve_right (measure_ne_top (K x) A)

/-- Weighting by a function positive exactly on `S`, together with the left
and right eigenrelations, makes every transition restricted to `S`
absolutely continuous with respect to the weighted measure. -/
theorem kernel_restrict_absolutelyContinuous_weighted
    {M : Type*} [MeasurableSpace M] [TopologicalSpace M]
    (K : Kernel M M) [IsFiniteKernel K] (μ : Measure M) (η : M → ℝ≥0∞)
    (hη : Measurable η) (S : Set M) (hS : MeasurableSet S)
    (hpos : ∀ x, η x ≠ 0 ↔ x ∈ S) (hsupp : S ⊆ μ.support)
    (hcont : ∀ A, MeasurableSet A → Continuous (fun x => (K x A).toReal))
    {rate : ℝ≥0∞} (hleft : K ∘ₘ μ = rate • μ)
    (hright : ∀ x, ∫⁻ y, η y ∂K x = rate * η x) (x : M) :
    (K x).restrict S ≪ μ.withDensity η := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hnull
  rw [Measure.restrict_apply hA]
  have hμAS : μ (A ∩ S) = 0 := by
    have h := (withDensity_apply_eq_zero hη).mp hnull
    have heq : {y | η y ≠ 0} ∩ A = A ∩ S := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, hpos y, and_comm]
    rwa [heq] at h
  by_cases hx : x ∈ S
  · exact kernel_null_on_support_of_eigenmeasure K μ hleft (hA.inter hS)
      (hcont _ (hA.inter hS)) hμAS (hsupp hx)
  · have hηx : η x = 0 := by simpa only [not_not] using mt (hpos x).mp hx
    have hzero : ∫⁻ y, η y ∂K x = 0 := by rw [hright x, hηx, mul_zero]
    have hae := (lintegral_eq_zero_iff hη).mp hzero
    have hKS : K x S = 0 := by
      have heq : S = {y | η y ≠ 0} := by ext y; exact (hpos y).symm
      rw [heq]
      exact (ae_iff.mp hae)
    exact measure_mono_null inter_subset_right hKS

/-- The second small-target finite-net argument. -/
theorem uniform_small_targets_of_restricted_absolutelyContinuous
    {M Y : Type*} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [MeasurableSpace Y]
    (ρ ν : Measure Y) [SigmaFinite ν] (K : Kernel M Y) [IsFiniteKernel K]
    (κ : M → Lp ℝ 1 ρ) (hκ : Continuous κ)
    (hK : ∀ x (A : Set Y), MeasurableSet A →
      (K x A).toReal = ∫ y in A, κ x y ∂ρ)
    (S : Set Y) (hac : ∀ x, (K x).restrict S ≪ ν)
    (U : ℕ → Set Y) (hUmeas : ∀ n, MeasurableSet (U n))
    (hUS : ∀ᶠ n in atTop, U n ⊆ S)
    (hU : Tendsto (fun n => ν (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x : M, (K x (U n)).toReal < ε := by
  have hpoint : ∀ f ∈ Set.range κ,
      Tendsto (fun n => ∫ y in U n, f y ∂ρ) atTop (𝓝 0) := by
    rintro f ⟨x, rfl⟩
    have ht := tendsto_measureReal_zero_of_absolutelyContinuous (hac x) U hU
    apply ht.congr'
    filter_upwards [hUS] with n hn
    rw [Measure.restrict_apply (hUmeas n), inter_eq_left.mpr hn, hK x _ (hUmeas n)]
  intro ε hε
  filter_upwards [uniform_small_sets_of_pointwise_L1 (isCompact_range hκ) U hpoint ε hε]
    with n hn x
  rw [hK x _ (hUmeas n)]
  exact (le_abs_self _).trans_lt (hn (κ x) (mem_range_self x))

namespace StandingHypothesis

variable {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {ρ : Measure M} {K : KilledKernel M}

/-- Uniform smallness of one-step transitions to sets small for the quasi-ergodic measure, given the
eigenmeasure, eigenfunction and support properties. -/
theorem HypothesisH.uniform_small_targets_weighted
    (h : HypothesisH ρ K) (μ : Measure M) (η : M → ℝ≥0∞)
    [SigmaFinite (μ.withDensity η)] (hη : Measurable η)
    (hpos : ∀ x, η x ≠ 0 ↔ x ∈ survivingSet K.kernel)
    (hsupp : survivingSet K.kernel ⊆ μ.support)
    {rate : ℝ≥0∞} (hleft : K.kernel ∘ₘ μ = rate • μ)
    (hright : ∀ x, ∫⁻ y, η y ∂K.kernel x = rate * η x)
    (U : ℕ → Set M) (hUmeas : ∀ n, MeasurableSet (U n))
    (hUS : ∀ᶠ n in atTop, U n ⊆ survivingSet K.kernel)
    (hU : Tendsto (fun n => μ.withDensity η (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x : M, (K.kernel x (U n)).toReal < ε := by
  have hcont : ∀ A, MeasurableSet A →
      Continuous (fun x => (K.kernel x A).toReal) := by
    intro A hA
    simp_rw [h.kernel_real_eq_integral _ A hA]
    exact continuous_setIntegral_of_continuous_L1 h.continuous_density A
  exact uniform_small_targets_of_restricted_absolutelyContinuous
    ρ (μ.withDensity η) K.kernel h.density h.continuous_density
    h.kernel_real_eq_integral (survivingSet K.kernel)
    (kernel_restrict_absolutelyContinuous_weighted K.kernel μ η hη
      (survivingSet K.kernel) (measurableSet_survivingSet K.kernel)
      hpos hsupp hcont hleft hright)
    U hUmeas hUS hU

end StandingHypothesis

end
end ConditionedStableLaws
