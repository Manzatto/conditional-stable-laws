import ConditionedStableLaws.HypothesisConfigurationBounds
import ConditionedStableLaws.RareTargetNormalization
import ConditionedStableLaws.LocalDensity

/-!
Singular-observable targets satisfy the geometric and one-step smallness conditions used by the
conditioned-chain configuration estimates.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace ConditionedStableLaws.CanonicalChain
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Uniform smallness supplies a concrete nonnegative envelope tending to zero; the envelope is the
supremum of one-step target probabilities. -/
theorem exists_small_target_envelope (x : M) (U : ℕ → Set M)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : M,
      (C.killedTransition y).real (U n) < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧
      (∀ n y, (C.killedTransition y).real (U n) ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) := by
  have : Nonempty M := ⟨x⟩
  have hb (n : ℕ) : BddAbove (Set.range (fun y => (C.killedTransition y).real (U n))) := by
    refine ⟨1, ?_⟩
    rintro z ⟨y,rfl⟩
    exact (ENNReal.toReal_mono ENNReal.one_ne_top
      ((measure_mono (subset_univ _)).trans (C.killedTransition_mass_le_one y))).trans_eq (by simp)
  let δ : ℕ → ℝ := fun n => ⨆ y, (C.killedTransition y).real (U n)
  have hbound (n : ℕ) (y : M) : (C.killedTransition y).real (U n) ≤ δ n := le_ciSup (hb n) y
  have hδ0 (n : ℕ) : 0 ≤ δ n := measureReal_nonneg.trans (hbound n x)
  refine ⟨δ,hδ0,hbound,?_⟩
  apply tendsto_order.mpr
  constructor
  · intro z hz
    exact Eventually.of_forall (fun n => hz.trans_le (hδ0 n))
  · intro ε hε
    filter_upwards [hsmall (ε/2) (half_pos hε)] with n hn
    exact (ciSup_le (fun y => (hn y).le)).trans_lt (half_lt_self hε)

variable [MetricSpace M] [CompactSpace M] [BorelSpace M] {ρ : Measure M}
open StandingHypothesis

omit [CompactSpace M] [BorelSpace M] in
/-- Continuity and positivity at the singularity give a uniform positive
lower bound on all sufficiently large rare targets. -/
theorem singular_targets_weight_lower
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    {x₀ : M} (hx₀ : d.weight x₀ ≠ 0) {β C₀ α level : ℝ}
    (hβ : 0 < β) (hC : 0 < C₀) (hα : 0 < α) (hl : 0 < level) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop, ∀ y ∈
      {z | level * powerScale C₀ α n < singularObservable x₀ β z}, a ≤ (d.weight y).toReal := by
  have hη : Continuous (fun y => (d.weight y).toReal) := continuous_iff_continuousAt.mpr
    (fun y => (ENNReal.continuousAt_toReal (d.weight_ne_top y)).comp hc.continuousAt)
  have hpos : 0 < (d.weight x₀).toReal := ENNReal.toReal_pos hx₀ (d.weight_ne_top _)
  let a := (d.weight x₀).toReal / 2
  have ha : 0 < a := half_pos hpos
  have hV : {y | a < (d.weight y).toReal} ∈ 𝓝 x₀ :=
    (isOpen_lt continuous_const hη).mem_nhds (half_lt_self hpos)
  refine ⟨a,ha,?_⟩
  filter_upwards [singular_targets_eventually_subset hβ hC hα hl hV] with n hn y hy
  exact (hn hy).le

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
/-- The fixed starting point eventually lies outside a diverging-threshold
rare target, including the finite-valued singularity convention. -/
theorem singular_target_excludes_start (x x₀ : M) {β C₀ α level : ℝ}
    (hC : 0 < C₀) (hα : 0 < α) (hl : 0 < level) :
    ∀ᶠ n in atTop, x ∉ {z | level * powerScale C₀ α n < singularObservable x₀ β z} := by
  have ht := (powerScale_tendsto_atTop hC hα).const_mul_atTop hl
  filter_upwards [ht.eventually_ge_atTop (singularObservable x₀ β x)] with n hn
  exact not_lt.mpr hn

/-- For singular targets, all chain-specific local inputs follow from H, the continuous normalized
eigen-data, and the scalar tail asymptotic. -/
theorem singular_target_chain_inputs
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ y, d.weight y ∂μ = 1) (x : d.State)
    {x₀ : M} (hx₀ : d.weight x₀ ≠ 0) {β C₀ α level : ℝ}
    (hβ : 0 < β) (hC : 0 < C₀) (hα : 0 < α) (hl : 0 < level)
    (htail : Tendsto (fun t : ℝ => (μ.withDensity d.weight).real
      {z | t < singularObservable x₀ β z} / (C₀*t^(-α))) atTop (𝓝 1)) :
    ∃ a : ℝ, ∃ δ : ℕ → ℝ, 0 < a ∧ (∀ n, 0 ≤ δ n) ∧
      (∀ᶠ n in atTop, ∀ y ∈ {z | level*powerScale C₀ α n < singularObservable x₀ β z},
        a ≤ (d.weight y).toReal) ∧
      (∀ n y, (C.killedTransition y).real
        {z | level*powerScale C₀ α n < singularObservable x₀ β z} ≤ δ n) ∧
      Tendsto δ atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, x.val ∉ {z | level*powerScale C₀ α n < singularObservable x₀ β z}) := by
  obtain ⟨a,ha,hlower⟩ := C.singular_targets_weight_lower d hc hx₀ hβ hC hα hl
  have hsmall := h.singular_targets_uniform_small d hc μ hleft hnorm hx₀ hβ hC hα hl htail
  obtain ⟨δ,hδ0,hδbound,hδ⟩ := C.exists_small_target_envelope x.val
    (fun n => {z | level*powerScale C₀ α n < singularObservable x₀ β z}) hsmall
  exact ⟨a,δ,ha,hδ0,hlower,hδbound,hδ,singular_target_excludes_start x.val x₀ hC hα hl⟩

/-- Admissibility gives the scalar tail ratio for the eigenfunction-weighted stationary law, by
identifying its density. -/
theorem admissible_weighted_tail
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) :
    Tendsto (fun t : ℝ => (μ.withDensity d.weight).real
      {z | t < singularObservable x₀ β z} /
        ((volumeConstant*(d.weight x₀).toReal*m x₀)*t^(-(dimension/β)))) atTop (𝓝 1) := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hη : Continuous (fun y => (d.weight y).toReal) := continuous_iff_continuousAt.mpr
    (fun y => (ENNReal.continuousAt_toReal (d.weight_ne_top y)).comp hc.continuousAt)
  have heq : μ.withDensity d.weight =
      ρ.withDensity (fun y => ENNReal.ofReal ((d.weight y).toReal*m y)) := by
    rw [hμ, ← withDensity_mul₀ hm.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      d.measurable_weight.aemeasurable]
    congr 1
    funext y
    simp only [Pi.mul_apply, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (d.weight_ne_top y)]
    exact mul_comm _ _
  rw [heq]
  exact (tail_asymptotics_withDensity hm hm0 hη (fun _ => ENNReal.toReal_nonneg) hadm
    (ENNReal.toReal_pos hx₀ (d.weight_ne_top _)) hβ).1

end ConditionedStableLaws.CanonicalChain
