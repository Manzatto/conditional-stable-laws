import ConditionedStableLaws.FiniteCountRemark
import ConditionedStableLaws.ConservativeCase
import Mathlib.Probability.Distributions.Uniform

/-!
# A chain satisfying H with dependent finite empirical counts

The refresh chain draws a fresh state from the reference probability measure at each positive time.
It satisfies H, including the cyclic partition condition. A three-state uniform instance gives
dependent counts for two disjoint targets at horizon two.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
noncomputable section
namespace ConditionedStableLaws.FiniteCountExample
open StandingHypothesis CanonicalChain

section Refresh
variable {M : Type*} [MeasurableSpace M] (ρ : Measure M) [IsProbabilityMeasure ρ]

/-- The cemetery is absorbing; every live state refreshes with law ρ. -/
def refreshChain : CanonicalChain M := by
  classical
  refine ⟨Kernel.piecewise measurableSet_cemetery
    (Kernel.const _ (Measure.dirac none)) (Kernel.const _ (ρ.map Option.some)), ?_, ?_⟩
  · refine ⟨fun z => ⟨?_⟩⟩
    rw [Kernel.piecewise_apply']
    split
    · simp
    · rw [Kernel.const_apply, Measure.map_apply measurable_some_state MeasurableSet.univ]
      simp
  · simp [Kernel.piecewise_apply]

@[simp] theorem refreshChain_killed (x : M) : (refreshChain ρ).killedTransition x = ρ := by
  classical
  ext A hA
  rw [CanonicalChain.killedTransition_apply _ _ _ hA]
  simp only [refreshChain, Kernel.piecewise_apply', mem_singleton_iff, Option.some_ne_none,
    ite_false, Kernel.const_apply]
  rw [Measure.map_apply measurable_some_state (measurableEmbedding_some_state.measurableSet_image' hA)]
  exact congrArg ρ (Set.preimage_image_eq _ (Option.some_injective M))

@[simp] theorem refreshChain_conservative (x : M) : (refreshChain ρ).killedTransition x univ = 1 := by
  rw [refreshChain_killed, measure_univ]

/-- The reference probability is the stationary (and hence quasi-stationary)
measure of the conservative refresh chain. -/
theorem refresh_stationary : (refreshChain ρ).killedTransition ∘ₘ ρ = ρ := by
  have he : (refreshChain ρ).killedTransition = Kernel.const M ρ := by
    ext x A hA
    rw [refreshChain_killed, Kernel.const_apply]
  rw [he, Measure.comp_eq_comp_const_apply, Kernel.const_comp', Kernel.const_apply]

theorem refreshChain_surviving : survivingSet (refreshChain ρ).killedTransition = univ := by
  ext x
  rw [mem_survivingSet_iff]
  simp only [mem_univ, iff_true]
  intro n _
  rw [kernel_pow_univ_of_conservative _ (refreshChain_conservative ρ)]
  exact zero_lt_one

/-- Explicit normalized eigenfunction data for the refresh chain. -/
def refreshEigenData : DoobTransform.EigenData (refreshChain ρ).killedTransition where
  rate := 1
  rate_ne_zero := one_ne_zero
  rate_ne_top := ENNReal.one_ne_top
  weight := fun _ => 1
  measurable_weight := measurable_const
  weight_ne_top := fun _ => ENNReal.one_ne_top
  right_eigen := fun x => by simp

/-- Every state is live for the explicit refresh eigenfunction. -/
def refreshState (x : M) : (refreshEigenData ρ).State := ⟨x, one_ne_zero⟩

/-- The left eigenmeasure identity. -/
theorem refresh_left_eigenmeasure :
    (refreshChain ρ).killedTransition ∘ₘ ρ = (refreshEigenData ρ).rate • ρ := by
  rw [refresh_stationary]
  exact (one_smul ℝ≥0∞ ρ).symm

variable [MetricSpace M] [CompactSpace M] [BorelSpace M] [ρ.IsOpenPosMeasure]

/-- The refresh chain satisfies every clause of H, including aperiodicity. -/
def refreshChain_hypothesisH : HypothesisH ρ (refreshChain ρ).toKilledKernel := by
  let oneLp : Lp ℝ 1 ρ := (memLp_const (1 : ℝ)).toLp (fun _ : M => (1 : ℝ))
  have hone : oneLp =ᵐ[ρ] fun _ : M => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
  have hS : survivingSet (refreshChain ρ).toKilledKernel.kernel = univ :=
    refreshChain_surviving ρ
  refine {
    reference_probability := inferInstance
    reference_fullSupport := inferInstance
    density := fun _ => oneLp
    density_nonneg := fun _ => hone.mono fun _ h => by rw [h]; exact zero_le_one
    kernel_eq_integral := ?_
    continuous_density := continuous_const
    surviving_mass_pos := ?_
    irreducible := ?_
    aperiodic := ?_
  }
  · intro x A hA
    change (refreshChain ρ).killedTransition x A = _
    rw [refreshChain_killed, integral_congr_ae (ae_restrict_of_ae hone), integral_const,
      smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
    exact (ENNReal.ofReal_toReal (measure_ne_top ρ A)).symm
  · change 0 < ρ (survivingSet (refreshChain ρ).killedTransition)
    rw [refreshChain_surviving, measure_univ]
    exact zero_lt_one
  · intro x _ A hA hne
    obtain ⟨U, hU, rfl⟩ := hA
    refine ⟨1, le_refl 1, ?_⟩
    change 0 < ((refreshChain ρ).killedTransition ^ 1) x _
    rw [pow_one, refreshChain_killed, hS, univ_inter]
    rw [hS, univ_inter] at hne
    exact hU.measure_pos ρ hne
  · intro k hk parts _hmeas hne hdis hunion hcycle
    have hsome : ∃ i, ρ (parts i) ≠ 0 := by
      by_contra hh
      push Not at hh
      have hz := measure_iUnion_null hh
      rw [hunion, hS, measure_univ] at hz
      exact one_ne_zero hz
    obtain ⟨i, hi⟩ := hsome
    have hfull (x : M) : x ∈ parts (cyclicNext hk i) := by
      apply hcycle i
      constructor
      · rw [hS]
        exact mem_univ _
      · change 0 < (refreshChain ρ).killedTransition x (parts i)
        rw [refreshChain_killed]
        exact pos_iff_ne_zero.mpr hi
    have hjeq (j : Fin k) : j = cyclicNext hk i := by
      by_contra hj
      obtain ⟨y, hy⟩ := hne j
      exact Set.disjoint_left.mp (hdis hj) hy (hfull y)
    have : Subsingleton (Fin k) := ⟨fun a b => (hjeq a).trans (hjeq b).symm⟩
    have hcard := Fintype.card_le_one_iff_subsingleton.mpr this
    simp only [Fintype.card_fin] at hcard
    omega

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] [ρ.IsOpenPosMeasure] in
/-- The time-one coordinate in the conditioned law has law ρ. -/
theorem refresh_time_one_probability (x : M) (n : ℕ) (A : Set M) (hA : MeasurableSet A) :
    ((refreshChain ρ).liveConditionedProbabilityMeasure (refreshEigenData ρ) (refreshState ρ x) n :
      Measure (Path M)) {ω | ω 1 ∈ Option.some '' A} = ρ A := by
  change (refreshChain ρ).conditionedMeasure x n _ = _
  rw [CanonicalChain.conditionedMeasure_eq_of_conservative _ (refreshChain_conservative ρ)]
  rw [← CanonicalChain.killedTransition_pow_apply _ x 1 A hA, pow_one, refreshChain_killed]

omit [ρ.IsOpenPosMeasure] in
/-- Two disjoint targets avoiding the initial state have dependent horizon-two
counts whenever both have positive reference probability. -/
theorem refresh_two_counts_dependent (x : M) {U V : Set M}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hd : Disjoint U V)
    (hxU : x ∉ U) (hxV : x ∉ V) (hpU : ρ U ≠ 0) (hpV : ρ V ≠ 0) :
    ¬ IndepFun
      (fun ω : Path M => (visitTimes (fun i : Fin 2 => ω i.val) (Option.some '' U)).card)
      (fun ω : Path M => (visitTimes (fun i : Fin 2 => ω i.val) (Option.some '' V)).card)
      ((refreshChain ρ).liveConditionedProbabilityMeasure (refreshEigenData ρ) (refreshState ρ x) 2 :
        Measure (Path M)) := by
  apply CanonicalChain.two_visit_counts_not_independent (refreshChain ρ) (refreshEigenData ρ)
    (refreshState ρ x) 2 hd hxU hxV
  · rwa [refresh_time_one_probability ρ x 2 U hU]
  · rwa [refresh_time_one_probability ρ x 2 V hV]

end Refresh
end ConditionedStableLaws.FiniteCountExample
