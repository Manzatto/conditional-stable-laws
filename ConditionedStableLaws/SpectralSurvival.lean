import ConditionedStableLaws.KernelMixing
import ConditionedStableLaws.QProcessLimit
import ConditionedStableLaws.EigenfunctionSupport

/-!
# From the operator gap to the canonical Q-process limit

The spectral input is an operator-norm rank-one gap for the L∞ operator of the killed kernel.
Uniform normalized survival and canonical conditioned finite-horizon convergence follow from it.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Spectral data for the normalized killed operator. The eigenvector and constant-one vector are
linked to their measurable representatives. -/
structure SurvivalGapData (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel) where
  mean : Lp ℝ ∞ ρ →L[ℝ] ℝ
  eigenvector : Lp ℝ ∞ ρ
  one : Lp ℝ ∞ ρ
  one_ae : one =ᵐ[ρ] fun _ => (1 : ℝ)
  mean_one : mean one = 1
  eigenvector_ae : eigenvector =ᵐ[ρ] fun x => (d.weight x).toReal
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  decay : ℝ
  decay_nonneg : 0 ≤ decay
  decay_lt_one : decay < 1
  gap : ∀ n : ℕ, 1 ≤ n →
    ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n -
      ConditionalMixing.rankOne mean eigenvector‖ ≤ constant * decay^n

/-- The bounded map producing continuous representatives after one step. -/
def HypothesisH.smoothedOperator (h : HypothesisH ρ K) (c : ℝ) :
    Lp ℝ ∞ ρ →L[ℝ] (M →ᵇ ℝ) := by
  letI : IsProbabilityMeasure ρ := h.reference_probability
  exact c • transitionIntegralOperator ρ ⟨h.density, h.continuous_density⟩

theorem HypothesisH.smoothedOperator_apply (h : HypothesisH ρ K) (c : ℝ)
    (f : Lp ℝ ∞ ρ) (x : M) : h.smoothedOperator c f x = h.stepEvaluation c x f := by
  rw [h.stepEvaluation_apply, h.kernel_integral_eq]
  change c * transitionIntegralOperator ρ ⟨h.density, h.continuous_density⟩ f x = _
  rw [transitionIntegralOperator_apply]
  rfl

/-- The continuous representative of the eigenvector equals the nonnegative eigenfunction at every
state, by its kernel eigenrelation. -/
theorem HypothesisH.smoothed_eigenvector (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (η : Lp ℝ ∞ ρ)
    (hη : η =ᵐ[ρ] fun x => (d.weight x).toReal) (x : M) :
    h.smoothedOperator (d.rate.toReal)⁻¹ η x = (d.weight x).toReal := by
  rw [h.smoothedOperator_apply, h.stepEvaluation_apply]
  rw [integral_congr_ae ((h.absolutelyContinuous x).ae_eq hη),
    integral_toReal d.measurable_weight.aemeasurable
      (ae_of_all _ (fun y => lt_top_iff_ne_top.mpr (d.weight_ne_top y))),
    d.right_eigen x, ENNReal.toReal_mul]
  exact inv_mul_cancel_left₀ (ENNReal.toReal_ne_zero.mpr ⟨d.rate_ne_zero, d.rate_ne_top⟩) _

/-- Evaluating a smoothed power gives the normalized survival mass. -/
theorem HypothesisH.smoothed_power_one (h : HypothesisH ρ K) (c : ℝ)
    (one : Lp ℝ ∞ ρ) (hone : one =ᵐ[ρ] fun _ => (1 : ℝ)) (n : ℕ) (x : M) :
    h.smoothedOperator c (((c • h.transitionOperator)^n) one) x =
      c^(n + 1) * ((K.kernel^(n + 1)) x).real univ := by
  rw [h.smoothedOperator_apply, h.stepEvaluation_power,
    h.kernelIterate_succ_congr c n hone x, kernelIterate_normalization,
    kernelIterate_one_eq_mass]

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- ENNReal and real versions of the normalized survival mass coincide. -/
theorem normalized_survival_toReal (d : DoobTransform.EigenData K.kernel) (n : ℕ) (x : M) :
    ((d.rate⁻¹)^n * (K.kernel^n) x univ).toReal =
      (d.rate.toReal)⁻¹ ^ n * ((K.kernel^n) x).real univ := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  rfl

namespace SurvivalGapData
variable {h : HypothesisH ρ K} {d : DoobTransform.EigenData K.kernel} (s : SurvivalGapData h d)

/-- Extending a positive-time gap estimate to time zero only enlarges its
constant by the norm of the explicit zero-time error. -/
def fullConstant : ℝ := s.constant + ‖(1 : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ) -
  ConditionalMixing.rankOne s.mean s.eigenvector‖

theorem fullConstant_nonneg : 0 ≤ s.fullConstant :=
  add_nonneg s.constant_nonneg (norm_nonneg _)

theorem full_gap (n : ℕ) :
    ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n -
      ConditionalMixing.rankOne s.mean s.eigenvector‖ ≤ s.fullConstant * s.decay^n := by
  cases n with
  | zero => simp [fullConstant, s.constant_nonneg]
  | succ n =>
      exact (s.gap (n + 1) (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _))
          (pow_nonneg s.decay_nonneg _))

/-- Uniform geometric error constant after one kernel step. -/
def survivalConstant : ℝ :=
  ‖h.smoothedOperator (d.rate.toReal)⁻¹‖ * s.fullConstant * ‖s.one‖

theorem survivalConstant_nonneg : 0 ≤ s.survivalConstant := by
  exact mul_nonneg (mul_nonneg (norm_nonneg (h.smoothedOperator (d.rate.toReal)⁻¹))
    s.fullConstant_nonneg) (norm_nonneg s.one)

/-- Pointwise evaluation is justified by smoothing, uniformly on the compact state space. This is
the survival estimate, with its one-step shift. -/
theorem normalized_survival_error (n : ℕ) (x : M) :
    |((d.rate⁻¹)^(n + 1) * (K.kernel^(n + 1)) x univ).toReal - (d.weight x).toReal| ≤
      s.survivalConstant * s.decay^n := by
  let S := h.smoothedOperator (d.rate.toReal)⁻¹
  let T := (d.rate.toReal)⁻¹ • h.transitionOperator
  let P := ConditionalMixing.rankOne s.mean s.eigenvector
  have hp : P s.one = s.eigenvector := by
    simp [P, ConditionalMixing.rankOne, s.mean_one]
  have heq : S ((T^n - P) s.one) x =
      ((d.rate⁻¹)^(n + 1) * (K.kernel^(n + 1)) x univ).toReal - (d.weight x).toReal := by
    rw [sub_apply, map_sub, BoundedContinuousFunction.sub_apply,
      hp, h.smoothed_eigenvector d s.eigenvector s.eigenvector_ae,
      h.smoothed_power_one _ s.one s.one_ae, normalized_survival_toReal]
  rw [← heq, ← Real.norm_eq_abs]
  calc
    ‖S ((T^n - P) s.one) x‖ ≤ ‖S ((T^n - P) s.one)‖ :=
      BoundedContinuousFunction.norm_coe_le_norm _ _
    _ ≤ ‖S‖ * ‖(T^n - P) s.one‖ := S.le_opNorm _
    _ ≤ ‖S‖ * (‖T^n - P‖ * ‖s.one‖) :=
      mul_le_mul_of_nonneg_left ((T^n - P).le_opNorm _) (norm_nonneg S)
    _ ≤ ‖S‖ * ((s.fullConstant * s.decay^n) * ‖s.one‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (s.full_gap n) (norm_nonneg _)) (norm_nonneg S)
    _ = _ := by dsimp [survivalConstant, S]; ring


include s

/-- The eigenfunction has a continuous representative, by smoothing and the eigenrelation. -/
theorem continuous_weight_toReal : Continuous (fun x => (d.weight x).toReal) := by
  have heq : (fun x => (d.weight x).toReal) =
      h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector := by
    funext x
    exact (h.smoothed_eigenvector d s.eigenvector s.eigenvector_ae x).symm
  rw [heq]
  exact (h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector).continuous

theorem continuous_weight : Continuous d.weight := by
  have heq : d.weight = fun x => ENNReal.ofReal ((d.weight x).toReal) := by
    funext x
    exact (ENNReal.ofReal_toReal (d.weight_ne_top x)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.comp s.continuous_weight_toReal

/-- Uniform normalized-survival convergence is a consequence of the operator gap and the first-step
smoothing estimate. -/
theorem normalized_survival_tendstoUniformly :
    TendstoUniformly
      (fun (n : ℕ) (x : M) => ((d.rate⁻¹)^n * (K.kernel^n) x univ).toReal)
      (fun x => (d.weight x).toReal) atTop := by
  have ht : Tendsto (fun n : ℕ => s.survivalConstant * s.decay^(n - 1)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one s.decay_nonneg s.decay_lt_one).comp
        (tendsto_sub_atTop_nat 1))
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (tendsto_order.mp ht).2 ε hε
  filter_upwards [he, eventually_ge_atTop 1] with n hn hn1
  intro x
  have hb := s.normalized_survival_error (n - 1) x
  rw [Nat.sub_add_cancel hn1] at hb
  rw [Real.dist_eq, abs_sub_comm]
  exact hb.trans_lt hn

/-- A single explicit finite bound for all normalized survival probabilities,
including time zero. -/
def survivalBound : ℝ :=
  1 + ‖h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector‖ + s.survivalConstant

theorem survivalBound_nonneg : 0 ≤ s.survivalBound := by
  dsimp [survivalBound]
  have := s.survivalConstant_nonneg
  positivity

theorem normalized_survival_real_le (n : ℕ) (x : M) :
    ((d.rate⁻¹)^n * (K.kernel^n) x univ).toReal ≤ s.survivalBound := by
  cases n with
  | zero =>
      simp only [pow_zero, one_mul, show (1 : Kernel M M) = Kernel.id from rfl,
        Kernel.id_apply, Measure.dirac_apply_of_mem (mem_univ x), ENNReal.toReal_one]
      dsimp [survivalBound]
      have := norm_nonneg (h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector)
      have := s.survivalConstant_nonneg
      linarith
  | succ n =>
      have he := s.normalized_survival_error n x
      have hp : s.decay^n ≤ 1 := pow_le_one₀ s.decay_nonneg s.decay_lt_one.le
      have herror : ((d.rate⁻¹)^(n+1) * (K.kernel^(n+1)) x univ).toReal -
          (d.weight x).toReal ≤ s.survivalConstant :=
        (le_abs_self _).trans (he.trans (by nlinarith [s.survivalConstant_nonneg]))
      have hw : (d.weight x).toReal ≤ ‖h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector‖ := by
        rw [← h.smoothed_eigenvector d s.eigenvector s.eigenvector_ae x]
        apply (le_abs_self _).trans
        simpa only [Real.norm_eq_abs] using
          (BoundedContinuousFunction.norm_coe_le_norm
            (h.smoothedOperator (d.rate.toReal)⁻¹ s.eigenvector) x)
      dsimp [survivalBound]
      linarith

theorem normalized_survival_le (n : ℕ) (x : M) :
    (d.rate⁻¹)^n * (K.kernel^n) x univ ≤ ENNReal.ofReal s.survivalBound := by
  have := killedKernel_power_isFinite K n
  apply (ENNReal.le_ofReal_iff_toReal_le
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr d.rate_ne_zero))
      (measure_ne_top _ _)) s.survivalBound_nonneg).mpr
  exact s.normalized_survival_real_le n x

end SurvivalGapData
end
end ConditionedStableLaws.StandingHypothesis

namespace ConditionedStableLaws.CanonicalChain
noncomputable section
open StandingHypothesis QProcessLimit
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The operator-norm gap identifies the Q-process limit. -/
theorem conditioned_cylinder_tendsto_doob_of_operator_gap
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (x : d.State) (n : ℕ) (A : Set (History (Option M) n)) (hA : MeasurableSet A) :
    Tendsto (fun N : ℕ =>
      C.conditionedMeasure x.val N {ω | Preorder.frestrictLe n ω ∈ A}) atTop
      (𝓝 (C.doobPathMeasure d x {ω | coeHistory (C.cemeteryEigenData d) n
        (Preorder.frestrictLe n ω) ∈ A})) := by
  exact C.conditioned_cylinder_tendsto_doob_of_uniform d
    s.normalized_survival_tendstoUniformly (ENNReal.ofReal s.survivalBound)
    ENNReal.ofReal_ne_top s.normalized_survival_le x n A hA

/-- H2 identifies the Q-process state space with every nonescaping starting
point. Continuity needed for that identification follows from smoothing. -/
theorem surviving_mem_doob_state_of_operator_gap
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hne : ∃ y, d.weight y ≠ 0) {x : M} (hx : x ∈ survivingSet C.killedTransition) :
    x ∈ d.liveSet := by
  have heq : d.liveSet = survivingSet C.killedTransition :=
    h.eigenfunction_liveSet_eq d s.continuous_weight hne
  exact heq.symm ▸ hx

set_option maxHeartbeats 800000 in
/-- Canonical finite-horizon convergence for every nonescaping starting state, with the Doob state
constructed from H2. -/
theorem conditioned_cylinder_tendsto_doob_of_surviving
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hne : ∃ y, d.weight y ≠ 0) (x : M) (hx : x ∈ survivingSet C.killedTransition)
    (n : ℕ) (A : Set (History (Option M) n)) (hA : MeasurableSet A) :
    Tendsto (fun N : ℕ =>
      C.conditionedMeasure x N {ω | Preorder.frestrictLe n ω ∈ A}) atTop
      (𝓝 (C.doobPathMeasure d
        ⟨x, C.surviving_mem_doob_state_of_operator_gap h d s hne hx⟩
        {ω | coeHistory (C.cemeteryEigenData d) n (Preorder.frestrictLe n ω) ∈ A})) := by
  exact C.conditioned_cylinder_tendsto_doob_of_operator_gap h d s
    ⟨x, C.surviving_mem_doob_state_of_operator_gap h d s hne hx⟩ n A hA

end
end ConditionedStableLaws.CanonicalChain
