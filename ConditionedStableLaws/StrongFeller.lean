import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import ConditionedStableLaws.StandingHypothesis

/-!
# Compact integral operators from continuous L¹ densities

The analytic consequence of (H1) used in the spectral framework, via Arzelà–Ascoli: a continuous
family of bounded linear functionals on a compact state space defines a compact operator into the
bounded continuous functions. The L¹–L∞ integral pairing then gives the transition operator.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal BoundedContinuousFunction

noncomputable section

namespace ConditionedStableLaws

section DualFamilies

variable {M E : Type*} [MetricSpace M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate a continuous family of bounded linear functionals on a vector. -/
def dualFamilyLinear (H : M →ᵇ (E →L[ℝ] ℝ)) : E →ₗ[ℝ] (M →ᵇ ℝ) where
  toFun v := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => H x v, H.continuous.clm_apply continuous_const⟩
  map_add' v w := by ext x; simp
  map_smul' c v := by ext x; simp

@[simp]
theorem dualFamilyLinear_apply (H : M →ᵇ (E →L[ℝ] ℝ)) (v : E) (x : M) :
    dualFamilyLinear H v x = H x v := rfl

theorem dualFamilyLinear_bound (H : M →ᵇ (E →L[ℝ] ℝ)) (v : E) :
    ‖dualFamilyLinear H v‖ ≤ ‖H‖ * ‖v‖ := by
  apply (BoundedContinuousFunction.norm_le (f := dualFamilyLinear H v)
    (C := ‖H‖ * ‖v‖) (by positivity)).mpr
  intro x
  exact ((H x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (H.norm_coe_le_norm x) (norm_nonneg v))

/-- The bounded linear operator associated with a continuous dual family. -/
def dualFamilyOperator (H : M →ᵇ (E →L[ℝ] ℝ)) : E →L[ℝ] (M →ᵇ ℝ) :=
  (dualFamilyLinear H).mkContinuous ‖H‖ (dualFamilyLinear_bound H)

@[simp]
theorem dualFamilyOperator_apply (H : M →ᵇ (E →L[ℝ] ℝ)) (v : E) (x : M) :
    dualFamilyOperator H v x = H x v := rfl

/-- The image of the unit ball has the modulus of continuity of the dual family. -/
theorem dualFamilyOperator_equicontinuous (H : M →ᵇ (E →L[ℝ] ℝ)) :
    Equicontinuous (fun f : dualFamilyOperator H '' Metric.closedBall (0 : E) 1 =>
      fun x : M => f.val x) := by
  intro x₀
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (H.continuous.continuousAt : ContinuousAt H x₀) ε hε
  refine ⟨δ, hδ, fun x hx f => ?_⟩
  obtain ⟨v, hv, hfv⟩ := f.property
  have hvnorm : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  change dist (f.val x₀) (f.val x) < ε
  rw [← hfv, dualFamilyOperator_apply, dualFamilyOperator_apply, dist_eq_norm]
  calc
    ‖H x₀ v - H x v‖ = ‖(H x₀ - H x) v‖ := by rw [sub_apply]
    _ ≤ ‖H x₀ - H x‖ * ‖v‖ := (H x₀ - H x).le_opNorm v
    _ ≤ ‖H x₀ - H x‖ := by nlinarith [norm_nonneg (H x₀ - H x)]
    _ < ε := by simpa only [dist_eq_norm, norm_sub_rev] using hcont hx

/-- Arzelà–Ascoli gives compactness of the operator. -/
theorem dualFamilyOperator_isCompact (H : M →ᵇ (E →L[ℝ] ℝ)) :
    IsCompactOperator (dualFamilyOperator H) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (dualFamilyOperator H).toLinearMap (show (0 : ℝ) < 1 by norm_num)).mpr
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-‖H‖) ‖H‖) isCompact_Icc
  · intro f x hf
    obtain ⟨v, hv, rfl⟩ := hf
    have hvnorm : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    have hb : ‖H x v‖ ≤ ‖H‖ := by
      calc
        ‖H x v‖ ≤ ‖H x‖ * ‖v‖ := (H x).le_opNorm v
        _ ≤ ‖H‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (H.norm_coe_le_norm x) (norm_nonneg v)
        _ ≤ ‖H‖ := by nlinarith [norm_nonneg H]
    change -‖H‖ ≤ H x v ∧ H x v ≤ ‖H‖
    exact abs_le.mp hb
  · exact dualFamilyOperator_equicontinuous H

end DualFamilies

section IntegralOperators

variable {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] (ρ : Measure M) [IsFiniteMeasure ρ]

/-- The L¹–L∞ integral pairing, continuous in both normed arguments. -/
def integralPairing : Lp ℝ 1 ρ →L[ℝ] Lp ℝ ∞ ρ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing ρ 1 ∞

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] [IsFiniteMeasure ρ] in
theorem integralPairing_apply (g : Lp ℝ 1 ρ) (f : Lp ℝ ∞ ρ) :
    integralPairing ρ g f = ∫ y, g y * f y ∂ρ := by
  exact (ContinuousLinearMap.mul ℝ ℝ).lpPairing_eq_integral g f

/-- An L¹-continuous density family induces an operator-norm-continuous dual family. -/
def densityDualFamily (κ : C(M, Lp ℝ 1 ρ)) : M →ᵇ (Lp ℝ ∞ ρ →L[ℝ] ℝ) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => integralPairing ρ (κ x), (integralPairing ρ).continuous.comp κ.continuous⟩

/-- The integral operator from L∞ equivalence classes to continuous representatives. -/
def transitionIntegralOperator (κ : C(M, Lp ℝ 1 ρ)) :
    Lp ℝ ∞ ρ →L[ℝ] (M →ᵇ ℝ) :=
  dualFamilyOperator (densityDualFamily ρ κ)

omit [BorelSpace M] [IsFiniteMeasure ρ] in
theorem transitionIntegralOperator_apply (κ : C(M, Lp ℝ 1 ρ))
    (f : Lp ℝ ∞ ρ) (x : M) :
    transitionIntegralOperator ρ κ f x = ∫ y, κ x y * f y ∂ρ := by
  exact integralPairing_apply ρ (κ x) f

omit [BorelSpace M] [IsFiniteMeasure ρ] in
/-- Strong Feller property from (H1): every essentially bounded input has a
continuous integral image on the full state space. -/
theorem continuous_transitionIntegral (κ : C(M, Lp ℝ 1 ρ)) (f : Lp ℝ ∞ ρ) :
    Continuous (fun x => ∫ y, κ x y * f y ∂ρ) := by
  simpa only [← transitionIntegralOperator_apply] using
    (transitionIntegralOperator ρ κ f).continuous

omit [BorelSpace M] [IsFiniteMeasure ρ] in
/-- The integral operator is compact with values in the supremum-norm space of continuous functions,
by the dual-family Arzelà–Ascoli argument. -/
theorem transitionIntegralOperator_isCompact (κ : C(M, Lp ℝ 1 ρ)) :
    IsCompactOperator (transitionIntegralOperator ρ κ) :=
  dualFamilyOperator_isCompact (densityDualFamily ρ κ)

/-- The killed integral operator acting on L∞ equivalence classes. -/
def transitionLInfinityOperator (κ : C(M, Lp ℝ 1 ρ)) :
    Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ :=
  (BoundedContinuousFunction.toLp ∞ ρ ℝ).comp (transitionIntegralOperator ρ κ)

/-- The L∞ operator has the displayed continuous integral as a representative. -/
theorem transitionLInfinityOperator_ae (κ : C(M, Lp ℝ 1 ρ)) (f : Lp ℝ ∞ ρ) :
    transitionLInfinityOperator ρ κ f =ᵐ[ρ] fun x => ∫ y, κ x y * f y ∂ρ := by
  simpa only [transitionLInfinityOperator, ContinuousLinearMap.comp_apply,
    ← transitionIntegralOperator_apply] using
    BoundedContinuousFunction.coeFn_toLp ∞ ρ ℝ (transitionIntegralOperator ρ κ f)

/-- Compactness on L∞ follows by composing the compact continuous-image operator
with the bounded map taking continuous functions to their L∞ classes. -/
theorem transitionLInfinityOperator_isCompact (κ : C(M, Lp ℝ 1 ρ)) :
    IsCompactOperator (transitionLInfinityOperator ρ κ) := by
  exact (transitionIntegralOperator_isCompact ρ κ).clm_comp
    (BoundedContinuousFunction.toLp ∞ ρ ℝ)

end IntegralOperators

namespace StandingHypothesis

variable {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {ρ : Measure M} {K : KilledKernel M}

/-- The setwise density identity in (H1) identifies the transition measure. -/
theorem HypothesisH.kernel_eq_withDensity (h : HypothesisH ρ K) (x : M) :
    K.kernel x = ρ.withDensity (fun y => ENNReal.ofReal (h.density x y)) := by
  ext A hA
  rw [h.kernel_eq_integral x A hA, withDensity_apply _ hA]
  exact ofReal_integral_eq_lintegral_ofReal
    ((memLp_one_iff_integrable.mp (Lp.memLp (h.density x))).restrict)
    (ae_restrict_of_ae (h.density_nonneg x))

/-- The constructed integral operator integrates against the killed kernel. -/
theorem HypothesisH.kernel_integral_eq (h : HypothesisH ρ K) (x : M) (f : M → ℝ) :
    ∫ y, f y ∂K.kernel x = ∫ y, h.density x y * f y ∂ρ := by
  rw [h.kernel_eq_withDensity x,
    integral_withDensity_eq_integral_toReal_smul₀
      (Lp.aestronglyMeasurable (h.density x)).aemeasurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [h.density_nonneg x] with y hy
  rw [ENNReal.toReal_ofReal hy, smul_eq_mul]

/-- The killed transition operator on L∞, constructed from (H1). -/
def HypothesisH.transitionOperator (h : HypothesisH ρ K) :
    Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := by
  letI : IsProbabilityMeasure ρ := h.reference_probability
  exact transitionLInfinityOperator ρ ⟨h.density, h.continuous_density⟩

/-- The representative of the constructed operator is the killed-kernel integral. -/
theorem HypothesisH.transitionOperator_ae (h : HypothesisH ρ K) (f : Lp ℝ ∞ ρ) :
    h.transitionOperator f =ᵐ[ρ] fun x => ∫ y, f y ∂K.kernel x := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hrep := transitionLInfinityOperator_ae ρ ⟨h.density, h.continuous_density⟩ f
  simpa only [HypothesisH.transitionOperator, h.kernel_integral_eq,
    ContinuousMap.coe_mk] using hrep

/-- Strong Feller property of the killed kernel. -/
theorem HypothesisH.strong_feller (h : HypothesisH ρ K) (f : Lp ℝ ∞ ρ) :
    Continuous (fun x => ∫ y, f y ∂K.kernel x) := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  simp_rw [h.kernel_integral_eq]
  exact continuous_transitionIntegral ρ ⟨h.density, h.continuous_density⟩ f

/-- Compactness of the killed transition operator, from (H1). -/
theorem HypothesisH.transitionOperator_isCompact (h : HypothesisH ρ K) :
    IsCompactOperator h.transitionOperator := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  exact transitionLInfinityOperator_isCompact ρ ⟨h.density, h.continuous_density⟩

/-- Positivity of the pointwise representative follows from the nonnegative density. -/
theorem HypothesisH.kernel_integral_nonneg (h : HypothesisH ρ K) (f : Lp ℝ ∞ ρ)
    (hf : ∀ᵐ y ∂ρ, 0 ≤ f y) (x : M) : 0 ≤ ∫ y, f y ∂K.kernel x := by
  rw [h.kernel_integral_eq]
  apply integral_nonneg_of_ae
  filter_upwards [h.density_nonneg x, hf] with y hy hf_y
  exact mul_nonneg hy hf_y

/-- The constructed bounded linear transition operator is positive on L∞ classes. -/
theorem HypothesisH.transitionOperator_nonneg (h : HypothesisH ρ K) (f : Lp ℝ ∞ ρ)
    (hf : ∀ᵐ y ∂ρ, 0 ≤ f y) : ∀ᵐ x ∂ρ, 0 ≤ h.transitionOperator f x := by
  filter_upwards [h.transitionOperator_ae f] with x hx
  rw [hx]
  exact h.kernel_integral_nonneg f hf x

end StandingHypothesis

end ConditionedStableLaws
