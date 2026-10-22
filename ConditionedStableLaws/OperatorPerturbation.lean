import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# Analytic resolvents and rank-one reduction for operator perturbations

The inverse is constructed from an exponential power bound, and the normalized perturbed eigenvector
equation is reduced to a scalar equation.
-/

open Filter Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 800000

namespace ConditionedStableLaws.OperatorPerturbation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- Exponential decay of positive powers suffices for the Neumann series, even when the norm of the
operator itself exceeds one. -/
theorem summable_powers [CompleteSpace E] (R : E →L[𝕜] E) {C r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hR : ∀ n : ℕ, 1 ≤ n → ‖R ^ n‖ ≤ C * r ^ n) : Summable (fun n : ℕ => R ^ n) := by
  apply (summable_nat_add_iff 1).mp
  apply ((summable_geometric_of_lt_one hr hr1).mul_left (C * r)).of_norm_bounded
  intro n
  simpa only [pow_succ, mul_assoc, mul_comm r, mul_left_comm r] using hR (n + 1) (by omega)

/-- The inverse of `1-R` built from its norm-convergent power series. -/
def neumannUnit (R : E →L[𝕜] E) (hs : Summable (fun n : ℕ => R ^ n)) : (E →L[𝕜] E)ˣ where
  val := 1 - R
  inv := ∑' n : ℕ, R ^ n
  val_inv := hs.one_sub_mul_tsum_pow
  inv_val := hs.tsum_pow_mul_one_sub

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
theorem inverse_one_sub_eq_tsum (R : E →L[𝕜] E) (hs : Summable (fun n : ℕ => R ^ n)) :
    Ring.inverse (1 - R) = ∑' n : ℕ, R ^ n := by
  exact Ring.inverse_unit (neumannUnit R hs)

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- The exact inverse bound used on the centered subspace in the CLT proof. -/
theorem norm_inverse_one_sub_le [CompleteSpace E] (R : E →L[𝕜] E) {C r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hR : ∀ n : ℕ, 1 ≤ n → ‖R ^ n‖ ≤ C * r ^ n) :
    ‖Ring.inverse (1 - R)‖ ≤ 1 + C * r / (1 - r) := by
  have hs := summable_powers R hr hr1 hR
  have hg := (summable_geometric_of_lt_one hr hr1).mul_left (C * r)
  have hb : ∀ n : ℕ, ‖R ^ (n + 1)‖ ≤ C * r * r ^ n := by
    intro n
    simpa only [pow_succ, mul_assoc, mul_comm r, mul_left_comm r] using hR (n + 1) (by omega)
  rw [inverse_one_sub_eq_tsum R hs, hs.tsum_eq_zero_add, pow_zero]
  calc
    ‖(1 : E →L[𝕜] E) + ∑' n : ℕ, R ^ (n + 1)‖ ≤
        ‖(1 : E →L[𝕜] E)‖ + ‖∑' n : ℕ, R ^ (n + 1)‖ := norm_add_le _ _
    _ ≤ 1 + ∑' n : ℕ, C * r * r ^ n := by
      gcongr
      · exact ContinuousLinearMap.norm_id_le
      · exact (norm_tsum_le_tsum_norm (hg.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
          (Summable.tsum_le_tsum hb (hg.of_nonneg_of_le (fun _ => norm_nonneg _) hb) hg)
    _ = 1 + C * r / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1, div_eq_mul_inv]

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- A Neumann inverse solves the centered resolvent equation. -/
theorem inverse_one_sub_apply (R : E →L[𝕜] E)
    (hs : Summable (fun n : ℕ => R ^ n)) (v : E) :
    (1 - R) ((∑' n : ℕ, R ^ n) v) = v := by
  have h := congrArg (fun A : E →L[𝕜] E => A v) hs.one_sub_mul_tsum_pow
  exact h

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- Inversion is analytic at the inverse constructed above. -/
theorem analyticAt_inverse_one_sub [CompleteSpace E] (R : E →L[𝕜] E)
    (hs : Summable (fun n : ℕ => R ^ n)) :
    AnalyticAt 𝕜 Ring.inverse (1 - R) :=
  _root_.analyticAt_inverse (neumannUnit R hs)

/-- The fixed normalized rank-one projection. -/
def projection (μ : E →L[𝕜] 𝕜) (η : E) : E →L[𝕜] E := μ.smulRight η

def complement (μ : E →L[𝕜] 𝕜) (η : E) : E →L[𝕜] E := 1 - projection μ η

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem projection_apply (μ : E →L[𝕜] 𝕜) (η v : E) :
    projection μ η v = μ v • η := rfl

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem complement_apply (μ : E →L[𝕜] 𝕜) (η v : E) :
    complement μ η v = v - μ v • η := rfl

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
theorem functional_complement (μ : E →L[𝕜] 𝕜) (η : E) (hμη : μ η = 1) (v : E) :
    μ (complement μ η v) = 0 := by simp [hμη]

/-- The operator denominator in the exact rank-one Schur reduction. -/
def denominator (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (z : 𝕜) (Δ : E →L[𝕜] E) : E →L[𝕜] E := z • 1 - R - complement μ η * Δ

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem denominator_base (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E) :
    denominator R μ η 1 0 = 1 - R := by simp [denominator]

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- The resolvent depends analytically on both spectral parameter and
operator perturbation near the unperturbed point. -/
theorem analyticAt_resolvent [CompleteSpace E] (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) :
    AnalyticAt 𝕜 (fun p : 𝕜 × (E →L[𝕜] E) => Ring.inverse (denominator R μ η p.1 p.2)) (1, 0) := by
  have ha : AnalyticAt 𝕜 (fun p : 𝕜 × (E →L[𝕜] E) => denominator R μ η p.1 p.2) (1, 0) := by
    have hf : AnalyticAt 𝕜 (fun p : 𝕜 × (E →L[𝕜] E) => p.1) (1, 0) :=
      (ContinuousLinearMap.fst 𝕜 𝕜 (E →L[𝕜] E)).analyticAt (1, 0)
    have hg : AnalyticAt 𝕜 (fun p : 𝕜 × (E →L[𝕜] E) => p.2) (1, 0) :=
      (ContinuousLinearMap.snd 𝕜 𝕜 (E →L[𝕜] E)).analyticAt (1, 0)
    exact ((hf.smul analyticAt_const).sub analyticAt_const).sub (analyticAt_const.mul hg)
  exact (analyticAt_inverse_one_sub R hs).comp_of_eq ha (denominator_base R μ η)

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- The denominator is invertible throughout a neighborhood. -/
theorem eventually_isUnit_denominator [CompleteSpace E] (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) :
    ∀ᶠ p : 𝕜 × (E →L[𝕜] E) in 𝓝 (1, 0), IsUnit (denominator R μ η p.1 p.2) := by
  have hc : Continuous (fun p : 𝕜 × (E →L[𝕜] E) => denominator R μ η p.1 p.2) := by
    exact ((continuous_fst.smul continuous_const).sub continuous_const).sub
      (continuous_const.mul continuous_snd)
  have hu : {A : E →L[𝕜] E | IsUnit A} ∈ 𝓝 (denominator R μ η 1 0) := by
    rw [denominator_base]
    exact Units.isOpen.mem_nhds (neumannUnit R hs).isUnit
  exact (hc.continuousAt (x := (1, 0))).preimage_mem_nhds (t := {A | IsUnit A}) hu

/-- Explicit complementary component of a normalized candidate eigenvector. -/
def correction (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (z : 𝕜) (Δ : E →L[𝕜] E) : E :=
  (Ring.inverse (denominator R μ η z Δ)) (complement μ η (Δ η))

/-- The remaining eigenvalue equation is scalar. -/
def scalarEquation (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (z : 𝕜) (Δ : E →L[𝕜] E) : 𝕜 := z - 1 - μ (Δ (η + correction R μ η z Δ))

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
theorem correction_equation (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (z : 𝕜) (Δ : E →L[𝕜] E) (hu : IsUnit (denominator R μ η z Δ)) :
    denominator R μ η z Δ (correction R μ η z Δ) = complement μ η (Δ η) := by
  exact congrArg (fun A : E →L[𝕜] E => A (complement μ η (Δ η)))
    (Ring.mul_inverse_cancel _ hu)

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- The resolvent correction lies in the kernel of the left eigenfunctional. -/
theorem functional_correction (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hμη : μ η = 1) (hμR : ∀ v, μ (R v) = 0)
    (z : 𝕜) (hz : z ≠ 0) (Δ : E →L[𝕜] E)
    (hu : IsUnit (denominator R μ η z Δ)) : μ (correction R μ η z Δ) = 0 := by
  have h := congrArg μ (correction_equation R μ η z Δ hu)
  simp only [denominator, sub_apply, smul_apply,
    one_apply_eq_self, mul_apply_eq_comp, map_sub, map_smul,
    hμR, functional_complement μ η hμη, sub_zero, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hz

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- Solving the scalar Schur equation constructs a normalized eigenvector of the perturbed bounded
linear operator. -/
theorem eigenvector_of_scalarEquation (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hμη : μ η = 1) (hμR : ∀ v, μ (R v) = 0) (hRη : R η = 0)
    (z : 𝕜) (hz : z ≠ 0) (Δ : E →L[𝕜] E)
    (hu : IsUnit (denominator R μ η z Δ)) (hroot : scalarEquation R μ η z Δ = 0) :
    μ (η + correction R μ η z Δ) = 1 ∧
      (projection μ η + R + Δ) (η + correction R μ η z Δ) =
        z • (η + correction R μ η z Δ) := by
  have hμh := functional_correction R μ η hμη hμR z hz Δ hu
  have h := correction_equation R μ η z Δ hu
  unfold scalarEquation at hroot
  generalize hv : correction R μ η z Δ = v at hμh h hroot ⊢
  constructor
  · simp [hμη, hμh]
  · simp only [denominator, sub_apply, smul_apply,
      one_apply_eq_self, mul_apply_eq_comp, complement_apply] at h
    have hz' : z = 1 + μ (Δ η) + μ (Δ v) := by
      simp only [map_add] at hroot
      linear_combination hroot
    simp only [add_apply, projection_apply, map_add, hRη, hμη, hμh,
      add_zero, one_smul, smul_add]
    rw [hz'] at h ⊢
    linear_combination (norm := module) -h

end ConditionedStableLaws.OperatorPerturbation
