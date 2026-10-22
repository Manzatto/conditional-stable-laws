import ConditionedStableLaws.SmallJumpMoment
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Scaling, absolute truncation, and reflection for the multiplier remark

Multiplication by a nonzero constant scales the normalizer by its absolute
value and the limit by its sign. Absolute-value truncation commutes with this
operation, so the same statement applies to the centering at exponent one.
Centered Gaussian laws are invariant under the resulting reflection.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section
namespace ConditionedStableLaws.MultiplierReflection

/-- Truncation by the absolute value, as required for signed observables. -/
def absTrunc {M : Type*} (f : M → ℝ) (B : ℝ) : M → ℝ :=
  {x | |f x| ≤ B}.indicator f

theorem absTrunc_const_mul {M : Type*} (f : M → ℝ) (B : ℝ)
    {c : ℝ} (hc : c ≠ 0) :
    absTrunc (fun x => c * f x) (|c| * B) = fun x => c * absTrunc f B x := by
  funext x
  have hpos : 0 < |c| := abs_pos.mpr hc
  have heq : |c * f x| ≤ |c| * B ↔ |f x| ≤ B := by
    rw [abs_mul, mul_le_mul_iff_right₀ hpos]
  simp only [absTrunc, Set.indicator_apply, Set.mem_ofPred_eq, heq]
  split <;> simp

theorem integral_absTrunc_const_mul {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (f : M → ℝ) (B : ℝ) {c : ℝ} (hc : c ≠ 0) :
    (∫ x, absTrunc (fun y => c * f y) (|c| * B) x ∂μ) =
      c * ∫ x, absTrunc f B x ∂μ := by
  rw [absTrunc_const_mul f B hc, integral_const_mul]

theorem absTrunc_eq_trunc_of_nonneg {M : Type*} [MeasurableSpace M]
    {f : M → ℝ} (hf : ∀ x, 0 ≤ f x) (B : ℝ) :
    absTrunc f B = SmallJumpMoment.trunc f B := by
  simp only [absTrunc, SmallJumpMoment.trunc, abs_of_nonneg (hf _)]

theorem normalized_const_mul (B A S c : ℝ) :
    (|c| * B)⁻¹ * (c * S - c * A) =
      (c / |c|) * (B⁻¹ * (S - A)) := by
  rw [mul_inv_rev]
  ring

theorem normalized_path_const_mul {M : Type*} [MeasurableSpace M]
    (f : M → ℝ) (n : ℕ) (ω : CanonicalChain.Path M) (B A c : ℝ) :
    (|c| * B)⁻¹ * (pathBirkhoffSum (fun x => c * f x) n ω - c * A) =
      (c / |c|) * (B⁻¹ * (pathBirkhoffSum f n ω - A)) := by
  rw [SmallJumpMoment.pathBirkhoffSum_const_mul]
  exact normalized_const_mul B A _ c

/-- Constant multiplication transfers a limit with arbitrary deterministic
centering and normalization, under probability laws that may vary with `n`. -/
theorem normalized_path_const_mul_tendsto
    {M Ω : Type*} [MeasurableSpace M] [MeasurableSpace Ω]
    {P : ℕ → Measure (CanonicalChain.Path M)} [∀ n, IsProbabilityMeasure (P n)]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {f : M → ℝ} {A B : ℕ → ℝ} {Z : Ω → ℝ}
    (h : TendstoInDistribution
      (fun n ω => (B n)⁻¹ * (pathBirkhoffSum f n ω - A n)) atTop Z P Q)
    (c : ℝ) :
    TendstoInDistribution
      (fun n ω => (|c| * B n)⁻¹ *
        (pathBirkhoffSum (fun x => c * f x) n ω - c * A n))
      atTop (fun ω => (c / |c|) * Z ω) P Q := by
  have ht := h.continuous_comp (continuous_const.mul continuous_id :
    Continuous (fun z : ℝ => (c / |c|) * z))
  apply ht.congr
  · intro n
    exact ae_of_all _ fun ω => (normalized_path_const_mul f n ω (B n) (A n) c).symm
  · exact ae_of_all _ fun _ => rfl

/-- A limit `c Z` on the scale `B` gives the limit `(c/|c|) Z` on the scale `|c| B`, with the same
observable and centering. -/
theorem rescale_normalizer_tendsto
    {M Ω : Type*} [MeasurableSpace M] [MeasurableSpace Ω]
    {P : ℕ → Measure (CanonicalChain.Path M)} [∀ n, IsProbabilityMeasure (P n)]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {f : M → ℝ} {A B : ℕ → ℝ} {Z : Ω → ℝ} (c : ℝ)
    (h : TendstoInDistribution
      (fun n ω => (B n)⁻¹ * (pathBirkhoffSum f n ω - A n)) atTop
      (fun ω => c * Z ω) P Q) :
    TendstoInDistribution
      (fun n ω => (|c| * B n)⁻¹ * (pathBirkhoffSum f n ω - A n)) atTop
      (fun ω => (c / |c|) * Z ω) P Q := by
  have ht := h.continuous_comp (continuous_const.mul continuous_id :
    Continuous (fun z : ℝ => |c|⁻¹ * z))
  apply ht.congr
  · intro n
    apply ae_of_all
    intro ω
    change |c|⁻¹ * ((B n)⁻¹ * (pathBirkhoffSum f n ω - A n)) = _
    rw [mul_inv_rev]
    ring
  · apply ae_of_all
    intro ω
    change |c|⁻¹ * (c * Z ω) = _
    ring

theorem sign_eq_one {c : ℝ} (hc : 0 < c) : c / |c| = 1 := by
  rw [abs_of_pos hc, div_self hc.ne']

theorem sign_eq_neg_one {c : ℝ} (hc : c < 0) : c / |c| = -1 := by
  rw [abs_of_neg hc, div_neg, div_self hc.ne]

/-- Reflection does not change a centered Gaussian law. -/
theorem gaussian_map_sign (v : ℝ≥0) {c : ℝ} (hc : c ≠ 0) :
    (gaussianReal 0 v).map (fun x : ℝ => (c / |c|) * x) = gaussianReal 0 v := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · simp only [sign_eq_neg_one hneg, neg_one_mul]
    simpa using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := v))
  · simp only [sign_eq_one hpos, one_mul]
    exact Measure.map_id

end ConditionedStableLaws.MultiplierReflection
