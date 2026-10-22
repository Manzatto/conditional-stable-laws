import ConditionedStableLaws.MidpointInterpolation
import ConditionedStableLaws.LpCompatibility
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Midpoint interpolation on real `L²`

A real operator on `L²` compatible with bounded realizations on `L¹` and `L∞` has norm at most `sqrt
(4 * M₀) * sqrt (4 * M₁)`. The proof reduces to real simple functions, applies the finite Hadamard
three-lines argument, and extends by density. The universal factor `4` comes from complexifying a
real bilinear form and is harmless for geometric decay.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace ConditionedStableLaws.LpMidpointInterpolation

variable {M : Type*} [MeasurableSpace M] {μ : Measure M} [IsFiniteMeasure μ]

lemma simpleFunc_comp_eq_sum_fiber (f : SimpleFunc M ℝ) (c : ℝ → ℝ) :
    (fun x => c (f x)) = fun x => ∑ a ∈ f.range, (f ⁻¹' {a}).indicator (fun _ => c a) x := by
  funext x
  classical
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro b hb hne
    simp [Ne.symm hne]
  · simp

lemma integral_simpleFunc_comp (f : SimpleFunc M ℝ) (c : ℝ → ℝ) :
    ∫ x, c (f x) ∂μ = ∑ a ∈ f.range, μ.real (f ⁻¹' {a}) * c a := by
  rw [simpleFunc_comp_eq_sum_fiber]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_indicator (f.measurableSet_fiber a)]
    simp [Measure.real]
  · intro a ha
    exact Integrable.indicator (integrable_const (c a)) (f.measurableSet_fiber a)

lemma integral_abs_simpleFunc_comp (f : SimpleFunc M ℝ) (c : ℝ → ℝ) :
    ∫ x, |c (f x)| ∂μ = ∑ a ∈ f.range, μ.real (f ⁻¹' {a}) * |c a| := by
  simpa using integral_simpleFunc_comp (μ := μ) f (fun a => |c a|)

lemma integral_sq_simpleFunc (f : SimpleFunc M ℝ) :
    ∫ x, (f x) ^ 2 ∂μ = ∑ a ∈ f.range, μ.real (f ⁻¹' {a}) * |a| ^ 2 := by
  simpa [sq_abs] using integral_simpleFunc_comp (μ := μ) f (fun a => a ^ 2)

def simpleToLp (p : ℝ≥0∞) (f : SimpleFunc M ℝ) : Lp ℝ p μ :=
  (f.memLp_of_isFiniteMeasure p μ).toLp f

lemma simpleToLp_ae (p : ℝ≥0∞) (f : SimpleFunc M ℝ) :
    (simpleToLp (μ := μ) p f : M → ℝ) =ᵐ[μ] f :=
  (f.memLp_of_isFiniteMeasure p μ).coeFn_toLp

lemma simpleToLp_toSimpleFunc {p : ℝ≥0∞} (f : Lp.simpleFunc ℝ p μ) :
    simpleToLp (μ := μ) p (Lp.simpleFunc.toSimpleFunc f) = (f : Lp ℝ p μ) := by
  unfold simpleToLp
  have h := congrArg (fun g : Lp.simpleFunc ℝ p μ => (g : Lp ℝ p μ))
    (Lp.simpleFunc.toLp_toSimpleFunc f)
  simpa only [Lp.simpleFunc.toLp_eq_toLp] using h

lemma norm_simpleToLp_one (f : SimpleFunc M ℝ) :
    ‖simpleToLp (μ := μ) 1 f‖ = ∫ x, |f x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [simpleToLp_ae (μ := μ) 1 f] with x hx
  rw [hx, Real.norm_eq_abs]

lemma norm_simpleToLp_map_one (f : SimpleFunc M ℝ) (c : ℝ → ℝ) :
    ‖simpleToLp (μ := μ) 1 (f.map c)‖ =
      ∑ a ∈ f.range, μ.real (f ⁻¹' {a}) * |c a| := by
  rw [norm_simpleToLp_one]
  change (∫ x, |c (f x)| ∂μ) = _
  exact integral_abs_simpleFunc_comp (μ := μ) f c

lemma norm_simpleToLp_top_le (f : SimpleFunc M ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B) : ‖simpleToLp (μ := μ) ∞ f‖ ≤ B := by
  have hae : ∀ᵐ x ∂μ, ‖(simpleToLp (μ := μ) ∞ f : M → ℝ) x‖ ≤ B := by
    filter_upwards [simpleToLp_ae (μ := μ) ∞ f] with x hx
    rw [hx, Real.norm_eq_abs]
    exact hB x
  simpa using (Lp.norm_le_of_ae_bound (p := (∞ : ℝ≥0∞)) hB0 hae)

lemma norm_simpleToLp_map_top_le (f : SimpleFunc M ℝ) (c : ℝ → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ a ∈ f.range, |c a| ≤ B) :
    ‖simpleToLp (μ := μ) ∞ (f.map c)‖ ≤ B := by
  apply norm_simpleToLp_top_le _ hB0
  intro x
  change |c (f x)| ≤ B
  exact hB (f x) (f.mem_range_self x)

lemma norm_simpleToLp_two_sq (f : SimpleFunc M ℝ) :
    ‖simpleToLp (μ := μ) 2 f‖ ^ 2 = ∑ a ∈ f.range, μ.real (f ⁻¹' {a}) * |a| ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  rw [integral_congr_ae]
  · exact integral_sq_simpleFunc (μ := μ) f
  · filter_upwards [simpleToLp_ae (μ := μ) 2 f] with x hx
    simp [hx]

def atom (f : SimpleFunc M ℝ) (a : ℝ) : SimpleFunc M ℝ :=
  f.map fun b => if b = a then 1 else 0

lemma atom_apply (f : SimpleFunc M ℝ) (a : ℝ) (x : M) :
    atom f a x = if f x = a then 1 else 0 := rfl

lemma simpleToLp_map_eq_sum_atoms (p : ℝ≥0∞) (f : SimpleFunc M ℝ) (c : ℝ → ℝ) :
    simpleToLp (μ := μ) p (f.map c) =
      ∑ a ∈ f.range, c a • simpleToLp (μ := μ) p (atom f a) := by
  apply Lp.ext
  have hatom : ∀ᵐ x ∂μ, ∀ a ∈ f.range,
      (simpleToLp (μ := μ) p (atom f a) : M → ℝ) x = atom f a x := by
    rw [eventually_all_finset]
    intro a ha
    exact simpleToLp_ae (μ := μ) p (atom f a)
  have hsmul : ∀ᵐ x ∂μ, ∀ a ∈ f.range,
      ((c a • simpleToLp (μ := μ) p (atom f a) : Lp ℝ p μ) : M → ℝ) x =
        c a * (simpleToLp (μ := μ) p (atom f a) : M → ℝ) x := by
    rw [eventually_all_finset]
    intro a ha
    filter_upwards [Lp.coeFn_smul (c a) (simpleToLp (μ := μ) p (atom f a))] with x hx
    simpa [Pi.smul_apply, smul_eq_mul] using hx
  filter_upwards [simpleToLp_ae (μ := μ) p (f.map c),
    Lp.coeFn_finsetSum f.range (fun a => c a • simpleToLp (μ := μ) p (atom f a)),
    hatom, hsmul] with x hleft hsum hatomx hsmulx
  rw [hleft, hsum]
  simp only [SimpleFunc.coe_map, Function.comp_apply, Finset.sum_apply]
  classical
  rw [Finset.sum_eq_single (f x)]
  · rw [hsmulx (f x) (f.mem_range_self x), hatomx (f x) (f.mem_range_self x)]
    simp [atom_apply]
  · intro b hb hne
    rw [hsmulx b hb, hatomx b hb]
    simp [atom_apply, Ne.symm hne]
  · intro hnot
    exact (hnot (f.mem_range_self x)).elim

lemma matrixBilinearReal_operator_eq
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f g : SimpleFunc M ℝ) (x y : ℝ → ℝ) :
    ConditionedStableLaws.MidpointInterpolation.matrixBilinearReal f.range g.range
      (fun b a => inner ℝ (T (simpleToLp (μ := μ) 2 (atom f a)))
        (simpleToLp (μ := μ) 2 (atom g b))) x y =
      inner ℝ (T (simpleToLp (μ := μ) 2 (f.map x)))
        (simpleToLp (μ := μ) 2 (g.map y)) := by
  rw [simpleToLp_map_eq_sum_atoms, simpleToLp_map_eq_sum_atoms]
  simp only [map_sum, map_smul, inner_sum, sum_inner, real_inner_smul_left,
    real_inner_smul_right,
    ConditionedStableLaws.MidpointInterpolation.matrixBilinearReal]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

omit [IsFiniteMeasure μ] in
lemma abs_integral_mul_le_L1_mul_bound (u : Lp ℝ 1 μ) {g : M → ℝ} {B : ℝ}
    (_hB0 : 0 ≤ B) (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ B) :
    |∫ x, u x * g x ∂μ| ≤ ‖u‖ * B := by
  calc
    |∫ x, u x * g x ∂μ| = ‖∫ x, u x * g x ∂μ‖ := rfl
    _ ≤ ∫ x, B * ‖u x‖ ∂μ := by
      apply norm_integral_le_of_norm_le ((L1.integrable_coeFn u).norm.const_mul B)
      filter_upwards [hg] with x hx
      rw [norm_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hx (norm_nonneg (u x))
    _ = B * ‖u‖ := by rw [integral_const_mul, L1.norm_eq_integral_norm]
    _ = ‖u‖ * B := mul_comm _ _

omit [IsFiniteMeasure μ] in
lemma abs_integral_mul_le_bound_mul_L1 {u : M → ℝ} (g : Lp ℝ 1 μ) {B : ℝ}
    (hB0 : 0 ≤ B) (hu : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) :
    |∫ x, u x * g x ∂μ| ≤ B * ‖g‖ := by
  rw [show (∫ x, u x * g x ∂μ) = ∫ x, g x * u x ∂μ by
    apply integral_congr_ae; filter_upwards with x; ring]
  exact (abs_integral_mul_le_L1_mul_bound g hB0 hu).trans_eq (mul_comm _ _)

open ConditionedStableLaws.Cited

lemma simple_matrix_endpoint_one
    (T₁ : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (T₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hcompat : LpCompatible T₂ T₁) {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (hT₁ : ∀ u, ‖T₁ u‖ ≤ M₀ * ‖u‖)
    (f g : SimpleFunc M ℝ) (x y : ℝ → ℝ)
    (hx : ∑ a ∈ f.range, μ.real (f ⁻¹' {a}) * |x a| ≤ 1)
    (hy : ∀ b ∈ g.range, |y b| ≤ 1) :
    |ConditionedStableLaws.MidpointInterpolation.matrixBilinearReal f.range g.range
      (fun b a => inner ℝ (T₂ (simpleToLp (μ := μ) 2 (atom f a)))
        (simpleToLp (μ := μ) 2 (atom g b))) x y| ≤ M₀ := by
  rw [matrixBilinearReal_operator_eq]
  let fx₂ := simpleToLp (μ := μ) 2 (f.map x)
  let fx₁ := simpleToLp (μ := μ) 1 (f.map x)
  let gy₂ := simpleToLp (μ := μ) 2 (g.map y)
  have hfx : (fx₂ : M → ℝ) =ᵐ[μ] fx₁ :=
    (simpleToLp_ae (μ := μ) 2 (f.map x)).trans
      (simpleToLp_ae (μ := μ) 1 (f.map x)).symm
  have hT := hcompat fx₂ fx₁ hfx
  have hgy : (gy₂ : M → ℝ) =ᵐ[μ] (g.map y : M → ℝ) :=
    simpleToLp_ae (μ := μ) 2 (g.map y)
  have heq : inner ℝ (T₂ fx₂) gy₂ = ∫ z, T₁ fx₁ z * (g.map y) z ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hT, hgy] with z hzT hzg
    simp only [Real.inner_apply, hzT, hzg]
  rw [heq]
  calc
    |∫ z, T₁ fx₁ z * (g.map y) z ∂μ| ≤ ‖T₁ fx₁‖ * 1 := by
      apply abs_integral_mul_le_L1_mul_bound _ zero_le_one
      filter_upwards with z
      rw [Real.norm_eq_abs]
      exact hy (g z) (g.mem_range_self z)
    _ ≤ (M₀ * ‖fx₁‖) * 1 :=
      mul_le_mul_of_nonneg_right (hT₁ fx₁) zero_le_one
    _ ≤ M₀ := by
      rw [mul_one]
      exact (mul_le_mul_of_nonneg_left (by
        simpa [fx₁, norm_simpleToLp_map_one] using hx) hM₀).trans_eq (mul_one M₀)

lemma simple_matrix_endpoint_top
    (T₁ : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (T₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ttop : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ)
    (hcompat₂₁ : LpCompatible T₂ T₁) (hcompat₁top : LpCompatible T₁ Ttop)
    {M₁ : ℝ} (hM₁ : 0 ≤ M₁) (hTtop : ∀ u, ‖Ttop u‖ ≤ M₁ * ‖u‖)
    (f g : SimpleFunc M ℝ) (x y : ℝ → ℝ)
    (hx : ∀ a ∈ f.range, |x a| ≤ 1)
    (hy : ∑ b ∈ g.range, μ.real (g ⁻¹' {b}) * |y b| ≤ 1) :
    |ConditionedStableLaws.MidpointInterpolation.matrixBilinearReal f.range g.range
      (fun b a => inner ℝ (T₂ (simpleToLp (μ := μ) 2 (atom f a)))
        (simpleToLp (μ := μ) 2 (atom g b))) x y| ≤ M₁ := by
  rw [matrixBilinearReal_operator_eq]
  let fx₂ := simpleToLp (μ := μ) 2 (f.map x)
  let fx₁ := simpleToLp (μ := μ) 1 (f.map x)
  let fxtop := simpleToLp (μ := μ) ∞ (f.map x)
  let gy₂ := simpleToLp (μ := μ) 2 (g.map y)
  let gy₁ := simpleToLp (μ := μ) 1 (g.map y)
  have hfx₂₁ : (fx₂ : M → ℝ) =ᵐ[μ] fx₁ :=
    (simpleToLp_ae (μ := μ) 2 (f.map x)).trans
      (simpleToLp_ae (μ := μ) 1 (f.map x)).symm
  have hfx₁top : (fx₁ : M → ℝ) =ᵐ[μ] fxtop :=
    (simpleToLp_ae (μ := μ) 1 (f.map x)).trans
      (simpleToLp_ae (μ := μ) ∞ (f.map x)).symm
  have hTout : (T₂ fx₂ : M → ℝ) =ᵐ[μ] Ttop fxtop :=
    (hcompat₂₁ fx₂ fx₁ hfx₂₁).trans
      (hcompat₁top fx₁ fxtop hfx₁top)
  have hgy₂₁ : (gy₂ : M → ℝ) =ᵐ[μ] gy₁ :=
    (simpleToLp_ae (μ := μ) 2 (g.map y)).trans
      (simpleToLp_ae (μ := μ) 1 (g.map y)).symm
  have heq : inner ℝ (T₂ fx₂) gy₂ = ∫ z, Ttop fxtop z * gy₁ z ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hTout, hgy₂₁] with z hzT hzg
    simp only [Real.inner_apply, hzT, hzg]
  rw [heq]
  have hbound : ∀ᵐ z ∂μ, ‖(Ttop fxtop : M → ℝ) z‖ ≤ ‖Ttop fxtop‖ :=
    ae_le_lpNorm_exponent_top (Lp.memLp (Ttop fxtop))
  calc
    |∫ z, Ttop fxtop z * gy₁ z ∂μ| ≤ ‖Ttop fxtop‖ * ‖gy₁‖ := by
      exact abs_integral_mul_le_bound_mul_L1 gy₁ (norm_nonneg _) hbound
    _ ≤ (M₁ * ‖fxtop‖) * ‖gy₁‖ :=
      mul_le_mul_of_nonneg_right (hTtop fxtop) (norm_nonneg _)
    _ ≤ (M₁ * 1) * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (norm_simpleToLp_map_top_le (μ := μ) f x zero_le_one hx) hM₁
      · simpa [gy₁, norm_simpleToLp_map_one] using hy
      · exact norm_nonneg _
      · positivity
    _ = M₁ := by ring

lemma matrixBilinear_cast_eq_real {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    ConditionedStableLaws.MidpointInterpolation.matrixBilinear s t A
      (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) =
      (ConditionedStableLaws.MidpointInterpolation.matrixBilinearReal s t A a b : ℝ) := by
  simp only [ConditionedStableLaws.MidpointInterpolation.matrixBilinear,
    ConditionedStableLaws.MidpointInterpolation.matrixBilinearReal]
  push_cast
  rfl

lemma simple_inner_le_of_unit
    (T₁ : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (T₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ttop : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ)
    (hcompat₂₁ : LpCompatible T₂ T₁) (hcompat₁top : LpCompatible T₁ Ttop)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT₁ : ∀ u, ‖T₁ u‖ ≤ M₀ * ‖u‖) (hTtop : ∀ u, ‖Ttop u‖ ≤ M₁ * ‖u‖)
    (f g : SimpleFunc M ℝ) (hf : ‖simpleToLp (μ := μ) 2 f‖ ≤ 1)
    (hg : ‖simpleToLp (μ := μ) 2 g‖ ≤ 1) :
    |inner ℝ (T₂ (simpleToLp (μ := μ) 2 f)) (simpleToLp (μ := μ) 2 g)| ≤
      Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁) := by
  let A : ℝ → ℝ → ℝ := fun b a =>
    inner ℝ (T₂ (simpleToLp (μ := μ) 2 (atom f a)))
      (simpleToLp (μ := μ) 2 (atom g b))
  have hfsq : ∑ a ∈ f.range, μ.real (f ⁻¹' {a}) * |a| ^ 2 ≤ 1 := by
    rw [← norm_simpleToLp_two_sq]
    nlinarith [norm_nonneg (simpleToLp (μ := μ) 2 f)]
  have hgsq : ∑ b ∈ g.range, μ.real (g ⁻¹' {b}) * |b| ^ 2 ≤ 1 := by
    rw [← norm_simpleToLp_two_sq]
    nlinarith [norm_nonneg (simpleToLp (μ := μ) 2 g)]
  have h := ConditionedStableLaws.MidpointInterpolation.finite_matrix_midpoint_interpolation_weighted_real
    f.range g.range A id id
    (fun a => μ.real (f ⁻¹' {a})) (fun b => μ.real (g ⁻¹' {b}))
    hM₀ hM₁ (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_nonneg)
    (by simpa using hfsq) (by simpa using hgsq)
    (simple_matrix_endpoint_one T₁ T₂ hcompat₂₁ hM₀ hT₁ f g)
    (simple_matrix_endpoint_top T₁ T₂ Ttop hcompat₂₁ hcompat₁top hM₁ hTtop f g)
  rw [matrixBilinear_cast_eq_real, Complex.norm_real, Real.norm_eq_abs] at h
  have hfid : f.map id = f := by ext z; rfl
  have hgid : g.map id = g := by ext z; rfl
  simpa [A, matrixBilinearReal_operator_eq, hfid, hgid] using h

lemma simpleToLp_smul (p : ℝ≥0∞) (c : ℝ) (f : SimpleFunc M ℝ) :
    simpleToLp (μ := μ) p (c • f) = c • simpleToLp (μ := μ) p f := by
  apply Lp.ext
  filter_upwards [simpleToLp_ae (μ := μ) p (c • f),
    Lp.coeFn_smul c (simpleToLp (μ := μ) p f), simpleToLp_ae (μ := μ) p f]
    with x hleft hright hf
  rw [hleft, hright, Pi.smul_apply, hf]
  rfl

lemma simple_inner_le
    (T₁ : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (T₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ttop : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ)
    (hcompat₂₁ : LpCompatible T₂ T₁) (hcompat₁top : LpCompatible T₁ Ttop)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT₁ : ∀ u, ‖T₁ u‖ ≤ M₀ * ‖u‖) (hTtop : ∀ u, ‖Ttop u‖ ≤ M₁ * ‖u‖)
    (f g : SimpleFunc M ℝ) :
    |inner ℝ (T₂ (simpleToLp (μ := μ) 2 f)) (simpleToLp (μ := μ) 2 g)| ≤
      (Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁)) *
        ‖simpleToLp (μ := μ) 2 f‖ * ‖simpleToLp (μ := μ) 2 g‖ := by
  let F := simpleToLp (μ := μ) 2 f
  let G := simpleToLp (μ := μ) 2 g
  by_cases hF : ‖F‖ = 0
  · have hF0 : F = 0 := norm_eq_zero.mp hF
    simp [F, hF0]
  by_cases hG : ‖G‖ = 0
  · have hG0 : G = 0 := norm_eq_zero.mp hG
    simp [G, hG0]
  let f' : SimpleFunc M ℝ := ‖F‖⁻¹ • f
  let g' : SimpleFunc M ℝ := ‖G‖⁻¹ • g
  have hFpos : 0 < ‖F‖ := (norm_pos_iff.mpr (norm_ne_zero_iff.mp hF))
  have hGpos : 0 < ‖G‖ := (norm_pos_iff.mpr (norm_ne_zero_iff.mp hG))
  have hf'norm : ‖simpleToLp (μ := μ) 2 f'‖ ≤ 1 := by
    dsimp [f']
    rw [simpleToLp_smul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hFpos, inv_mul_cancel₀ hFpos.ne']
  have hg'norm : ‖simpleToLp (μ := μ) 2 g'‖ ≤ 1 := by
    dsimp [g']
    rw [simpleToLp_smul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hGpos, inv_mul_cancel₀ hGpos.ne']
  have hunit := simple_inner_le_of_unit T₁ T₂ Ttop hcompat₂₁ hcompat₁top
    hM₀ hM₁ hT₁ hTtop f' g' hf'norm hg'norm
  have hscale : inner ℝ (T₂ F) G = ‖F‖ * ‖G‖ *
      inner ℝ (T₂ (simpleToLp (μ := μ) 2 f')) (simpleToLp (μ := μ) 2 g') := by
    dsimp [F, G, f', g']
    rw [simpleToLp_smul, simpleToLp_smul, map_smul,
      real_inner_smul_left, real_inner_smul_right]
    field_simp [show ‖simpleToLp (μ := μ) 2 f‖ ≠ 0 by simpa [F] using hF,
      show ‖simpleToLp (μ := μ) 2 g‖ ≠ 0 by simpa [G] using hG]
  rw [show simpleToLp (μ := μ) 2 f = F from rfl,
    show simpleToLp (μ := μ) 2 g = G from rfl, hscale, abs_mul, abs_mul,
    abs_of_pos hFpos, abs_of_pos hGpos]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hunit (mul_nonneg hFpos.le hGpos.le)

lemma lpSimple_inner_le_all
    (T₁ : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (T₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ttop : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ)
    (hcompat₂₁ : LpCompatible T₂ T₁) (hcompat₁top : LpCompatible T₁ Ttop)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT₁ : ∀ u, ‖T₁ u‖ ≤ M₀ * ‖u‖) (hTtop : ∀ u, ‖Ttop u‖ ≤ M₁ * ‖u‖)
    (f : Lp.simpleFunc ℝ 2 μ) (G : Lp ℝ 2 μ) :
    |inner ℝ (T₂ (f : Lp ℝ 2 μ)) G| ≤
      (Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁)) * ‖(f : Lp ℝ 2 μ)‖ * ‖G‖ := by
  let C := Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁)
  refine (Lp.simpleFunc.denseRange (p := (2 : ℝ≥0∞)) (μ := μ) (by norm_num)).induction_on G ?_ ?_
  · exact isClosed_le
      (continuous_abs.comp (continuous_const.inner continuous_id))
      ((continuous_const.mul continuous_norm))
  · intro g
    have h := simple_inner_le T₁ T₂ Ttop hcompat₂₁ hcompat₁top hM₀ hM₁ hT₁ hTtop
      (Lp.simpleFunc.toSimpleFunc f) (Lp.simpleFunc.toSimpleFunc g)
    simpa [C, simpleToLp_toSimpleFunc] using h

lemma lpSimple_norm_le
    (T₁ : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (T₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ttop : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ)
    (hcompat₂₁ : LpCompatible T₂ T₁) (hcompat₁top : LpCompatible T₁ Ttop)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT₁ : ∀ u, ‖T₁ u‖ ≤ M₀ * ‖u‖) (hTtop : ∀ u, ‖Ttop u‖ ≤ M₁ * ‖u‖)
    (f : Lp.simpleFunc ℝ 2 μ) :
    ‖T₂ (f : Lp ℝ 2 μ)‖ ≤
      (Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁)) * ‖(f : Lp ℝ 2 μ)‖ := by
  let F : Lp ℝ 2 μ := f
  let C := Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁)
  have h := lpSimple_inner_le_all T₁ T₂ Ttop hcompat₂₁ hcompat₁top
    hM₀ hM₁ hT₁ hTtop f (T₂ F)
  rw [real_inner_self_eq_norm_sq, abs_sq] at h
  by_cases hz : ‖T₂ F‖ = 0
  · rw [show T₂ (f : Lp ℝ 2 μ) = T₂ F from rfl, hz]
    positivity
  · have hp : 0 < ‖T₂ F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    dsimp [F] at h ⊢
    nlinarith

theorem midpoint_interpolation_norm
    (T₁ : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (T₂ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ttop : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ)
    (hcompat₂₁ : LpCompatible T₂ T₁) (hcompat₁top : LpCompatible T₁ Ttop)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT₁ : ∀ u, ‖T₁ u‖ ≤ M₀ * ‖u‖) (hTtop : ∀ u, ‖Ttop u‖ ≤ M₁ * ‖u‖)
    (F : Lp ℝ 2 μ) :
    ‖T₂ F‖ ≤ (Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁)) * ‖F‖ := by
  refine (Lp.simpleFunc.denseRange (p := (2 : ℝ≥0∞)) (μ := μ) (by norm_num)).induction_on F ?_ ?_
  · exact isClosed_le (continuous_norm.comp T₂.continuous)
      (continuous_const.mul continuous_norm)
  · intro f
    exact lpSimple_norm_le T₁ T₂ Ttop hcompat₂₁ hcompat₁top
      hM₀ hM₁ hT₁ hTtop f

end ConditionedStableLaws.LpMidpointInterpolation
