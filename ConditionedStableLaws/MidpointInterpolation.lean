import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Basic.Real.Sign
import Mathlib.Tactic

/-!
# Finite midpoint interpolation

The finite-dimensional analytic core of the Riesz–Thorin estimate at the midpoint, via Hadamard's
three-lines theorem. The weighted real-matrix formulation at the end is tailored to the atoms of
real simple functions on finite measure spaces. Complexification costs the harmless universal factor
`4`; only geometric decay is needed, so a sharp interpolation constant is unnecessary.
-/

open Complex Set Filter
open scoped ComplexConjugate
noncomputable section

namespace ConditionedStableLaws.MidpointInterpolation

def leftDeform (a : ℝ) (z : ℂ) : ℂ :=
  if a = 0 then 0 else (Real.sign a : ℂ) * Complex.exp ((2 * (1 - z)) * (Real.log |a| : ℂ))

def rightDeform (a : ℝ) (z : ℂ) : ℂ :=
  if a = 0 then 0 else (Real.sign a : ℂ) * Complex.exp ((2 * z) * (Real.log |a| : ℂ))

lemma real_sign_mul_abs (a : ℝ) : Real.sign a * |a| = a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha]
    ring
  · simp
  · rw [Real.sign_of_pos ha, abs_of_pos ha]
    ring

lemma abs_real_sign_of_ne_zero {a : ℝ} (ha : a ≠ 0) : |Real.sign a| = 1 := by
  rcases ha.lt_or_gt with h | h
  · rw [Real.sign_of_neg h]
    simp
  · rw [Real.sign_of_pos h]
    simp

lemma leftDeform_half (a : ℝ) : leftDeform a (1 / 2 : ℂ) = a := by
  by_cases ha : a = 0
  · simp [leftDeform, ha]
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [leftDeform, ite_eq_right ha]
    have he : (2 * (1 - (1 / 2 : ℂ))) * (Real.log |a| : ℂ) = (Real.log |a| : ℂ) := by
      ring
    rw [he, ← Complex.ofReal_exp, Real.exp_log habs]
    exact_mod_cast real_sign_mul_abs a

lemma rightDeform_half (a : ℝ) : rightDeform a (1 / 2 : ℂ) = a := by
  by_cases ha : a = 0
  · simp [rightDeform, ha]
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [rightDeform, ite_eq_right ha]
    have he : (2 * (1 / 2 : ℂ)) * (Real.log |a| : ℂ) = (Real.log |a| : ℂ) := by
      ring
    rw [he, ← Complex.ofReal_exp, Real.exp_log habs]
    exact_mod_cast real_sign_mul_abs a

lemma norm_leftDeform_of_re_eq_zero {a : ℝ} {z : ℂ} (hz : z.re = 0) :
    ‖leftDeform a z‖ = |a| ^ 2 := by
  by_cases ha : a = 0
  · simp [leftDeform, ha]
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [leftDeform, ite_eq_right ha, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_real_sign_of_ne_zero ha, Complex.norm_exp]
    norm_num [mul_re, hz]
    rw [← Real.log_abs a, two_mul, Real.exp_add, Real.exp_log habs]
    simp [pow_two]

lemma norm_rightDeform_of_re_eq_one {a : ℝ} {z : ℂ} (hz : z.re = 1) :
    ‖rightDeform a z‖ = |a| ^ 2 := by
  by_cases ha : a = 0
  · simp [rightDeform, ha]
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [rightDeform, ite_eq_right ha, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_real_sign_of_ne_zero ha, Complex.norm_exp]
    norm_num [mul_re, hz]
    rw [← Real.log_abs a, two_mul, Real.exp_add, Real.exp_log habs]
    simp [pow_two]

lemma norm_leftDeform_of_re_eq_one {a : ℝ} {z : ℂ} (hz : z.re = 1) :
    ‖leftDeform a z‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [leftDeform, ha]
  · rw [leftDeform, ite_eq_right ha, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_real_sign_of_ne_zero ha, Complex.norm_exp]
    simp [mul_re, hz]

lemma norm_rightDeform_of_re_eq_zero {a : ℝ} {z : ℂ} (hz : z.re = 0) :
    ‖rightDeform a z‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [rightDeform, ha]
  · rw [rightDeform, ite_eq_right ha, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_real_sign_of_ne_zero ha, Complex.norm_exp]
    simp [mul_re, hz]

lemma differentiable_leftDeform (a : ℝ) : Differentiable ℂ (leftDeform a) := by
  unfold leftDeform
  split_ifs
  · fun_prop
  · fun_prop

lemma differentiable_rightDeform (a : ℝ) : Differentiable ℂ (rightDeform a) := by
  unfold rightDeform
  split_ifs
  · fun_prop
  · fun_prop

attribute [fun_prop] differentiable_leftDeform differentiable_rightDeform

lemma norm_leftDeform_eq (a : ℝ) (z : ℂ) :
    ‖leftDeform a z‖ = if a = 0 then 0 else Real.exp (2 * (1 - z.re) * Real.log |a|) := by
  by_cases ha : a = 0
  · simp [leftDeform, ha]
  · rw [leftDeform, ite_eq_right ha, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_real_sign_of_ne_zero ha, one_mul, Complex.norm_exp, ite_eq_right ha]
    norm_num [mul_re]

lemma norm_rightDeform_eq (a : ℝ) (z : ℂ) :
    ‖rightDeform a z‖ = if a = 0 then 0 else Real.exp (2 * z.re * Real.log |a|) := by
  by_cases ha : a = 0
  · simp [rightDeform, ha]
  · rw [rightDeform, ite_eq_right ha, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_real_sign_of_ne_zero ha, one_mul, Complex.norm_exp, ite_eq_right ha]
    norm_num [mul_re]

lemma norm_leftDeform_le_exp_abs_log {a : ℝ} {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖leftDeform a z‖ ≤ Real.exp (2 * |Real.log (|a|)|) := by
  rw [norm_leftDeform_eq]
  split_ifs with ha
  · positivity
  · apply Real.exp_le_exp.mpr
    have hx : 0 ≤ 1 - z.re := sub_nonneg.mpr hz1
    have hx1 : 1 - z.re ≤ 1 := by linarith
    by_cases hl : 0 ≤ Real.log |a|
    · rw [abs_of_nonneg hl]
      exact mul_le_mul_of_nonneg_right (by nlinarith : 2 * (1 - z.re) ≤ 2) hl
    · have hl' : Real.log |a| < 0 := lt_of_not_ge hl
      exact (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hx) hl'.le).trans
        (mul_nonneg (by norm_num) (abs_nonneg _))

lemma norm_rightDeform_le_exp_abs_log {a : ℝ} {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖rightDeform a z‖ ≤ Real.exp (2 * |Real.log (|a|)|) := by
  rw [norm_rightDeform_eq]
  split_ifs with ha
  · positivity
  · apply Real.exp_le_exp.mpr
    by_cases hl : 0 ≤ Real.log |a|
    · rw [abs_of_nonneg hl]
      exact mul_le_mul_of_nonneg_right (by nlinarith : 2 * z.re ≤ 2) hl
    · have hl' : Real.log |a| < 0 := lt_of_not_ge hl
      exact (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hz0) hl'.le).trans
        (mul_nonneg (by norm_num) (abs_nonneg _))
def exponentialPolynomial {ι : Type*} (s : Finset ι) (c : ι → ℂ) (r : ι → ℝ) : ℂ → ℂ :=
  fun z => ∑ i ∈ s, c i * Complex.exp ((r i : ℂ) * z)

lemma differentiable_exponentialPolynomial {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (r : ι → ℝ) : Differentiable ℂ (exponentialPolynomial s c r) := by
  unfold exponentialPolynomial
  fun_prop

lemma norm_exp_real_mul_le_exp_abs {r : ℝ} {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.exp ((r : ℂ) * z)‖ ≤ Real.exp |r| := by
  rw [Complex.norm_exp]
  have hre : (((r : ℂ) * z).re) = r * z.re := by simp
  rw [hre]
  apply Real.exp_le_exp.mpr
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr hz1
  · have hr' : r < 0 := lt_of_not_ge hr
    exact (mul_nonpos_of_nonpos_of_nonneg hr'.le hz0).trans (abs_nonneg r)

lemma exponentialPolynomial_bddAbove {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (r : ι → ℝ) : BddAbove ((norm ∘ exponentialPolynomial s c r) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  refine ⟨∑ i ∈ s, ‖c i‖ * Real.exp |r i|, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  simp only [Function.comp_apply, exponentialPolynomial]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  refine (norm_mul_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_exp_real_mul_le_exp_abs hz.1 hz.2) (norm_nonneg _)

lemma exponentialPolynomial_midpoint_le {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (r : ι → ℝ) {A B : ℝ}
    (hA : ∀ z : ℂ, z.re = 0 → ‖exponentialPolynomial s c r z‖ ≤ A)
    (hB : ∀ z : ℂ, z.re = 1 → ‖exponentialPolynomial s c r z‖ ≤ B) :
    ‖exponentialPolynomial s c r (1 / 2 : ℂ)‖ ≤ Real.sqrt A * Real.sqrt B := by
  have hz : (1 / 2 : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    constructor <;> norm_num
  have hd : DiffContOnCl ℂ (exponentialPolynomial s c r)
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
    (differentiable_exponentialPolynomial s c r).diffContOnCl
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (exponentialPolynomial s c r) hz hd (exponentialPolynomial_bddAbove s c r)
    (fun z hz => hA z hz) (fun z hz => hB z hz)
  norm_num at h ⊢
  simpa only [Real.sqrt_eq_rpow] using h

def matrixBilinear {ι κ : Type*} (s : Finset ι) (t : Finset κ) (A : κ → ι → ℝ)
    (x : ι → ℂ) (y : κ → ℂ) : ℂ :=
  ∑ j ∈ t, ∑ i ∈ s, (A j i : ℂ) * x i * y j

def matrixBilinearReal {ι κ : Type*} (s : Finset ι) (t : Finset κ) (A : κ → ι → ℝ)
    (x : ι → ℝ) (y : κ → ℝ) : ℝ :=
  ∑ j ∈ t, ∑ i ∈ s, A j i * x i * y j

lemma matrixBilinear_eq_parts {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (x : ι → ℂ) (y : κ → ℂ) :
    matrixBilinear s t A x y =
      (matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).re) -
        matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).im) : ℝ) +
      Complex.I * (matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).im) +
        matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).re) : ℝ) := by
  apply Complex.ext <;>
    simp [matrixBilinear, matrixBilinearReal, mul_re, mul_im,
      Finset.sum_add_distrib]

lemma sum_abs_re_le_sum_norm {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    ∑ i ∈ s, |(x i).re| ≤ ∑ i ∈ s, ‖x i‖ := by
  exact Finset.sum_le_sum fun i hi => abs_re_le_norm (x i)

lemma sum_abs_im_le_sum_norm {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    ∑ i ∈ s, |(x i).im| ≤ ∑ i ∈ s, ‖x i‖ := by
  exact Finset.sum_le_sum fun i hi => abs_im_le_norm (x i)

lemma matrixBilinear_complex_bound_of_real {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) {M : ℝ} (_hM : 0 ≤ M)
    (h : ∀ (x : ι → ℝ) (y : κ → ℝ), (∑ i ∈ s, |x i|) ≤ 1 →
      (∀ j ∈ t, |y j| ≤ 1) → |matrixBilinearReal s t A x y| ≤ M)
    (x : ι → ℂ) (y : κ → ℂ) (hx : (∑ i ∈ s, ‖x i‖) ≤ 1)
    (hy : ∀ j ∈ t, ‖y j‖ ≤ 1) : ‖matrixBilinear s t A x y‖ ≤ 4 * M := by
  have hxr : (∑ i ∈ s, |(x i).re|) ≤ 1 := (sum_abs_re_le_sum_norm s x).trans hx
  have hxi : (∑ i ∈ s, |(x i).im|) ≤ 1 := (sum_abs_im_le_sum_norm s x).trans hx
  have hyr : ∀ j ∈ t, |(y j).re| ≤ 1 := fun j hj =>
    (abs_re_le_norm (y j)).trans (hy j hj)
  have hyi : ∀ j ∈ t, |(y j).im| ≤ 1 := fun j hj =>
    (abs_im_le_norm (y j)).trans (hy j hj)
  rw [matrixBilinear_eq_parts]
  calc
    ‖((matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).re) -
          matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).im) : ℝ) : ℂ) +
        Complex.I * ((matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).im) +
          matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).re) : ℝ) : ℂ)‖
        ≤ ‖((matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).re) -
          matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).im) : ℝ) : ℂ)‖ +
          ‖Complex.I * ((matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).im) +
          matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).re) : ℝ) : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ (M + M) + (M + M) := by
      simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      apply add_le_add
      · exact (abs_sub _ _).trans (add_le_add (h _ _ hxr hyr) (h _ _ hxi hyi))
      · exact (abs_add_le _ _).trans (add_le_add (h _ _ hxr hyi) (h _ _ hxi hyr))
    _ = 4 * M := by ring

lemma matrixBilinear_transpose {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (x : ι → ℂ) (y : κ → ℂ) :
    matrixBilinear t s (fun i j => A j i) y x = matrixBilinear s t A x y := by
  simp only [matrixBilinear]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma matrixBilinearReal_transpose {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    matrixBilinearReal t s (fun i j => A j i) y x = matrixBilinearReal s t A x y := by
  simp only [matrixBilinearReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

def matrixDeformation {ι κ : Type*} (s : Finset ι) (t : Finset κ) (A : κ → ι → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) : ℂ → ℂ :=
  fun z => matrixBilinear s t A (fun i => leftDeform (a i) z) (fun j => rightDeform (b j) z)

lemma differentiable_matrixDeformation {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    Differentiable ℂ (matrixDeformation s t A a b) := by
  unfold matrixDeformation matrixBilinear
  fun_prop

lemma matrixDeformation_bddAbove {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    BddAbove ((norm ∘ matrixDeformation s t A a b) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  let C : ℝ := ∑ j ∈ t, ∑ i ∈ s,
    ‖A j i‖ * Real.exp (2 * |Real.log (|a i|)|) * Real.exp (2 * |Real.log (|b j|)|)
  refine ⟨C, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  simp only [Function.comp_apply, matrixDeformation, matrixBilinear]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  calc
    ‖(A j i : ℂ) * leftDeform (a i) z * rightDeform (b j) z‖
        ≤ ‖A j i‖ * ‖leftDeform (a i) z‖ * ‖rightDeform (b j) z‖ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact le_rfl
    _ ≤ ‖A j i‖ * Real.exp (2 * |Real.log (|a i|)|) *
          ‖rightDeform (b j) z‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_leftDeform_le_exp_abs_log hz.1 hz.2)
          (norm_nonneg _)) (norm_nonneg _)
    _ ≤ ‖A j i‖ * Real.exp (2 * |Real.log (|a i|)|) *
          Real.exp (2 * |Real.log (|b j|)|) := by
      exact mul_le_mul_of_nonneg_left (norm_rightDeform_le_exp_abs_log hz.1 hz.2)
        (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))

lemma matrixDeformation_half {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    matrixDeformation s t A a b (1 / 2 : ℂ) =
      matrixBilinear s t A (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) := by
  simp only [matrixDeformation, matrixBilinear, leftDeform_half, rightDeform_half]

lemma finite_matrix_midpoint_interpolation {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (a : ι → ℝ) (b : κ → ℝ) {M₀ M₁ : ℝ}
    (ha : ∑ i ∈ s, |a i| ^ 2 ≤ 1) (hb : ∑ j ∈ t, |b j| ^ 2 ≤ 1)
    (h₀ : ∀ (x : ι → ℂ) (y : κ → ℂ), (∑ i ∈ s, ‖x i‖) ≤ 1 →
      (∀ j ∈ t, ‖y j‖ ≤ 1) → ‖matrixBilinear s t A x y‖ ≤ M₀)
    (h₁ : ∀ (x : ι → ℂ) (y : κ → ℂ), (∀ i ∈ s, ‖x i‖ ≤ 1) →
      (∑ j ∈ t, ‖y j‖) ≤ 1 → ‖matrixBilinear s t A x y‖ ≤ M₁) :
    ‖matrixBilinear s t A (fun i => (a i : ℂ)) (fun j => (b j : ℂ))‖ ≤
      Real.sqrt M₀ * Real.sqrt M₁ := by
  rw [← matrixDeformation_half s t A a b]
  have hz : (1 / 2 : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    constructor <;> norm_num
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (matrixDeformation s t A a b) hz
    (differentiable_matrixDeformation s t A a b).diffContOnCl
    (matrixDeformation_bddAbove s t A a b)
      (a := M₀) (b := M₁) (by
        intro z hz
        apply h₀
        · simpa only [norm_leftDeform_of_re_eq_zero hz, Real.norm_eq_abs] using ha
        · intro j hj
          exact norm_rightDeform_of_re_eq_zero hz) (by
        intro z hz
        apply h₁
        · intro i hi
          exact norm_leftDeform_of_re_eq_one hz
        · simpa only [norm_rightDeform_of_re_eq_one hz, Real.norm_eq_abs] using hb)
  norm_num at h
  simpa only [Real.sqrt_eq_rpow] using h

lemma finite_matrix_midpoint_interpolation_real {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℝ) (a : ι → ℝ) (b : κ → ℝ) {M₀ M₁ : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (ha : ∑ i ∈ s, |a i| ^ 2 ≤ 1) (hb : ∑ j ∈ t, |b j| ^ 2 ≤ 1)
    (h₀ : ∀ (x : ι → ℝ) (y : κ → ℝ), (∑ i ∈ s, |x i|) ≤ 1 →
      (∀ j ∈ t, |y j| ≤ 1) → |matrixBilinearReal s t A x y| ≤ M₀)
    (h₁ : ∀ (x : ι → ℝ) (y : κ → ℝ), (∀ i ∈ s, |x i| ≤ 1) →
      (∑ j ∈ t, |y j|) ≤ 1 → |matrixBilinearReal s t A x y| ≤ M₁) :
    ‖matrixBilinear s t A (fun i => (a i : ℂ)) (fun j => (b j : ℂ))‖ ≤
      Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁) := by
  apply finite_matrix_midpoint_interpolation s t A a b ha hb
  · exact matrixBilinear_complex_bound_of_real s t A hM₀ h₀
  · intro x y hx hy
    rw [← matrixBilinear_transpose s t A x y]
    apply matrixBilinear_complex_bound_of_real t s (fun i j => A j i) hM₁
    · intro y' x' hy' hx'
      rw [matrixBilinearReal_transpose]
      exact h₁ x' y' hx' hy'
    · exact hy
    · exact hx

lemma finite_matrix_midpoint_interpolation_weighted_real {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (A : κ → ι → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (w : ι → ℝ) (v : κ → ℝ) {M₀ M₁ : ℝ}
    (_hM₀ : 0 ≤ M₀) (_hM₁ : 0 ≤ M₁)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ j ∈ t, 0 ≤ v j)
    (ha : ∑ i ∈ s, w i * |a i| ^ 2 ≤ 1) (hb : ∑ j ∈ t, v j * |b j| ^ 2 ≤ 1)
    (h₀ : ∀ (x : ι → ℝ) (y : κ → ℝ), (∑ i ∈ s, w i * |x i|) ≤ 1 →
      (∀ j ∈ t, |y j| ≤ 1) → |matrixBilinearReal s t A x y| ≤ M₀)
    (h₁ : ∀ (x : ι → ℝ) (y : κ → ℝ), (∀ i ∈ s, |x i| ≤ 1) →
      (∑ j ∈ t, v j * |y j|) ≤ 1 → |matrixBilinearReal s t A x y| ≤ M₁) :
    ‖matrixBilinear s t A (fun i => (a i : ℂ)) (fun j => (b j : ℂ))‖ ≤
      Real.sqrt (4 * M₀) * Real.sqrt (4 * M₁) := by
  rw [← matrixDeformation_half s t A a b]
  have hz : (1 / 2 : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    constructor <;> norm_num
  have h₀c : ∀ (x : ι → ℂ) (y : κ → ℂ),
      (∑ i ∈ s, w i * ‖x i‖) ≤ 1 → (∀ j ∈ t, ‖y j‖ ≤ 1) →
      ‖matrixBilinear s t A x y‖ ≤ 4 * M₀ := by
    intro x y hx hy
    have hxr : (∑ i ∈ s, w i * |(x i).re|) ≤ 1 := by
      apply (Finset.sum_le_sum fun i hi => ?_).trans hx
      exact mul_le_mul_of_nonneg_left (abs_re_le_norm (x i)) (hw i hi)
    have hxi : (∑ i ∈ s, w i * |(x i).im|) ≤ 1 := by
      apply (Finset.sum_le_sum fun i hi => ?_).trans hx
      exact mul_le_mul_of_nonneg_left (abs_im_le_norm (x i)) (hw i hi)
    have hyr : ∀ j ∈ t, |(y j).re| ≤ 1 := fun j hj =>
      (abs_re_le_norm (y j)).trans (hy j hj)
    have hyi : ∀ j ∈ t, |(y j).im| ≤ 1 := fun j hj =>
      (abs_im_le_norm (y j)).trans (hy j hj)
    rw [matrixBilinear_eq_parts]
    calc
      ‖((matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).re) -
            matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).im) : ℝ) : ℂ) +
          Complex.I * ((matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).im) +
            matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).re) : ℝ) : ℂ)‖
          ≤ ‖((matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).re) -
            matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).im) : ℝ) : ℂ)‖ +
            ‖Complex.I * ((matrixBilinearReal s t A (fun i => (x i).re) (fun j => (y j).im) +
            matrixBilinearReal s t A (fun i => (x i).im) (fun j => (y j).re) : ℝ) : ℂ)‖ :=
        norm_add_le _ _
      _ ≤ (M₀ + M₀) + (M₀ + M₀) := by
        simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        apply add_le_add
        · exact (abs_sub _ _).trans (add_le_add (h₀ _ _ hxr hyr) (h₀ _ _ hxi hyi))
        · exact (abs_add_le _ _).trans (add_le_add (h₀ _ _ hxr hyi) (h₀ _ _ hxi hyr))
      _ = 4 * M₀ := by ring
  have h₁c : ∀ (x : ι → ℂ) (y : κ → ℂ),
      (∀ i ∈ s, ‖x i‖ ≤ 1) → (∑ j ∈ t, v j * ‖y j‖) ≤ 1 →
      ‖matrixBilinear s t A x y‖ ≤ 4 * M₁ := by
    intro x y hx hy
    rw [← matrixBilinear_transpose s t A x y]
    -- Apply the preceding weighted complexification with the two index sets swapped.
    have hyr : (∑ j ∈ t, v j * |(y j).re|) ≤ 1 := by
      apply (Finset.sum_le_sum fun j hj => ?_).trans hy
      exact mul_le_mul_of_nonneg_left (abs_re_le_norm (y j)) (hv j hj)
    have hyi : (∑ j ∈ t, v j * |(y j).im|) ≤ 1 := by
      apply (Finset.sum_le_sum fun j hj => ?_).trans hy
      exact mul_le_mul_of_nonneg_left (abs_im_le_norm (y j)) (hv j hj)
    have hxr : ∀ i ∈ s, |(x i).re| ≤ 1 := fun i hi =>
      (abs_re_le_norm (x i)).trans (hx i hi)
    have hxi : ∀ i ∈ s, |(x i).im| ≤ 1 := fun i hi =>
      (abs_im_le_norm (x i)).trans (hx i hi)
    rw [matrixBilinear_eq_parts]
    calc
      ‖((matrixBilinearReal t s (fun i j => A j i) (fun j => (y j).re)
            (fun i => (x i).re) - matrixBilinearReal t s (fun i j => A j i)
            (fun j => (y j).im) (fun i => (x i).im) : ℝ) : ℂ) +
          Complex.I * ((matrixBilinearReal t s (fun i j => A j i) (fun j => (y j).re)
            (fun i => (x i).im) + matrixBilinearReal t s (fun i j => A j i)
            (fun j => (y j).im) (fun i => (x i).re) : ℝ) : ℂ)‖
          ≤ ‖((matrixBilinearReal t s (fun i j => A j i) (fun j => (y j).re)
            (fun i => (x i).re) - matrixBilinearReal t s (fun i j => A j i)
            (fun j => (y j).im) (fun i => (x i).im) : ℝ) : ℂ)‖ +
            ‖Complex.I * ((matrixBilinearReal t s (fun i j => A j i) (fun j => (y j).re)
            (fun i => (x i).im) + matrixBilinearReal t s (fun i j => A j i)
            (fun j => (y j).im) (fun i => (x i).re) : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (M₁ + M₁) + (M₁ + M₁) := by
        simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        simp_rw [matrixBilinearReal_transpose]
        apply add_le_add
        · exact (abs_sub _ _).trans (add_le_add (h₁ _ _ hxr hyr) (h₁ _ _ hxi hyi))
        · exact (abs_add_le _ _).trans (add_le_add (h₁ _ _ hxi hyr) (h₁ _ _ hxr hyi))
      _ = 4 * M₁ := by ring
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (matrixDeformation s t A a b) hz
    (differentiable_matrixDeformation s t A a b).diffContOnCl
    (matrixDeformation_bddAbove s t A a b)
      (a := 4 * M₀) (b := 4 * M₁) (by
        intro z hz
        apply h₀c
        · simpa only [norm_leftDeform_of_re_eq_zero hz, Real.norm_eq_abs] using ha
        · intro j hj
          exact norm_rightDeform_of_re_eq_zero hz) (by
        intro z hz
        apply h₁c
        · intro i hi
          exact norm_leftDeform_of_re_eq_one hz
        · simpa only [norm_rightDeform_of_re_eq_one hz, Real.norm_eq_abs] using hb)
  norm_num at h
  simpa only [Real.sqrt_eq_rpow] using h

end ConditionedStableLaws.MidpointInterpolation
