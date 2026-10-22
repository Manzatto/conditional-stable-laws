import ConditionedStableLaws.Cited.Interpolation
import ConditionedStableLaws.CompactSpectral
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Kernel integral operators on `L¹(μ)`, `L²(μ)`, and `L∞(μ)` for a left eigenmeasure

Let `K` be a finite kernel and `μ` a finite measure with `K ∘ₘ μ = c • μ`. The kernel integral `f ↦
(x ↦ ∫ f dK(x))` need not respect `μ`-a.e. equality pointwise, since `K(x,·)` need not be absolutely
continuous with respect to `μ`. It does so `μ`-almost everywhere: a `μ`-null set is `K(x,·)`-null
for `μ`-a.e. `x`. Hence the kernel integral induces bounded operators on `L¹(μ)`, `L²(μ)`, and
`L∞(μ)`. On `L²`, the bound follows from the integral Cauchy–Schwarz inequality. The endpoint
operators form a compatible pair in the sense of interpolation theory.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace ConditionedStableLaws.KernelLp

noncomputable section

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} {μ : Measure M} {c : ℝ≥0∞}

/-- The kernel integral of a real function. -/
def kint (K : Kernel M M) (f : M → ℝ) (x : M) : ℝ := ∫ y, f y ∂K x

theorem ae_ae (hK : K ∘ₘ μ = c • μ) {p : M → Prop} (h : ∀ᵐ y ∂μ, p y) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂K x, p y :=
  Measure.ae_ae_of_ae_comp (by rw [hK]; exact Measure.ae_smul_measure h c)

/-- `μ`-a.e. equal functions have `μ`-a.e. equal kernel integrals. -/
theorem kint_congr (hK : K ∘ₘ μ = c • μ) {f g : M → ℝ} (hfg : f =ᵐ[μ] g) :
    kint K f =ᵐ[μ] kint K g := by
  filter_upwards [ae_ae hK hfg] with x hx
  exact integral_congr_ae hx

theorem stronglyMeasurable_kint {f : M → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (kint K f) :=
  hf.integral_kernel

/-- Integration of a nonnegative function against `K ∘ₘ μ`. -/
theorem lintegral_lintegral_kernel (hK : K ∘ₘ μ = c • μ) {g : M → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, ∫⁻ y, g y ∂K x ∂μ = c * ∫⁻ y, g y ∂μ := by
  rw [← Measure.lintegral_bind K.aemeasurable hg.aemeasurable]
  change ∫⁻ y, g y ∂(K ∘ₘ μ) = _
  rw [hK, lintegral_smul_measure]
  rfl

theorem lintegral_enorm_kint_le (hK : K ∘ₘ μ = c • μ) {f : M → ℝ}
    (hf : StronglyMeasurable f) :
    ∫⁻ x, ‖kint K f x‖ₑ ∂μ ≤ c * ∫⁻ y, ‖f y‖ₑ ∂μ := by
  rw [← lintegral_lintegral_kernel hK hf.measurable.enorm]
  exact lintegral_mono fun x => enorm_integral_le_lintegral_enorm _

theorem ae_integrable_kernel (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) {f : M → ℝ}
    (hf : StronglyMeasurable f) (hfi : Integrable f μ) :
    ∀ᵐ x ∂μ, Integrable f (K x) := by
  have hfin : ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂K x ∂μ ≠ ∞ := by
    rw [lintegral_lintegral_kernel hK hf.measurable.enorm]
    exact ENNReal.mul_ne_top hc hfi.2.ne
  filter_upwards [ae_lt_top (hf.measurable.enorm.lintegral_kernel) hfin] with x hx
  exact ⟨hf.aestronglyMeasurable, hx⟩

variable [IsFiniteKernel K]

theorem ae_integrable_kernel_of_bound (hK : K ∘ₘ μ = c • μ) {f : M → ℝ}
    (hf : StronglyMeasurable f) {B : ℝ} (hB : ∀ᵐ y ∂μ, ‖f y‖ ≤ B) :
    ∀ᵐ x ∂μ, Integrable f (K x) := by
  filter_upwards [ae_ae hK hB] with x hx
  exact Integrable.of_bound hf.aestronglyMeasurable B hx

/-- A uniform bound on the kernel masses. -/
def massBound (K : Kernel M M) [IsFiniteKernel K] : ℝ := K.bound.toReal

theorem massBound_nonneg : 0 ≤ massBound K := ENNReal.toReal_nonneg

theorem measureReal_univ_le_massBound (x : M) : (K x).real univ ≤ massBound K :=
  ENNReal.toReal_mono K.bound_ne_top (K.measure_le_bound x univ)

theorem ae_norm_kint_le (hK : K ∘ₘ μ = c • μ) {f : M → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ y ∂μ, ‖f y‖ ≤ B) :
    ∀ᵐ x ∂μ, ‖kint K f x‖ ≤ B * massBound K := by
  filter_upwards [ae_ae hK hB] with x hx
  exact (norm_integral_le_of_norm_le_const hx).trans
    (mul_le_mul_of_nonneg_left (measureReal_univ_le_massBound x) hB0)

/-! ## The operator on `L¹(μ)` -/

variable [IsFiniteMeasure μ]

omit [IsFiniteKernel K] [IsFiniteMeasure μ] in
theorem memLp_one_kint (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) (f : Lp ℝ 1 μ) :
    MemLp (kint K f) 1 μ := by
  rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm
    (stronglyMeasurable_kint (Lp.stronglyMeasurable f)).aestronglyMeasurable]
  refine (lintegral_enorm_kint_le hK (Lp.stronglyMeasurable f)).trans_lt ?_
  rw [← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  exact ENNReal.mul_lt_top hc.lt_top (Lp.memLp f)

omit [IsFiniteKernel K] [IsFiniteMeasure μ] in
theorem kint_add_ae {f g : M → ℝ}
    (hf : ∀ᵐ x ∂μ, Integrable f (K x)) (hg : ∀ᵐ x ∂μ, Integrable g (K x)) :
    kint K (f + g) =ᵐ[μ] kint K f + kint K g := by
  filter_upwards [hf, hg] with x hfx hgx
  exact integral_add hfx hgx

omit [IsFiniteKernel K] in
theorem kint_smul (r : ℝ) (f : M → ℝ) : kint K (r • f) = r • kint K f := by
  funext x
  exact integral_smul r f

/-- The kernel operator on `L¹(μ)`. -/
def opL1 (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_one_kint hK hc f).toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        have hi (u : Lp ℝ 1 μ) := ae_integrable_kernel hK hc (Lp.stronglyMeasurable u)
          (L1.integrable_coeFn u)
        exact (kint_congr hK (Lp.coeFn_add f g)).trans (kint_add_ae (hi f) (hi g))
      map_smul' := by
        intro r f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        rw [← kint_smul]
        exact kint_congr hK (Lp.coeFn_smul r f) }
    c.toReal (by
      intro f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
      rw [Lp.norm_def, ← ENNReal.toReal_mul]
      apply ENNReal.toReal_mono (ENNReal.mul_ne_top hc (Lp.memLp f).ne)
      rw [eLpNorm_one_eq_lintegral_enorm
          (stronglyMeasurable_kint (Lp.stronglyMeasurable f)).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
      exact lintegral_enorm_kint_le hK (Lp.stronglyMeasurable f))

omit [IsFiniteKernel K] [IsFiniteMeasure μ] in
theorem opL1_ae (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) (f : Lp ℝ 1 μ) :
    opL1 hK hc f =ᵐ[μ] kint K f :=
  (memLp_one_kint hK hc f).coeFn_toLp

omit [IsFiniteKernel K] [IsFiniteMeasure μ] in
theorem norm_opL1_le (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) : ‖opL1 hK hc‖ ≤ c.toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

omit [IsFiniteKernel K] [IsFiniteMeasure μ] in
/-- `∫ (∫ f dK(x)) dμ(x) = c ∫ f dμ` for a left eigenmeasure. -/
theorem integral_kint (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) {f : M → ℝ}
    (hfi : Integrable f μ) : ∫ x, kint K f x ∂μ = c.toReal * ∫ y, f y ∂μ := by
  have hfic : Integrable f (K ∘ₘ μ) := by
    rw [hK]
    exact hfi.smul_measure hc
  have hi : (∫ y, f y ∂(K ∘ₘ μ)) = ∫ x, ∫ y, f y ∂K x ∂μ := by
    rw [Measure.comp_eq_comp_const_apply] at hfic ⊢
    exact Kernel.integral_comp hfic
  change (∫ x, ∫ y, f y ∂K x ∂μ) = _
  rw [← hi, hK, integral_smul_measure, smul_eq_mul]

/-! ## The operator on `L²(μ)` -/

/-- Integral Cauchy--Schwarz for a finite measure, in the squared form used for
kernel operators. -/
theorem integral_sq_le_measure_mul_integral_sq (ν : Measure M) [IsFiniteMeasure ν]
    {f : M → ℝ} (hf : MemLp f 2 ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ν.real univ * ∫ x, f x ^ 2 ∂ν := by
  have hi : ‖∫ x, f x ∂ν‖ ≤ ∫ x, ‖f x‖ ∂ν := norm_integral_le_integral_norm f
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) ν := by norm_num; exact hf
  have hh := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f)
    (g := fun _ : M => (1 : ℝ)) (p := 2) (q := 2) Real.HolderConjugate.two_two hf'
      (memLp_const 1)
  simp only [norm_one, mul_one, integral_const, smul_eq_mul] at hh
  norm_num at hh
  have hsq0 : 0 ≤ ∫ x, f x ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have hmass0 : 0 ≤ ν.real univ := measureReal_nonneg
  rw [show ‖∫ x, f x ∂ν‖ = |∫ x, f x ∂ν| by rfl] at hi
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have hsqrt : Real.sqrt (∫ x, f x ^ 2 ∂ν) * Real.sqrt (ν.real univ) =
      Real.sqrt (ν.real univ * ∫ x, f x ^ 2 ∂ν) := by
    rw [Real.sqrt_mul hmass0, mul_comm]
  rw [hsqrt] at hh
  have habs : |∫ x, f x ∂ν| ≤ Real.sqrt (ν.real univ * ∫ x, f x ^ 2 ∂ν) := hi.trans hh
  have hsquare := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).2 habs
  simpa only [sq_abs, Real.sq_sqrt (mul_nonneg hmass0 hsq0)] using hsquare

omit [IsFiniteMeasure μ] in
/-- The kernel integral of an `L²(μ)` function again belongs to `L²(μ)` when
`μ` is a left eigenmeasure of the kernel. -/
theorem memLp_two_kint (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) (f : Lp ℝ 2 μ) :
    MemLp (kint K f) 2 μ := by
  have hsq : Integrable (fun y => (f y) ^ 2) μ := (Lp.memLp f).integrable_sq
  have hsq1 : MemLp (fun y => (f y) ^ 2) 1 μ := memLp_one_iff_integrable.mpr hsq
  let g : Lp ℝ 1 μ := hsq1.toLp _
  have hg : Integrable ((opL1 hK hc g : Lp ℝ 1 μ) : M → ℝ) μ := L1.integrable_coeFn _
  have hkg : ((opL1 hK hc g : Lp ℝ 1 μ) : M → ℝ) =ᵐ[μ]
      kint K (fun y => (f y) ^ 2) :=
    (opL1_ae hK hc g).trans (kint_congr hK hsq1.coeFn_toLp)
  have hk_sq : Integrable (kint K (fun y => (f y) ^ 2)) μ := hg.congr hkg
  have hbound : ∀ᵐ x ∂μ, (kint K f x) ^ 2 ≤
      massBound K * kint K (fun y => (f y) ^ 2) x := by
    have hi := ae_integrable_kernel hK hc ((Lp.stronglyMeasurable f).pow 2) hsq
    filter_upwards [hi] with x hfx
    have hfx2 : MemLp (f : M → ℝ) 2 (K x) :=
      (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable f).aestronglyMeasurable).2 hfx
    exact (integral_sq_le_measure_mul_integral_sq (K x) hfx2).trans
      (mul_le_mul_of_nonneg_right (measureReal_univ_le_massBound x)
        (integral_nonneg fun y => sq_nonneg (f y)))
  rw [memLp_two_iff_integrable_sq
    (stronglyMeasurable_kint (Lp.stronglyMeasurable f)).aestronglyMeasurable]
  exact (hk_sq.const_mul (massBound K)).mono_nonneg
    ((stronglyMeasurable_kint (Lp.stronglyMeasurable f)).pow 2).aestronglyMeasurable
    (ae_of_all _ fun x => sq_nonneg _) hbound

omit [IsFiniteMeasure μ] in
theorem integral_sq_kint_le (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞)
    (f : Lp ℝ 2 μ) :
    ∫ x, (kint K f x) ^ 2 ∂μ ≤
      massBound K * c.toReal * ∫ y, (f y) ^ 2 ∂μ := by
  have hsq : Integrable (fun y => (f y) ^ 2) μ := (Lp.memLp f).integrable_sq
  have hsq1 : MemLp (fun y => (f y) ^ 2) 1 μ := memLp_one_iff_integrable.mpr hsq
  let g : Lp ℝ 1 μ := hsq1.toLp _
  have hg : Integrable ((opL1 hK hc g : Lp ℝ 1 μ) : M → ℝ) μ := L1.integrable_coeFn _
  have hkg : ((opL1 hK hc g : Lp ℝ 1 μ) : M → ℝ) =ᵐ[μ]
      kint K (fun y => (f y) ^ 2) :=
    (opL1_ae hK hc g).trans (kint_congr hK hsq1.coeFn_toLp)
  have hk_sq : Integrable (kint K (fun y => (f y) ^ 2)) μ := hg.congr hkg
  have hbound : ∀ᵐ x ∂μ, (kint K f x) ^ 2 ≤
      massBound K * kint K (fun y => (f y) ^ 2) x := by
    have hi := ae_integrable_kernel hK hc ((Lp.stronglyMeasurable f).pow 2) hsq
    filter_upwards [hi] with x hfx
    have hfx2 : MemLp (f : M → ℝ) 2 (K x) :=
      (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable f).aestronglyMeasurable).2 hfx
    exact (integral_sq_le_measure_mul_integral_sq (K x) hfx2).trans
      (mul_le_mul_of_nonneg_right (measureReal_univ_le_massBound x)
        (integral_nonneg fun y => sq_nonneg (f y)))
  calc
    ∫ x, (kint K f x) ^ 2 ∂μ ≤
        ∫ x, massBound K * kint K (fun y => (f y) ^ 2) x ∂μ :=
      integral_mono_ae (memLp_two_kint hK hc f).integrable_sq
        (hk_sq.const_mul _) hbound
    _ = massBound K * c.toReal * ∫ y, (f y) ^ 2 ∂μ := by
      rw [integral_const_mul, integral_kint hK hc hsq]
      ring

omit [IsFiniteKernel K] [IsFiniteMeasure μ] in
theorem norm_toLp_two_sq {f : M → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

omit [IsFiniteMeasure μ] in
theorem norm_kint_toLp_le (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞)
    (f : Lp ℝ 2 μ) :
    ‖(memLp_two_kint hK hc f).toLp (kint K f)‖ ≤
      Real.sqrt (massBound K * c.toReal) * ‖f‖ := by
  have hbc : 0 ≤ massBound K * c.toReal :=
    mul_nonneg massBound_nonneg ENNReal.toReal_nonneg
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
  rw [norm_toLp_two_sq]
  calc
    ∫ x, (kint K f x) ^ 2 ∂μ ≤
        massBound K * c.toReal * ∫ y, (f y) ^ 2 ∂μ :=
      integral_sq_kint_le hK hc f
    _ = (Real.sqrt (massBound K * c.toReal) * ‖f‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hbc, ← norm_toLp_two_sq (Lp.memLp f), Lp.toLp_coeFn]

/-- The kernel operator on `L²(μ)`, constructed directly from the kernel. -/
def opL2 (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_two_kint hK hc f).toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        have hi (u : Lp ℝ 2 μ) := ae_integrable_kernel hK hc (Lp.stronglyMeasurable u)
          ((Lp.memLp u).integrable (by norm_num))
        exact (kint_congr hK (Lp.coeFn_add f g)).trans (kint_add_ae (hi f) (hi g))
      map_smul' := by
        intro r f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        rw [← kint_smul]
        exact kint_congr hK (Lp.coeFn_smul r f) }
    (Real.sqrt (massBound K * c.toReal)) (norm_kint_toLp_le hK hc)

theorem opL2_ae (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) (f : Lp ℝ 2 μ) :
    opL2 hK hc f =ᵐ[μ] kint K f :=
  (memLp_two_kint hK hc f).coeFn_toLp

theorem norm_opL2_le (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) :
    ‖opL2 hK hc‖ ≤ Real.sqrt (massBound K * c.toReal) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

/-! ## The operator on `L∞(μ)` -/

omit [IsFiniteMeasure μ] in
theorem memLp_top_kint (hK : K ∘ₘ μ = c • μ) (f : Lp ℝ ∞ μ) :
    MemLp (kint K f) ∞ μ :=
  memLp_top_of_bound (stronglyMeasurable_kint (Lp.stronglyMeasurable f)).aestronglyMeasurable
    _ (ae_norm_kint_le hK (norm_nonneg f) (StandingHypothesis.lp_infinity_ae_norm_le f))

/-- The kernel operator on `L∞(μ)`. -/
def opLinf (hK : K ∘ₘ μ = c • μ) : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_top_kint hK f).toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        have hi (u : Lp ℝ ∞ μ) := ae_integrable_kernel_of_bound hK (Lp.stronglyMeasurable u)
          (StandingHypothesis.lp_infinity_ae_norm_le u)
        exact (kint_congr hK (Lp.coeFn_add f g)).trans (kint_add_ae (hi f) (hi g))
      map_smul' := by
        intro r f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        rw [← kint_smul]
        exact kint_congr hK (Lp.coeFn_smul r f) }
    (massBound K) (by
      intro f
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_comm]
      refine (Lp.norm_le_of_ae_bound (f := (memLp_top_kint hK f).toLp (kint K f))
        (C := ‖f‖ * massBound K) (mul_nonneg (norm_nonneg f) massBound_nonneg) ?_).trans_eq
        (by simp)
      filter_upwards [MemLp.coeFn_toLp (memLp_top_kint hK f),
        ae_norm_kint_le hK (norm_nonneg f) (StandingHypothesis.lp_infinity_ae_norm_le f)] with x hx hb
      rw [hx]
      exact hb)

theorem opLinf_ae (hK : K ∘ₘ μ = c • μ) (f : Lp ℝ ∞ μ) :
    opLinf hK f =ᵐ[μ] kint K f :=
  (memLp_top_kint hK f).coeFn_toLp

theorem norm_opLinf_le (hK : K ∘ₘ μ = c • μ) : ‖opLinf hK‖ ≤ massBound K :=
  LinearMap.mkContinuous_norm_le _ massBound_nonneg _

/-- The `L¹` and `L∞` realizations are the same operator on `L¹ + L∞`. -/
theorem opL1_opLinf_compatible (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) :
    Cited.LpCompatible (opL1 hK hc) (opLinf hK) := by
  intro f g hfg
  exact (opL1_ae hK hc f).trans ((kint_congr hK hfg).trans (opLinf_ae hK g).symm)


/-! ## Integral identities and mean functionals -/

omit [IsFiniteKernel K] in
theorem integrable_of_Linf (f : Lp ℝ ∞ μ) : Integrable (f : M → ℝ) μ :=
  (Lp.memLp f).integrable le_top

/-- Integration against `μ` on `L¹(μ)`. -/
def meanL1 : Lp ℝ 1 μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        rw [integral_congr_ae (Lp.coeFn_add f g)]
        exact integral_add (L1.integrable_coeFn f) (L1.integrable_coeFn g)
      map_smul' := by
        intro r f
        rw [integral_congr_ae (Lp.coeFn_smul r f), RingHom.id_apply]
        exact integral_smul r _ }
    1 (by
      intro f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [L1.norm_eq_integral_norm]
      exact norm_integral_le_integral_norm _)

omit [IsFiniteKernel K] [IsFiniteMeasure μ] in
theorem meanL1_apply (f : Lp ℝ 1 μ) : meanL1 (μ := μ) f = ∫ x, f x ∂μ := rfl

omit [IsFiniteKernel K] [IsFiniteMeasure μ] in
theorem norm_meanL1_le : ‖meanL1 (μ := μ)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Integration against the finite measure `μ` on `L∞(μ)`. -/
def meanLinf : Lp ℝ ∞ μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        rw [integral_congr_ae (Lp.coeFn_add f g)]
        exact integral_add (integrable_of_Linf f) (integrable_of_Linf g)
      map_smul' := by
        intro r f
        rw [integral_congr_ae (Lp.coeFn_smul r f), RingHom.id_apply]
        exact integral_smul r _ }
    (μ.real univ) (by
      intro f
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const (StandingHypothesis.lp_infinity_ae_norm_le f))

omit [IsFiniteKernel K] in
theorem meanLinf_apply (f : Lp ℝ ∞ μ) : meanLinf (μ := μ) f = ∫ x, f x ∂μ := rfl

end

end ConditionedStableLaws.KernelLp
