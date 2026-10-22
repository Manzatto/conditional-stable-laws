import ConditionedStableLaws.RealSimplicity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Moduli of complex peripheral eigenfunctions

The eigenrelation here is an equality for the killed kernel, at every state. At the positive left
eigenvalue, equality of moduli forces the norm of a complex eigenfunction to be a real positive
eigenfunction. H2 and real simplicity then identify that norm with a positive multiple of the
leading eigenfunction.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws.ComplexIntegral
noncomputable section

/-- The unit phase of a nonzero complex number (and zero at zero). -/
def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp only [phase, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr hz)

theorem phase_mul (z w : ℂ) : phase (z*w) = phase z * phase w := by
  simp only [phase, norm_mul, Complex.ofReal_mul, div_mul_div_comm]

theorem phase_mul_norm (z : ℂ) : phase z * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

/-- Equality in the integral triangle inequality fixes the phase almost
everywhere. The phase is supplied as a unit complex number. -/
theorem ae_eq_phase_mul_norm {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : Integrable f μ) (u : ℂ) (hu : ‖u‖ = 1)
    (heq : (∫ x, f x ∂μ) = u * (∫ x, ‖f x‖ ∂μ : ℝ)) :
    ∀ᵐ x ∂μ, f x = u * (‖f x‖ : ℂ) := by
  have hnorm (x : A) : ‖(starRingEnd ℂ) u * f x‖ = ‖f x‖ := by
    rw [norm_mul, Complex.norm_conj, hu, one_mul]
  have hpos (x : A) : 0 ≤ ‖f x‖ - ((starRingEnd ℂ) u * f x).re :=
    sub_nonneg.mpr ((Complex.re_le_norm _).trans_eq (hnorm x))
  have hi : (∫ x, ‖f x‖ - ((starRingEnd ℂ) u * f x).re ∂μ) = 0 := by
    change (∫ x, ‖f x‖ - RCLike.re ((starRingEnd ℂ) u * f x) ∂μ) = 0
    rw [integral_sub hf.norm (hf.const_mul ((starRingEnd ℂ) u)).re,
      integral_re (hf.const_mul ((starRingEnd ℂ) u)), integral_const_mul, heq,
      ← mul_assoc, Complex.conj_mul', hu]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg hpos
    (hf.norm.sub (hf.const_mul ((starRingEnd ℂ) u)).re)).mp hi
  filter_upwards [hae] with x hx
  have hre : ((starRingEnd ℂ) u * f x).re = ‖f x‖ := (sub_eq_zero.mp hx).symm
  have him : ((starRingEnd ℂ) u * f x).im = 0 := by
    apply Complex.abs_re_eq_norm.mp
    rw [hre, abs_of_nonneg (norm_nonneg _), hnorm]
  have hw : (starRingEnd ℂ) u * f x = (‖f x‖ : ℂ) :=
    Complex.ext hre him
  have hm := congrArg (fun w : ℂ => u * w) hw
  rw [← mul_assoc, Complex.mul_conj', hu] at hm
  simpa using hm

/-- Equality in the integral norm bound transports the phase of every
nonzero value to the phase of the integral. -/
theorem ae_phase_eq {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : Integrable f μ) (hne : (∫ x, f x ∂μ) ≠ 0)
    (heq : (∫ x, ‖f x‖ ∂μ) = ‖∫ x, f x ∂μ‖) :
    ∀ᵐ x ∂μ, f x ≠ 0 → phase (f x) = phase (∫ y, f y ∂μ) := by
  have ha := ae_eq_phase_mul_norm hf (phase (∫ x, f x ∂μ)) (norm_phase hne) (by
    rw [heq, phase_mul_norm])
  filter_upwards [ha] with x hx hfx
  exact (div_eq_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hfx))).mpr hx

end
end ConditionedStableLaws.ComplexIntegral

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- The complex eigenrelation iterates under the killed kernel. -/
theorem complex_eigenfunction_pow (f : M →ᵇ ℂ) {z : ℂ}
    (heq : ∀ x, (∫ y, f y ∂K.kernel x) = z * f x) (n : ℕ) (x : M) :
    (∫ y, f y ∂(K.kernel^n) x) = z^n * f x := by
  induction n generalizing x with
  | zero =>
      simp only [pow_zero, show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply]
      simp
  | succ n ih =>
      have := killedKernel_power_isFinite K n
      have := killedKernel_power_isFinite K (n+1)
      rw [pow_succ]
      change (∫ y, f y ∂((K.kernel^n) ∘ₖ K.kernel) x) = _
      rw [Kernel.integral_comp (η := K.kernel^n) (κ := K.kernel) (a := x)
        (f.integrable _)]
      simp_rw [ih]
      rw [integral_const_mul, heq, pow_succ]
      ring

/-- Every complex eigenfunction with nonzero eigenvalue vanishes on Z. -/
theorem complex_eigenfunction_zero_on_escaping (f : M →ᵇ ℂ) {z : ℂ} (hz : z ≠ 0)
    (heq : ∀ x, (∫ y, f y ∂K.kernel x) = z * f x)
    {x : M} (hx : x ∈ escapingSet K.kernel) : f x = 0 := by
  obtain ⟨n, _, hn⟩ := hx
  have hm : (K.kernel^n) x = 0 := Measure.measure_univ_eq_zero.mp hn
  have hp := complex_eigenfunction_pow f heq n x
  rw [hm, integral_zero_measure] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left (pow_ne_zero n hz)

/-- A complex eigenfunction on the peripheral circle has a real eigenfunction
as its pointwise norm. -/
theorem HypothesisH.norm_complex_eigenfunction (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (f : M →ᵇ ℂ) {z : ℂ} (hz : ‖z‖ = r)
    (heq : ∀ x, (∫ y, f y ∂K.kernel x) = z * f x) :
    h.continuousKernelOperator f.normComp = r • f.normComp := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hz ▸ hr)
  let G : M →ᵇ ℝ := h.continuousKernelOperator f.normComp - r • f.normComp
  have hGpos (x : M) : 0 ≤ G x := by
    change 0 ≤ h.continuousKernelOperator f.normComp x - r * ‖f x‖
    apply sub_nonneg.mpr
    have hi := norm_integral_le_integral_norm (f := (f : M → ℂ)) (μ := K.kernel x)
    rw [heq, norm_mul, hz] at hi
    simpa only [h.continuousKernelOperator_apply, BoundedContinuousFunction.coe_normComp,
      Function.comp_apply] using hi
  have hiG : (∫ x, G x ∂μ) = 0 := by
    change (∫ x, h.continuousKernelOperator f.normComp x - r * f.normComp x ∂μ) = 0
    rw [integral_sub ((h.continuousKernelOperator f.normComp).integrable μ)
        (f.normComp.integrable μ |>.const_mul r), integral_const_mul,
      h.integral_continuousKernelOperator_of_eigenmeasure μ hr.le hleft]
    exact sub_self _
  have hae : (G : M → ℝ) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hGpos (G.integrable μ)).mp hiG
  have hzero (x : M) (hx : x ∈ survivingSet K.kernel) : G x = 0 :=
    Measure.support_subset_of_isClosed (isClosed_eq G.continuous continuous_const) hae
      (h.eigenmeasure_full_surviving_support μ hr hleft hx)
  ext x
  by_cases hx : x ∈ survivingSet K.kernel
  · exact sub_eq_zero.mp (hzero x hx)
  · have hxz : x ∈ escapingSet K.kernel := by
      simpa only [survivingSet, mem_compl_iff, not_not] using hx
    have hfx : f x = 0 := complex_eigenfunction_zero_on_escaping f hz0 heq hxz
    have hKae : ∀ᵐ y ∂K.kernel x, y ∈ escapingSet K.kernel :=
      ae_iff.mpr (escaping_no_jump_to_surviving K.kernel hxz)
    have hzfun : (fun y => ‖f y‖) =ᵐ[K.kernel x] 0 := by
      filter_upwards [hKae] with y hy
      simp [complex_eigenfunction_zero_on_escaping f hz0 heq hy]
    change h.continuousKernelOperator f.normComp x = r * ‖f x‖
    rw [h.continuousKernelOperator_apply, hfx, norm_zero, mul_zero]
    exact (integral_congr_ae hzfun).trans (integral_zero _ _)

/-- Every nonzero peripheral eigenfunction has modulus a strictly positive
multiple of the leading real eigenfunction. -/
theorem HypothesisH.norm_complex_eigenfunction_eq_pos_smul (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η)
    (f : M →ᵇ ℂ) (hf : f ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (heq : ∀ x, (∫ y, f y ∂K.kernel x) = z * f x) :
    ∃ c : ℝ, 0 < c ∧ f.normComp = c • η := by
  have hnormeq := h.norm_complex_eigenfunction μ hr hleft f hz heq
  have hnormne : f.normComp ≠ 0 := by
    intro hzero
    apply hf
    ext x
    exact norm_eq_zero.mp (congrArg (fun g : M →ᵇ ℝ => g x) hzero)
  obtain ⟨c, hc⟩ := h.real_eigenfunction_eq_smul μ hr hleft η hηne hηpos hηeq _ hnormeq
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  have hp := h.eigenfunction_positive_on_surviving hr f.normComp hnormne
    (fun y => norm_nonneg (f y)) hnormeq hx
  have hηx := h.eigenfunction_positive_on_surviving hr η hηne hηpos hηeq hx
  rw [hc] at hp
  change 0 < c * η x at hp
  exact ⟨c, (mul_pos_iff_of_pos_right hηx).mp hp, hc⟩

/-- A nonzero peripheral eigenfunction cannot vanish at a live state. -/
theorem HypothesisH.complex_eigenfunction_ne_zero_on_surviving (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (f : M →ᵇ ℂ) (hf : f ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (heq : ∀ x, (∫ y, f y ∂K.kernel x) = z * f x)
    {x : M} (hx : x ∈ survivingSet K.kernel) : f x ≠ 0 := by
  have hnormne : f.normComp ≠ 0 := by
    intro hzero
    apply hf
    ext y
    exact norm_eq_zero.mp (congrArg (fun g : M →ᵇ ℝ => g y) hzero)
  exact norm_pos_iff.mp (h.eigenfunction_positive_on_surviving hr f.normComp hnormne
    (fun y => norm_nonneg (f y)) (h.norm_complex_eigenfunction μ hr hleft f hz heq) hx)

/-- At every positive or zero time, surviving transitions of a peripheral eigenfunction rotate its
phase by the corresponding power of the eigenvalue. The almost-everywhere assertion refers to the
killed kernel power. -/
theorem HypothesisH.complex_eigenfunction_phase_transport (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (f : M →ᵇ ℂ) (hf : f ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (heq : ∀ x, (∫ y, f y ∂K.kernel x) = z * f x)
    (n : ℕ) {x : M} (hx : x ∈ survivingSet K.kernel) :
    ∀ᵐ y ∂(K.kernel^n) x, y ∈ survivingSet K.kernel →
      ComplexIntegral.phase (f y) = ComplexIntegral.phase (z^n) * ComplexIntegral.phase (f x) := by
  have := killedKernel_power_isFinite K n
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hz ▸ hr)
  have hfx := h.complex_eigenfunction_ne_zero_on_surviving μ hr hleft f hf hz heq hx
  have heigen := h.norm_complex_eigenfunction μ hr hleft f hz heq
  have hinorm : (∫ y, ‖f y‖ ∂(K.kernel^n) x) = ‖∫ y, f y ∂(K.kernel^n) x‖ := by
    have hp := congrArg (fun g : M →ᵇ ℝ => g x) (h.pow_apply_eigenfunction heigen n)
    rw [h.continuousKernelOperator_pow_apply] at hp
    change (∫ y, ‖f y‖ ∂(K.kernel^n) x) = r^n * ‖f x‖ at hp
    rw [complex_eigenfunction_pow f heq, norm_mul, norm_pow, hz]
    exact hp
  have hae := ComplexIntegral.ae_phase_eq (f.integrable ((K.kernel^n) x)) (by
    rw [complex_eigenfunction_pow f heq]
    exact mul_ne_zero (pow_ne_zero n hz0) hfx) hinorm
  filter_upwards [hae] with y hy hys
  rw [← ComplexIntegral.phase_mul, ← complex_eigenfunction_pow f heq]
  exact hy (h.complex_eigenfunction_ne_zero_on_surviving μ hr hleft f hf hz heq hys)

end
end ConditionedStableLaws.StandingHypothesis
