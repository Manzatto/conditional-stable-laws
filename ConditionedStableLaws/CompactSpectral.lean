import ConditionedStableLaws.SpectralSurvival
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Compact spectral foundations for the killed operator

Contraction, and the compact-operator passage from approximate eigenvectors to eigenvectors,
including preservation of a closed positive cone. Nonzero spectral points yield continuous kernel
eigenfunctions.
-/

open MeasureTheory ProbabilityTheory Filter Set Module
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws
noncomputable section

namespace CompactSpectral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compactness turns unit approximate eigenvectors into a nonzero eigenvector. A closed constraint,
such as positivity, is retained in the limit. -/
theorem eigenvector_of_approximate (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (a : ℝ) (ha : a ≠ 0) (S : Set E) (hS : IsClosed S)
    (f : ℕ → E) (hfnorm : ∀ n, ‖f n‖ = 1) (hfS : ∀ n, f n ∈ S)
    (happrox : Tendsto (fun n => T (f n) - a • f n) atTop (𝓝 0)) :
    ∃ v : E, v ∈ S ∧ ‖v‖ = 1 ∧ T v = a • v := by
  obtain ⟨A, hA, hTA⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, _hyA, φ, hφ, hy⟩ := hA.tendsto_subseq
    (fun n => hTA ⟨f n, by simp [Metric.mem_closedBall, hfnorm], rfl⟩)
  have hres := happrox.comp hφ.tendsto_atTop
  have hscaled : Tendsto (fun n => a • f (φ n)) atTop (𝓝 y) := by
    convert hy.sub hres using 1
    · funext n
      change a • f (φ n) = T (f (φ n)) - (T (f (φ n)) - a • f (φ n))
      abel
    · simp
  have hv : Tendsto (fun n => f (φ n)) atTop (𝓝 (a⁻¹ • y)) := by
    simpa only [inv_smul_smul₀ ha] using hscaled.const_smul a⁻¹
  refine ⟨a⁻¹ • y, hS.mem_of_tendsto hv (Eventually.of_forall (fun n => hfS (φ n))), ?_, ?_⟩
  · have hnorm := continuous_norm.continuousAt.tendsto.comp hv
    exact tendsto_nhds_unique hnorm (by simpa only [Function.comp_def, hfnorm]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  · have he : T (a⁻¹ • y) = y := tendsto_nhds_unique
      (T.continuous.continuousAt.tendsto.comp hv) hy
    rw [he, smul_inv_smul₀ ha]

/-- The positive cone of continuous real functions is closed in the supremum
norm, so compact approximate-eigenvector extraction preserves positivity. -/
theorem isClosed_nonnegative {M : Type*} [TopologicalSpace M] :
    IsClosed {f : M →ᵇ ℝ | ∀ x, 0 ≤ f x} := by
  have heq : {f : M →ᵇ ℝ | ∀ x, 0 ≤ f x} = ⋂ x : M, {f : M →ᵇ ℝ | 0 ≤ f x} := by
    ext f
    simp
  rw [heq]
  exact isClosed_iInter (fun x => isClosed_le continuous_const (BoundedContinuousFunction.lipschitz_eval_const x).continuous)

/-- Nonzero eigenspaces of a compact operator are finite dimensional. This
is the finite-dimensional reduction needed before peripheral spectral analysis. -/
theorem finiteDimensional_eigenspace (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (a : ℝ) (ha : a ≠ 0) : FiniteDimensional ℝ (Module.End.eigenspace (T : Module.End ℝ E) a) := by
  let V := Module.End.eigenspace (T : Module.End ℝ E) a
  have hmem (v : E) : v ∈ V ↔ T v = a • v := Module.End.mem_eigenspace_iff
  have hclosed : IsClosed (V : Set E) := by
    have heq : (V : Set E) = {v | T v = a • v} := Set.ext hmem
    rw [heq]
    exact isClosed_eq T.continuous (continuous_const.smul continuous_id)
  have hV : ∀ v ∈ V, T v ∈ V := by
    intro v hv
    apply (hmem _).mpr
    rw [(hmem v).mp hv, map_smul, (hmem v).mp hv]
  have hcompact : IsCompactOperator ((T : Module.End ℝ E).restrict hV) :=
    hT.restrict hV hclosed
  have hscaled := hcompact.smul a⁻¹
  have hid : (a⁻¹ • ((T : Module.End ℝ E).restrict hV) : V → V) = id := by
    funext v
    apply Subtype.ext
    change a⁻¹ • T v.val = v.val
    rw [(hmem v.val).mp v.property, inv_smul_smul₀ ha]
  rw [hid] at hscaled
  exact FiniteDimensional.of_isCompactOperator_id hscaled

end CompactSpectral

namespace StandingHypothesis
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Every L∞ class has its norm as an almost-everywhere pointwise bound. -/
theorem lp_infinity_ae_norm_le (f : Lp ℝ ∞ ρ) : ∀ᵐ x ∂ρ, ‖f x‖ ≤ ‖f‖ := by
  simpa only [Lp.norm_def, toReal_eLpNorm] using ae_le_lpNorm_exponent_top (Lp.memLp f)

/-- The killed integral is a contraction at every starting point, by the subprobability mass and
absolute continuity. -/
theorem HypothesisH.kernel_integral_norm_le (h : HypothesisH ρ K)
    (f : Lp ℝ ∞ ρ) (x : M) : ‖∫ y, f y ∂K.kernel x‖ ≤ ‖f‖ := by
  have hb := norm_integral_le_of_norm_le_const
    ((h.absolutelyContinuous x).ae_le (lp_infinity_ae_norm_le f))
  have hm : (K.kernel x).real univ ≤ 1 := by
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one x)).trans_eq (by simp)
  exact hb.trans (by nlinarith [norm_nonneg f])

/-- The L∞ killed transition has operator norm at most one. -/
theorem HypothesisH.transitionOperator_norm_le_one (h : HypothesisH ρ K) :
    ‖h.transitionOperator‖ ≤ 1 := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  apply h.transitionOperator.opNorm_le_bound zero_le_one
  intro f
  have hb : ∀ᵐ x ∂ρ, ‖h.transitionOperator f x‖ ≤ ‖f‖ := by
    filter_upwards [h.transitionOperator_ae f] with x hx
    rw [hx]
    exact h.kernel_integral_norm_le f x
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg f) hb

/-- Nonzero real spectral points give nonzero eigenvectors, by compactness and the Fredholm
alternative. -/
theorem HypothesisH.exists_eigenvector_of_mem_spectrum (h : HypothesisH ρ K)
    (a : ℝ) (ha : a ≠ 0) (hspec : a ∈ spectrum ℝ h.transitionOperator) :
    ∃ f : Lp ℝ ∞ ρ, f ≠ 0 ∧ h.transitionOperator f = a • f := by
  have he := (h.transitionOperator_isCompact.hasEigenvalue_iff_mem_spectrum ha).mpr hspec
  obtain ⟨f, hf⟩ := he.exists_hasEigenvector
  exact ⟨f, hf.2, hf.apply_eq_smul⟩

/-- Every nonzero eigenvector has eigenvalue of modulus at most one. -/
theorem HypothesisH.eigenvalue_abs_le_one (h : HypothesisH ρ K)
    (a : ℝ) (f : Lp ℝ ∞ ρ) (hf : f ≠ 0) (heigen : h.transitionOperator f = a • f) :
    |a| ≤ 1 := by
  have hb : ‖h.transitionOperator f‖ ≤ ‖f‖ :=
    (h.transitionOperator.le_opNorm f).trans (by
      nlinarith [h.transitionOperator_norm_le_one, norm_nonneg f])
  rw [heigen, norm_smul, Real.norm_eq_abs] at hb
  have hp : 0 < ‖f‖ := norm_pos_iff.mpr hf
  nlinarith

/-- Every real spectral value has modulus at most one. -/
theorem HypothesisH.real_spectrum_abs_le_one (h : HypothesisH ρ K)
    (a : ℝ) (hspec : a ∈ spectrum ℝ h.transitionOperator) : |a| ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · obtain ⟨f, hf, he⟩ := h.exists_eigenvector_of_mem_spectrum a ha hspec
    exact h.eigenvalue_abs_le_one a f hf he

/-- Canonical continuous representative of a nonzero-eigenvalue eigenvector. -/
def HypothesisH.eigenfunctionRepresentative (h : HypothesisH ρ K)
    (a : ℝ) (f : Lp ℝ ∞ ρ) : M →ᵇ ℝ := h.smoothedOperator a⁻¹ f

theorem HypothesisH.eigenfunctionRepresentative_ae (h : HypothesisH ρ K)
    (a : ℝ) (ha : a ≠ 0) (f : Lp ℝ ∞ ρ) (heigen : h.transitionOperator f = a • f) :
    (h.eigenfunctionRepresentative a f : M → ℝ) =ᵐ[ρ] f := by
  have hrep := h.transitionOperator_ae f
  rw [heigen] at hrep
  filter_upwards [hrep, Lp.coeFn_smul a f] with x hx hs
  rw [hs] at hx
  rw [eigenfunctionRepresentative, h.smoothedOperator_apply, h.stepEvaluation_apply,
    ← hx]
  exact inv_mul_cancel_left₀ ha _

/-- The representative satisfies the kernel eigenrelation at every state,
not merely almost everywhere. -/
theorem HypothesisH.eigenfunctionRepresentative_eigen (h : HypothesisH ρ K)
    (a : ℝ) (ha : a ≠ 0) (f : Lp ℝ ∞ ρ) (heigen : h.transitionOperator f = a • f)
    (x : M) :
    (∫ y, h.eigenfunctionRepresentative a f y ∂K.kernel x) =
      a * h.eigenfunctionRepresentative a f x := by
  rw [integral_congr_ae ((h.absolutelyContinuous x).ae_eq
    (h.eigenfunctionRepresentative_ae a ha f heigen)), eigenfunctionRepresentative,
    h.smoothedOperator_apply, h.stepEvaluation_apply]
  exact (mul_inv_cancel_left₀ ha _).symm

theorem HypothesisH.eigenfunctionRepresentative_ne_zero (h : HypothesisH ρ K)
    (a : ℝ) (ha : a ≠ 0) (f : Lp ℝ ∞ ρ) (hf : f ≠ 0)
    (heigen : h.transitionOperator f = a • f) : h.eigenfunctionRepresentative a f ≠ 0 := by
  intro hzero
  apply hf
  apply Lp.ext
  refine (h.eigenfunctionRepresentative_ae a ha f heigen).symm.trans ?_
  rw [hzero]
  exact (Lp.coeFn_zero ℝ ∞ ρ).symm

/-- A nonzero spectral point produces a nonzero continuous solution of the kernel eigenfunction
equation. -/
theorem HypothesisH.exists_continuous_eigenfunction_of_mem_spectrum (h : HypothesisH ρ K)
    (a : ℝ) (ha : a ≠ 0) (hspec : a ∈ spectrum ℝ h.transitionOperator) :
    ∃ f : M →ᵇ ℝ, f ≠ 0 ∧ ∀ x, (∫ y, f y ∂K.kernel x) = a * f x := by
  obtain ⟨f, hf, he⟩ := h.exists_eigenvector_of_mem_spectrum a ha hspec
  exact ⟨h.eigenfunctionRepresentative a f, h.eigenfunctionRepresentative_ne_zero a ha f hf he,
    h.eigenfunctionRepresentative_eigen a ha f he⟩

/-- The same kernel acting on continuous functions, with the supremum norm. This is the natural
closed-cone space for Krein–Rutman. -/
def HypothesisH.continuousKernelOperator (h : HypothesisH ρ K) :
    (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ) := by
  letI : IsProbabilityMeasure ρ := h.reference_probability
  exact (h.smoothedOperator 1).comp (BoundedContinuousFunction.toLp ∞ ρ ℝ)

theorem HypothesisH.continuousKernelOperator_apply (h : HypothesisH ρ K)
    (f : M →ᵇ ℝ) (x : M) : h.continuousKernelOperator f x = ∫ y, f y ∂K.kernel x := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  change h.smoothedOperator 1 (BoundedContinuousFunction.toLp ∞ ρ ℝ f) x = _
  rw [h.smoothedOperator_apply, h.stepEvaluation_apply, one_mul]
  exact integral_congr_ae ((h.absolutelyContinuous x).ae_eq
    (BoundedContinuousFunction.coeFn_toLp ∞ ρ ℝ f))

theorem HypothesisH.continuousKernelOperator_isCompact (h : HypothesisH ρ K) :
    IsCompactOperator h.continuousKernelOperator := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  have hs : IsCompactOperator (h.smoothedOperator 1) :=
    (transitionIntegralOperator_isCompact ρ ⟨h.density, h.continuous_density⟩).smul (1 : ℝ)
  exact hs.comp_clm (BoundedContinuousFunction.toLp ∞ ρ ℝ)

theorem HypothesisH.continuousKernelOperator_nonneg (h : HypothesisH ρ K)
    (f : M →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : M) :
    0 ≤ h.continuousKernelOperator f x := by
  rw [h.continuousKernelOperator_apply]
  exact integral_nonneg hf

/-- Powers of the continuous operator are powers of the killed kernel. This also fixes the time-zero
convention. -/
theorem HypothesisH.continuousKernelOperator_pow_apply (h : HypothesisH ρ K)
    (n : ℕ) (f : M →ᵇ ℝ) (x : M) :
    (h.continuousKernelOperator^n) f x = ∫ y, f y ∂(K.kernel^n) x := by
  induction n generalizing x with
  | zero =>
      simp only [pow_zero, show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply]
      simp
  | succ n ih =>
      have := killedKernel_power_isFinite K n
      have := killedKernel_power_isFinite K (n + 1)
      rw [pow_succ']
      change h.continuousKernelOperator ((h.continuousKernelOperator^n) f) x = _
      rw [h.continuousKernelOperator_apply]
      simp_rw [ih]
      rw [pow_succ]
      exact (Kernel.integral_comp (η := K.kernel^n) (κ := K.kernel) (a := x)
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))).symm

/-- H2's positive-measure nonescaping region rules out finite-time nilpotence of the continuous
killed operator. -/
theorem HypothesisH.continuousKernelOperator_pow_ne_zero (h : HypothesisH ρ K) (n : ℕ) :
    h.continuousKernelOperator^n ≠ 0 := by
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  have := killedKernel_power_isFinite K n
  have hm : 0 < (K.kernel^n) x univ := by
    cases n with
    | zero => simp [show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply]
    | succ n => exact (mem_survivingSet_iff K.kernel x).mp hx (n+1) (by omega)
  have hreal : 0 < ((K.kernel^n) x).real univ :=
    ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)
  intro hzero
  have he := h.continuousKernelOperator_pow_apply n (BoundedContinuousFunction.const M (1 : ℝ)) x
  rw [hzero] at he
  have hbad : (0 : ℝ) = ((K.kernel^n) x).real univ := by simpa using he
  exact hreal.ne' hbad.symm

/-- For the killed operator, a positive approximate-eigenvector sequence produces a nonzero
continuous positive eigenfunction. -/
theorem HypothesisH.exists_positive_eigenfunction_of_approximate (h : HypothesisH ρ K)
    (a : ℝ) (ha : 0 < a) (f : ℕ → (M →ᵇ ℝ))
    (hfnorm : ∀ n, ‖f n‖ = 1) (hfpos : ∀ n x, 0 ≤ f n x)
    (happrox : Tendsto (fun n => h.continuousKernelOperator (f n) - a • f n) atTop (𝓝 0)) :
    ∃ η : M →ᵇ ℝ, (∀ x, 0 ≤ η x) ∧ ‖η‖ = 1 ∧
      ∀ x, (∫ y, η y ∂K.kernel x) = a * η x := by
  obtain ⟨η, hη, hnorm, he⟩ := CompactSpectral.eigenvector_of_approximate
    h.continuousKernelOperator h.continuousKernelOperator_isCompact a ha.ne'
    {g | ∀ x, 0 ≤ g x} CompactSpectral.isClosed_nonnegative f hfnorm hfpos happrox
  refine ⟨η, hη, hnorm, fun x => ?_⟩
  have hx := congrArg (fun g : M →ᵇ ℝ => g x) he
  simpa only [h.continuousKernelOperator_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul] using hx

/-- Positive approximate eigenvectors produce the exact eigen-data structure used by the Doob
construction, and H2 identifies its positive region. -/
theorem HypothesisH.exists_eigenData_of_approximate (h : HypothesisH ρ K)
    (a : ℝ) (ha : 0 < a) (f : ℕ → (M →ᵇ ℝ))
    (hfnorm : ∀ n, ‖f n‖ = 1) (hfpos : ∀ n x, 0 ≤ f n x)
    (happrox : Tendsto (fun n => h.continuousKernelOperator (f n) - a • f n) atTop (𝓝 0)) :
    ∃ d : DoobTransform.EigenData K.kernel, d.rate = ENNReal.ofReal a ∧
      Continuous d.weight ∧ (∃ x, d.weight x ≠ 0) ∧ d.liveSet = survivingSet K.kernel := by
  obtain ⟨η, hpos, hnorm, heigen⟩ :=
    h.exists_positive_eigenfunction_of_approximate a ha f hfnorm hfpos happrox
  let d : DoobTransform.EigenData K.kernel := {
    rate := ENNReal.ofReal a
    rate_ne_zero := (ENNReal.ofReal_pos.mpr ha).ne'
    rate_ne_top := ENNReal.ofReal_ne_top
    weight := fun x => ENNReal.ofReal (η x)
    measurable_weight := η.continuous.measurable.ennreal_ofReal
    weight_ne_top := fun _ => ENNReal.ofReal_ne_top
    right_eigen := by
      intro x
      rw [← ofReal_integral_eq_lintegral_ofReal
        (η.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace η))
        (ae_of_all _ hpos), heigen x, ENNReal.ofReal_mul ha.le] }
  have hcont : Continuous d.weight := ENNReal.continuous_ofReal.comp η.continuous
  have hnonzero : ∃ x, d.weight x ≠ 0 := by
    by_contra! hz
    have hη : η = 0 := by
      ext x
      have hx : η x ≤ 0 := ENNReal.ofReal_eq_zero.mp (hz x)
      exact le_antisymm hx (hpos x)
    rw [hη, norm_zero] at hnorm
    norm_num at hnorm
  exact ⟨d, rfl, hcont, hnonzero, h.eigenfunction_liveSet_eq d hcont hnonzero⟩

end StandingHypothesis
end
end ConditionedStableLaws
