import ConditionedStableLaws.PositiveEigenmeasure
import ConditionedStableLaws.NormalizedEigenData

/-!
# Real eigenspace simplicity at the positive eigenvalue

Positivity and the left eigenmeasure force the absolute value of a real
eigenfunction to remain an eigenfunction. H2 then makes evaluation at any
nonescaping point injective on that eigenspace.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

theorem HypothesisH.pow_apply_eigenfunction (h : HypothesisH ρ K)
    {r : ℝ} {f : M →ᵇ ℝ} (heq : h.continuousKernelOperator f = r • f) (n : ℕ) :
    (h.continuousKernelOperator^n) f = r^n • f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' h.continuousKernelOperator, mul_apply_eq_comp, ih, map_smul, heq,
      smul_smul, pow_succ]

/-- Every nonzero-rate eigenfunction vanishes at all finite-extinction states. -/
theorem HypothesisH.eigenfunction_zero_on_escaping (h : HypothesisH ρ K)
    {r : ℝ} (hr : r ≠ 0) {f : M →ᵇ ℝ} (heq : h.continuousKernelOperator f = r • f)
    {x : M} (hx : x ∈ escapingSet K.kernel) : f x = 0 := by
  obtain ⟨n, _, hn⟩ := hx
  have hm : (K.kernel^n) x = 0 := Measure.measure_univ_eq_zero.mp hn
  have hp := congrArg (fun g : M →ᵇ ℝ => g x) (h.pow_apply_eigenfunction heq n)
  rw [h.continuousKernelOperator_pow_apply, hm, integral_zero_measure] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left (pow_ne_zero n hr)

/-- H2 makes a nonzero nonnegative eigenfunction strictly positive at every
nonescaping state, with no requirement on its closed support. -/
theorem HypothesisH.eigenfunction_positive_on_surviving (h : HypothesisH ρ K)
    {r : ℝ} (hr : 0 < r) (f : M →ᵇ ℝ) (hf : f ≠ 0) (hpos : ∀ x, 0 ≤ f x)
    (heq : h.continuousKernelOperator f = r • f) {x : M}
    (hx : x ∈ survivingSet K.kernel) : 0 < f x := by
  have hsubset : Function.support f ⊆ survivingSet K.kernel := by
    intro y hy
    change y ∉ escapingSet K.kernel
    intro hyz
    exact hy (h.eigenfunction_zero_on_escaping hr.ne' heq hyz)
  have hne : (Function.support f).Nonempty := by
    by_contra hempty
    apply hf
    ext y
    by_contra hy
    exact hempty ⟨y, hy⟩
  have hrel : RelativelyOpen (Function.support f) (survivingSet K.kernel) :=
    ⟨Function.support f, f.continuous.isOpen_support, (inter_eq_right.mpr hsubset).symm⟩
  obtain ⟨n, _, hn⟩ := h.irreducible x hx _ hrel hne
  have := killedKernel_power_isFinite K n
  have hi : 0 < ∫ y, f y ∂(K.kernel^n) x :=
    (integral_pos_iff_support_of_nonneg hpos (f.integrable _)).mpr hn
  have hp := congrArg (fun g : M →ᵇ ℝ => g x) (h.pow_apply_eigenfunction heq n)
  rw [h.continuousKernelOperator_pow_apply] at hp
  change (∫ y, f y ∂(K.kernel^n) x) = r^n * f x at hp
  rw [hp] at hi
  exact (mul_pos_iff.mp hi).resolve_right (fun hh => (not_lt_of_ge (pow_pos hr n).le) hh.1) |>.2

theorem HypothesisH.integral_continuousKernelOperator_of_eigenmeasure
    (h : HypothesisH ρ K) (μ : Measure M) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ) (f : M →ᵇ ℝ) :
    (∫ x, h.continuousKernelOperator f x ∂μ) = r * ∫ x, f x ∂μ := by
  have hi : (∫ y, f y ∂(K.kernel ∘ₘ μ)) = ∫ x, ∫ y, f y ∂K.kernel x ∂μ := by
    rw [Measure.comp_eq_comp_const_apply]
    exact Kernel.integral_comp (f.integrable _)
  rw [hleft, integral_smul_measure, ENNReal.toReal_ofReal hr, smul_eq_mul] at hi
  simpa only [h.continuousKernelOperator_apply] using hi.symm

/-- The absolute value of a real eigenfunction is an eigenfunction. The
support inclusion used here is already a consequence of H and the positive
left/right eigen-data. -/
theorem HypothesisH.abs_eigenfunction (h : HypothesisH ρ K)
    (μ : Measure M) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (hsupp : survivingSet K.kernel ⊆ μ.support)
    (f : M →ᵇ ℝ) (heq : h.continuousKernelOperator f = r • f) :
    h.continuousKernelOperator |f| = r • |f| := by
  let G : M →ᵇ ℝ := h.continuousKernelOperator |f| - r • |f|
  have hGpos (x : M) : 0 ≤ G x := by
    change 0 ≤ h.continuousKernelOperator |f| x - r * |f x|
    apply sub_nonneg.mpr
    have hi := abs_integral_le_integral_abs (f := (f : M → ℝ)) (μ := K.kernel x)
    rw [← h.continuousKernelOperator_apply, heq] at hi
    simpa only [h.continuousKernelOperator_apply, BoundedContinuousFunction.coe_abs,
      Pi.abs_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul,
      abs_mul, abs_of_pos hr] using hi
  have hiG : (∫ x, G x ∂μ) = 0 := by
    change (∫ x, h.continuousKernelOperator |f| x - r * (|f|) x ∂μ) = 0
    rw [integral_sub ((h.continuousKernelOperator |f|).integrable μ)
        ((|f|).integrable μ |>.const_mul r), integral_const_mul,
      h.integral_continuousKernelOperator_of_eigenmeasure μ hr.le hleft]
    exact sub_self _
  have hae : (G : M → ℝ) =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hGpos (G.integrable μ)).mp hiG
  have hzero : ∀ x ∈ survivingSet K.kernel, G x = 0 := by
    intro x hx
    exact Measure.support_subset_of_isClosed
      (isClosed_eq G.continuous continuous_const) hae (hsupp hx)
  ext x
  by_cases hx : x ∈ survivingSet K.kernel
  · exact sub_eq_zero.mp (hzero x hx)
  · have hxz : x ∈ escapingSet K.kernel := by simpa only [survivingSet, mem_compl_iff, not_not] using hx
    have hfx : f x = 0 := h.eigenfunction_zero_on_escaping hr.ne' heq hxz
    have hKae : ∀ᵐ y ∂K.kernel x, y ∈ escapingSet K.kernel := by
      apply ae_iff.mpr
      exact escaping_no_jump_to_surviving K.kernel hxz
    have hz : (fun y => |f y|) =ᵐ[K.kernel x] 0 := by
      filter_upwards [hKae] with y hy
      simp [h.eigenfunction_zero_on_escaping hr.ne' heq hy]
    change h.continuousKernelOperator |f| x = r * |f x|
    rw [h.continuousKernelOperator_apply, hfx, abs_zero, mul_zero]
    exact (integral_congr_ae hz).trans (integral_zero _ _)

/-- Every positive-rate left probability eigenmeasure has support containing the full nonescaping
region. -/
theorem HypothesisH.eigenmeasure_full_surviving_support (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ) :
    survivingSet K.kernel ⊆ μ.support := by
  obtain ⟨d, _, hc, hne, _⟩ := h.exists_right_eigenData
  have hdr := h.left_eigenvalue_eq d hc hne μ (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top hleft
  have hld : K.kernel ∘ₘ μ = d.rate • μ := by rwa [hdr] at hleft
  exact h.survivingSet_subset_eigenmeasure_support d μ hld
    (h.eigenfunction_integral_pos d hc hne μ hld)

/-- A real eigenfunction vanishing at a single nonescaping state vanishes
everywhere. This is the key one-dimensionality argument. -/
theorem HypothesisH.eigenfunction_zero_of_eval_zero (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (f : M →ᵇ ℝ) (heq : h.continuousKernelOperator f = r • f)
    {x : M} (hx : x ∈ survivingSet K.kernel) (hfx : f x = 0) : f = 0 := by
  by_contra hf
  have habs : |f| ≠ 0 := by
    intro hz
    apply hf
    ext y
    have hy := congrArg (fun g : M →ᵇ ℝ => g y) hz
    exact abs_eq_zero.mp hy
  have heabs := h.abs_eigenfunction μ hr hleft
    (h.eigenmeasure_full_surviving_support μ hr hleft) f heq
  have hp := h.eigenfunction_positive_on_surviving hr |f| habs (fun y => abs_nonneg (f y)) heabs hx
  change 0 < |f x| at hp
  simp [hfx] at hp

/-- Any real eigenfunction at the positive rate is a scalar multiple of a
fixed nonzero positive eigenfunction. -/
theorem HypothesisH.real_eigenfunction_eq_smul (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η)
    (f : M →ᵇ ℝ) (heq : h.continuousKernelOperator f = r • f) :
    ∃ c : ℝ, f = c • η := by
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  have hηx : 0 < η x := h.eigenfunction_positive_on_surviving hr η hηne hηpos hηeq hx
  let c : ℝ := f x / η x
  have he : h.continuousKernelOperator (f-c • η) = r • (f-c • η) := by
    rw [map_sub, map_smul, heq, hηeq]
    module
  have hzero : f - c • η = 0 := h.eigenfunction_zero_of_eval_zero μ hr hleft _ he hx (by
    change f x - (f x / η x) * η x = 0
    rw [div_mul_cancel₀ _ hηx.ne', sub_self])
  exact ⟨c, sub_eq_zero.mp hzero⟩

/-- The real pairing of any nonzero positive continuous eigenfunction with
any same-rate left probability eigenmeasure is strictly positive. -/
theorem HypothesisH.real_eigenfunction_integral_pos (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η) : 0 < ∫ x, η x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg hηpos (η.integrable μ)).mpr
  have hsubset : survivingSet K.kernel ⊆ Function.support η := by
    intro x hx
    exact (h.eigenfunction_positive_on_surviving hr η hηne hηpos hηeq hx).ne'
  exact (h.eigenmeasure_surviving_mass_pos μ (ENNReal.ofReal r)
    (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top hleft).trans_le (measure_mono hsubset)

/-- A generalized eigenvector cannot map to a nonzero multiple of the positive eigenfunction. This
follows by applying the left eigenmeasure. -/
theorem HypothesisH.generalized_eigenfunction_coefficient_zero (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η)
    (g : M →ᵇ ℝ) {c : ℝ} (heq : h.continuousKernelOperator g - r • g = c • η) : c = 0 := by
  have hi := congrArg (fun f : M →ᵇ ℝ => ∫ x, f x ∂μ) heq
  change (∫ x, h.continuousKernelOperator g x - r * g x ∂μ) = ∫ x, c * η x ∂μ at hi
  rw [integral_sub ((h.continuousKernelOperator g).integrable μ) ((g.integrable μ).const_mul r),
    integral_const_mul, integral_const_mul,
    h.integral_continuousKernelOperator_of_eigenmeasure μ hr.le hleft, sub_self] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_right
    (h.real_eigenfunction_integral_pos μ hr hleft η hηne hηpos hηeq).ne'

/-- Every generalized real eigenvector of order two is already an
eigenvector. Thus the one-dimensional eigenspace has no nontrivial Jordan chain. -/
theorem HypothesisH.generalized_eigenfunction_is_eigenfunction (h : HypothesisH ρ K)
    (μ : Measure M) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η)
    (g : M →ᵇ ℝ)
    (heq : h.continuousKernelOperator (h.continuousKernelOperator g-r • g) =
      r • (h.continuousKernelOperator g-r • g)) : h.continuousKernelOperator g = r • g := by
  obtain ⟨c, hc⟩ := h.real_eigenfunction_eq_smul μ hr hleft η hηne hηpos hηeq _ heq
  have hc0 := h.generalized_eigenfunction_coefficient_zero μ hr hleft η hηne hηpos hηeq g hc
  rw [hc0, zero_smul] at hc
  exact sub_eq_zero.mp hc

/-- The same-rate eigenpair constructed from H has a one-dimensional real eigenspace. -/
theorem HypothesisH.exists_simple_real_eigenpair (h : HypothesisH ρ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ η : M →ᵇ ℝ,
      (∀ x, 0 ≤ η x) ∧ ‖η‖ = 1 ∧ h.continuousKernelOperator η = r • η ∧
      ∀ f : M →ᵇ ℝ, h.continuousKernelOperator f = r • f → ∃ c : ℝ, f = c • η := by
  obtain ⟨r, hr, hrone, η, hη, hnorm, heq, μ, hleft⟩ := h.exists_positive_eigenpair_and_eigenmeasure
  refine ⟨r, hr, hrone, η, hη, hnorm, heq, fun f hf => ?_⟩
  have hne : η ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; norm_num)
  exact h.real_eigenfunction_eq_smul μ hr hleft η hne hη heq f hf

/-- H gives a positive real eigenvalue whose eigenspace is generated by one
positive function and has no nontrivial generalized eigenvector of order two. -/
theorem HypothesisH.exists_real_simple_eigenpair_no_jordan (h : HypothesisH ρ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ η : M →ᵇ ℝ,
      (∀ x, 0 ≤ η x) ∧ ‖η‖ = 1 ∧ h.continuousKernelOperator η = r • η ∧
      (∀ f : M →ᵇ ℝ, h.continuousKernelOperator f = r • f → ∃ c : ℝ, f = c • η) ∧
      (∀ g : M →ᵇ ℝ,
        h.continuousKernelOperator (h.continuousKernelOperator g-r • g) =
          r • (h.continuousKernelOperator g-r • g) → h.continuousKernelOperator g = r • g) := by
  obtain ⟨r, hr, hrone, η, hη, hnorm, heq, μ, hleft⟩ := h.exists_positive_eigenpair_and_eigenmeasure
  have hne : η ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; norm_num)
  exact ⟨r, hr, hrone, η, hη, hnorm, heq,
    fun f hf => h.real_eigenfunction_eq_smul μ hr hleft η hne hη heq f hf,
    fun g hg => h.generalized_eigenfunction_is_eigenfunction μ hr hleft η hne hη heq g hg⟩

end
end ConditionedStableLaws.StandingHypothesis
