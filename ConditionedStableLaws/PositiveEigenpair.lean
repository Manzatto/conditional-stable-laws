import ConditionedStableLaws.PositiveResolvent
import ConditionedStableLaws.PositiveOrderUnit

/-!
# Positive eigenfunction construction at the norm-growth rate

Compactness supplies the limits of bounded resolvent sequences and of
normalized unbounded resolvent sequences. These analytic statements are
combined below with the order-unit estimate and the growth rate derived from H.
-/

open Set Filter
open scoped Topology BoundedContinuousFunction

namespace ConditionedStableLaws.PositiveEigenpair
noncomputable section
variable {M : Type*} [TopologicalSpace M]

/-- A bounded sequence of resolvent vectors approaching a nonzero rate has
a limit solving the resolvent equation at that rate. -/
theorem critical_solution_of_bounded_vectors
    (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) (hT : IsCompactOperator T)
    {r : ℝ} (hr : r ≠ 0) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 r))
    (hane : ∀ n, a n ≠ 0) (f : ℕ → M →ᵇ ℝ) (hf : ∀ n x, 1 ≤ f n x)
    (heq : ∀ n, T (f n) = a n • (f n - 1))
    {B : ℝ} (hB : ∀ n, ‖f n‖ ≤ B) :
    ∃ v : M →ᵇ ℝ, (∀ x, 1 ≤ v x) ∧ T v = r • (v-1) := by
  obtain ⟨A, hA, hTA⟩ := hT.image_closedBall_subset_compact B
  obtain ⟨y, _hyA, φ, hφ, hy⟩ := hA.tendsto_subseq
    (fun n => hTA ⟨f n, by simpa only [Metric.mem_closedBall, dist_zero_right] using hB n, rfl⟩)
  have hid (n : ℕ) : f n = 1 + (a n)⁻¹ • T (f n) := by
    rw [heq n, inv_smul_smul₀ (hane n)]
    abel
  let v : M →ᵇ ℝ := 1 + r⁻¹ • y
  have hv : Tendsto (fun n => f (φ n)) atTop (𝓝 v) := by
    have hh := (tendsto_const_nhds (x := (1 : M →ᵇ ℝ))).add
      (((ha.comp hφ.tendsto_atTop).inv₀ hr).smul hy)
    exact hh.congr (fun n => (hid (φ n)).symm)
  refine ⟨v, fun x => ?_, ?_⟩
  · exact ge_of_tendsto' ((BoundedContinuousFunction.evalCLM ℝ x).continuous.continuousAt.tendsto.comp hv)
      (fun n => hf (φ n) x)
  · have hl := T.continuous.continuousAt.tendsto.comp hv
    have hrhs := (ha.comp hφ.tendsto_atTop).smul
      (hv.sub (tendsto_const_nhds (x := (1 : M →ᵇ ℝ))))
    exact tendsto_nhds_unique hl (hrhs.congr (fun n => (heq (φ n)).symm))

/-- Divergent resolvent vectors normalize to positive unit approximate eigenvectors, and compactness
turns these into an eigenfunction. -/
theorem eigenfunction_of_unbounded_vectors [Nonempty M]
    (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) (hT : IsCompactOperator T)
    {r : ℝ} (hr : r ≠ 0) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 r))
    (f : ℕ → M →ᵇ ℝ) (hf : ∀ n x, 1 ≤ f n x)
    (heq : ∀ n, T (f n) = a n • (f n - 1))
    (hunbounded : Tendsto (fun n => ‖f n‖) atTop atTop) :
    ∃ v : M →ᵇ ℝ, (∀ x, 0 ≤ v x) ∧ ‖v‖ = 1 ∧ T v = r • v := by
  let u : ℕ → M →ᵇ ℝ := fun n => ‖f n‖⁻¹ • f n
  have hfnz (n : ℕ) : f n ≠ 0 := by
    intro hz
    obtain ⟨x⟩ := ‹Nonempty M›
    have hh := hf n x
    simp [hz] at hh
    norm_num at hh
  have hunorm (n : ℕ) : ‖u n‖ = 1 := by
    simp only [u, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hfnz n))]
  have hupos (n : ℕ) (x : M) : 0 ≤ u n x :=
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (zero_le_one.trans (hf n x))
  have hinv : Tendsto (fun n => ‖f n‖⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hunbounded
  have hres (n : ℕ) : T (u n) - r • u n =
      (a n-r) • u n - (a n * ‖f n‖⁻¹) • (1 : M →ᵇ ℝ) := by
    dsimp [u]
    rw [map_smul, heq n]
    module
  have hbound (n : ℕ) : ‖T (u n) - r • u n‖ ≤
      |a n-r| + ‖a n * ‖f n‖⁻¹‖ * ‖(1 : M →ᵇ ℝ)‖ := by
    rw [hres]
    simpa only [norm_smul, hunorm, mul_one, Real.norm_eq_abs] using
      norm_sub_le ((a n-r) • u n) ((a n * ‖f n‖⁻¹) • (1 : M →ᵇ ℝ))
  have hbend : Tendsto (fun n => |a n-r| + ‖a n * ‖f n‖⁻¹‖ * ‖(1 : M →ᵇ ℝ)‖)
      atTop (𝓝 0) := by
    simpa using ((ha.sub (tendsto_const_nhds (x := r))).abs).add
      ((ha.mul hinv).norm.mul_const ‖(1 : M →ᵇ ℝ)‖)
  have happrox : Tendsto (fun n => T (u n) - r • u n) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hbound hbend)
  exact CompactSpectral.eigenvector_of_approximate T hT r hr _ CompactSpectral.isClosed_nonnegative
    u hunorm hupos happrox

/-- A compact positive operator with a strictly positive norm-growth rate has a positive
eigenfunction at that rate, constructed from the Neumann series. -/
theorem resolvent_norm_tendsto_atTop
    (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) (hcompact : IsCompactOperator T)
    (hT : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x)
    {r : ℝ} (hr : 0 < r) (hlower : ∀ n : ℕ, r^n ≤ ‖T^n‖)
    (hupper : ∀ q : ℝ, r < q → ∀ᶠ n : ℕ in atTop, ‖T^n‖ ≤ q^n)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 r)) (hagt : ∀ n, r < a n)
    (hanti : Antitone a) :
    Tendsto (fun n => ‖PositiveResolvent.vector T (a n)‖) atTop atTop := by
  have hapos (n : ℕ) : 0 < a n := hr.trans (hagt n)
  have hs (n : ℕ) := PositiveResolvent.scaled_powers_summable T hr.le (hagt n) hupper
  let f : ℕ → M →ᵇ ℝ := fun n => PositiveResolvent.vector T (a n)
  have hf (n : ℕ) (x : M) : 1 ≤ f n x :=
    PositiveResolvent.vector_ge_one T hT (hapos n) (hs n) x
  have heq (n : ℕ) : T (f n) = a n • (f n - 1) :=
    PositiveResolvent.vector_equation T (hapos n).ne' (hs n)
  have hmono : Monotone (fun n => ‖f n‖) := by
    intro i j hij
    exact PositiveResolvent.vector_norm_antitone T hT (hapos j) (hanti hij) (hs j) (hs i)
  apply tendsto_atTop_atTop_of_monotone' hmono
  rintro ⟨B, hB⟩
  obtain ⟨v, hv, hveq⟩ := critical_solution_of_bounded_vectors T hcompact hr.ne'
    a ha (fun n => (hapos n).ne') f hf heq (fun n => hB ⟨n, rfl⟩)
  apply PositiveOrderUnit.critical_resolvent_impossible T hT hr hlower v hv
  intro x
  exact congrArg (fun g : M →ᵇ ℝ => g x) hveq

/-- Existence at the positive norm-growth rate, via normalized Neumann
vectors and compactness. -/
theorem exists_positive_eigenfunction [Nonempty M]
    (T : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ)) (hcompact : IsCompactOperator T)
    (hT : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x)
    {r : ℝ} (hr : 0 < r) (hlower : ∀ n : ℕ, r^n ≤ ‖T^n‖)
    (hupper : ∀ q : ℝ, r < q → ∀ᶠ n : ℕ in atTop, ‖T^n‖ ≤ q^n) :
    ∃ v : M →ᵇ ℝ, (∀ x, 0 ≤ v x) ∧ ‖v‖ = 1 ∧ T v = r • v := by
  let a : ℕ → ℝ := fun n => r + 1 / ((n : ℝ)+1)
  have hagt (n : ℕ) : r < a n := by
    exact lt_add_of_pos_right r (by positivity)
  have hapos (n : ℕ) : 0 < a n := hr.trans (hagt n)
  have ha : Tendsto a atTop (𝓝 r) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := r)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hanti : Antitone a := by
    intro i j hij
    dsimp [a]
    gcongr
  have hs (n : ℕ) : Summable (fun k : ℕ => ((a n)⁻¹ • T)^k) :=
    PositiveResolvent.scaled_powers_summable T hr.le (hagt n) hupper
  let f : ℕ → M →ᵇ ℝ := fun n => PositiveResolvent.vector T (a n)
  have hf (n : ℕ) (x : M) : 1 ≤ f n x :=
    PositiveResolvent.vector_ge_one T hT (hapos n) (hs n) x
  have heq (n : ℕ) : T (f n) = a n • (f n - 1) :=
    PositiveResolvent.vector_equation T (hapos n).ne' (hs n)
  have hmono : Monotone (fun n => ‖f n‖) := by
    intro i j hij
    exact PositiveResolvent.vector_norm_antitone T hT (hapos j) (hanti hij) (hs j) (hs i)
  have hnotbdd : ¬ BddAbove (range (fun n => ‖f n‖)) := by
    rintro ⟨B, hB⟩
    obtain ⟨v, hv, hveq⟩ := critical_solution_of_bounded_vectors T hcompact hr.ne'
      a ha (fun n => (hapos n).ne') f hf heq (fun n => hB ⟨n, rfl⟩)
    apply PositiveOrderUnit.critical_resolvent_impossible T hT hr hlower v hv
    intro x
    exact congrArg (fun g : M →ᵇ ℝ => g x) hveq
  exact eigenfunction_of_unbounded_vectors T hcompact hr.ne' a ha f hf heq
    (tendsto_atTop_atTop_of_monotone' hmono hnotbdd)

end
end ConditionedStableLaws.PositiveEigenpair

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
open MeasureTheory
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- The standing assumptions themselves imply a nonzero nonnegative
continuous eigenfunction with positive eigenvalue at most one. -/
theorem HypothesisH.exists_positive_eigenpair (h : HypothesisH ρ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ η : M →ᵇ ℝ,
      (∀ x, 0 ≤ η x) ∧ ‖η‖ = 1 ∧ h.continuousKernelOperator η = r • η := by
  have : Nonempty M := (nonempty_of_measure_ne_zero h.surviving_mass_pos.ne').to_subtype.map Subtype.val
  obtain ⟨r, hr, hrone, _, hlower, hupper⟩ := h.exists_positive_operator_growth_rate
  obtain ⟨η, hη, hnorm, heq⟩ := PositiveEigenpair.exists_positive_eigenfunction
    h.continuousKernelOperator h.continuousKernelOperator_isCompact
    h.continuousKernelOperator_nonneg hr hlower hupper
  exact ⟨r, hr, hrone, η, hη, hnorm, heq⟩

/-- Under H there is a killed-kernel integral eigenfunction. -/
theorem HypothesisH.exists_positive_integral_eigenfunction (h : HypothesisH ρ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ η : M →ᵇ ℝ,
      (∀ x, 0 ≤ η x) ∧ ‖η‖ = 1 ∧ ∀ x, (∫ y, η y ∂K.kernel x) = r * η x := by
  obtain ⟨r, hr, hrone, η, hη, hnorm, heq⟩ := h.exists_positive_eigenpair
  refine ⟨r, hr, hrone, η, hη, hnorm, fun x => ?_⟩
  have hx := congrArg (fun g : M →ᵇ ℝ => g x) heq
  simpa only [h.continuousKernelOperator_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul] using hx

/-- H gives the right eigen-data used to construct the Doob kernel, and its live region is exactly
the nonescaping set. -/
theorem HypothesisH.exists_right_eigenData (h : HypothesisH ρ K) :
    ∃ d : DoobTransform.EigenData K.kernel, d.rate ≤ 1 ∧ Continuous d.weight ∧
      (∃ x, d.weight x ≠ 0) ∧ d.liveSet = survivingSet K.kernel := by
  obtain ⟨r, hr, hrone, η, hη, hnorm, heq⟩ := h.exists_positive_eigenpair
  have happrox : Tendsto (fun _n : ℕ => h.continuousKernelOperator η - r • η) atTop (𝓝 0) := by
    simpa only [heq, sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : M →ᵇ ℝ)) atTop (𝓝 0))
  obtain ⟨d, hdr, hcont, hnonzero, hlive⟩ := h.exists_eigenData_of_approximate r hr
    (fun _ => η) (fun _ => hnorm) (fun _ => hη) happrox
  exact ⟨d, by rw [hdr]; exact (ENNReal.ofReal_le_ofReal hrone).trans_eq (by simp), hcont, hnonzero, hlive⟩

end
end ConditionedStableLaws.StandingHypothesis
