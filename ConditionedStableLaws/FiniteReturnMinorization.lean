import ConditionedStableLaws.CompactSpectral
import ConditionedStableLaws.NonEscapingOpen
import Mathlib.Topology.UrysohnsLemma

/-!
# A positive finite-polynomial minorization from H1 and H2

A continuous bump inside the nonescaping region is reached from every point of its compact support.
A finite subcover and a positive minimum turn H2 into an inequality `(P + ... + P^N) ψ ≥ c ψ` with
`c > 0` and `ψ ≠ 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- A nonzero positive continuous bump whose closed support stays entirely
inside the nonescaping region, obtained before any spectral construction. -/
theorem HypothesisH.exists_surviving_bump (h : HypothesisH ρ K) :
    ∃ ψ : M →ᵇ ℝ, ψ ≠ 0 ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      tsupport ψ ⊆ survivingSet K.kernel := by
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  obtain ⟨f, hsupp, hone, hbound⟩ := exists_tsupport_one_of_isOpen_isClosed
    h.isOpen_survivingSet isClosed_closure.isCompact isClosed_singleton
    (singleton_subset_iff.mpr hx)
  refine ⟨BoundedContinuousFunction.mkOfCompact f, ?_, hbound, hsupp⟩
  intro hz
  have he : f x = 1 := hone (mem_singleton x)
  have hzero := congrArg (fun g : M →ᵇ ℝ => g x) hz
  change f x = 0 at hzero
  linarith

/-- H2 reaches the positive support of a nonzero continuous function. -/
theorem HypothesisH.exists_positive_power_on_surviving (h : HypothesisH ρ K)
    (ψ : M →ᵇ ℝ) (hψ : ψ ≠ 0) (hpos : ∀ x, 0 ≤ ψ x)
    (hsupp : tsupport ψ ⊆ survivingSet K.kernel) {x : M}
    (hx : x ∈ survivingSet K.kernel) :
    ∃ n : ℕ, 1 ≤ n ∧ 0 < (h.continuousKernelOperator^n) ψ x := by
  have hopen : IsOpen (Function.support ψ) := ψ.continuous.isOpen_support
  have hsubset : Function.support ψ ⊆ survivingSet K.kernel := (subset_tsupport ψ).trans hsupp
  have hrel : RelativelyOpen (Function.support ψ) (survivingSet K.kernel) :=
    ⟨Function.support ψ, hopen, (inter_eq_right.mpr hsubset).symm⟩
  have hne : (Function.support ψ).Nonempty := by
    by_contra hempty
    apply hψ
    ext y
    by_contra hy
    exact hempty ⟨y, hy⟩
  obtain ⟨n, hn, hreach⟩ := h.irreducible x hx _ hrel hne
  have := killedKernel_power_isFinite K n
  refine ⟨n, hn, ?_⟩
  rw [h.continuousKernelOperator_pow_apply]
  exact (integral_pos_iff_support_of_nonneg hpos
    (ψ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ψ))).mpr hreach

/-- The compact support admits a common positive lower bound for a finite
sum of positive-time kernel iterates. -/
theorem HypothesisH.finite_power_minorization (h : HypothesisH ρ K)
    (ψ : M →ᵇ ℝ) (hψ : ψ ≠ 0) (hpos : ∀ x, 0 ≤ ψ x)
    (hsupp : tsupport ψ ⊆ survivingSet K.kernel) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ x, c * ψ x ≤ ∑ n ∈ Finset.range N, (h.continuousKernelOperator^(n+1)) ψ x := by
  let T := h.continuousKernelOperator
  have hnonneg (n : ℕ) (x : M) : 0 ≤ (T^n) ψ x := by
    rw [h.continuousKernelOperator_pow_apply]
    exact integral_nonneg hpos
  let U : ℕ → Set M := fun n => {x | 0 < (T^(n+1)) ψ x}
  have hU : ∀ n, IsOpen (U n) := fun n => isOpen_lt continuous_const ((T^(n+1)) ψ).continuous
  have hcover : tsupport ψ ⊆ ⋃ n, U n := by
    intro x hx
    obtain ⟨n, hn, hp⟩ := h.exists_positive_power_on_surviving ψ hψ hpos hsupp (hsupp hx)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact mem_iUnion.mpr ⟨m, hp⟩
  obtain ⟨t, ht⟩ := (isClosed_tsupport ψ).isCompact.elim_finite_subcover U hU hcover
  let F : M → ℝ := fun x => ∑ n ∈ t, (T^(n+1)) ψ x
  have hF : Continuous F := by
    exact continuous_finsetSum _ (fun n _ => ((T^(n+1)) ψ).continuous)
  have hFpos : ∀ x ∈ tsupport ψ, 0 < F x := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := mem_iUnion₂.mp (ht hx)
    exact Finset.sum_pos' (fun m _ => hnonneg (m+1) x) ⟨n, hn, hnx⟩
  have hsne : (tsupport ψ).Nonempty := by
    by_contra hempty
    apply hψ
    ext x
    by_contra hx
    exact hempty ⟨x, (subset_tsupport ψ) hx⟩
  obtain ⟨x₀, hx₀, hmin⟩ := (isClosed_tsupport ψ).isCompact.exists_isMinOn hsne hF.continuousOn
  have hδ : 0 < F x₀ := hFpos x₀ hx₀
  let c := F x₀ / (‖ψ‖ + 1)
  have hc : 0 < c := div_pos hδ (by positivity)
  obtain ⟨N, htN⟩ := Finset.exists_nat_subset_range t
  refine ⟨N, c, hc, fun x => ?_⟩
  have hle : c * ψ x ≤ F x := by
    by_cases hx : x ∈ tsupport ψ
    · have hb : ψ x ≤ ‖ψ‖ + 1 := (le_abs_self _).trans (by
        have hn := BoundedContinuousFunction.norm_coe_le_norm ψ x
        rw [Real.norm_eq_abs] at hn
        linarith)
      have hcψ := mul_le_mul_of_nonneg_left hb hc.le
      have heq : c * (‖ψ‖ + 1) = F x₀ := div_mul_cancel₀ _ (by positivity)
      rw [heq] at hcψ
      exact hcψ.trans (hmin hx)
    · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hz, mul_zero]
      exact Finset.sum_nonneg (fun n _ => hnonneg (n+1) x)
  exact hle.trans (Finset.sum_le_sum_of_subset_of_nonneg htN (fun n _ _ => hnonneg (n+1) x))

/-- A strictly positive finite-polynomial subeigenvalue is obtained directly
from the standing assumptions, with a nonzero positive test function. -/
theorem HypothesisH.exists_finite_power_minorization (h : HypothesisH ρ K) :
    ∃ ψ : M →ᵇ ℝ, ψ ≠ 0 ∧ (∀ x, 0 ≤ ψ x) ∧
      ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
        ∀ x, c * ψ x ≤ ∑ n ∈ Finset.range N, (h.continuousKernelOperator^(n+1)) ψ x := by
  obtain ⟨ψ, hψ, hp, hs⟩ := h.exists_surviving_bump
  exact ⟨ψ, hψ, fun x => (hp x).1, h.finite_power_minorization ψ hψ (fun x => (hp x).1) hs⟩

end
end ConditionedStableLaws.StandingHypothesis
