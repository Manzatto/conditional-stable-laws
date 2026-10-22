import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Compact operators and weak convergence

A compact operator takes a bounded weakly convergent sequence to a norm-convergent sequence. This is
used for fixed-lag covariances in the Gaussian boundary case. Weak convergence is expressed against
every continuous linear functional.
-/

open Filter Set
open scoped Topology InnerProductSpace

namespace ConditionedStableLaws

/-- Compactness upgrades bounded weak convergence to norm convergence after
applying the operator. The proof identifies every norm cluster point using
the separating continuous dual. -/
theorem compactOperator_tendsto_of_weak
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (hT : IsCompactOperator T)
    (u : ℕ → E) (x : E) (hbounded : Bornology.IsBounded (range u))
    (hweak : ∀ ℓ : E →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ x))) :
    Tendsto (fun n => T (u n)) atTop (𝓝 (T x)) := by
  have hcompact : IsCompact (closure (T '' range u)) :=
    hT.isCompact_closure_image_of_bounded hbounded
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => subset_closure ⟨u n, mem_range_self n, rfl⟩)
  intro y _hy hcluster
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ℓ
  exact tendsto_nhds_unique (ℓ.continuous.continuousAt.tendsto.comp hlim)
    ((hweak (ℓ.comp T)).comp hφ.tendsto_atTop)

/-- In a real Hilbert space it suffices to test weak convergence against
inner products. This is the form used for normalized truncated observables. -/
theorem compactOperator_tendsto_of_inner
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (hT : IsCompactOperator T)
    (u : ℕ → E) (x : E) (hbounded : Bornology.IsBounded (range u))
    (hweak : ∀ v : E, Tendsto (fun n => ⟪v, u n⟫_ℝ) atTop (𝓝 ⟪v, x⟫_ℝ)) :
    Tendsto (fun n => T (u n)) atTop (𝓝 (T x)) := by
  apply compactOperator_tendsto_of_weak T hT u x hbounded
  intro ℓ
  obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℝ E).surjective ℓ
  simpa using hweak v

/-- A bounded weakly null sequence has vanishing quadratic correlations with
each fixed compact operator. -/
theorem inner_compactOperator_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (u : ℕ → E) (C : ℝ) (hbounded : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ v : E, Tendsto (fun n => ⟪v, u n⟫_ℝ) atTop (𝓝 0)) :
    Tendsto (fun n => ⟪u n, T (u n)⟫_ℝ) atTop (𝓝 0) := by
  have hb : Bornology.IsBounded (range u) := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := C)).subset
    rintro _ ⟨n, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbounded n
  have ht : Tendsto (fun n => T (u n)) atTop (𝓝 0) := by
    simpa using compactOperator_tendsto_of_inner T hT u 0 hb (by simpa using hweak)
  apply squeeze_zero_norm (fun n => ?_) (by simpa using ht.norm.const_mul C)
  exact (norm_inner_le_norm (u n) (T (u n))).trans
    (mul_le_mul_of_nonneg_right (hbounded n) (norm_nonneg _))

end ConditionedStableLaws
