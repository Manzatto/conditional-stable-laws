import ConditionedStableLaws.CompactSpectral
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# From `L∞(ρ)` to `L∞(μ)` when `μ ≪ ρ`

If `μ ≪ ρ`, every `ρ`-class determines a `μ`-class, giving a norm-nonincreasing linear map `J :
L∞(ρ) → L∞(μ)`. Every `μ`-class has a bounded measurable representative, hence a lift through `J`
without increase of norm. Consequently an operator on `L∞(μ)` intertwined by `J` with a compact
(respectively norm-bounded) operator on `L∞(ρ)` is compact (respectively has no larger norm).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.RestrictLp

noncomputable section

section Transfer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Compactness passes through a map with norm-preserving lifts. -/
theorem isCompactOperator_of_intertwine (J : E →L[ℝ] F)
    (hlift : ∀ g : F, ∃ f : E, ‖f‖ ≤ ‖g‖ ∧ J f = g)
    {A : F →L[ℝ] F} {B : E →L[ℝ] E} (hAB : A.comp J = J.comp B)
    (hB : IsCompactOperator B) : IsCompactOperator A := by
  obtain ⟨S, hS, hSnhds⟩ := hB
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hSnhds
  refine ⟨J '' S, hS.image J.continuous, Metric.mem_nhds_iff.2 ⟨r, hr, fun g hg => ?_⟩⟩
  obtain ⟨f, hf, rfl⟩ := hlift g
  refine ⟨B f, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hg ⊢
    exact hf.trans_lt hg
  · exact (congrArg (fun T : E →L[ℝ] F => T f) hAB).symm

/-- Operator norms do not increase through a map with norm-preserving lifts
of norm at most one. -/
theorem opNorm_le_of_intertwine (J : E →L[ℝ] F) (hJ : ‖J‖ ≤ 1)
    (hlift : ∀ g : F, ∃ f : E, ‖f‖ ≤ ‖g‖ ∧ J f = g)
    {A : F →L[ℝ] F} {B : E →L[ℝ] E} (hAB : A.comp J = J.comp B) : ‖A‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
  obtain ⟨f, hf, rfl⟩ := hlift g
  have he : A (J f) = J (B f) := congrArg (fun T : E →L[ℝ] F => T f) hAB
  rw [he]
  calc ‖J (B f)‖ ≤ ‖J‖ * ‖B f‖ := J.le_opNorm _
    _ ≤ 1 * (‖B‖ * ‖f‖) := mul_le_mul hJ (B.le_opNorm f) (norm_nonneg _) zero_le_one
    _ ≤ ‖B‖ * ‖J f‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hf (norm_nonneg _)

/-- Intertwining passes to powers. -/
theorem intertwine_pow (J : E →L[ℝ] F) {A : F →L[ℝ] F} {B : E →L[ℝ] E}
    (hAB : A.comp J = J.comp B) (n : ℕ) : (A ^ n).comp J = J.comp (B ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc, hAB, ← ContinuousLinearMap.comp_assoc, ih,
        ContinuousLinearMap.comp_assoc]

end Transfer

section Restriction

variable {M : Type*} [MeasurableSpace M] {ρ μ : Measure M} [IsFiniteMeasure μ]
  [IsFiniteMeasure ρ]

omit [IsFiniteMeasure μ] [IsFiniteMeasure ρ] in
theorem memLp_top_of_ac (hμρ : μ ≪ ρ) (f : Lp ℝ ∞ ρ) : MemLp (f : M → ℝ) ∞ μ :=
  memLp_top_of_bound ((Lp.aestronglyMeasurable f).mono_ac hμρ) ‖f‖
    (hμρ.ae_le (StandingHypothesis.lp_infinity_ae_norm_le f))

/-- The restriction `J : L∞(ρ) → L∞(μ)` for `μ ≪ ρ`. -/
def restrictInf (hμρ : μ ≪ ρ) : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_top_of_ac hμρ f).toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hμρ.ae_le (Lp.coeFn_add f g))
      map_smul' := by
        intro r f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hμρ.ae_le (Lp.coeFn_smul r f)) }
    1 (by
      intro f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      refine (Lp.norm_le_of_ae_bound (f := (memLp_top_of_ac hμρ f).toLp _) (C := ‖f‖)
        (norm_nonneg f) ?_).trans_eq (by simp)
      filter_upwards [(memLp_top_of_ac hμρ f).coeFn_toLp,
        hμρ.ae_le (StandingHypothesis.lp_infinity_ae_norm_le f)] with x hx hb
      rw [hx]
      exact hb)

omit [IsFiniteMeasure ρ] in
theorem restrictInf_ae (hμρ : μ ≪ ρ) (f : Lp ℝ ∞ ρ) : restrictInf hμρ f =ᵐ[μ] f :=
  (memLp_top_of_ac hμρ f).coeFn_toLp

omit [IsFiniteMeasure ρ] in
theorem norm_restrictInf_le (hμρ : μ ≪ ρ) : ‖restrictInf hμρ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Every `μ`-class lifts to a `ρ`-class of no larger norm. -/
theorem exists_lift (hμρ : μ ≪ ρ) (g : Lp ℝ ∞ μ) :
    ∃ f : Lp ℝ ∞ ρ, ‖f‖ ≤ ‖g‖ ∧ restrictInf hμρ f = g := by
  set S : Set M := {y | ‖g y‖ ≤ ‖g‖}
  have hS : MeasurableSet S :=
    measurableSet_le (Lp.stronglyMeasurable g).measurable.norm measurable_const
  set g' : M → ℝ := S.indicator g
  have hg'm : StronglyMeasurable g' := (Lp.stronglyMeasurable g).indicator hS
  have hbound (y : M) : ‖g' y‖ ≤ ‖g‖ := by
    by_cases hy : y ∈ S
    · simp only [g', Set.indicator_of_mem hy]; exact hy
    · simp only [g', Set.indicator_of_notMem hy, norm_zero]; exact norm_nonneg _
  have hmem : MemLp g' ∞ ρ := memLp_top_of_bound hg'm.aestronglyMeasurable _ (ae_of_all _ hbound)
  have hgg' : g' =ᵐ[μ] g := by
    filter_upwards [StandingHypothesis.lp_infinity_ae_norm_le g] with y hy
    exact Set.indicator_of_mem (s := S) hy _
  refine ⟨hmem.toLp g', ?_, ?_⟩
  · refine (Lp.norm_le_of_ae_bound (f := hmem.toLp g') (C := ‖g‖) (norm_nonneg g) ?_).trans_eq
      (by simp)
    filter_upwards [hmem.coeFn_toLp] with y hy
    rw [hy]
    exact hbound y
  · apply Lp.ext
    filter_upwards [restrictInf_ae hμρ (hmem.toLp g'), hμρ.ae_le hmem.coeFn_toLp, hgg']
      with y h1 h2 h3
    rw [h1, h2, h3]

end Restriction

end

end ConditionedStableLaws.RestrictLp
