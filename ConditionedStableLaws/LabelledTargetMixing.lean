import ConditionedStableLaws.ChainConfigurationBounds

/-!
# Separated mixing for labelled target events

Labels retain their measurable representatives even when two different sets determine the same L∞
class. One initial transition justifies all point evaluations. The conclusion concerns canonical
path events.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 800000
namespace ConditionedStableLaws.LabelledTargetMixing
variable {M I : Type*} [MeasurableSpace M] (ρ : Measure M) [IsFiniteMeasure ρ]

/-- The L∞ indicator class of a measurable target. -/
def targetVector (U : Set M) (hU : MeasurableSet U) : Lp ℝ ∞ ρ :=
  indicatorConstLp ∞ hU (measure_ne_top ρ U) 1

theorem targetVector_ae (U : Set M) (hU : MeasurableSet U) :
    targetVector ρ U hU =ᵐ[ρ] U.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn

theorem targetVector_norm_le (U : Set M) (hU : MeasurableSet U) :
    ‖targetVector ρ U hU‖ ≤ 1 := by
  simpa only [targetVector, ENNReal.toReal_top, div_zero, Real.rpow_zero, mul_one, norm_one]
    using (norm_indicatorConstLp_le (p := ∞) (hs := hU) (hμs := measure_ne_top ρ U) (c := (1 : ℝ)))

def setWord (A : I → Set M) (w : List (ℕ × I)) : List (ℕ × Set M) :=
  w.map (fun p => (p.1, A p.2))

theorem measurable_setWord (A : I → Set M) (hA : ∀ j, MeasurableSet (A j))
    (w : List (ℕ × I)) : ∀ p ∈ setWord A w, MeasurableSet p.2 := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, _, rfl⟩
  exact hA _

end ConditionedStableLaws.LabelledTargetMixing

namespace ConditionedStableLaws.StandingHypothesis
open PathMixing
variable {M I : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M]
  [BorelSpace M] {ρ : Measure M} {K : KilledKernel M}

/-- Labelled representative bridge; injectivity of the assignment to L∞
classes is unnecessary. -/
theorem HypothesisH.realKernelWord_labelled_ae (h : HypothesisH ρ K)
    (w : List (ℕ × I)) (v : I → Lp ℝ ∞ ρ) (f : I → M → ℝ≥0∞)
    (hf : ∀ j, (fun y => (f j y).toReal) =ᵐ[ρ] v j) (g : M → ℝ) :
    realKernelWord K (w.map (fun p => (p.1, f p.2))) g =ᵐ[ρ]
      StandingHypothesis.kernelWord 1 K (w.map (fun p => (p.1, v p.2))) g := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, j⟩
      apply h.kernelIterate_congr_ae
      filter_upwards [hf j, ih] with y hy hw
      rw [hy, hw]

end ConditionedStableLaws.StandingHypothesis

namespace ConditionedStableLaws.CanonicalChain
open PathMixing StandingHypothesis ConditionalMixing LabelledTargetMixing
variable {M I : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M]
  [BorelSpace M] {ρ : Measure M} (C : CanonicalChain M)

/-- The exact path-event ratio corresponding to a labelled operator word.
The first elapsed gap is `n+1`, with its first step reserved for smoothing. -/
theorem conditioned_labelled_event_real_lp (h : HypothesisH ρ C.toKilledKernel)
    (x : M) (n : ℕ) (j : I) (w : List (ℕ × I))
    (A : I → Set M) (hA : ∀ j, MeasurableSet (A j))
    (v : I → Lp ℝ ∞ ρ) (hrep : ∀ j, v j =ᵐ[ρ] (A j).indicator (fun _ => (1 : ℝ))) (t : ℕ) :
    (C.conditionedMeasure x (n + (w.map Prod.fst).sum + t + 1)).real
        (pathEvent (setWord A ((n+1,j)::w))) =
      kernelIterate 1 C.toKilledKernel 1
        (StandingHypothesis.kernelWord 1 C.toKilledKernel
          (((n,j)::w).map (fun p => (p.1, v p.2)))
          (kernelIterate 1 C.toKilledKernel t (fun _ => 1))) x /
        ((C.killedTransition ^ (n + (w.map Prod.fst).sum + t + 1)) x).real univ := by
  have he := C.conditioned_multitime_event_real x (setWord A ((n+1,j)::w))
    (measurable_setWord A hA _) t
  have htime : totalTime (indicatorObservations (setWord A ((n+1,j)::w))) + t =
      n + (w.map Prod.fst).sum + t + 1 := by
    simp [totalTime, indicatorObservations, setWord, List.map_map, Function.comp_def]
    change n + 1 + (w.map Prod.fst).sum + t = _
    omega
  rw [htime] at he
  rw [he]
  congr 1
  let f : I → M → ℝ≥0∞ := fun j => (A j).indicator (fun _ => 1)
  have hf (i : I) : (fun y => (f i y).toReal) =ᵐ[ρ] v i := by
    filter_upwards [(hrep i).symm] with y hy
    rw [← hy]
    by_cases hyA : y ∈ A i <;> simp [f, hyA]
  have ht := h.realKernelWord_labelled_ae ((n,j)::w) v f hf
    (kernelIterate 1 C.toKilledKernel t (fun _ => 1))
  have hh := h.kernelIterate_succ_congr 1 0 ht x
  simpa only [setWord, indicatorObservations, List.map_cons, List.map_map,
    Function.comp_def, realKernelWord, kernelIterate, one_mul, f] using hh

/-- Separated-target mixing for arbitrary labels and target sets. The error constant is independent
of their measures and representatives. -/
theorem conditioned_labelled_event_mixing (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition)
    (μ : Measure M) (hμρ : μ ≪ ρ)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (η one : Lp ℝ ∞ ρ) (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal)
    (x : M) (hone : mean one = 1) (hone_rep : one =ᵐ[ρ] fun _ => (1 : ℝ))
    (ha : 0 < h.stepEvaluation (d.rate.toReal)⁻¹ x η)
    (n : ℕ) (j : I) (w : List (ℕ × I))
    (A : I → Set M) (hA : ∀ j, MeasurableSet (A j))
    (t m : ℕ) (U B θ : ℝ) (hU : 1 ≤ U) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne mean η‖ ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n‖ ≤ U)
    (hgap : ∀ n, 1 ≤ n →
      ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n-rankOne mean η‖ ≤ B*θ^n)
    (htimes : ∀ p ∈ ((n,j)::w), 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t)
    (hsmall : ‖h.stepEvaluation (d.rate.toReal)⁻¹ x‖*B*θ^m*‖one‖ ≤
      h.stepEvaluation (d.rate.toReal)⁻¹ x η / 2) :
    |(C.conditionedMeasure x (n+(w.map Prod.fst).sum+t+1)).real
        (pathEvent (setWord A ((n+1,j)::w))) -
      (((n,j)::w).map fun p => (μ.withDensity d.weight).real (A p.2)).prod| ≤
      (2 / h.stepEvaluation (d.rate.toReal)⁻¹ x η)*‖h.stepEvaluation (d.rate.toReal)⁻¹ x‖*
        B*‖one‖*((w.length+2 : ℝ)*U^(w.length+2)+(‖mean‖*‖η‖)^(w.length+1))*θ^m := by
  let : IsProbabilityMeasure ρ := h.reference_probability
  let v : I → Lp ℝ ∞ ρ := fun i => targetVector ρ (A i) (hA i)
  have hv := fun i => targetVector_ae ρ (A i) (hA i)
  rw [C.conditioned_labelled_event_real_lp h x n j w A hA v hv t]
  have hcoef (i : I) : mean (lpMultiplication ρ (v i) η) = (μ.withDensity d.weight).real (A i) := by
    apply weighted_target_mean (K := C.toKilledKernel) d μ hμρ mean hmean (A i) (hA i)
    filter_upwards [lpMultiplication_ae ρ (v i) η, hv i, hη] with y hm hy hηy
    rw [hm, hy, hηy]
    by_cases hyA : y ∈ A i <;> simp [hyA]
  have hc : (d.rate.toReal)⁻¹ ≠ 0 := inv_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨d.rate_ne_zero, d.rate_ne_top⟩)
  have hb := h.kernel_mixing (d.rate.toReal)⁻¹ hc mean η one x hone hone_rep ha
    (((n,j)::w).map (fun p => (p.1, v p.2))) t m U B θ hU hB hθ0 hθ1 hP hQ hgap
    (by intro p hp; rcases List.mem_map.mp hp with ⟨q,hq,rfl⟩; exact htimes q hq) ht hsmall
  have hprodAll (z : List (ℕ × I)) : (z.map fun p => ‖v p.2‖).prod ≤ 1 := by
    induction z with
    | nil => simp
    | cons p z ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (mul_le_mul_of_nonneg_left ih (norm_nonneg _)).trans
          (by simpa only [mul_one] using targetVector_norm_le ρ (A p.2) (hA p.2))
  have hprod := hprodAll ((n,j)::w)
  simp only [List.map_cons] at hprod
  simp only [List.map_map, Function.comp_def, List.length_map, List.length_cons,
    List.map_cons, List.sum_cons, hcoef] at hb
  have hlen : w.length + 1 + 1 = w.length + 2 := by omega
  have hh := hb.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  norm_num only [mul_one, hlen, Nat.cast_add, Nat.cast_one, add_assoc, List.map_cons] at hh ⊢
  exact hh

end ConditionedStableLaws.CanonicalChain
