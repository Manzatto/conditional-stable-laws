import ConditionedStableLaws.PathMixing

/-!
# Consecutive observation blocks and separated-cluster mixing

A block contains its first observation and an arbitrary finite list of internal
observation gaps. Only the gaps outside the blocks are required to be long.
The exact operator regrouping and the error estimate retain every block norm.
The elapsed time in the survival denominator includes the internal block gaps.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace ConditionedStableLaws.ClusterMixing
open ConditionalMixing

/-- A nonempty consecutive cluster, with gaps measured from its first observation. -/
structure Block (A : Type*) where
  first : A
  internal : List (ℕ × A)

/-- Expand the cluster partition into the original chronological observations. -/
def flatten {A : Type*} (w : List (ℕ × Block A)) : List (ℕ × A) :=
  w.flatMap (fun p => (p.1, p.2.first) :: p.2.internal)

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The block operator: first observation followed by its internal transition/observation word. -/
def blockOperator (Q : E →L[ℝ] E) (obs : A → E →L[ℝ] E) (b : Block A) : E →L[ℝ] E :=
  obs b.first * operatorWord (fun n => Q ^ n) (b.internal.map (fun p => (p.1, obs p.2)))

def blockObservations (Q : E →L[ℝ] E) (obs : A → E →L[ℝ] E)
    (w : List (ℕ × Block A)) : List (ℕ × (E →L[ℝ] E)) :=
  w.map (fun p => (p.1, blockOperator Q obs p.2))

/-- Exact regrouping, including arbitrary internal gap lengths. -/
theorem operatorWord_flatten (Q : E →L[ℝ] E) (obs : A → E →L[ℝ] E)
    (w : List (ℕ × Block A)) :
    operatorWord (fun n => Q ^ n) ((flatten w).map (fun p => (p.1, obs p.2))) =
      operatorWord (fun n => Q ^ n) (blockObservations Q obs w) := by
  induction w with
  | nil => simp [flatten, blockObservations, operatorWord]
  | cons p w ih =>
      rcases p with ⟨n, b⟩
      simp only [flatten, List.flatMap_cons, List.cons_append, List.map_cons,
        List.map_append, operatorWord, operatorWord_append] at *
      rw [ih]
      simp only [blockObservations, List.map_cons, operatorWord, blockOperator]
      simp only [mul_assoc]

/-- Inserting terminal survival commutes with exact block regrouping. -/
theorem operatorWord_flatten_terminal (Q : E →L[ℝ] E) (obs : A → E →L[ℝ] E)
    (w : List (ℕ × Block A)) (t : ℕ) :
    operatorWord (fun n => Q ^ n)
        (((flatten w).map (fun p => (p.1, obs p.2))) ++ [(t, 1)]) =
      operatorWord (fun n => Q ^ n) (blockObservations Q obs w ++ [(t, 1)]) := by
  rw [operatorWord_append, operatorWord_append, operatorWord_flatten]

/-- Internal-gap uniformity: powers are bounded, but internal gaps need not
satisfy the long-gap condition used between clusters. -/
theorem blockOperator_norm_le (Q : E →L[ℝ] E) (obs : A → E →L[ℝ] E)
    (b : Block A) (U : ℝ) (hU : 1 ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ U) :
    ‖blockOperator Q obs b‖ ≤ ‖obs b.first‖ * U ^ b.internal.length *
      ((b.internal.map fun p => ‖obs p.2‖).prod) := by
  have hU0 : 0 ≤ U := le_trans zero_le_one hU
  have hp (n : ℕ) : ‖Q ^ n‖ ≤ U := by
    cases n with
    | zero => exact ContinuousLinearMap.norm_id_le.trans hU
    | succ n => exact hQ (n + 1) (by omega)
  have hb := operatorWord_norm_le (fun n => Q ^ n)
    (b.internal.map (fun p => (p.1, obs p.2))) U hU0 (fun p _ => hp p.1)
  calc
    _ ≤ ‖obs b.first‖ * ‖operatorWord (fun n => Q ^ n)
        (b.internal.map (fun p => (p.1, obs p.2)))‖ := norm_mul_le _ _
    _ ≤ ‖obs b.first‖ * (U ^ b.internal.length *
        (b.internal.map fun p => ‖obs p.2‖).prod) := by
      apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simpa only [List.length_map, observationNorms, List.map_map, Function.comp_def] using hb
    _ = _ := by ring

/-- Uniform block norm when observations are contractions (in particular,
indicator multiplication operators). -/
theorem blockOperator_norm_le_pow (Q : E →L[ℝ] E) (obs : A → E →L[ℝ] E)
    (b : Block A) (U : ℝ) (hU : 1 ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ U)
    (hfirst : ‖obs b.first‖ ≤ 1) (hinternal : ∀ p ∈ b.internal, ‖obs p.2‖ ≤ 1) :
    ‖blockOperator Q obs b‖ ≤ U ^ b.internal.length := by
  have hprod : (b.internal.map fun p => ‖obs p.2‖).prod ≤ 1 := by
    have hp : ∀ v : List (ℕ × A), (∀ p ∈ v, ‖obs p.2‖ ≤ 1) →
        (v.map fun p => ‖obs p.2‖).prod ≤ 1 := by
      intro v
      induction v with
      | nil => simp
      | cons p v ih =>
          intro hv
          have ht := ih (fun q hq => hv q (by simp [hq]))
          have hh := hv p (by simp)
          simpa only [List.map_cons, List.prod_cons, mul_one] using
            mul_le_mul hh ht (List.prod_nonneg (fun a ha => by
              rcases List.mem_map.mp ha with ⟨q, hq, rfl⟩; exact norm_nonneg _)) zero_le_one
    exact hp b.internal hinternal
  have hU0 : 0 ≤ U := le_trans zero_le_one hU
  refine (blockOperator_norm_le Q obs b U hU hQ).trans ?_
  calc
    _ ≤ 1 * U ^ b.internal.length * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfirst (pow_nonneg hU0 _)) hprod
        (List.prod_nonneg (fun a ha => by
          rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩; exact norm_nonneg _))
        (by positivity)
    _ = _ := by ring

/-- Uniform product of block norms, retaining the sharper product in the
main estimate until this optional contraction bound is applied. -/
theorem blockObservationNorms_le (Q : E →L[ℝ] E) (obs : A → E →L[ℝ] E)
    (w : List (ℕ × Block A)) (U : ℝ) (hU : 1 ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ U)
    (hobs : ∀ p ∈ w, ‖obs p.2.first‖ ≤ 1 ∧
      ∀ q ∈ p.2.internal, ‖obs q.2‖ ≤ 1) :
    observationNorms (blockObservations Q obs w) ≤
      U ^ (w.map fun p => p.2.internal.length).sum := by
  induction w with
  | nil => simp [blockObservations, observationNorms]
  | cons p w ih =>
      have hp := hobs p (by simp)
      have ht := ih (fun p hp => hobs p (by simp [hp]))
      simp only [blockObservations, List.map_cons, observationNorms, List.prod_cons,
        List.sum_cons, pow_add] at *
      exact mul_le_mul (blockOperator_norm_le_pow Q obs p.2 U hU hQ hp.1 hp.2) ht
        (observationNorms_nonneg (blockObservations Q obs w))
        (pow_nonneg (le_trans zero_le_one hU) _)

/-- General denominator time: block operators already contain internal elapsed
time, so the denominator exponent must not be computed from external gaps alone. -/
theorem conditional_word_mixing_at_time (Q : E →L[ℝ] E) (μ : E →L[ℝ] ℝ)
    (η one : E) (ev : E →L[ℝ] ℝ) (hone : μ one = 1) (ha : 0 < ev η)
    (w : List (ℕ × (E →L[ℝ] E))) (t m N : ℕ) (U C θ : ℝ)
    (hU : 1 ≤ U) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne μ η‖ ≤ U) (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ U)
    (hgap : ∀ n, 1 ≤ n → ‖Q ^ n - rankOne μ η‖ ≤ C * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t)
    (hN : 1 ≤ N) (hNm : m ≤ N)
    (hsmall : ‖ev‖ * C * θ ^ m * ‖one‖ ≤ ev η / 2) :
    |ev (operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) one) /
        ev ((Q ^ N) one) - (w.map fun p => μ (p.2 η)).prod| ≤
      (2 / ev η) * ‖ev‖ * C * ‖one‖ *
        ((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖μ‖ * ‖η‖) ^ w.length) *
        θ ^ m * observationNorms w := by
  let c : ℝ := (w.map fun p => μ (p.2 η)).prod
  let B : ℝ := (w.length + 1 : ℝ) * C * U ^ (w.length + 1) * θ ^ m *
    observationNorms w * ‖one‖
  let D : ℝ := ‖ev‖ * C * θ ^ m * ‖one‖
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hden := spectral_denominator_error Q μ η one ev hone N m C θ
    hC hθ0 hθ1 (hgap N hN) hNm
  have hword : ‖operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) one - c • η‖ ≤ B := by
    simpa only [hone, mul_one] using
      operatorWord_mixing_estimate Q μ η one w t m U C θ
        hU hC hθ0 hθ1 hP hQ hgap htimes ht
  have hnum : |ev (operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) one) - ev η * c| ≤
      ‖ev‖ * B := by
    have heq : ev (operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) one) - ev η * c =
        ev (operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) one - c • η) := by
      simp only [map_sub, map_smul, smul_eq_mul, mul_comm]
    rw [heq]
    exact (ev.le_opNorm _).trans (mul_le_mul_of_nonneg_left hword (norm_nonneg ev))
  have hratio := quotient_error_bound
    (ev (operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) one))
    (ev ((Q ^ N) one)) (ev η) c (‖ev‖ * B) D ha
    (hden.trans hsmall) hnum hden
  have hc := rankOne_coefficient_bound μ η w
  calc
    _ ≤ (2 / ev η) * (‖ev‖ * B + |c| * D) := hratio
    _ ≤ (2 / ev η) * (‖ev‖ * B +
        ((‖μ‖ * ‖η‖) ^ w.length * observationNorms w) * D) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc hD0)) (by positivity)
    _ = _ := by dsimp [B, D]; ring

/-- Quantitative separated-cluster factorization, with every block norm retained and the correct
total-time survival denominator. -/
theorem cluster_operator_mixing (Q : E →L[ℝ] E) (obs : A → E →L[ℝ] E)
    (μ : E →L[ℝ] ℝ) (η one : E) (ev : E →L[ℝ] ℝ)
    (hone : μ one = 1) (ha : 0 < ev η)
    (w : List (ℕ × Block A)) (t m : ℕ) (U C θ : ℝ)
    (hU : 1 ≤ U) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne μ η‖ ≤ U) (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ U)
    (hgap : ∀ n, 1 ≤ n → ‖Q ^ n - rankOne μ η‖ ≤ C * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t)
    (hsmall : ‖ev‖ * C * θ ^ m * ‖one‖ ≤ ev η / 2) :
    |ev (operatorWord (fun n => Q ^ n)
        (((flatten w).map (fun p => (p.1, obs p.2))) ++ [(t, 1)]) one) /
        ev ((Q ^ (((flatten w).map Prod.fst).sum + t)) one) -
          (w.map fun p => μ (blockOperator Q obs p.2 η)).prod| ≤
      (2 / ev η) * ‖ev‖ * C * ‖one‖ *
        ((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖μ‖ * ‖η‖) ^ w.length) *
        θ ^ m * observationNorms (blockObservations Q obs w) := by
  rw [operatorWord_flatten_terminal]
  have hb := conditional_word_mixing_at_time Q μ η one ev hone ha
    (blockObservations Q obs w) t m (((flatten w).map Prod.fst).sum + t) U C θ
    hU hC hθ0 hθ1 hP hQ hgap (by
      intro p hp
      rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
      exact htimes q hq) ht (by omega) (by omega) hsmall
  simpa only [blockObservations, List.map_map, Function.comp_def, List.length_map] using hb

end ConditionedStableLaws.ClusterMixing

namespace ConditionedStableLaws.CanonicalChain
open ClusterMixing ConditionalMixing StandingHypothesis PathMixing
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  (C : CanonicalChain M) {ρ : Measure M}

/-- Exact block representation of a survival-conditioned path product. The initial unit observation
represents the one smoothing step needed for pointwise evaluation on L∞. All internal cluster gaps
count toward survival. -/
theorem integral_conditioned_blocks_operator (h : HypothesisH ρ C.toKilledKernel)
    (c : ℝ) (hc : c ≠ 0) (one : Lp ℝ ∞ ρ)
    (hone : one =ᵐ[ρ] fun _ => (1 : ℝ)) (x : M)
    (w : List (ℕ × Block (Lp ℝ ∞ ρ))) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfm : ∀ p ∈ flatten w, Measurable (f p.2))
    (hfb : ∀ p ∈ flatten w, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ flatten w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2) (t : ℕ) :
    (∫ ω, (pathProduct (liftObservations
        ((1, fun _ => 1) :: (flatten w).map (fun p => (p.1, f p.2)))) ω).toReal
      ∂C.conditionedMeasure x (((flatten w).map Prod.fst).sum + t + 1)) =
      h.stepEvaluation c x
        (operatorWord (fun n => (c • h.transitionOperator) ^ n)
          (blockObservations (c • h.transitionOperator) (lpMultiplication ρ) w ++ [(t, 1)]) one) /
      h.stepEvaluation c x
        (((c • h.transitionOperator) ^ (((flatten w).map Prod.fst).sum + t)) one) := by
  rw [C.integral_conditioned_pathProduct_lp h x (flatten w) f hfm hfb hrep t]
  symm
  rw [← operatorWord_flatten_terminal]
  change h.stepEvaluation c x
    (operatorWord (fun n => (c • h.transitionOperator) ^ n)
      (multiplicationObservations ρ (flatten w) ++ [(t, 1)]) one) / _ = _
  rw [h.stepEvaluation_operatorWord, h.stepEvaluation_power]
  have hn : kernelIterate c C.toKilledKernel 1
      (StandingHypothesis.kernelWord c C.toKilledKernel (flatten w)
        (kernelIterate c C.toKilledKernel t one)) x =
      kernelIterate c C.toKilledKernel 1
        (StandingHypothesis.kernelWord c C.toKilledKernel (flatten w)
          (kernelIterate c C.toKilledKernel t (fun _ => 1))) x :=
    h.kernelIterate_succ_congr c 0
      (h.kernelWord_congr_ae c (flatten w) (h.kernelIterate_congr_ae c t hone)) x
  have hd : kernelIterate c C.toKilledKernel
      (((flatten w).map Prod.fst).sum + t + 1) one x =
      kernelIterate c C.toKilledKernel (((flatten w).map Prod.fst).sum + t + 1)
        (fun _ => 1) x :=
    h.kernelIterate_succ_congr c (((flatten w).map Prod.fst).sum + t) hone x
  rw [hn, hd, kernelCorrelation_ratio_normalization c hc,
    kernelIterate_one_eq_mass]
  rfl

/-- Conditioned-path cluster mixing. The leading coefficients are `μ(Bℓ η)` and the error retains
the product of the block norms. -/
theorem conditioned_cluster_mixing (h : HypothesisH ρ C.toKilledKernel)
    (c : ℝ) (hc : c ≠ 0) (μ : Lp ℝ ∞ ρ →L[ℝ] ℝ) (η one : Lp ℝ ∞ ρ) (x : M)
    (hone : μ one = 1) (hone_rep : one =ᵐ[ρ] fun _ => (1 : ℝ))
    (ha : 0 < h.stepEvaluation c x η)
    (w : List (ℕ × Block (Lp ℝ ∞ ρ))) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfm : ∀ p ∈ flatten w, Measurable (f p.2))
    (hfb : ∀ p ∈ flatten w, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ flatten w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2)
    (t m : ℕ) (U A θ : ℝ)
    (hU : 1 ≤ U) (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne μ η‖ ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖(c • h.transitionOperator) ^ n‖ ≤ U)
    (hgap : ∀ n, 1 ≤ n → ‖(c • h.transitionOperator) ^ n - rankOne μ η‖ ≤ A * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t)
    (hsmall : ‖h.stepEvaluation c x‖ * A * θ ^ m * ‖one‖ ≤ h.stepEvaluation c x η / 2) :
    |(∫ ω, (pathProduct (liftObservations
        ((1, fun _ => 1) :: (flatten w).map (fun p => (p.1, f p.2)))) ω).toReal
      ∂C.conditionedMeasure x (((flatten w).map Prod.fst).sum + t + 1)) -
        (w.map fun p => μ (blockOperator (c • h.transitionOperator)
          (lpMultiplication ρ) p.2 η)).prod| ≤
      (2 / h.stepEvaluation c x η) * ‖h.stepEvaluation c x‖ * A * ‖one‖ *
        ((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖μ‖ * ‖η‖) ^ w.length) *
        θ ^ m * observationNorms
          (blockObservations (c • h.transitionOperator) (lpMultiplication ρ) w) := by
  rw [C.integral_conditioned_blocks_operator h c hc one hone_rep x w f hfm hfb hrep t]
  rw [← operatorWord_flatten_terminal]
  exact cluster_operator_mixing (c • h.transitionOperator) (lpMultiplication ρ)
    μ η one (h.stepEvaluation c x) hone ha w t m U A θ
    hU hA hθ0 hθ1 hP hQ hgap htimes ht hsmall

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.ClusterMixing
open ConditionalMixing
variable {M : Type*} [MeasurableSpace M] {ρ : Measure M}

/-- Every observation in a cluster occurs in the expanded word. -/
theorem mem_flatten_first (w : List (ℕ × Block (Lp ℝ ∞ ρ)))
    (p : ℕ × Block (Lp ℝ ∞ ρ)) (hp : p ∈ w) : (p.1, p.2.first) ∈ flatten w := by
  apply List.mem_flatMap.mpr
  exact ⟨p, hp, by simp⟩

theorem mem_flatten_internal (w : List (ℕ × Block (Lp ℝ ∞ ρ)))
    (p : ℕ × Block (Lp ℝ ∞ ρ)) (hp : p ∈ w) (q : ℕ × Lp ℝ ∞ ρ)
    (hq : q ∈ p.2.internal) : q ∈ flatten w := by
  apply List.mem_flatMap.mpr
  exact ⟨p, hp, by simp [hq]⟩

/-- Bounded representatives give contraction multiplication operators. -/
theorem multiplication_norm_le_one_of_rep (a : Lp ℝ ∞ ρ) (f : M → ℝ≥0∞)
    (hfb : ∀ y, f y ≤ 1) (hrep : (fun y => (f y).toReal) =ᵐ[ρ] a) :
    ‖lpMultiplication ρ a‖ ≤ 1 := by
  refine (lpMultiplication_norm_le ρ a).trans ?_
  have hb : ∀ᵐ y ∂ρ, ‖a y‖ ≤ 1 := by
    filter_upwards [hrep] with y hy
    rw [← hy, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (hfb y)).trans_eq (by simp)
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable a)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hb)).trans_eq (by simp)

/-- Uniformity in all target sets and all internal time gaps follows from the block bound, with
exponent equal to the number of internal observations. -/
theorem blockNorms_le_of_representatives (Q : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ)
    (w : List (ℕ × Block (Lp ℝ ∞ ρ))) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfb : ∀ p ∈ flatten w, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ flatten w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2)
    (U : ℝ) (hU : 1 ≤ U) (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ U) :
    observationNorms (blockObservations Q (lpMultiplication ρ) w) ≤
      U ^ (w.map fun p => p.2.internal.length).sum := by
  apply blockObservationNorms_le Q (lpMultiplication ρ) w U hU hQ
  intro p hp
  constructor
  · exact multiplication_norm_le_one_of_rep p.2.first (f p.2.first)
      (hfb _ (mem_flatten_first w p hp)) (hrep _ (mem_flatten_first w p hp))
  · intro q hq
    exact multiplication_norm_le_one_of_rep q.2 (f q.2)
      (hfb _ (mem_flatten_internal w p hp q hq)) (hrep _ (mem_flatten_internal w p hp q hq))

end ConditionedStableLaws.ClusterMixing

namespace ConditionedStableLaws.ClusterMixing

/-- The number of observations is the number of clusters plus their internal
observations, so the uniform block bound depends only on the original order. -/
theorem length_flatten {A : Type*} (w : List (ℕ × Block A)) :
    (flatten w).length = w.length + (w.map fun p => p.2.internal.length).sum := by
  induction w with
  | nil => simp [flatten]
  | cons p w ih =>
      simp only [flatten, List.flatMap_cons, List.length_append, List.length_cons,
        List.map_cons, List.sum_cons] at *
      omega

/-- The total elapsed observation time includes both external and internal gaps, as required by the
survival normalization. -/
theorem sum_gaps_flatten {A : Type*} (w : List (ℕ × Block A)) :
    ((flatten w).map Prod.fst).sum =
      (w.map Prod.fst).sum + (w.map fun p => (p.2.internal.map Prod.fst).sum).sum := by
  induction w with
  | nil => simp [flatten]
  | cons p w ih =>
      simp only [flatten, List.flatMap_cons, List.cons_append, List.map_cons,
        List.map_append, List.sum_cons, List.sum_append] at *
      omega

end ConditionedStableLaws.ClusterMixing
