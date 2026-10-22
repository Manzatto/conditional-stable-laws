import ConditionedStableLaws.StrongFeller
import ConditionedStableLaws.ConditionalMixing
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# State-space mixing with pointwise evaluation

One application of the killed transition kernel is a bounded linear functional on L∞, by the L¹
density in (H1). This evaluates the operator expansion at a specified state without point evaluation
of an L∞ equivalence class. Operator words are identified with nested kernel integrals.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace ConditionedStableLaws

namespace StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M]
  [BorelSpace M] {ρ : Measure M} {K : KilledKernel M}

/-- Point evaluation after one kernel step, as a bounded linear functional on L∞ classes. Scaling by
`c` covers the normalized operator. -/
def HypothesisH.stepEvaluation (h : HypothesisH ρ K) (c : ℝ) (x : M) :
    Lp ℝ ∞ ρ →L[ℝ] ℝ := c • integralPairing ρ (h.density x)

theorem HypothesisH.stepEvaluation_apply (h : HypothesisH ρ K)
    (c : ℝ) (x : M) (f : Lp ℝ ∞ ρ) :
    h.stepEvaluation c x f = c * ∫ y, f y ∂K.kernel x := by
  rw [h.kernel_integral_eq]
  change c * integralPairing ρ (h.density x) f = _
  rw [integralPairing_apply]

/-- Iterated (possibly normalized) transition integrals. -/
def kernelIterate (c : ℝ) (K : KilledKernel M) : ℕ → (M → ℝ) → M → ℝ
  | 0, f => f
  | n + 1, f => fun x => c * ∫ y, kernelIterate c K n f y ∂K.kernel x

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem killedKernel_power_isFinite (K : KilledKernel M) (n : ℕ) :
    IsFiniteKernel (K.kernel ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel M M); infer_instance
  | succ n ih =>
      have := ih
      rw [pow_succ]
      change IsFiniteKernel ((K.kernel ^ n) ∘ₖ K.kernel)
      infer_instance

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The iterated constant-one integral is the finite-time survival mass of the killed transition
kernel. -/
theorem kernelIterate_one_eq_mass (K : KilledKernel M) (n : ℕ) (x : M) :
    kernelIterate 1 K n (fun _ => 1) x = ((K.kernel ^ n) x).real Set.univ := by
  have haux : ∀ n : ℕ, ∀ x : M,
      kernelIterate 1 K n (fun _ => 1) x = ∫ y, (1 : ℝ) ∂(K.kernel ^ n) x := by
    intro n
    induction n with
    | zero =>
        intro x
        change 1 = ∫ _, (1 : ℝ) ∂Measure.dirac x
        simp
    | succ n ih =>
        intro x
        have := killedKernel_power_isFinite K n
        simp only [kernelIterate, one_mul, ih, pow_succ]
        exact (Kernel.integral_comp (η := K.kernel ^ n) (κ := K.kernel)
          (a := x) (integrable_const (1 : ℝ))).symm
  rw [haux]
  simp

/-- Null-set changes of input do not change any positive-time iterate, because
every transition measure is absolutely continuous with respect to `ρ`. -/
theorem HypothesisH.kernelIterate_congr_ae (h : HypothesisH ρ K) (c : ℝ)
    (n : ℕ) {f g : M → ℝ} (hfg : f =ᵐ[ρ] g) :
    kernelIterate c K n f =ᵐ[ρ] kernelIterate c K n g := by
  induction n with
  | zero => exact hfg
  | succ n ih =>
      apply Eventually.of_forall
      intro x
      simp only [kernelIterate]
      congr 1
      exact integral_congr_ae ((h.absolutelyContinuous x).ae_eq ih)

theorem HypothesisH.kernelIterate_succ_congr (h : HypothesisH ρ K) (c : ℝ)
    (n : ℕ) {f g : M → ℝ} (hfg : f =ᵐ[ρ] g) (x : M) :
    kernelIterate c K (n + 1) f x = kernelIterate c K (n + 1) g x := by
  simp only [kernelIterate]
  congr 1
  exact integral_congr_ae ((h.absolutelyContinuous x).ae_eq
    (h.kernelIterate_congr_ae c n hfg))

/-- Every power of the constructed L∞ operator has the iterated kernel integral as a representative,
including time zero. -/
theorem HypothesisH.operator_power_ae (h : HypothesisH ρ K) (c : ℝ)
    (n : ℕ) (f : Lp ℝ ∞ ρ) :
    ((c • h.transitionOperator) ^ n) f =ᵐ[ρ] kernelIterate c K n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      change (c • h.transitionOperator (((c • h.transitionOperator) ^ n) f)) =ᵐ[ρ] _
      refine (Lp.coeFn_smul c _).trans ?_
      filter_upwards [h.transitionOperator_ae (((c • h.transitionOperator) ^ n) f)] with x hx
      simp only [Pi.smul_apply, smul_eq_mul, hx, kernelIterate]
      congr 1
      exact integral_congr_ae ((h.absolutelyContinuous x).ae_eq ih)

/-- After the first step, the representative identity holds at every state. -/
theorem HypothesisH.stepEvaluation_power (h : HypothesisH ρ K) (c : ℝ)
    (n : ℕ) (f : Lp ℝ ∞ ρ) (x : M) :
    h.stepEvaluation c x (((c • h.transitionOperator) ^ n) f) =
      kernelIterate c K (n + 1) f x := by
  rw [h.stepEvaluation_apply]
  simp only [kernelIterate]
  congr 1
  exact integral_congr_ae ((h.absolutelyContinuous x).ae_eq (h.operator_power_ae c n f))

open ConditionalMixing

/-- Nested integrals for time/observable pairs, with measurable representatives of the L∞
observations. -/
def kernelWord (c : ℝ) (K : KilledKernel M) :
    List (ℕ × Lp ℝ ∞ ρ) → (M → ℝ) → M → ℝ
  | [], f => f
  | (n, g) :: w, f =>
      kernelIterate c K n (fun y => g y * kernelWord c K w f y)

theorem HypothesisH.kernelWord_congr_ae (h : HypothesisH ρ K) (c : ℝ)
    (w : List (ℕ × Lp ℝ ∞ ρ)) {f g : M → ℝ} (hfg : f =ᵐ[ρ] g) :
    kernelWord c K w f =ᵐ[ρ] kernelWord c K w g := by
  induction w with
  | nil => exact hfg
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      apply h.kernelIterate_congr_ae
      filter_upwards [ih] with y hy
      rw [hy]

/-- The operator word is the sequence of killed-kernel integrals, with multiplication by each
observed random variable in the correct order. -/
theorem HypothesisH.operatorWord_ae (h : HypothesisH ρ K) (c : ℝ)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (f : Lp ℝ ∞ ρ) :
    operatorWord (fun n => (c • h.transitionOperator) ^ n)
      (multiplicationObservations ρ w) f =ᵐ[ρ] kernelWord c K w f := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, g⟩
      change ((c • h.transitionOperator) ^ n)
        (lpMultiplication ρ g (operatorWord (fun n => (c • h.transitionOperator) ^ n)
          (multiplicationObservations ρ w) f)) =ᵐ[ρ] _
      refine (h.operator_power_ae c n _).trans ?_
      apply h.kernelIterate_congr_ae
      filter_upwards [lpMultiplication_ae ρ g
        (operatorWord (fun n => (c • h.transitionOperator) ^ n)
          (multiplicationObservations ρ w) f), ih] with y hmul hy
      rw [hmul, hy]

/-- Adding a final survival gap is represented by a final power with the identity
observation; this is the numerator in the conditional mixing formula. -/
theorem HypothesisH.operatorWord_terminal_ae (h : HypothesisH ρ K) (c : ℝ)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (t : ℕ) (f : Lp ℝ ∞ ρ) :
    operatorWord (fun n => (c • h.transitionOperator) ^ n)
      (multiplicationObservations ρ w ++ [(t, 1)]) f =ᵐ[ρ]
        kernelWord c K w (kernelIterate c K t f) := by
  rw [operatorWord_append]
  change operatorWord (fun n => (c • h.transitionOperator) ^ n)
    (multiplicationObservations ρ w) (((c • h.transitionOperator) ^ t) f) =ᵐ[ρ] _
  exact (h.operatorWord_ae c w _).trans
    (h.kernelWord_congr_ae c w (h.operator_power_ae c t f))

/-- Pointwise, at every state, the bounded evaluation of the full word equals the nested-kernel
correlation with one initial transition. -/
theorem HypothesisH.stepEvaluation_operatorWord (h : HypothesisH ρ K) (c : ℝ)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (t : ℕ) (f : Lp ℝ ∞ ρ) (x : M) :
    h.stepEvaluation c x (operatorWord (fun n => (c • h.transitionOperator) ^ n)
      (multiplicationObservations ρ w ++ [(t, 1)]) f) =
      kernelIterate c K 1 (kernelWord c K w (kernelIterate c K t f)) x := by
  rw [h.stepEvaluation_apply]
  simp only [kernelIterate]
  congr 1
  exact integral_congr_ae ((h.absolutelyContinuous x).ae_eq
    (h.operatorWord_terminal_ae c w t f))

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem kernelIterate_const_mul (c a : ℝ) (K : KilledKernel M) (n : ℕ)
    (f : M → ℝ) (x : M) :
    kernelIterate c K n (fun y => a * f y) x = a * kernelIterate c K n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [kernelIterate, ih, integral_const_mul]
      ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The normalization contributes exactly one scalar per elapsed time step. -/
theorem kernelIterate_normalization (c : ℝ) (K : KilledKernel M) (n : ℕ)
    (f : M → ℝ) (x : M) :
    kernelIterate c K n f x = c ^ n * kernelIterate 1 K n f x := by
  induction n generalizing x with
  | zero => simp [kernelIterate]
  | succ n ih =>
      simp only [kernelIterate, ih, integral_const_mul, one_mul, pow_succ]
      ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem kernelWord_const_mul (c a : ℝ) (K : KilledKernel M)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (f : M → ℝ) (x : M) :
    kernelWord c K w (fun y => a * f y) x = a * kernelWord c K w f x := by
  induction w generalizing x with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, g⟩
      simp only [kernelWord, ih]
      have heq : (fun y => g y * (a * kernelWord c K w f y)) =
          (fun y => a * (g y * kernelWord c K w f y)) := by
        funext y
        ring
      rw [heq, kernelIterate_const_mul]

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem kernelWord_normalization (c : ℝ) (K : KilledKernel M)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (f : M → ℝ) (x : M) :
    kernelWord c K w f x = c ^ (w.map Prod.fst).sum * kernelWord 1 K w f x := by
  induction w generalizing x with
  | nil => simp [kernelWord]
  | cons p w ih =>
      rcases p with ⟨n, g⟩
      simp only [kernelWord, ih, List.map_cons, List.sum_cons, pow_add]
      have heq : (fun y => g y * (c ^ (w.map Prod.fst).sum * kernelWord 1 K w f y)) =
          (fun y => c ^ (w.map Prod.fst).sum * (g y * kernelWord 1 K w f y)) := by
        funext y
        ring
      rw [heq, kernelIterate_const_mul, kernelIterate_normalization]
      ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem kernelCorrelation_normalization (c : ℝ) (K : KilledKernel M)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (t : ℕ) (f : M → ℝ) (x : M) :
    kernelIterate c K 1 (kernelWord c K w (kernelIterate c K t f)) x =
      c ^ ((w.map Prod.fst).sum + t + 1) *
        kernelIterate 1 K 1 (kernelWord 1 K w (kernelIterate 1 K t f)) x := by
  have hterminal : kernelIterate c K t f =
      fun y => c ^ t * kernelIterate 1 K t f y := by
    funext y
    exact kernelIterate_normalization c K t f y
  have hinner : kernelWord c K w (kernelIterate c K t f) =
      (fun y => c ^ ((w.map Prod.fst).sum + t) *
        kernelWord 1 K w (kernelIterate 1 K t f) y) := by
    funext y
    rw [hterminal, kernelWord_const_mul, kernelWord_normalization, pow_add]
    ring
  rw [hinner, kernelIterate_const_mul, kernelIterate_normalization]
  simp only [pow_add, pow_one]
  ring

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- Normalizing by an eigenvalue cancels exactly in the conditional ratio. -/
theorem kernelCorrelation_ratio_normalization (c : ℝ) (hc : c ≠ 0) (K : KilledKernel M)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (t : ℕ) (f : M → ℝ) (x : M) :
    kernelIterate c K 1 (kernelWord c K w (kernelIterate c K t f)) x /
        kernelIterate c K ((w.map Prod.fst).sum + t + 1) f x =
      kernelIterate 1 K 1 (kernelWord 1 K w (kernelIterate 1 K t f)) x /
        kernelIterate 1 K ((w.map Prod.fst).sum + t + 1) f x := by
  rw [kernelCorrelation_normalization,
    kernelIterate_normalization c K ((w.map Prod.fst).sum + t + 1) f x]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hc)

/-- All-orders mixing for nested killed-kernel integrals at a fixed state. The terminal function is
the constant one, so the denominator is the iterated survival integral. The leading factors are
`μ(g_j η)`. The first observation gap includes an additional initial step, performed by a bounded
evaluation functional. This gives the usual estimate with the minimum gap reduced by one, absorbed
into the mixing constant for a geometric rate. -/
theorem HypothesisH.kernel_mixing (h : HypothesisH ρ K) (c : ℝ) (hc : c ≠ 0)
    (μ : Lp ℝ ∞ ρ →L[ℝ] ℝ) (η one : Lp ℝ ∞ ρ) (x : M)
    (hone : μ one = 1) (hone_rep : one =ᵐ[ρ] fun _ => (1 : ℝ))
    (ha : 0 < h.stepEvaluation c x η)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (t m : ℕ) (U C θ : ℝ)
    (hU : 1 ≤ U) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne μ η‖ ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖(c • h.transitionOperator) ^ n‖ ≤ U)
    (hgap : ∀ n, 1 ≤ n → ‖(c • h.transitionOperator) ^ n - rankOne μ η‖ ≤ C * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t)
    (hsmall : ‖h.stepEvaluation c x‖ * C * θ ^ m * ‖one‖ ≤ h.stepEvaluation c x η / 2) :
    |kernelIterate 1 K 1 (kernelWord 1 K w (kernelIterate 1 K t (fun _ => 1))) x /
        ((K.kernel ^ ((w.map Prod.fst).sum + t + 1)) x).real Set.univ -
          (w.map fun p => μ (lpMultiplication ρ p.2 η)).prod| ≤
      (2 / h.stepEvaluation c x η) * ‖h.stepEvaluation c x‖ * C * ‖one‖ *
        ((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖μ‖ * ‖η‖) ^ w.length) *
        θ ^ m * (w.map fun p => ‖p.2‖).prod := by
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have htimes' : ∀ p ∈ multiplicationObservations ρ w, 1 ≤ p.1 ∧ m ≤ p.1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact htimes q hq
  have hb := conditional_operatorWord_mixing (c • h.transitionOperator) μ η one
    (h.stepEvaluation c x) hone ha (multiplicationObservations ρ w) t m U C θ
    hU hC hθ0 hθ1 hP hQ hgap htimes' ht hsmall
  rw [h.stepEvaluation_operatorWord, h.stepEvaluation_power] at hb
  simp only [multiplicationObservations, List.map_map, Function.comp_def,
    List.length_map] at hb
  rw [kernelCorrelation_ratio_normalization c hc] at hb
  have hnum : kernelIterate 1 K 1 (kernelWord 1 K w (kernelIterate 1 K t one)) x =
      kernelIterate 1 K 1 (kernelWord 1 K w (kernelIterate 1 K t (fun _ => 1))) x :=
    h.kernelIterate_succ_congr 1 0
      (h.kernelWord_congr_ae 1 w (h.kernelIterate_congr_ae 1 t hone_rep)) x
  have hden : kernelIterate 1 K ((w.map Prod.fst).sum + t + 1) one x =
      kernelIterate 1 K ((w.map Prod.fst).sum + t + 1) (fun _ => 1) x :=
    h.kernelIterate_succ_congr 1 ((w.map Prod.fst).sum + t) hone_rep x
  rw [hnum, hden] at hb
  rw [kernelIterate_one_eq_mass K ((w.map Prod.fst).sum + t + 1) x] at hb
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_left (multiplicationObservations_norms_le ρ w) (by positivity)

end StandingHypothesis

end ConditionedStableLaws
