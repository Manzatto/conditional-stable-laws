import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic

/-!
# Quantitative operator expansion for conditional mixing

The operator calculation for mixing of all orders, for arbitrary finite lists of observation
operators. Given a spectral approximation, the mixed-word estimate and the rank-one factorization
follow.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ConditionedStableLaws.ConditionalMixing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized Markov operator word, in chronological order.  The second
entry of each pair is the bounded operator multiplying by an observation. -/
def operatorWord (T : ℕ → E →L[ℝ] E) : List (ℕ × (E →L[ℝ] E)) → E →L[ℝ] E
  | [] => 1
  | (n, A) :: rest => T n * A * operatorWord T rest

/-- Product of the observation-operator norms. -/
def observationNorms (w : List (ℕ × (E →L[ℝ] E))) : ℝ :=
  (w.map fun p => ‖p.2‖).prod

theorem observationNorms_nonneg (w : List (ℕ × (E →L[ℝ] E))) :
    0 ≤ observationNorms w := by
  induction w with
  | nil => simp [observationNorms]
  | cons p w ih => simpa only [observationNorms, List.map_cons, List.prod_cons]
      using mul_nonneg (norm_nonneg p.2) ih

/-- A uniform norm bound for the full Markov word. -/
theorem operatorWord_norm_le (T : ℕ → E →L[ℝ] E)
    (w : List (ℕ × (E →L[ℝ] E))) (K : ℝ) (hK : 0 ≤ K)
    (hT : ∀ p ∈ w, ‖T p.1‖ ≤ K) :
    ‖operatorWord T w‖ ≤ K ^ w.length * observationNorms w := by
  induction w with
  | nil =>
      simp only [operatorWord, List.length_nil, pow_zero, observationNorms,
        List.map_nil, List.prod_nil, mul_one]
      exact ContinuousLinearMap.norm_id_le
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      have hhead := hT (n, A) (by simp)
      have htail := ih (fun p hp => hT p (by simp [hp]))
      calc
        ‖operatorWord T ((n, A) :: w)‖
            ≤ ‖T n‖ * ‖A‖ * ‖operatorWord T w‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ K * ‖A‖ * (K ^ w.length * observationNorms w) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hhead (norm_nonneg A))
            htail (norm_nonneg _) (mul_nonneg hK (norm_nonneg A))
        _ = K ^ (((n, A) :: w).length) * observationNorms ((n, A) :: w) := by
          simp only [List.length_cons, observationNorms, List.map_cons, List.prod_cons,
            pow_succ]
          ring

/-- Exact recursive telescoping identity: one spectral error is exposed at
the first observation, and the remaining error occurs in the suffix. -/
theorem operatorWord_sub_cons (T : ℕ → E →L[ℝ] E) (P : E →L[ℝ] E)
    (n : ℕ) (A : E →L[ℝ] E) (w : List (ℕ × (E →L[ℝ] E))) :
    operatorWord T ((n, A) :: w) - operatorWord (fun _ => P) ((n, A) :: w) =
      (T n - P) * A * operatorWord T w +
        P * A * (operatorWord T w - operatorWord (fun _ => P) w) := by
  simp only [operatorWord]
  noncomm_ring

/-- All mixed terms are bounded, with the product of every observation norm.
The harmless extra factor `K` allows the statement also to cover the empty word. -/
theorem operatorWord_sub_norm_le (T : ℕ → E →L[ℝ] E) (P : E →L[ℝ] E)
    (w : List (ℕ × (E →L[ℝ] E))) (K ε : ℝ)
    (hK : 1 ≤ K) (hε : 0 ≤ ε) (hP : ‖P‖ ≤ K)
    (hT : ∀ p ∈ w, ‖T p.1‖ ≤ K)
    (herror : ∀ p ∈ w, ‖T p.1 - P‖ ≤ ε) :
    ‖operatorWord T w - operatorWord (fun _ => P) w‖ ≤
      (w.length : ℝ) * ε * K ^ w.length * observationNorms w := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  induction w with
  | nil => simp [operatorWord, observationNorms]
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      have hTtail : ∀ p ∈ w, ‖T p.1‖ ≤ K := fun p hp => hT p (by simp [hp])
      have hetail : ∀ p ∈ w, ‖T p.1 - P‖ ≤ ε :=
        fun p hp => herror p (by simp [hp])
      have hhead := herror (n, A) (by simp)
      have htail := ih hTtail hetail
      have hword := operatorWord_norm_le T w K hK0 hTtail
      have hobs := observationNorms_nonneg w
      rw [operatorWord_sub_cons]
      calc
        ‖(T n - P) * A * operatorWord T w +
            P * A * (operatorWord T w - operatorWord (fun _ => P) w)‖
            ≤ ‖T n - P‖ * ‖A‖ * ‖operatorWord T w‖ +
              ‖P‖ * ‖A‖ * ‖operatorWord T w - operatorWord (fun _ => P) w‖ := by
          exact (norm_add_le _ _).trans (add_le_add
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _)))
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _))))
        _ ≤ ε * ‖A‖ * (K ^ w.length * observationNorms w) +
              K * ‖A‖ * ((w.length : ℝ) * ε * K ^ w.length * observationNorms w) := by
          apply add_le_add
          · exact mul_le_mul (mul_le_mul_of_nonneg_right hhead (norm_nonneg _))
              hword (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))
          · exact mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
              htail (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))
        _ ≤ (((n, A) :: w).length : ℝ) * ε * K ^ (((n, A) :: w).length) *
              observationNorms ((n, A) :: w) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one, observationNorms,
            List.map_cons, List.prod_cons, pow_succ] at *
          nlinarith [mul_nonneg (sub_nonneg.mpr hK)
            (mul_nonneg hε (mul_nonneg (norm_nonneg A)
              (mul_nonneg (pow_nonneg hK0 w.length) hobs)))]

/-- Spectral-gap specialization: every observation gap is at least `m`, so
the error decays geometrically in `m`, uniformly over all observation operators. -/
theorem operatorWord_spectral_error (Q P : E →L[ℝ] E)
    (w : List (ℕ × (E →L[ℝ] E))) (m : ℕ) (K C θ : ℝ)
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖P‖ ≤ K) (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ K)
    (hgap : ∀ n, 1 ≤ n → ‖Q ^ n - P‖ ≤ C * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) :
    ‖operatorWord (fun n => Q ^ n) w - operatorWord (fun _ => P) w‖ ≤
      (w.length : ℝ) * C * K ^ w.length * θ ^ m * observationNorms w := by
  have hb := operatorWord_sub_norm_le (fun n => Q ^ n) P w K (C * θ ^ m)
    hK (mul_nonneg hC (pow_nonneg hθ0 m)) hP
    (fun p hp => hQ p.1 (htimes p hp).1)
    (fun p hp => (hgap p.1 (htimes p hp).1).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ1 (htimes p hp).2) hC))
  convert hb using 1
  ring

/-- The rank-one map `f ↦ μ(f) η`, as a continuous linear operator. -/
def rankOne (μ : E →L[ℝ] ℝ) (η : E) : E →L[ℝ] E := μ.smulRight η

/-- Exact factorization of a projection word on the eigenfunction.  For
multiplication by `g`, each factor is `μ(g η) = ν(g)`. -/
theorem rankOne_word_eigenvector (μ : E →L[ℝ] ℝ) (η : E)
    (w : List (ℕ × (E →L[ℝ] E))) :
    operatorWord (fun _ => rankOne μ η) w η =
      (w.map fun p => μ (p.2 η)).prod • η := by
  induction w with
  | nil => simp [operatorWord]
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      change rankOne μ η (A (operatorWord (fun _ => rankOne μ η) w η)) = _
      rw [ih]
      simp only [rankOne, ContinuousLinearMap.smulRight_apply, map_smul,
        List.map_cons, List.prod_cons, mul_smul]
      exact smul_comm _ _ _

theorem operatorWord_append (T : ℕ → E →L[ℝ] E)
    (w z : List (ℕ × (E →L[ℝ] E))) :
    operatorWord T (w ++ z) = operatorWord T w * operatorWord T z := by
  induction w with
  | nil => simp [operatorWord]
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      simp only [List.cons_append, operatorWord, ih, mul_assoc]

/-- The terminal observation has `μ`-mean; all earlier observations have
`ν`-means.  Choosing the terminal vector to be the constant one gives the
all-`ν` formula for conditioning beyond the last observation. -/
theorem rankOne_word_terminal (μ : E →L[ℝ] ℝ) (η v : E)
    (w : List (ℕ × (E →L[ℝ] E))) (t : ℕ) :
    operatorWord (fun _ => rankOne μ η) (w ++ [(t, 1)]) v =
      ((w.map fun p => μ (p.2 η)).prod * μ v) • η := by
  rw [operatorWord_append]
  change operatorWord (fun _ => rankOne μ η) w (μ v • η) = _
  rw [map_smul, rankOne_word_eigenvector, smul_smul, mul_comm]

theorem observationNorms_append_identity_le
    (w : List (ℕ × (E →L[ℝ] E))) (t : ℕ) :
    observationNorms (w ++ [(t, 1)]) ≤ observationNorms w := by
  have hnorm : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  simpa only [observationNorms, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one] using
    mul_le_mul_of_nonneg_left hnorm (observationNorms_nonneg w)

/-- The all-orders numerator estimate, including the exceptional last observation. Its inputs are a
spectral gap and separated observation times; its conclusion is the factorized leading term plus a
quantitative error. -/
theorem operatorWord_mixing_estimate (Q : E →L[ℝ] E) (μ : E →L[ℝ] ℝ)
    (η v : E) (w : List (ℕ × (E →L[ℝ] E))) (t m : ℕ) (K C θ : ℝ)
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne μ η‖ ≤ K) (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ K)
    (hgap : ∀ n, 1 ≤ n → ‖Q ^ n - rankOne μ η‖ ≤ C * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t) :
    ‖operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) v -
        ((w.map fun p => μ (p.2 η)).prod * μ v) • η‖ ≤
      (w.length + 1 : ℝ) * C * K ^ (w.length + 1) * θ ^ m *
        observationNorms w * ‖v‖ := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have htimes' : ∀ p ∈ w ++ [(t, (1 : E →L[ℝ] E))], 1 ≤ p.1 ∧ m ≤ p.1 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact htimes p hp
    · have hp' := List.mem_singleton.mp hp
      subst p
      exact ht
  have hbound := operatorWord_spectral_error Q (rankOne μ η)
    (w ++ [(t, 1)]) m K C θ hK hC hθ0 hθ1 hP hQ hgap htimes'
  rw [← rankOne_word_terminal μ η v w t]
  change ‖(operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) -
      operatorWord (fun _ => rankOne μ η) (w ++ [(t, 1)])) v‖ ≤ _
  refine ((ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg v))).trans ?_
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (observationNorms_append_identity_le w t)
      (by positivity)) (norm_nonneg v)

/-- Dividing by a survival denominator close to its strictly positive leading term preserves a
quantitative error bound. -/
theorem quotient_error_bound (b d a c B D : ℝ) (ha : 0 < a)
    (hden : |d - a| ≤ a / 2) (hnum : |b - a * c| ≤ B)
    (hdenerror : |d - a| ≤ D) :
    |b / d - c| ≤ (2 / a) * (B + |c| * D) := by
  have hd : a / 2 ≤ d := by have := (abs_le.mp hden).1; linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by linarith) hd
  have heq : b / d - c = ((b - a * c) - c * (d - a)) / d := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hdpos]
  have hb : |(b - a * c) - c * (d - a)| ≤ B + |c| * D := by
    exact (abs_sub _ _).trans (add_le_add hnum
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdenerror (abs_nonneg c)))
  have hB : 0 ≤ B + |c| * D := le_trans (abs_nonneg _) hb
  calc
    |(b - a * c) - c * (d - a)| / d ≤ (B + |c| * D) / d :=
      div_le_div_of_nonneg_right hb hdpos.le
    _ ≤ (2 / a) * (B + |c| * D) := by
      apply (div_le_iff₀ hdpos).mpr
      have := mul_le_mul_of_nonneg_left hd hB
      apply (mul_le_mul_iff_right₀ ha).mp
      field_simp
      nlinarith

/-- The uniform power bound used in the word estimates follows already from
the spectral approximation. -/
theorem uniform_power_bound_from_gap (Q P : E →L[ℝ] E) (C θ : ℝ)
    (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hgap : ∀ n, 1 ≤ n → ‖Q ^ n - P‖ ≤ C * θ ^ n) (n : ℕ) (hn : 1 ≤ n) :
    ‖Q ^ n‖ ≤ max 1 (‖P‖ + C) := by
  have hnθ : θ ^ n ≤ 1 := by
    simpa using pow_le_pow_of_le_one hθ0 hθ1 (Nat.zero_le n)
  calc
    ‖Q ^ n‖ ≤ ‖P‖ + ‖Q ^ n - P‖ := by
      have heq : Q ^ n = P + (Q ^ n - P) := by abel
      conv_lhs => rw [heq]
      exact norm_add_le _ _
    _ ≤ ‖P‖ + C * θ ^ n := add_le_add le_rfl (hgap n hn)
    _ ≤ ‖P‖ + C := add_le_add le_rfl (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnθ hC)
    _ ≤ max 1 (‖P‖ + C) := le_max_right _ _

/-- The coefficient in the leading term carries the product of the observation
norms, so it can be absorbed in the same all-orders mixing bound. -/
theorem rankOne_coefficient_bound (μ : E →L[ℝ] ℝ) (η : E)
    (w : List (ℕ × (E →L[ℝ] E))) :
    |(w.map fun p => μ (p.2 η)).prod| ≤
      (‖μ‖ * ‖η‖) ^ w.length * observationNorms w := by
  induction w with
  | nil => simp [observationNorms]
  | cons p w ih =>
      have hhead : |μ (p.2 η)| ≤ ‖μ‖ * ‖p.2‖ * ‖η‖ := by
        calc
          |μ (p.2 η)| ≤ ‖μ‖ * ‖p.2 η‖ := μ.le_opNorm _
          _ ≤ ‖μ‖ * (‖p.2‖ * ‖η‖) :=
            mul_le_mul_of_nonneg_left (p.2.le_opNorm η) (norm_nonneg μ)
          _ = _ := by ring
      simp only [List.map_cons, List.prod_cons, abs_mul]
      calc
        |μ (p.2 η)| * |(w.map fun q => μ (q.2 η)).prod|
            ≤ (‖μ‖ * ‖p.2‖ * ‖η‖) *
              ((‖μ‖ * ‖η‖) ^ w.length * observationNorms w) :=
          mul_le_mul hhead ih (abs_nonneg _) (by positivity)
        _ = (‖μ‖ * ‖η‖) ^ (p :: w).length * observationNorms (p :: w) := by
          simp only [List.length_cons, observationNorms, List.map_cons,
            List.prod_cons, pow_succ]
          ring

/-- Applying a bounded observation functional to a spectral remainder gives
the scalar survival-denominator estimate. -/
theorem spectral_denominator_error (Q : E →L[ℝ] E) (μ : E →L[ℝ] ℝ)
    (η one : E) (ev : E →L[ℝ] ℝ) (hone : μ one = 1)
    (N m : ℕ) (C θ : ℝ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hgap : ‖Q ^ N - rankOne μ η‖ ≤ C * θ ^ N) (hNm : m ≤ N) :
    |ev ((Q ^ N) one) - ev η| ≤ ‖ev‖ * C * θ ^ m * ‖one‖ := by
  have heq : ev ((Q ^ N) one) - ev η =
      ev ((Q ^ N - rankOne μ η) one) := by
    simp [rankOne, hone]
  rw [heq]
  calc
    |ev ((Q ^ N - rankOne μ η) one)|
        ≤ ‖ev‖ * ‖(Q ^ N - rankOne μ η) one‖ := ev.le_opNorm _
    _ ≤ ‖ev‖ * (‖Q ^ N - rankOne μ η‖ * ‖one‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg ev)
    _ ≤ ‖ev‖ * ((C * θ ^ N) * ‖one‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hgap (norm_nonneg one)) (norm_nonneg ev)
    _ ≤ ‖ev‖ * C * θ ^ m * ‖one‖ := by
      have hpow := pow_le_pow_of_le_one hθ0 hθ1 hNm
      nlinarith [mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (mul_nonneg (norm_nonneg ev) hC) (norm_nonneg one))]

/-- Full quantitative factorization of the normalized operator ratio. The denominator uses the total
elapsed time, including the final survival gap. The smallness hypothesis is an explicit
spectral-error bound, and positivity of the denominator follows. -/
theorem conditional_operatorWord_mixing (Q : E →L[ℝ] E) (μ : E →L[ℝ] ℝ)
    (η one : E) (ev : E →L[ℝ] ℝ) (hone : μ one = 1) (ha : 0 < ev η)
    (w : List (ℕ × (E →L[ℝ] E))) (t m : ℕ) (K C θ : ℝ)
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne μ η‖ ≤ K) (hQ : ∀ n, 1 ≤ n → ‖Q ^ n‖ ≤ K)
    (hgap : ∀ n, 1 ≤ n → ‖Q ^ n - rankOne μ η‖ ≤ C * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t)
    (hsmall : ‖ev‖ * C * θ ^ m * ‖one‖ ≤ ev η / 2) :
    |ev (operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) one) /
        ev ((Q ^ ((w.map Prod.fst).sum + t)) one) -
          (w.map fun p => μ (p.2 η)).prod| ≤
      (2 / ev η) * ‖ev‖ * C * ‖one‖ *
        ((w.length + 1 : ℝ) * K ^ (w.length + 1) + (‖μ‖ * ‖η‖) ^ w.length) *
        θ ^ m * observationNorms w := by
  let c : ℝ := (w.map fun p => μ (p.2 η)).prod
  let N : ℕ := (w.map Prod.fst).sum + t
  let B : ℝ := (w.length + 1 : ℝ) * C * K ^ (w.length + 1) * θ ^ m *
    observationNorms w * ‖one‖
  let D : ℝ := ‖ev‖ * C * θ ^ m * ‖one‖
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNm : m ≤ N := by dsimp [N]; omega
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hden := spectral_denominator_error Q μ η one ev hone N m C θ
    hC hθ0 hθ1 (hgap N hN) hNm
  have hword : ‖operatorWord (fun n => Q ^ n) (w ++ [(t, 1)]) one - c • η‖ ≤ B := by
    simpa only [hone, mul_one] using
      operatorWord_mixing_estimate Q μ η one w t m K C θ
        hK hC hθ0 hθ1 hP hQ hgap htimes ht
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

section LInfinityObservations

variable {M : Type*} [MeasurableSpace M] (ρ : Measure M)

/-- The multiplication operator `M_g f = g f` on L∞ equivalence classes. -/
def lpMultiplication (g : Lp ℝ ∞ ρ) : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL ρ ∞ ∞ ∞ g

theorem lpMultiplication_ae (g f : Lp ℝ ∞ ρ) :
    lpMultiplication ρ g f =ᵐ[ρ] fun x => g x * f x := by
  exact (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder g f

/-- The operator bound holds for essentially bounded observations, including noncontinuous ones. -/
theorem lpMultiplication_norm_le (g : Lp ℝ ∞ ρ) :
    ‖lpMultiplication ρ g‖ ≤ ‖g‖ := by
  calc
    ‖lpMultiplication ρ g‖ ≤
        ‖(ContinuousLinearMap.mul ℝ ℝ).holderL ρ ∞ ∞ ∞‖ * ‖g‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖g‖ :=
      mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.mul ℝ ℝ).norm_holderL_le (norm_nonneg g)
    _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) (norm_nonneg g)
    _ = ‖g‖ := one_mul _

/-- Passage from time/observable pairs to the operators in the word formula. -/
def multiplicationObservations (w : List (ℕ × Lp ℝ ∞ ρ)) :
    List (ℕ × (Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ)) :=
  w.map fun p => (p.1, lpMultiplication ρ p.2)

theorem multiplicationObservations_norms_le (w : List (ℕ × Lp ℝ ∞ ρ)) :
    observationNorms (multiplicationObservations ρ w) ≤
      (w.map fun p => ‖p.2‖).prod := by
  induction w with
  | nil => simp [multiplicationObservations, observationNorms]
  | cons p w ih =>
      simp only [multiplicationObservations, List.map_cons, observationNorms,
        List.prod_cons] at *
      exact mul_le_mul (lpMultiplication_norm_le ρ p.2) ih
        (observationNorms_nonneg (multiplicationObservations ρ w)) (norm_nonneg p.2)

end LInfinityObservations

end ConditionedStableLaws.ConditionalMixing
