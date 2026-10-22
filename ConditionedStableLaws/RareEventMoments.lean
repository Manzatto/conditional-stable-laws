import ConditionedStableLaws.FactorialMoments
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rare-event factorial moment estimates

The estimates separate three errors in the moment argument: factorization on interior separated
configurations, the total contribution of close or boundary configurations, and their number. The
limit theorem uses quantitative bounds on those errors.
-/

open Filter Finset Classical MeasureTheory
open scoped BigOperators Topology

namespace ConditionedStableLaws

noncomputable section

/-- The logarithmic gap cutoff used to make spectral mixing errors small. -/
def logCutoff (a : ℝ) (n : ℕ) : ℕ := ⌈a * Real.log n⌉₊

/-- Every fixed nonnegative logarithmic cutoff is sublinear. -/
theorem logCutoff_div_tendsto_zero (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (logCutoff a n : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
    convert
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop) using 1
    ext n
    simp
  have hbound := (hlog.const_mul a).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simp only [mul_zero, zero_add] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ hbound
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg ha (Real.log_nonneg hn1))).le
  calc
    (logCutoff a n : ℝ) / n ≤ (a * Real.log n + 1) / n :=
      div_le_div_of_nonneg_right hceil (Nat.cast_nonneg n)
    _ = a * (Real.log n / n) + 1 / n := by ring

/-- Choosing the logarithmic coefficient so that `a log θ ≤ -(r+1)`
turns a geometric mixing error into an inverse polynomial error. -/
theorem geometric_logCutoff_le_inv_pow {θ a : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (r : ℕ) (ha : a * Real.log θ ≤ -((r + 1 : ℕ) : ℝ)) {n : ℕ} (hn : 0 < n) :
    θ ^ logCutoff a n ≤ 1 / (n : ℝ) ^ (r + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    θ ^ logCutoff a n = θ ^ (logCutoff a n : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ θ ^ (a * Real.log n) :=
      Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 (Nat.le_ceil _)
    _ = Real.exp ((a * Real.log θ) * Real.log n) := by
      rw [Real.rpow_def_of_pos hθ0]
      congr 1
      ring
    _ ≤ Real.exp (-((r + 1 : ℕ) : ℝ) * Real.log n) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha (Real.log_nonneg hn1))
    _ = 1 / (n : ℝ) ^ (r + 1) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0, one_div]

/-- The scaled mixing error needed in the factorial-moment theorem vanishes
for a sufficiently large logarithmic cutoff. -/
theorem scaled_geometric_logCutoff_tendsto_zero {θ a C : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) (r : ℕ)
    (ha : a * Real.log θ ≤ -((r + 1 : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ r * (C * θ ^ logCutoff a n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    _ ≤ (n : ℝ) ^ r * (C * (1 / (n : ℝ) ^ (r + 1))) := by
      gcongr
      exact geometric_logCutoff_le_inv_pow hθ0 hθ1 r ha hn
    _ = C / n := by rw [pow_succ]; field_simp

/-- A joint visit event for a specified ordered time configuration. -/
def jointVisitEvent {Ω A : Type*} {n r : ℕ} (X : Fin n → Ω → A)
    (U : Set A) (t : Fin r → Fin n) : Set Ω := {ω | ∀ i, X (t i) ω ∈ U}

theorem measurableSet_jointVisitEvent {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] {n r : ℕ} (X : Fin n → Ω → A) (hX : ∀ j, Measurable (X j))
    (U : Set A) (hU : MeasurableSet U) (t : Fin r → Fin n) :
    MeasurableSet (jointVisitEvent X U t) := by
  simpa only [jointVisitEvent, Set.ofPred_forall, Set.preimage] using
    MeasurableSet.iInter (fun i => hU.preimage (hX (t i)))

/-- Joint-event probabilities, extended by zero to configurations that repeat a time. This is the
weight occurring in factorial moments. -/
def factorialEventWeight {Ω A : Type*} [MeasurableSpace Ω] {n r : ℕ}
    (P : Measure Ω) (X : Fin n → Ω → A) (U : Set A) (t : Fin r → Fin n) : ℝ :=
  if Function.Injective t then P.real (jointVisitEvent X U t) else 0

/-- The finite sum of these weights is the sum over embeddings. -/
theorem sum_factorialEventWeight {Ω A : Type*} [MeasurableSpace Ω] {n r : ℕ}
    (P : Measure Ω) (X : Fin n → Ω → A) (U : Set A) :
    (∑ t : Fin r → Fin n, factorialEventWeight P X U t) =
      ∑ e : Fin r ↪ Fin n, P.real (jointVisitEvent X U e) := by
  simp only [factorialEventWeight]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := Function.Injective) _ (by simp)]
  exact (Equiv.subtypeInjectiveEquivEmbedding (Fin r) (Fin n)).sum_comp
    (fun e : Fin r ↪ Fin n => P.real (jointVisitEvent X U e))

/-- Exact expectation identity: the factorial moment of the visit count equals the finite sum of
joint event probabilities over distinct times. -/
theorem integral_visit_descFactorial_eq_sum {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] {n r : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (X : Fin n → Ω → A) (hX : ∀ j, Measurable (X j))
    (U : Set A) (hU : MeasurableSet U) :
    (∫ ω, ((visitTimes (fun t => X t ω) U).card.descFactorial r : ℝ) ∂P) =
      ∑ t : Fin r → Fin n, factorialEventWeight P X U t := by
  have hpoint (ω : Ω) :
      ((visitTimes (fun t => X t ω) U).card.descFactorial r : ℝ) =
        ∑ e : Fin r ↪ Fin n,
          (jointVisitEvent X U e).indicator (fun _ => (1 : ℝ)) ω := by
    have hn := descFactorial_card_eq_sum_injective
      (visitTimes (fun t => X t ω) U) r
    simp only [visitTimes, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.prod_boole, forall_const] at hn
    simp only [Set.indicator_apply, jointVisitEvent, Set.mem_ofPred_eq]
    exact_mod_cast hn
  rw [sum_factorialEventWeight]
  calc
    _ = ∫ ω, ∑ e : Fin r ↪ Fin n,
        (jointVisitEvent X U e).indicator (fun _ => (1 : ℝ)) ω ∂P :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∑ e : Fin r ↪ Fin n, ∫ ω,
        (jointVisitEvent X U e).indicator (fun _ => (1 : ℝ)) ω ∂P := by
      apply integral_finsetSum
      intro e _
      exact (integrable_const (1 : ℝ)).indicator (measurableSet_jointVisitEvent X hX U hU e)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      exact integral_indicator_one (measurableSet_jointVisitEvent X hX U hU e)

/-- A finite quantitative version of the separated/close configuration
decomposition. The weight may be a joint event probability and is typically
zero on noninjective tuples. -/
theorem configuration_sum_error_le_reference {n r L : ℕ} (w : (Fin r → Fin n) → ℝ)
    (q e c : ℝ) (he : 0 ≤ e)
    (hsep : ∀ t ∈ interiorSeparatedConfigurations n r L, |w t - q| ≤ e)
    (hclose : |∑ t ∈ excludedConfigurations n r L, w t| ≤ c) :
    |(∑ t, w t) - (n : ℝ) ^ r * q| ≤
      (n : ℝ) ^ r * e + c +
        ((r : ℝ) + 1) ^ 2 * (2 * (L : ℝ) + 1) * (n : ℝ) ^ (r - 1) * |q| := by
  let good := interiorSeparatedConfigurations n r L
  let bad := excludedConfigurations n r L
  have hpart : (∑ t, (w t - q)) =
      (∑ t ∈ good, (w t - q)) + ∑ t ∈ bad, (w t - q) := by
    exact (Finset.sum_sdiff (f := fun t => w t - q) (Finset.subset_univ bad)).symm
  have hgood : |∑ t ∈ good, (w t - q)| ≤ (n : ℝ) ^ r * e := by
    calc
      _ ≤ ∑ t ∈ good, |w t - q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ good.card • e := Finset.sum_le_card_nsmul _ _ _ hsep
      _ ≤ (n : ℝ) ^ r * e := by
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ he
        have hgc : good.card ≤ n ^ r := by
          simpa using Finset.card_le_card (Finset.subset_univ good)
        exact_mod_cast hgc
  have hbad : |∑ t ∈ bad, (w t - q)| ≤ c + (bad.card : ℝ) * |q| := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ |∑ t ∈ bad, w t| + |(bad.card : ℝ) * q| := abs_sub _ _
      _ ≤ c + (bad.card : ℝ) * |q| := by
        simpa only [abs_mul,
          abs_of_nonneg (Nat.cast_nonneg bad.card : (0 : ℝ) ≤ (bad.card : ℝ))] using
          add_le_add hclose (le_refl |(bad.card : ℝ) * q|)
  have hbadcard : (bad.card : ℝ) ≤
      ((r : ℝ) + 1) ^ 2 * (2 * (L : ℝ) + 1) * (n : ℝ) ^ (r - 1) := by
    exact_mod_cast card_excludedConfigurations_le n r L
  have hsum : (∑ t, w t) - (n : ℝ) ^ r * q = ∑ t, (w t - q) := by
    simp [Finset.sum_sub_distrib]
  rw [hsum, hpart]
  calc
    _ ≤ |∑ t ∈ good, (w t - q)| + |∑ t ∈ bad, (w t - q)| := abs_add_le _ _
    _ ≤ (n : ℝ) ^ r * e + (c + (bad.card : ℝ) * |q|) := add_le_add hgood hbad
    _ ≤ (n : ℝ) ^ r * e + c +
        ((r : ℝ) + 1) ^ 2 * (2 * (L : ℝ) + 1) * (n : ℝ) ^ (r - 1) * |q| := by
      have hh := mul_le_mul_of_nonneg_right hbadcard (abs_nonneg q)
      linarith

/-- Specialization to a single target with independent weight `p^r`. -/
theorem configuration_sum_error_le {n r L : ℕ} (w : (Fin r → Fin n) → ℝ)
    (p e c : ℝ) (he : 0 ≤ e)
    (hsep : ∀ t ∈ interiorSeparatedConfigurations n r L, |w t - p ^ r| ≤ e)
    (hclose : |∑ t ∈ excludedConfigurations n r L, w t| ≤ c) :
    |(∑ t, w t) - ((n : ℝ) * p) ^ r| ≤
      (n : ℝ) ^ r * e + c +
        ((r : ℝ) + 1) ^ 2 * (2 * (L : ℝ) + 1) * (n : ℝ) ^ (r - 1) * |p| ^ r := by
  simpa only [mul_pow, abs_pow] using
    configuration_sum_error_le_reference w (p ^ r) e c he hsep hclose

/-- If the cutoff is sublinear and `n pₙ` has a finite limit, the number of
excluded configurations times the independent event weight vanishes. -/
theorem close_comparison_error_tendsto_zero {r : ℕ} (hr : 0 < r)
    {L : ℕ → ℕ} {p : ℕ → ℝ} {rate : ℝ}
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 rate)) :
    Tendsto (fun n : ℕ => ((r : ℝ) + 1) ^ 2 * (2 * (L n : ℝ) + 1) *
      (n : ℝ) ^ (r - 1) * |p n| ^ r) atTop (𝓝 0) := by
  have hcut : Tendsto (fun n : ℕ => (2 * (L n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have hh := (hL.const_mul 2).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    convert hh using 1 <;> simp [add_div, mul_div_assoc]
  have h := (hcut.const_mul (((r : ℝ) + 1) ^ 2)).mul (hp.abs.pow r)
  simp only [mul_zero, zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), mul_pow]
  rw [pow_succ (n : ℝ)]
  field_simp

/-- Convergence of the finite configuration sum from separated-tuple factorization, a negligible
close/cluster contribution, and rare-event scaling. -/
theorem configuration_sum_tendsto {r : ℕ} (hr : 0 < r)
    (w : ∀ n : ℕ, (Fin r → Fin n) → ℝ) {L : ℕ → ℕ}
    {p e c : ℕ → ℝ} {rate : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 rate))
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (he : ∀ᶠ n in atTop, 0 ≤ e n)
    (hmix : Tendsto (fun n : ℕ => (n : ℝ) ^ r * e n) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 0))
    (hsep : ∀ᶠ n in atTop, ∀ t ∈ interiorSeparatedConfigurations n r (L n),
      |w n t - p n ^ r| ≤ e n)
    (hclose : ∀ᶠ n in atTop,
      |∑ t ∈ excludedConfigurations n r (L n), w n t| ≤ c n) :
    Tendsto (fun n => ∑ t, w n t) atTop (𝓝 (rate ^ r)) := by
  have herror := (hmix.add hc).add (close_comparison_error_tendsto_zero hr hL hp)
  simp only [zero_add] at herror
  have hdist : Tendsto (fun n : ℕ => |(∑ t, w n t) - ((n : ℝ) * p n) ^ r|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) _ herror
    filter_upwards [he, hsep, hclose] with n hen hsepn hclosen
    exact configuration_sum_error_le (w n) (p n) (e n) (c n) hen hsepn hclosen
  apply (hp.pow r).congr_dist
  simpa only [Real.dist_eq, abs_sub_comm] using hdist

/-- The reference product may contain different target probabilities. -/
theorem close_reference_error_tendsto_zero {r : ℕ} (hr : 0 < r)
    {L : ℕ → ℕ} {q : ℕ → ℝ} {limit : ℝ}
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (hq : Tendsto (fun n : ℕ => (n : ℝ) ^ r * q n) atTop (𝓝 limit)) :
    Tendsto (fun n : ℕ => ((r : ℝ) + 1) ^ 2 * (2 * (L n : ℝ) + 1) *
      (n : ℝ) ^ (r - 1) * |q n|) atTop (𝓝 0) := by
  have hcut : Tendsto (fun n : ℕ => (2 * (L n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have hh := (hL.const_mul 2).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    convert hh using 1 <;> simp [add_div, mul_div_assoc]
  have h := (hcut.const_mul (((r : ℝ) + 1) ^ 2)).mul hq.abs
  simp only [mul_zero, zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, abs_mul,
    abs_pow, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  rw [pow_succ (n : ℝ)]
  field_simp

/-- Moment-sum convergence with any reference product having the prescribed
rare-event scaling; the reference is independent of the configuration. -/
theorem configuration_sum_tendsto_reference {r : ℕ} (hr : 0 < r)
    (w : ∀ n : ℕ, (Fin r → Fin n) → ℝ) {L : ℕ → ℕ}
    {q e c : ℕ → ℝ} {limit : ℝ}
    (hq : Tendsto (fun n : ℕ => (n : ℝ) ^ r * q n) atTop (𝓝 limit))
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (he : ∀ᶠ n in atTop, 0 ≤ e n)
    (hmix : Tendsto (fun n : ℕ => (n : ℝ) ^ r * e n) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 0))
    (hsep : ∀ᶠ n in atTop, ∀ t ∈ interiorSeparatedConfigurations n r (L n),
      |w n t - q n| ≤ e n)
    (hclose : ∀ᶠ n in atTop,
      |∑ t ∈ excludedConfigurations n r (L n), w n t| ≤ c n) :
    Tendsto (fun n => ∑ t, w n t) atTop (𝓝 limit) := by
  have herror := (hmix.add hc).add (close_reference_error_tendsto_zero hr hL hq)
  simp only [zero_add] at herror
  have hdist : Tendsto (fun n : ℕ => |(∑ t, w n t) - (n : ℝ) ^ r * q n|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) _ herror
    filter_upwards [he, hsep, hclose] with n hen hsepn hclosen
    exact configuration_sum_error_le_reference (w n) (q n) (e n) (c n) hen hsepn hclosen
  apply hq.congr_dist
  simpa only [Real.dist_eq, abs_sub_comm] using hdist

/-- Marginal rare-event scaling implies the correct scaling of any finite
mixed monomial of the marginal probabilities. -/
theorem scaled_prod_tendsto {J : Type*} [Fintype J] (r : J → ℕ)
    (p : J → ℕ → ℝ) (rate : J → ℝ)
    (hp : ∀ j, Tendsto (fun n : ℕ => (n : ℝ) * p j n) atTop (𝓝 (rate j))) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (∑ j, r j) * ∏ j, p j n ^ r j)
      atTop (𝓝 (∏ j, rate j ^ r j)) := by
  have h := tendsto_finsetProd Finset.univ (fun j _ => (hp j).pow (r j))
  convert h using 1
  ext n
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The preceding limit applied to factorial moments, allowing the probability law itself to vary
with `n` as under survival conditioning. -/
theorem factorial_moment_tendsto {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] {r : ℕ} (hr : 0 < r)
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n j, Measurable (X n j))
    (U : ℕ → Set A) (hU : ∀ n, MeasurableSet (U n))
    {L : ℕ → ℕ} {p e c : ℕ → ℝ} {rate : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 rate))
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (he : ∀ᶠ n in atTop, 0 ≤ e n)
    (hmix : Tendsto (fun n : ℕ => (n : ℝ) ^ r * e n) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 0))
    (hsep : ∀ᶠ n in atTop, ∀ t ∈ interiorSeparatedConfigurations n r (L n),
      |factorialEventWeight (P n) (X n) (U n) t - p n ^ r| ≤ e n)
    (hclose : ∀ᶠ n in atTop,
      |∑ t ∈ excludedConfigurations n r (L n), factorialEventWeight (P n) (X n) (U n) t| ≤ c n) :
    Tendsto (fun n => ∫ ω,
      ((visitTimes (fun t => X n t ω) (U n)).card.descFactorial r : ℝ) ∂P n)
      atTop (𝓝 (rate ^ r)) := by
  have h := configuration_sum_tendsto hr
    (fun n => factorialEventWeight (P n) (X n) (U n)) hp hL he hmix hc hsep hclose
  apply h.congr
  intro n
  exact (integral_visit_descFactorial_eq_sum (P n) (X n) (hX n) (U n) (hU n)).symm

section Mixed

variable {J Ω A : Type*} [Fintype J] [MeasurableSpace Ω]

/-- Enumerate the total collection of labelled factorial slots. -/
def factorialSlotsEquiv (r : J → ℕ) : (Σ j, Fin (r j)) ≃ Fin (∑ j, r j) :=
  Fintype.equivFinOfCardEq (by simp)

/-- A mixed joint event assigns each factorial slot its own target label. -/
def mixedJointVisitEvent {n : ℕ} (X : Fin n → Ω → A) (U : J → Set A)
    (r : J → ℕ) (t : Fin (∑ j, r j) → Fin n) : Set Ω :=
  {ω | ∀ a : Σ j, Fin (r j), X (t (factorialSlotsEquiv r a)) ω ∈ U a.1}

theorem measurableSet_mixedJointVisitEvent [MeasurableSpace A] {n : ℕ}
    (X : Fin n → Ω → A) (hX : ∀ j, Measurable (X j))
    (U : J → Set A) (hU : ∀ j, MeasurableSet (U j)) (r : J → ℕ)
    (t : Fin (∑ j, r j) → Fin n) : MeasurableSet (mixedJointVisitEvent X U r t) := by
  simpa only [mixedJointVisitEvent, Set.ofPred_forall, Set.preimage] using
    MeasurableSet.iInter
      (fun a : Σ j, Fin (r j) => (hU a.1).preimage (hX (t (factorialSlotsEquiv r a))))

/-- Mixed joint probabilities, zero for any repeated time across any labels. -/
def mixedFactorialEventWeight {n : ℕ} (P : Measure Ω) (X : Fin n → Ω → A)
    (U : J → Set A) (r : J → ℕ) (t : Fin (∑ j, r j) → Fin n) : ℝ :=
  if Function.Injective t then P.real (mixedJointVisitEvent X U r t) else 0

theorem sum_mixedFactorialEventWeight {n : ℕ} (P : Measure Ω) (X : Fin n → Ω → A)
    (U : J → Set A) (r : J → ℕ) :
    (∑ t, mixedFactorialEventWeight P X U r t) =
      ∑ e : Fin (∑ j, r j) ↪ Fin n, P.real (mixedJointVisitEvent X U r e) := by
  simp only [mixedFactorialEventWeight]
  rw [← Finset.sum_filter, Finset.sum_subtype (p := Function.Injective) _ (by simp)]
  exact (Equiv.subtypeInjectiveEquivEmbedding (Fin (∑ j, r j)) (Fin n)).sum_comp
    (fun e : Fin (∑ j, r j) ↪ Fin n => P.real (mixedJointVisitEvent X U r e))

/-- Exact mixed-factorial expectation identity for disjoint targets. -/
theorem integral_prod_visit_descFactorial_eq_sum [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (X : Fin n → Ω → A) (hX : ∀ j, Measurable (X j))
    (U : J → Set A) (hU : ∀ j, MeasurableSet (U j))
    (hdis : Pairwise fun i j => Disjoint (U i) (U j)) (r : J → ℕ) :
    (∫ ω, ∏ j, ((visitTimes (fun t => X t ω) (U j)).card.descFactorial (r j) : ℝ) ∂P) =
      ∑ t, mixedFactorialEventWeight P X U r t := by
  have hpoint (ω : Ω) :
      (∏ j, ((visitTimes (fun t => X t ω) (U j)).card.descFactorial (r j) : ℝ)) =
        ∑ e : Fin (∑ j, r j) ↪ Fin n,
          (mixedJointVisitEvent X U r e).indicator (fun _ => (1 : ℝ)) ω := by
    have hh := prod_visit_descFactorial_eq_real (fun t => X t ω) U hdis r
    simp only [Finset.prod_boole, Finset.mem_univ, forall_const] at hh
    let eqv := Equiv.embeddingCongr (factorialSlotsEquiv r) (Equiv.refl (Fin n))
    calc
      _ = ∑ e : (Σ j, Fin (r j)) ↪ Fin n,
          (mixedJointVisitEvent X U r (eqv e)).indicator (fun _ => (1 : ℝ)) ω := by
        simpa [mixedJointVisitEvent, eqv, Equiv.embeddingCongr, Set.indicator_apply] using hh
      _ = _ := eqv.sum_comp (fun e : Fin (∑ j, r j) ↪ Fin n =>
        (mixedJointVisitEvent X U r e).indicator (fun _ => (1 : ℝ)) ω)
  rw [sum_mixedFactorialEventWeight]
  calc
    _ = ∫ ω, ∑ e : Fin (∑ j, r j) ↪ Fin n,
        (mixedJointVisitEvent X U r e).indicator (fun _ => (1 : ℝ)) ω ∂P :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∑ e : Fin (∑ j, r j) ↪ Fin n, ∫ ω,
        (mixedJointVisitEvent X U r e).indicator (fun _ => (1 : ℝ)) ω ∂P := by
      apply integral_finsetSum
      intro e _
      exact (integrable_const (1 : ℝ)).indicator
        (measurableSet_mixedJointVisitEvent X hX U hU r e)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      exact integral_indicator_one (measurableSet_mixedJointVisitEvent X hX U hU r e)

/-- Mixed factorial moments converge to the product of the marginal powers
under the explicit interior mixing and close-or-boundary contribution bounds.
The measures can vary with `n`, as in survival-conditioned laws. -/
theorem mixed_factorial_moment_tendsto [MeasurableSpace A]
    (r : J → ℕ) (hr : 0 < ∑ j, r j)
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n j, Measurable (X n j))
    (U : ℕ → J → Set A) (hU : ∀ n j, MeasurableSet (U n j))
    (hdis : ∀ n, Pairwise fun i j => Disjoint (U n i) (U n j))
    {L : ℕ → ℕ} (p : J → ℕ → ℝ) (rate : J → ℝ) {e c : ℕ → ℝ}
    (hp : ∀ j, Tendsto (fun n : ℕ => (n : ℝ) * p j n) atTop (𝓝 (rate j)))
    (hL : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0))
    (he : ∀ᶠ n in atTop, 0 ≤ e n)
    (hmix : Tendsto (fun n : ℕ => (n : ℝ) ^ (∑ j, r j) * e n) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 0))
    (hsep : ∀ᶠ n in atTop, ∀ t ∈ interiorSeparatedConfigurations n (∑ j, r j) (L n),
      |mixedFactorialEventWeight (P n) (X n) (U n) r t - ∏ j, p j n ^ r j| ≤ e n)
    (hclose : ∀ᶠ n in atTop,
      |∑ t ∈ excludedConfigurations n (∑ j, r j) (L n),
        mixedFactorialEventWeight (P n) (X n) (U n) r t| ≤ c n) :
    Tendsto (fun n => ∫ ω,
      ∏ j, ((visitTimes (fun t => X n t ω) (U n j)).card.descFactorial (r j) : ℝ) ∂P n)
      atTop (𝓝 (∏ j, rate j ^ r j)) := by
  have h := configuration_sum_tendsto_reference hr
    (fun n => mixedFactorialEventWeight (P n) (X n) (U n) r)
    (scaled_prod_tendsto r p rate hp) hL he hmix hc hsep hclose
  apply h.congr
  intro n
  exact (integral_prod_visit_descFactorial_eq_sum
    (P n) (X n) (hX n) (U n) (hU n) (hdis n) r).symm

/-- The zeroth mixed factorial moment is exactly one for every probability law. -/
@[simp]
theorem integral_prod_visit_descFactorial_zero {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → A) (U : J → Set A) :
    (∫ ω, ∏ j, ((visitTimes (fun t => X t ω) (U j)).card.descFactorial 0 : ℝ) ∂P) = 1 := by
  simp

end Mixed

end

end ConditionedStableLaws
