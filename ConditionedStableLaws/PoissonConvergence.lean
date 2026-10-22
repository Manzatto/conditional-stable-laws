import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Poisson convergence from falling-factorial moments

The proof uses finite inclusion-exclusion, with an explicit remainder bounded by one higher
factorial moment.
-/

open Filter Finset MeasureTheory ProbabilityTheory Classical
open scoped Topology BigOperators NNReal

namespace ConditionedStableLaws

noncomputable section

private theorem descFactorial_add (x k j : ℕ) :
    x.descFactorial (k + j) = x.descFactorial k * (x - k).descFactorial j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, Nat.descFactorial_succ, ih, Nat.descFactorial_succ]
    simp only [Nat.sub_sub]
    ring_nf

/-- The coefficient occurring in the inclusion-exclusion formula for an atom. -/
def factorialCoefficient (x k j : ℕ) : ℝ :=
  (x.descFactorial (k + j) : ℝ) / ((k.factorial : ℝ) * (j.factorial : ℝ))

theorem factorialCoefficient_eq_choose (x k j : ℕ) :
    factorialCoefficient x k j = (x.choose k : ℝ) * ((x - k).choose j : ℝ) := by
  rw [factorialCoefficient, descFactorial_add,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  field_simp

/-- The truncation includes terms `j = 0,...,R`. -/
def poissonBonferroni (x k R : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * factorialCoefficient x k j

theorem poissonBonferroni_eq_choose (x k R : ℕ) :
    poissonBonferroni x k R = (x.choose k : ℝ) *
      ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * ((x - k).choose j : ℝ) := by
  simp only [poissonBonferroni, factorialCoefficient_eq_choose, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

private theorem alternating_choose_real (m R : ℕ) :
    (∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * ((m + 1).choose j : ℝ)) =
      (-1 : ℝ) ^ R * (m.choose R : ℝ) := by
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := m) (m := R))

/-- A finite inclusion-exclusion error bound, valid for every natural count.
The right side is a factorial moment coefficient, with no exponential bound
on the count required. -/
theorem abs_indicator_sub_poissonBonferroni_le (x k R : ℕ) :
    |(if x = k then 1 else 0 : ℝ) - poissonBonferroni x k R| ≤
      factorialCoefficient x k R := by
  rw [poissonBonferroni_eq_choose, factorialCoefficient_eq_choose]
  rcases lt_trichotomy x k with hlt | rfl | hgt
  · simp [Nat.choose_eq_zero_of_lt hlt, Nat.ne_of_lt hlt]
  · have hz : (∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * (Nat.choose 0 j : ℝ)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        simp
      · simp
    simp [hz]
  · have hneq : x ≠ k := Nat.ne_of_gt hgt
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hgt)
    rw [ite_eq_right hneq, hm, alternating_choose_real]
    simp only [zero_sub, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (Nat.cast_nonneg (x.choose k) : (0 : ℝ) ≤ (x.choose k : ℝ)),
      abs_of_nonneg (Nat.cast_nonneg (m.choose R) : (0 : ℝ) ≤ (m.choose R : ℝ)),
      one_mul]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.choose_le_succ m R

/-- The falling-factorial moment, as a real integral. -/
def factorialMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℕ)
    (r : ℕ) : ℝ := ∫ ω, ((Y ω).descFactorial r : ℝ) ∂P

/-- Bounded natural-valued counts have all factorial moments integrable.
In particular this applies to the visit counts, which are bounded by `n`. -/
theorem integrable_descFactorial_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {Y : Ω → ℕ} (hYm : Measurable Y)
    {B : ℕ} (hB : ∀ ω, Y ω ≤ B) (r : ℕ) :
    Integrable (fun ω => ((Y ω).descFactorial r : ℝ)) P := by
  have hm : Measurable (fun ω => ((Y ω).descFactorial r : ℝ)) :=
    (Measurable.of_discrete : Measurable (fun j : ℕ => (j.descFactorial r : ℝ))).comp hYm
  apply Integrable.of_bound hm.aestronglyMeasurable (B.descFactorial r : ℝ)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Nat.descFactorial_le r (hB ω)

theorem integrable_factorialCoefficient {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → ℕ}
    (hY : ∀ r, Integrable (fun ω => ((Y ω).descFactorial r : ℝ)) P) (k j : ℕ) :
    Integrable (fun ω => factorialCoefficient (Y ω) k j) P :=
  (hY (k + j)).div_const _

theorem integral_factorialCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℕ) (k j : ℕ) :
    (∫ ω, factorialCoefficient (Y ω) k j ∂P) =
      factorialMoment P Y (k + j) / ((k.factorial : ℝ) * (j.factorial : ℝ)) := by
  simp only [factorialCoefficient, integral_div, factorialMoment]

theorem integrable_poissonBonferroni {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → ℕ}
    (hY : ∀ r, Integrable (fun ω => ((Y ω).descFactorial r : ℝ)) P) (k R : ℕ) :
    Integrable (fun ω => poissonBonferroni (Y ω) k R) P := by
  apply integrable_finsetSum
  intro j _
  exact (integrable_factorialCoefficient hY k j).const_mul _

theorem integral_poissonBonferroni {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → ℕ}
    (hY : ∀ r, Integrable (fun ω => ((Y ω).descFactorial r : ℝ)) P) (k R : ℕ) :
    (∫ ω, poissonBonferroni (Y ω) k R ∂P) =
      ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * factorialMoment P Y (k + j) /
        ((k.factorial : ℝ) * (j.factorial : ℝ)) := by
  rw [show (fun ω => poissonBonferroni (Y ω) k R) =
    (fun ω => ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * factorialCoefficient (Y ω) k j)
      from rfl]
  rw [integral_finsetSum _ (fun j _ => (integrable_factorialCoefficient hY k j).const_mul _)]
  simp only [integral_const_mul, integral_factorialCoefficient, mul_div_assoc]

/-- The atom probability is approximated by a finite polynomial in factorial
moments, with an explicit error controlled by a further factorial moment. -/
theorem atom_probability_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℕ) (hYm : Measurable Y)
    (hY : ∀ r, Integrable (fun ω => ((Y ω).descFactorial r : ℝ)) P) (k R : ℕ) :
    |P.real {ω | Y ω = k} -
      ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * factorialMoment P Y (k + j) /
        ((k.factorial : ℝ) * (j.factorial : ℝ))| ≤
      factorialMoment P Y (k + R) / ((k.factorial : ℝ) * (R.factorial : ℝ)) := by
  let A : Set Ω := {ω | Y ω = k}
  have hA : MeasurableSet A := hYm (measurableSet_singleton k)
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have hb := integrable_poissonBonferroni hY k R
  have hAtom : P.real {ω | Y ω = k} = ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P := by
    simpa using (integral_indicator_const (μ := P) (1 : ℝ) hA).symm
  rw [← integral_poissonBonferroni hY k R, hAtom, ← integral_sub hi hb,
    ← integral_factorialCoefficient P Y k R]
  calc
    _ ≤ ∫ ω, |A.indicator (fun _ => (1 : ℝ)) ω - poissonBonferroni (Y ω) k R| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ _ := integral_mono (hi.sub hb).abs (integrable_factorialCoefficient hY k R) (fun ω => by
      simpa only [A, Set.indicator_apply, Set.mem_ofPred_eq] using
        abs_indicator_sub_poissonBonferroni_le (Y ω) k R)

theorem tendsto_of_finite_approximations {a : ℕ → ℝ}
    {b c : ℕ → ℕ → ℝ} {B C : ℕ → ℝ} {limit : ℝ}
    (hbound : ∀ R n, |a n - b R n| ≤ c R n)
    (hb : ∀ R, Tendsto (b R) atTop (𝓝 (B R)))
    (hc : ∀ R, Tendsto (c R) atTop (𝓝 (C R)))
    (hB : Tendsto B atTop (𝓝 limit)) (hC : Tendsto C atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 limit) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨R, hBR, hCR⟩ := ((Metric.tendsto_nhds.mp hB) (ε / 4) hε4).and
    ((Metric.tendsto_nhds.mp hC) (ε / 4) hε4) |>.exists
  filter_upwards [(Metric.tendsto_nhds.mp (hb R)) (ε / 4) hε4,
    (Metric.tendsto_nhds.mp (hc R)) (ε / 4) hε4] with n hbn hcn
  simp only [Real.dist_eq, sub_zero] at hBR hCR hbn hcn ⊢
  have htri : |a n - limit| ≤ |a n - b R n| + |b R n - B R| + |B R - limit| := by
    calc
      _ = |(a n - b R n) + (b R n - B R) + (B R - limit)| := by congr 1; ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
  have hcR : C R < ε / 4 := (le_abs_self _).trans_lt hCR
  have hcn' : c R n < C R + ε / 4 := by linarith [(le_abs_self (c R n - C R)).trans_lt hcn]
  linarith [hbound R n]

/-- The deterministic limit of the finite moment polynomial is the Poisson mass. -/
theorem poisson_polynomial_tendsto (rate : ℝ) (k : ℕ) :
    Tendsto (fun R : ℕ => ∑ j ∈ Finset.range (R + 1),
      (-1 : ℝ) ^ j * rate ^ (k + j) / ((k.factorial : ℝ) * (j.factorial : ℝ)))
      atTop (𝓝 (Real.exp (-rate) * rate ^ k / (k.factorial : ℝ))) := by
  have hs : HasSum (fun j : ℕ => (-rate) ^ j / (j.factorial : ℝ)) (Real.exp (-rate)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (-rate)
  have h := ((hs.mul_left (rate ^ k / (k.factorial : ℝ))).tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  · ext R
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add, neg_eq_neg_one_mul, mul_pow]
    ring_nf
  · ring_nf

/-- The limiting remainder bound vanishes with the truncation order. -/
theorem poisson_remainder_tendsto_zero (rate : ℝ) (k : ℕ) :
    Tendsto (fun R : ℕ => rate ^ (k + R) /
      ((k.factorial : ℝ) * (R.factorial : ℝ))) atTop (𝓝 0) := by
  have hs : Summable (fun j : ℕ => rate ^ j / (j.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp rate).summable
  have h := hs.tendsto_atTop_zero.const_mul (rate ^ k / (k.factorial : ℝ))
  simp only [mul_zero] at h
  convert h using 1
  ext R
  rw [pow_add]
  ring_nf

/-- Convergence of every integrable falling-factorial moment gives convergence
of each atom probability to the Poisson formula, under varying laws. -/
theorem atom_probability_tendsto_of_factorial_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Y : ℕ → Ω → ℕ) (hYm : ∀ n, Measurable (Y n))
    (hYi : ∀ n r, Integrable (fun ω => ((Y n ω).descFactorial r : ℝ)) (P n))
    (rate : ℝ)
    (hm : ∀ r, Tendsto (fun n => factorialMoment (P n) (Y n) r) atTop (𝓝 (rate ^ r)))
    (k : ℕ) :
    Tendsto (fun n => (P n).real {ω | Y n ω = k}) atTop
      (𝓝 (Real.exp (-rate) * rate ^ k / (k.factorial : ℝ))) := by
  apply tendsto_of_finite_approximations
    (b := fun R n => ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j *
      factorialMoment (P n) (Y n) (k + j) / ((k.factorial : ℝ) * (j.factorial : ℝ)))
    (c := fun R n => factorialMoment (P n) (Y n) (k + R) /
      ((k.factorial : ℝ) * (R.factorial : ℝ)))
    (B := fun R => ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j *
      rate ^ (k + j) / ((k.factorial : ℝ) * (j.factorial : ℝ)))
    (C := fun R => rate ^ (k + R) / ((k.factorial : ℝ) * (R.factorial : ℝ)))
  · intro R n
    exact atom_probability_error_le (P n) (Y n) (hYm n) (hYi n) k R
  · intro R
    exact tendsto_finsetSum _ (fun j _ => ((hm (k + j)).const_mul ((-1 : ℝ) ^ j)).div_const _)
  · intro R
    exact (hm (k + R)).div_const _
  · exact poisson_polynomial_tendsto rate k
  · exact poisson_remainder_tendsto_zero rate k

/-- On the discrete natural numbers, convergence of all atom probabilities to
a probability law implies weak convergence of the laws. -/
theorem probabilityMeasure_nat_tendsto_of_atoms (μ : ℕ → ProbabilityMeasure ℕ)
    (ν : ProbabilityMeasure ℕ)
    (h : ∀ k, Tendsto (fun n => (μ n : Measure ℕ).real {k}) atTop
      (𝓝 ((ν : Measure ℕ).real {k}))) : Tendsto μ atTop (𝓝 ν) := by
  let S : Set (Set ℕ) := {s | ∃ k, s = {k}}
  have hS : IsPiSystem S := by
    rintro s ⟨k, rfl⟩ t ⟨j, rfl⟩ hne
    obtain ⟨x, hx, hx'⟩ := hne
    have hkj : k = j := (Set.mem_singleton_iff.mp hx).symm.trans (Set.mem_singleton_iff.mp hx')
    refine ⟨k, ?_⟩
    rw [← hkj, Set.inter_self]
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨k, rfl⟩
    exact measurableSet_singleton k
  · intro u _ x hx
    exact ⟨{x}, ⟨x, rfl⟩, isOpen_discrete _ |>.mem_nhds (Set.mem_singleton x),
      Set.singleton_subset_iff.mpr hx⟩
  · rintro s ⟨k, rfl⟩
    apply NNReal.tendsto_coe.mp
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using h k

/-- The natural-valued law of a random variable. -/
def natProbabilityLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℕ) : ProbabilityMeasure ℕ :=
  ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) Y

/-- The Poisson law bundled with its probability property and weak topology. -/
def poissonProbabilityMeasure (rate : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨poissonMeasure rate, inferInstance⟩

/-- The univariate Poisson method of falling-factorial moments, from finite inclusion-exclusion. The
random variables and probability laws may both vary with `n`. -/
theorem poisson_convergence_of_factorial_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Y : ℕ → Ω → ℕ) (hYm : ∀ n, Measurable (Y n))
    (hYi : ∀ n r, Integrable (fun ω => ((Y n ω).descFactorial r : ℝ)) (P n))
    (rate : ℝ≥0)
    (hm : ∀ r, Tendsto (fun n => factorialMoment (P n) (Y n) r) atTop
      (𝓝 ((rate : ℝ) ^ r))) :
    Tendsto (fun n => natProbabilityLaw (P n) (Y n)) atTop
      (𝓝 (poissonProbabilityMeasure rate)) := by
  apply probabilityMeasure_nat_tendsto_of_atoms
  intro k
  have h := atom_probability_tendsto_of_factorial_moments P Y hYm hYi (rate : ℝ) hm k
  have hmap (n : ℕ) : (natProbabilityLaw (P n) (Y n) : Measure ℕ).real {k} =
      (P n).real {ω | Y n ω = k} := by
    change ((P n).map (Y n)).real {k} = _
    rw [Measure.real, Measure.map_apply (hYm n) (measurableSet_singleton k)]
    rfl
  have hpois : (poissonProbabilityMeasure rate : Measure ℕ).real {k} =
      Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ k / (k.factorial : ℝ) :=
    poissonMeasure_real_singleton rate k
  simpa only [hmap, hpois] using h

end

end ConditionedStableLaws
