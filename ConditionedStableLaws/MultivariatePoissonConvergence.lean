import ConditionedStableLaws.PoissonConvergence
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Independent Poisson limits from mixed factorial moments

Finite products of the univariate inclusion-exclusion polynomials approximate joint atom indicators.
Their explicit remainder is a polynomial in mixed factorial moments. This gives the joint limiting
law; the prelimit variables need not be independent.
-/

open Filter Finset MeasureTheory ProbabilityTheory Classical
open scoped Topology BigOperators NNReal

namespace ConditionedStableLaws

noncomputable section

private theorem abs_prod_sub_prod_le {J : Type*} (s : Finset J)
    (a b c : J → ℝ) (ha : ∀ j ∈ s, |a j| ≤ 1)
    (hc : ∀ j ∈ s, |a j - b j| ≤ c j) :
    |∏ j ∈ s, a j - ∏ j ∈ s, b j| ≤ (∏ j ∈ s, (1 + c j)) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have ci : 0 ≤ c i := (abs_nonneg _).trans (hc i (Finset.mem_insert_self _ _))
    have hb : |∏ j ∈ s, b j| ≤ ∏ j ∈ s, (1 + c j) := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro j hj
      have hj' : j ∈ insert i s := Finset.mem_insert_of_mem hj
      have he : b j = a j - (a j - b j) := by ring
      rw [he]
      exact (abs_sub _ _).trans (add_le_add (ha j hj') (hc j hj'))
    have hold := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert his, Finset.prod_insert his, Finset.prod_insert his]
    calc
      _ = |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
          (a i - b i) * ∏ j ∈ s, b j| := by congr 1; ring
      _ ≤ |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
          |a i - b i| * |∏ j ∈ s, b j| := by
        simpa only [abs_mul] using abs_add_le
          (a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j))
          ((a i - b i) * ∏ j ∈ s, b j)
      _ ≤ 1 * ((∏ j ∈ s, (1 + c j)) - 1) + c i * ∏ j ∈ s, (1 + c j) := by
        apply add_le_add
        · exact mul_le_mul (ha i (Finset.mem_insert_self _ _)) hold (abs_nonneg _) (by norm_num)
        · exact mul_le_mul (hc i (Finset.mem_insert_self _ _)) hb (abs_nonneg _) ci
      _ = _ := by ring

variable {J : Type*} [Fintype J]

/-- A rectangular inclusion-exclusion approximation to a vector atom. -/
def mixedPoissonBonferroni (x k : J → ℕ) (R : ℕ) : ℝ :=
  ∏ j, poissonBonferroni (x j) (k j) R

/-- A nonnegative polynomial remainder involving mixed factorial powers. -/
def mixedPoissonRemainder (x k : J → ℕ) (R : ℕ) : ℝ :=
  (∏ j, (1 + factorialCoefficient (x j) (k j) R)) - 1

theorem abs_indicator_sub_mixedPoissonBonferroni_le (x k : J → ℕ) (R : ℕ) :
    |(if x = k then 1 else 0 : ℝ) - mixedPoissonBonferroni x k R| ≤
      mixedPoissonRemainder x k R := by
  have hh := abs_prod_sub_prod_le Finset.univ
    (fun j => if x j = k j then (1 : ℝ) else 0)
    (fun j => poissonBonferroni (x j) (k j) R)
    (fun j => factorialCoefficient (x j) (k j) R)
    (by intro j _; split_ifs <;> norm_num)
    (fun j _ => abs_indicator_sub_poissonBonferroni_le (x j) (k j) R)
  simpa only [Finset.prod_boole, Finset.mem_univ, forall_const, ← funext_iff,
    mixedPoissonBonferroni, mixedPoissonRemainder] using hh

/-- Mixed falling-factorial moments of the vector of counts. -/
def mixedFactorialMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → J → ℕ) (r : J → ℕ) : ℝ :=
  ∫ ω, ∏ j, ((Y ω j).descFactorial (r j) : ℝ) ∂P

/-- Coordinatewise bounded measurable counts have all mixed factorial
moments integrable, as needed for finite visit counts. -/
theorem integrable_mixed_descFactorial_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {Y : Ω → J → ℕ} (hYm : Measurable Y)
    (B : J → ℕ) (hB : ∀ ω j, Y ω j ≤ B j) (r : J → ℕ) :
    Integrable (fun ω => ∏ j, ((Y ω j).descFactorial (r j) : ℝ)) P := by
  have hm : Measurable (fun ω => ∏ j, ((Y ω j).descFactorial (r j) : ℝ)) :=
    (Measurable.of_discrete : Measurable
      (fun x : J → ℕ => ∏ j, ((x j).descFactorial (r j) : ℝ))).comp hYm
  apply Integrable.of_bound hm.aestronglyMeasurable (∏ j, ((B j).descFactorial (r j) : ℝ))
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))]
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
  intro j _
  exact_mod_cast Nat.descFactorial_le (r j) (hB ω j)

/-- A finite product of polynomials expressed in the falling-factorial basis. -/
def factorialPolynomial {K : J → Type*} [∀ j, Fintype (K j)]
    (coefficient : ∀ j, K j → ℝ) (order : ∀ j, K j → ℕ) (x : J → ℕ) : ℝ :=
  ∏ j, ∑ q, coefficient j q * (x j).descFactorial (order j q)

theorem factorialPolynomial_expansion {K : J → Type*} [∀ j, Fintype (K j)]
    (coefficient : ∀ j, K j → ℝ) (order : ∀ j, K j → ℕ) (x : J → ℕ) :
    factorialPolynomial coefficient order x =
      ∑ q : ∀ j, K j, (∏ j, coefficient j (q j)) *
        ∏ j, ((x j).descFactorial (order j (q j)) : ℝ) := by
  simp only [factorialPolynomial, Fintype.prod_sum, Finset.prod_mul_distrib]

theorem integrable_factorialPolynomial {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → J → ℕ}
    (hY : ∀ r : J → ℕ, Integrable (fun ω => ∏ j, ((Y ω j).descFactorial (r j) : ℝ)) P)
    {K : J → Type*} [∀ j, Fintype (K j)]
    (coefficient : ∀ j, K j → ℝ) (order : ∀ j, K j → ℕ) :
    Integrable (fun ω => factorialPolynomial coefficient order (Y ω)) P := by
  simp only [factorialPolynomial_expansion]
  apply integrable_finsetSum
  intro q _
  exact (hY (fun j => order j (q j))).const_mul _

theorem integral_factorialPolynomial {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → J → ℕ}
    (hY : ∀ r : J → ℕ, Integrable (fun ω => ∏ j, ((Y ω j).descFactorial (r j) : ℝ)) P)
    {K : J → Type*} [∀ j, Fintype (K j)]
    (coefficient : ∀ j, K j → ℝ) (order : ∀ j, K j → ℕ) :
    (∫ ω, factorialPolynomial coefficient order (Y ω) ∂P) =
      ∑ q : ∀ j, K j, (∏ j, coefficient j (q j)) *
        mixedFactorialMoment P Y (fun j => order j (q j)) := by
  simp only [factorialPolynomial_expansion]
  rw [integral_finsetSum _ (fun q _ => (hY (fun j => order j (q j))).const_mul _)]
  simp only [integral_const_mul, mixedFactorialMoment]

theorem integral_factorialPolynomial_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) (Y : ℕ → Ω → J → ℕ)
    (hY : ∀ n (r : J → ℕ), Integrable (fun ω => ∏ j, ((Y n ω j).descFactorial (r j) : ℝ)) (P n))
    (rate : J → ℝ)
    (hm : ∀ r, Tendsto (fun n => mixedFactorialMoment (P n) (Y n) r) atTop
      (𝓝 (∏ j, rate j ^ r j)))
    {K : J → Type*} [∀ j, Fintype (K j)]
    (coefficient : ∀ j, K j → ℝ) (order : ∀ j, K j → ℕ) :
    Tendsto (fun n => ∫ ω, factorialPolynomial coefficient order (Y n ω) ∂P n)
      atTop (𝓝 (∏ j, ∑ q, coefficient j q * rate j ^ order j q)) := by
  simp only [integral_factorialPolynomial (hY _)]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]
  exact tendsto_finsetSum _ (fun q _ =>
    (hm (fun j => order j (q j))).const_mul (∏ j, coefficient j (q j)))

theorem mixedPoissonBonferroni_eq_polynomial (x k : J → ℕ) (R : ℕ) :
    mixedPoissonBonferroni x k R = factorialPolynomial
      (fun j (q : Fin (R + 1)) => (-1 : ℝ) ^ q.val /
        ((k j).factorial * (q.val.factorial : ℝ)))
      (fun j (q : Fin (R + 1)) => k j + q.val) x := by
  apply Finset.prod_congr rfl
  intro j _
  rw [poissonBonferroni, Fin.sum_univ_eq_sum_range
    (fun q : ℕ => (-1 : ℝ) ^ q / ((k j).factorial * (q.factorial : ℝ)) *
      ((x j).descFactorial (k j + q) : ℝ))]
  apply Finset.sum_congr rfl
  intro q _
  simp only [factorialCoefficient]
  ring

theorem mixedPoissonRemainder_eq_polynomial (x k : J → ℕ) (R : ℕ) :
    mixedPoissonRemainder x k R = factorialPolynomial
      (fun j (q : Bool) => if q then (1 : ℝ) / ((k j).factorial * (R.factorial : ℝ)) else 1)
      (fun j (q : Bool) => if q then k j + R else 0) x - 1 := by
  simp only [mixedPoissonRemainder, factorialPolynomial, Fintype.sum_bool,
    Bool.false_eq_true, ite_false, ite_true, Nat.descFactorial_zero, Nat.cast_one,
    mul_one, factorialCoefficient, one_div]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  ring

/-- The finite mixed moment polynomial at the limiting marginal rates. -/
def mixedPoissonPolynomialLimit (rate : J → ℝ) (k : J → ℕ) (R : ℕ) : ℝ :=
  ∏ j, ∑ q ∈ Finset.range (R + 1), (-1 : ℝ) ^ q * rate j ^ (k j + q) /
    ((k j).factorial * (q.factorial : ℝ))

/-- The limiting bound for the rectangular inclusion-exclusion remainder. -/
def mixedPoissonRemainderLimit (rate : J → ℝ) (k : J → ℕ) (R : ℕ) : ℝ :=
  (∏ j, (1 + rate j ^ (k j + R) / ((k j).factorial * (R.factorial : ℝ)))) - 1

theorem mixedPoissonPolynomialLimit_tendsto (rate : J → ℝ) (k : J → ℕ) :
    Tendsto (mixedPoissonPolynomialLimit rate k) atTop
      (𝓝 (∏ j, Real.exp (-rate j) * rate j ^ k j / (k j).factorial)) :=
  tendsto_finsetProd _ (fun j _ => poisson_polynomial_tendsto (rate j) (k j))

theorem mixedPoissonRemainderLimit_tendsto_zero (rate : J → ℝ) (k : J → ℕ) :
    Tendsto (mixedPoissonRemainderLimit rate k) atTop (𝓝 0) := by
  have h := (tendsto_finsetProd Finset.univ
    (fun j _ => (poisson_remainder_tendsto_zero (rate j) (k j)).const_add 1)).sub_const 1
  convert h using 1
  · rfl
  · simp

theorem integrable_mixedPoissonBonferroni {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → J → ℕ}
    (hY : ∀ r : J → ℕ, Integrable (fun ω => ∏ j, ((Y ω j).descFactorial (r j) : ℝ)) P)
    (k : J → ℕ) (R : ℕ) : Integrable (fun ω => mixedPoissonBonferroni (Y ω) k R) P := by
  simp only [mixedPoissonBonferroni_eq_polynomial]
  exact integrable_factorialPolynomial hY _ _

theorem integrable_mixedPoissonRemainder {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {Y : Ω → J → ℕ}
    (hY : ∀ r : J → ℕ, Integrable (fun ω => ∏ j, ((Y ω j).descFactorial (r j) : ℝ)) P)
    (k : J → ℕ) (R : ℕ) : Integrable (fun ω => mixedPoissonRemainder (Y ω) k R) P := by
  simp only [mixedPoissonRemainder_eq_polynomial]
  exact (integrable_factorialPolynomial hY _ _).sub (integrable_const _)

theorem integral_mixedPoissonBonferroni_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) (Y : ℕ → Ω → J → ℕ)
    (hY : ∀ n (r : J → ℕ), Integrable (fun ω => ∏ j, ((Y n ω j).descFactorial (r j) : ℝ)) (P n))
    (rate : J → ℝ)
    (hm : ∀ r, Tendsto (fun n => mixedFactorialMoment (P n) (Y n) r) atTop
      (𝓝 (∏ j, rate j ^ r j))) (k : J → ℕ) (R : ℕ) :
    Tendsto (fun n => ∫ ω, mixedPoissonBonferroni (Y n ω) k R ∂P n) atTop
      (𝓝 (mixedPoissonPolynomialLimit rate k R)) := by
  simp only [mixedPoissonBonferroni_eq_polynomial]
  convert integral_factorialPolynomial_tendsto P Y hY rate hm
    (fun j (q : Fin (R + 1)) => (-1 : ℝ) ^ q.val /
      ((k j).factorial * (q.val.factorial : ℝ)))
    (fun j (q : Fin (R + 1)) => k j + q.val) using 1
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => (-1 : ℝ) ^ q / ((k j).factorial * (q.factorial : ℝ)) * rate j ^ (k j + q))]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem integral_mixedPoissonRemainder_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)] (Y : ℕ → Ω → J → ℕ)
    (hY : ∀ n (r : J → ℕ), Integrable (fun ω => ∏ j, ((Y n ω j).descFactorial (r j) : ℝ)) (P n))
    (rate : J → ℝ)
    (hm : ∀ r, Tendsto (fun n => mixedFactorialMoment (P n) (Y n) r) atTop
      (𝓝 (∏ j, rate j ^ r j))) (k : J → ℕ) (R : ℕ) :
    Tendsto (fun n => ∫ ω, mixedPoissonRemainder (Y n ω) k R ∂P n) atTop
      (𝓝 (mixedPoissonRemainderLimit rate k R)) := by
  simp only [mixedPoissonRemainder_eq_polynomial,
    integral_sub (integrable_factorialPolynomial (hY _) _ _) (integrable_const _), integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hh := (integral_factorialPolynomial_tendsto P Y hY rate hm
    (fun j (q : Bool) => if q then (1 : ℝ) / ((k j).factorial * (R.factorial : ℝ)) else 1)
    (fun j (q : Bool) => if q then k j + R else 0)).sub_const 1
  simpa [mixedPoissonRemainderLimit, Fintype.sum_bool, mul_comm, div_eq_mul_inv, add_comm] using hh

/-- An explicit error bound for the probability of a vector atom. -/
theorem mixed_atom_probability_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → J → ℕ) (hYm : Measurable Y)
    (hYi : ∀ r : J → ℕ, Integrable (fun ω => ∏ j, ((Y ω j).descFactorial (r j) : ℝ)) P)
    (k : J → ℕ) (R : ℕ) :
    |P.real {ω | Y ω = k} - ∫ ω, mixedPoissonBonferroni (Y ω) k R ∂P| ≤
      ∫ ω, mixedPoissonRemainder (Y ω) k R ∂P := by
  let A : Set Ω := {ω | Y ω = k}
  have hA : MeasurableSet A := hYm (measurableSet_singleton k)
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have hb := integrable_mixedPoissonBonferroni hYi k R
  have hAtom : P.real {ω | Y ω = k} = ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P := by
    simpa using (integral_indicator_const (μ := P) (1 : ℝ) hA).symm
  rw [hAtom, ← integral_sub hi hb]
  calc
    _ ≤ ∫ ω, |A.indicator (fun _ => (1 : ℝ)) ω - mixedPoissonBonferroni (Y ω) k R| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ _ := integral_mono (hi.sub hb).abs (integrable_mixedPoissonRemainder hYi k R)
      (fun ω => by
        simpa only [A, Set.indicator_apply, Set.mem_ofPred_eq] using
          abs_indicator_sub_mixedPoissonBonferroni_le (Y ω) k R)

/-- All mixed factorial moment limits determine every joint atom probability. The prelimit vectors
need not have independent coordinates. -/
theorem mixed_atom_probability_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Y : ℕ → Ω → J → ℕ) (hYm : ∀ n, Measurable (Y n))
    (hYi : ∀ n (r : J → ℕ), Integrable (fun ω => ∏ j, ((Y n ω j).descFactorial (r j) : ℝ)) (P n))
    (rate : J → ℝ)
    (hm : ∀ r, Tendsto (fun n => mixedFactorialMoment (P n) (Y n) r) atTop
      (𝓝 (∏ j, rate j ^ r j))) (k : J → ℕ) :
    Tendsto (fun n => (P n).real {ω | Y n ω = k}) atTop
      (𝓝 (∏ j, Real.exp (-rate j) * rate j ^ k j / (k j).factorial)) := by
  apply tendsto_of_finite_approximations
    (b := fun R n => ∫ ω, mixedPoissonBonferroni (Y n ω) k R ∂P n)
    (c := fun R n => ∫ ω, mixedPoissonRemainder (Y n ω) k R ∂P n)
    (B := mixedPoissonPolynomialLimit rate k) (C := mixedPoissonRemainderLimit rate k)
  · intro R n
    exact mixed_atom_probability_error_le (P n) (Y n) (hYm n) (hYi n) k R
  · intro R
    exact integral_mixedPoissonBonferroni_tendsto P Y hYi rate hm k R
  · intro R
    exact integral_mixedPoissonRemainder_tendsto P Y hYi rate hm k R
  · exact mixedPoissonPolynomialLimit_tendsto rate k
  · exact mixedPoissonRemainderLimit_tendsto_zero rate k

/-- Point probabilities determine weak convergence on a finite vector of
natural-valued coordinates. -/
theorem probabilityMeasure_natVector_tendsto_of_atoms
    (μ : ℕ → ProbabilityMeasure (J → ℕ)) (ν : ProbabilityMeasure (J → ℕ))
    (h : ∀ k, Tendsto (fun n => (μ n : Measure (J → ℕ)).real {k}) atTop
      (𝓝 ((ν : Measure (J → ℕ)).real {k}))) : Tendsto μ atTop (𝓝 ν) := by
  let S : Set (Set (J → ℕ)) := {s | ∃ k, s = {k}}
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

/-- The finite product of Poisson laws. -/
def independentPoissonProbabilityMeasure (rate : J → ℝ≥0) : ProbabilityMeasure (J → ℕ) :=
  ⟨Measure.pi (fun j => poissonMeasure (rate j)), inferInstance⟩

theorem independentPoissonProbabilityMeasure_real_singleton (rate : J → ℝ≥0) (k : J → ℕ) :
    (independentPoissonProbabilityMeasure rate : Measure (J → ℕ)).real {k} =
      ∏ j, Real.exp (-(rate j : ℝ)) * (rate j : ℝ) ^ k j / (k j).factorial := by
  change (Measure.pi (fun j => poissonMeasure (rate j))).real {k} = _
  rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun j _ => poissonMeasure_real_singleton (rate j) (k j))

/-- The coordinates of the limiting law are independent. -/
theorem independentPoissonProbabilityMeasure_independent (rate : J → ℝ≥0) :
    iIndepFun (fun j (x : J → ℕ) => x j)
      (independentPoissonProbabilityMeasure rate : Measure (J → ℕ)) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- Each limiting coordinate has the prescribed Poisson law. -/
theorem independentPoissonProbabilityMeasure_coordinate_hasLaw (rate : J → ℝ≥0) (j : J) :
    HasLaw (fun x : J → ℕ => x j) (poissonMeasure (rate j))
      (independentPoissonProbabilityMeasure rate : Measure (J → ℕ)) :=
  (measurePreserving_eval (fun i => poissonMeasure (rate i)) j).hasLaw

/-- The joint law of a natural-valued vector. -/
def natVectorProbabilityLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → J → ℕ) : ProbabilityMeasure (J → ℕ) :=
  ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) Y

/-- The finite multivariate method of falling-factorial moments: convergence of all mixed moments to
the product monomials gives weak convergence of the vector laws to independent Poisson coordinates.
-/
theorem independent_poisson_convergence_of_mixed_factorial_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Y : ℕ → Ω → J → ℕ) (hYm : ∀ n, Measurable (Y n))
    (hYi : ∀ n (r : J → ℕ), Integrable (fun ω => ∏ j, ((Y n ω j).descFactorial (r j) : ℝ)) (P n))
    (rate : J → ℝ≥0)
    (hm : ∀ r, Tendsto (fun n => mixedFactorialMoment (P n) (Y n) r) atTop
      (𝓝 (∏ j, (rate j : ℝ) ^ r j))) :
    Tendsto (fun n => natVectorProbabilityLaw (P n) (Y n)) atTop
      (𝓝 (independentPoissonProbabilityMeasure rate)) := by
  apply probabilityMeasure_natVector_tendsto_of_atoms
  intro k
  have h := mixed_atom_probability_tendsto P Y hYm hYi (fun j => (rate j : ℝ)) hm k
  have hmap (n : ℕ) : (natVectorProbabilityLaw (P n) (Y n) : Measure (J → ℕ)).real {k} =
      (P n).real {ω | Y n ω = k} := by
    change ((P n).map (Y n)).real {k} = _
    rw [Measure.real, Measure.map_apply (hYm n) (measurableSet_singleton k)]
    rfl
  simpa only [hmap, independentPoissonProbabilityMeasure_real_singleton] using h

end

end ConditionedStableLaws
