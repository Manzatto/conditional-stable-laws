import ConditionedStableLaws.RareEventMoments
import ConditionedStableLaws.MultivariatePoissonConvergence

/-!
# From rare-event configuration estimates to independent Poisson counts

The counting and probability arguments for measurable visits under varying laws. The inputs are
explicit separated-event error and excluded-configuration bounds for each order; moment convergence
and weak convergence are conclusions.
-/

open Filter MeasureTheory Set Classical
open scoped Topology BigOperators NNReal

namespace ConditionedStableLaws
noncomputable section

variable {Ω A J : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype J]

/-- The finite vector of visit counts. -/
def visitCountVector {n : ℕ} (X : Fin n → Ω → A) (U : J → Set A) (ω : Ω) : J → ℕ :=
  fun j => (visitTimes (fun t => X t ω) (U j)).card

omit [Fintype J] in
theorem measurable_visitCountVector {n : ℕ} (X : Fin n → Ω → A)
    (hX : ∀ t, Measurable (X t)) (U : J → Set A) (hU : ∀ j, MeasurableSet (U j)) :
    Measurable (visitCountVector X U) := by
  apply Measurable.of_eval
  intro j
  have heq : (fun ω => visitCountVector X U ω j) =
      (fun ω => ∑ t : Fin n, if X t ω ∈ U j then (1 : ℕ) else 0) := by
    funext ω
    simp [visitCountVector, visitTimes, Finset.sum_boole]
  rw [heq]
  exact Finset.measurable_sum _ fun t _ =>
    Measurable.ite ((hU j).preimage (hX t)) measurable_const measurable_const

omit [MeasurableSpace Ω] [MeasurableSpace A] [Fintype J] in
theorem visitCountVector_le {n : ℕ} (X : Fin n → Ω → A) (U : J → Set A)
    (ω : Ω) (j : J) : visitCountVector X U ω j ≤ n := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

/-- The concrete analytic estimates required at one positive mixed order.
The exclusion set includes both short inter-observation gaps and endpoint
strips, so no mixing assertion is imposed on time-zero observations. -/
structure RareConfigurationEstimates
    (P : ℕ → Measure Ω) (X : ∀ n : ℕ, Fin n → Ω → A)
    (U : ℕ → J → Set A) (p : J → ℕ → ℝ) (r : J → ℕ) where
  cutoff : ℕ → ℕ
  error : ℕ → ℝ
  excludedBound : ℕ → ℝ
  cutoff_sublinear : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0)
  error_nonneg : ∀ᶠ n in atTop, 0 ≤ error n
  scaled_error_tendsto : Tendsto (fun n : ℕ => (n : ℝ) ^ (∑ j, r j) * error n)
    atTop (𝓝 0)
  excluded_tendsto : Tendsto excludedBound atTop (𝓝 0)
  separated_error : ∀ᶠ n in atTop,
    ∀ t ∈ interiorSeparatedConfigurations n (∑ j, r j) (cutoff n),
      |mixedFactorialEventWeight (P n) (X n) (U n) r t - ∏ j, p j n ^ r j| ≤ error n
  excluded_error : ∀ᶠ n in atTop,
    |∑ t ∈ excludedConfigurations n (∑ j, r j) (cutoff n),
      mixedFactorialEventWeight (P n) (X n) (U n) r t| ≤ excludedBound n

/-- Explicit rare-event estimates at every positive mixed order imply the joint independent-Poisson
limit for the visit-count vectors. -/
theorem independent_poisson_visit_counts_of_configuration_estimates
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (U : ℕ → J → Set A) (hU : ∀ n j, MeasurableSet (U n j))
    (hdis : ∀ n, Pairwise fun i j => Disjoint (U n i) (U n j))
    (p : J → ℕ → ℝ) (rate : J → ℝ≥0)
    (hp : ∀ j, Tendsto (fun n : ℕ => (n : ℝ) * p j n) atTop (𝓝 (rate j : ℝ)))
    (estimates : ∀ r : J → ℕ, 0 < ∑ j, r j → RareConfigurationEstimates P X U p r) :
    Tendsto (fun n => natVectorProbabilityLaw (P n) (visitCountVector (X n) (U n)))
      atTop (𝓝 (independentPoissonProbabilityMeasure rate)) := by
  apply independent_poisson_convergence_of_mixed_factorial_moments P
    (fun n => visitCountVector (X n) (U n))
    (fun n => measurable_visitCountVector (X n) (hX n) (U n) (hU n))
  · intro n r
    exact integrable_mixed_descFactorial_of_bounded
      (measurable_visitCountVector (X n) (hX n) (U n) (hU n))
      (fun _ => n) (visitCountVector_le (X n) (U n)) r
  · intro r
    by_cases hr : 0 < ∑ j, r j
    · let e := estimates r hr
      exact mixed_factorial_moment_tendsto r hr P X hX U hU hdis p (fun j => (rate j : ℝ))
        hp e.cutoff_sublinear e.error_nonneg e.scaled_error_tendsto e.excluded_tendsto
        e.separated_error e.excluded_error
    · have hr0 : ∀ j, r j = 0 := by
        have hsum : ∑ j, r j = 0 := Nat.eq_zero_of_not_pos hr
        exact fun j => (Finset.sum_eq_zero_iff.mp hsum) j (Finset.mem_univ _)
      simp [mixedFactorialMoment, hr0]

end
end ConditionedStableLaws
