import ConditionedStableLaws.PositivePolynomial
import Mathlib.Analysis.Subadditive

/-!
# A strictly positive operator growth rate

Fekete's lemma applied to `log ‖P^n‖` gives a positive norm-growth limit, using the exponential
lower bound from H.
-/

open Set Filter
open scoped Topology BoundedContinuousFunction

namespace ConditionedStableLaws.OperatorGrowth
noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]

omit [NormOneClass A] in
theorem log_norm_pow_subadditive (T : A)
    (hpos : ∀ n : ℕ, 0 < ‖T^n‖) :
    Subadditive (fun n : ℕ => Real.log ‖T^n‖) := by
  intro m n
  dsimp
  rw [pow_add]
  exact (Real.log_le_log (by rw [← pow_add]; exact hpos (m+n))
    (norm_mul_le _ _)).trans_eq (Real.log_mul (hpos m).ne' (hpos n).ne')

theorem log_norm_pow_bddBelow (T : A) {c : ℝ} (hc : 0 < c)
    (hb : ∀ n : ℕ, c^n ≤ ‖T^n‖) :
    BddBelow (range (fun n : ℕ => Real.log ‖T^n‖ / n)) := by
  refine ⟨min 0 (Real.log c), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · simp [hn]
  · have hnreal : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hl := Real.log_le_log (pow_pos hc n) (hb n)
    rw [Real.log_pow] at hl
    exact (min_le_right _ _).trans ((le_div_iff₀ hnreal).mpr (by simpa [mul_comm] using hl))

/-- Positive lower growth yields a limit and sharp upper bounds at every strictly larger rate. The
exponential/logarithmic root expression is the usual positive real `n`-th root for `n > 0`. -/
theorem exists_positive_growth_rate (T : A) {c : ℝ} (hc : 0 < c)
    (hb : ∀ n : ℕ, c^n ≤ ‖T^n‖) :
    ∃ r : ℝ, 0 < r ∧ c ≤ r ∧ r ≤ ‖T‖ ∧
      Tendsto (fun n : ℕ => Real.exp (Real.log ‖T^n‖ / n)) atTop (𝓝 r) ∧
      (∀ n : ℕ, r^n ≤ ‖T^n‖) ∧
      (∀ q : ℝ, r < q → ∀ᶠ n : ℕ in atTop, ‖T^n‖ ≤ q^n) := by
  have hp : ∀ n : ℕ, 0 < ‖T^n‖ := fun n => (pow_pos hc n).trans_le (hb n)
  let hsub := log_norm_pow_subadditive T hp
  have hbd := log_norm_pow_bddBelow T hc hb
  let L := hsub.lim
  let r := Real.exp L
  have hlim : Tendsto (fun n : ℕ => Real.log ‖T^n‖ / n) atTop (𝓝 L) := hsub.tendsto_lim hbd
  have hlower : Real.log c ≤ L := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hl := Real.log_le_log (pow_pos hc n) (hb n)
    rw [Real.log_pow] at hl
    exact (le_div_iff₀ hnreal).mpr (by simpa [mul_comm] using hl)
  have hrupper : r ≤ ‖T‖ := by
    have hu := hsub.lim_le_div hbd (n := 1) (by omega)
    have hTpos : 0 < ‖T‖ := by simpa using hp 1
    simpa only [pow_one, Nat.cast_one, div_one, Real.exp_log hTpos] using
      Real.exp_le_exp.mpr hu
  refine ⟨r, Real.exp_pos L, ?_, hrupper, Real.continuous_exp.continuousAt.tendsto.comp hlim,
    ?_, ?_⟩
  · simpa only [Real.exp_log hc] using Real.exp_le_exp.mpr hlower
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · have hnreal : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hu := (le_div_iff₀ hnreal).mp (hsub.lim_le_div hbd hn)
      change L * (n : ℝ) ≤ Real.log ‖T^n‖ at hu
      have he := Real.exp_le_exp.mpr hu
      simpa only [mul_comm L, Real.exp_nat_mul, Real.exp_log (hp n)] using he
  · intro q hq
    have hqpos : 0 < q := (Real.exp_pos L).trans hq
    have hLq : L < Real.log q := by
      exact (Real.exp_lt_exp.mp (by simpa only [Real.exp_log hqpos] using hq))
    filter_upwards [hlim.eventually (gt_mem_nhds hLq), eventually_ge_atTop 1] with n hn hnpos
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have he := Real.exp_le_exp.mpr ((div_lt_iff₀ hnreal).mp hn).le
    simpa only [Real.exp_log (hp n), mul_comm (Real.log q), Real.exp_nat_mul,
      Real.exp_log hqpos] using he

end
end ConditionedStableLaws.OperatorGrowth

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
open MeasureTheory
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- H gives a strictly positive norm-growth rate for its continuous killed transition operator,
bounded above by one. -/
theorem HypothesisH.exists_positive_operator_growth_rate (h : HypothesisH ρ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      Tendsto (fun n : ℕ => Real.exp (Real.log ‖h.continuousKernelOperator^n‖ / n))
        atTop (𝓝 r) ∧
      (∀ n : ℕ, r^n ≤ ‖h.continuousKernelOperator^n‖) ∧
      (∀ q : ℝ, r < q → ∀ᶠ n : ℕ in atTop, ‖h.continuousKernelOperator^n‖ ≤ q^n) := by
  obtain ⟨x₀, _⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  have : Nontrivial (M →ᵇ ℝ) := ⟨⟨0, 1, fun he => by
    have he' := congrArg (fun f : M →ᵇ ℝ => f x₀) he
    norm_num at he'⟩⟩
  obtain ⟨c, hc, hb⟩ := h.exists_continuousKernelOperator_pow_norm_lower_bound
  obtain ⟨r, hr, _, hrT, htend, hlower, hupper⟩ :=
    OperatorGrowth.exists_positive_growth_rate h.continuousKernelOperator hc hb
  exact ⟨r, hr, hrT.trans h.continuousKernelOperator_norm_le_one, htend, hlower, hupper⟩

end
end ConditionedStableLaws.StandingHypothesis
