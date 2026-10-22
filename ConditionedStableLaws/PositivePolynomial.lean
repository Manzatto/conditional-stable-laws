import ConditionedStableLaws.FiniteReturnMinorization

/-!
# Iterating the positive finite-polynomial minorization

A positive operator satisfying `S ψ ≥ c ψ`, where `ψ ≥ 0` is nonzero and `c > 0`, has `‖S^n‖ ≥ c^n`.
Applied to the return polynomial constructed from H1 and H2, this gives an exponential lower bound.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.PositivePolynomial
noncomputable section
variable {M : Type*} [TopologicalSpace M]

theorem map_le_map
    (S : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hS : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ S f x)
    {f g : M →ᵇ ℝ} (hfg : ∀ x, f x ≤ g x) (x : M) : S f x ≤ S g x := by
  have hp := hS (g-f) (fun y => sub_nonneg.mpr (hfg y)) x
  simpa only [map_sub, BoundedContinuousFunction.sub_apply, sub_nonneg] using hp

theorem pow_minorization
    (S : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hS : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ S f x)
    (ψ : M →ᵇ ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hminor : ∀ x, c * ψ x ≤ S ψ x) (n : ℕ) (x : M) :
    c^n * ψ x ≤ (S^n) ψ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hm := map_le_map S hS (f := c^n • ψ) (g := (S^n) ψ) (fun y => ih y) x
    simp only [map_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul] at hm
    rw [pow_succ' S, mul_apply_eq_comp]
    calc
      c^(n+1) * ψ x = c^n * (c * ψ x) := by ring
      _ ≤ c^n * S ψ x := mul_le_mul_of_nonneg_left (hminor x) (pow_nonneg hc n)
      _ ≤ S ((S^n) ψ) x := hm

theorem pow_norm_lower_bound
    (S : (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ))
    (hS : ∀ f : M →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ S f x)
    (ψ : M →ᵇ ℝ) (hψ : ψ ≠ 0) (hpos : ∀ x, 0 ≤ ψ x)
    {c : ℝ} (hc : 0 ≤ c) (hminor : ∀ x, c * ψ x ≤ S ψ x) (n : ℕ) :
    c^n ≤ ‖S^n‖ := by
  have hl : ‖c^n • ψ‖ ≤ ‖(S^n) ψ‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro x
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hc n) (hpos x))]
    exact (pow_minorization S hS ψ hc hminor n x).trans
      ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm ((S^n) ψ) x))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc n)] at hl
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hψ)).mp
    (hl.trans ((S^n).le_opNorm ψ))

/-- A finite positive-time polynomial of a contraction is controlled by the
same power of the original operator. -/
theorem sum_pow_norm_le {A : Type*} [NormedRing A] [NormOneClass A]
    (T : A) (hT : ‖T‖ ≤ 1) (N k : ℕ) :
    ‖(∑ n ∈ Finset.range N, T^(n+1))^k‖ ≤ (N : ℝ)^k * ‖T^k‖ := by
  let V : A := ∑ n ∈ Finset.range N, T^n
  have heq : (∑ n ∈ Finset.range N, T^(n+1)) = T*V := by
    simp [V, Finset.mul_sum, pow_succ']
  have hcomm : Commute T V := by
    exact Commute.sum_right _ _ _ (fun n _ => Commute.self_pow T n)
  have hV : ‖V‖ ≤ (N : ℝ) := by
    calc
      ‖V‖ ≤ ∑ n ∈ Finset.range N, ‖T^n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun n _ =>
        (norm_pow_le T n).trans (by simpa using pow_le_pow_left₀ (norm_nonneg T) hT n))
      _ = (N : ℝ) := by simp
  rw [heq, hcomm.mul_pow]
  exact (norm_mul_le _ _).trans (by
    rw [mul_comm ((N : ℝ)^k)]
    exact mul_le_mul_of_nonneg_left ((norm_pow_le V k).trans
      (pow_le_pow_left₀ (norm_nonneg V) hV k)) (norm_nonneg (T^k)))

end
end ConditionedStableLaws.PositivePolynomial

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- The finite return polynomial `P + ... + P^N` on continuous functions. -/
def HypothesisH.returnOperator (h : HypothesisH ρ K) (N : ℕ) :
    (M →ᵇ ℝ) →L[ℝ] (M →ᵇ ℝ) :=
  ∑ n ∈ Finset.range N, h.continuousKernelOperator^(n+1)

theorem HypothesisH.returnOperator_apply (h : HypothesisH ρ K) (N : ℕ)
    (f : M →ᵇ ℝ) (x : M) :
    h.returnOperator N f x = ∑ n ∈ Finset.range N, (h.continuousKernelOperator^(n+1)) f x := by
  simp [HypothesisH.returnOperator,
    BoundedContinuousFunction.sum_apply]

theorem HypothesisH.returnOperator_nonneg (h : HypothesisH ρ K) (N : ℕ)
    (f : M →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : M) : 0 ≤ h.returnOperator N f x := by
  rw [h.returnOperator_apply]
  exact Finset.sum_nonneg (fun n _ => by
    rw [h.continuousKernelOperator_pow_apply]
    exact integral_nonneg hf)

theorem HypothesisH.continuousKernelOperator_norm_le_one (h : HypothesisH ρ K) :
    ‖h.continuousKernelOperator‖ ≤ 1 := by
  apply h.continuousKernelOperator.opNorm_le_bound zero_le_one
  intro f
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  rw [h.continuousKernelOperator_apply]
  have hb := norm_integral_le_of_norm_le_const
    (ae_of_all (K.kernel x) (BoundedContinuousFunction.norm_coe_le_norm f))
  have hm : (K.kernel x).real univ ≤ 1 := by
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one x)).trans_eq (by simp)
  exact hb.trans (by nlinarith [norm_nonneg f])

/-- H1 and H2 force an exponential lower bound for the powers of some finite
return polynomial. This rules out arbitrarily fast exponential decay for
that polynomial, before constructing any eigenpair. -/
theorem HypothesisH.exists_returnOperator_pow_norm_lower_bound (h : HypothesisH ρ K) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c^n ≤ ‖(h.returnOperator N)^n‖ := by
  obtain ⟨ψ, hψ, hpos, N, c, hc, hminor⟩ := h.exists_finite_power_minorization
  refine ⟨N, c, hc, fun n => PositivePolynomial.pow_norm_lower_bound
    (h.returnOperator N) (h.returnOperator_nonneg N) ψ hψ hpos hc.le ?_ n⟩
  intro x
  rw [h.returnOperator_apply]
  exact hminor x

/-- The killed operator cannot have arbitrarily fast exponential decay: H1 and H2 give a fixed
strictly positive lower rate for every power. -/
theorem HypothesisH.exists_continuousKernelOperator_pow_norm_lower_bound
    (h : HypothesisH ρ K) :
    ∃ r : ℝ, 0 < r ∧ ∀ n : ℕ, r^n ≤ ‖h.continuousKernelOperator^n‖ := by
  obtain ⟨x₀, _⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  have : Nontrivial (M →ᵇ ℝ) := ⟨⟨0, 1, fun he => by
    have he' := congrArg (fun f : M →ᵇ ℝ => f x₀) he
    norm_num at he'⟩⟩
  obtain ⟨N, c, hc, hb⟩ := h.exists_returnOperator_pow_norm_lower_bound
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    have hbad := hb 1
    simp only [hz, HypothesisH.returnOperator, Finset.range_zero, Finset.sum_empty,
      pow_one, ContinuousLinearMap.opNorm_zero] at hbad
    linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨c/N, div_pos hc hNreal, fun n => ?_⟩
  rw [div_pow, div_le_iff₀ (pow_pos hNreal n)]
  have hu := PositivePolynomial.sum_pow_norm_le h.continuousKernelOperator
    h.continuousKernelOperator_norm_le_one N n
  exact (hb n).trans (by simpa only [HypothesisH.returnOperator, mul_comm] using hu)

end
end ConditionedStableLaws.StandingHypothesis
