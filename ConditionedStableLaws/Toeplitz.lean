import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Toeplitz's lemma

The weighted-average lemma of Toeplitz (1911) (see also Loève, p. 250, and Li–Hu, Theorem 1.1(i)):
nonnegative weights that vanish in each fixed coordinate and have uniformly bounded row sums send
null sequences to null sequences.
-/

open Filter Finset
open scoped Topology

namespace ConditionedStableLaws

theorem toeplitz_tendsto_zero (w : ℕ → ℕ → ℝ) (x : ℕ → ℝ) {C : ℝ}
    (hw : ∀ n i, 0 ≤ w n i) (hcol : ∀ i, Tendsto (fun n => w n i) atTop (𝓝 0))
    (hrow : ∀ n, ∑ i ∈ range n, w n i ≤ C) (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ range n, w n i * x i) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hC : 0 ≤ C := (sum_nonneg fun i _ => hw 0 i).trans (hrow 0)
  -- Tail of `x` below `ε / (2 (C + 1))`.
  set δ := ε / (2 * (C + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx δ hδpos
  -- The finitely many head terms vanish in the limit.
  have hhead : Tendsto (fun n => ∑ i ∈ range N, w n i * x i) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (range N) fun i _ => (hcol i).mul_const (x i)
  obtain ⟨N', hN'⟩ := Metric.tendsto_atTop.1 hhead (ε / 2) (half_pos hε)
  refine ⟨max N N', fun n hn => ?_⟩
  have hNn : N ≤ n := le_of_max_le_left hn
  rw [Real.dist_eq, sub_zero, ← sum_range_add_sum_Ico _ hNn]
  have h1 : |∑ i ∈ range N, w n i * x i| < ε / 2 := by
    simpa [Real.dist_eq] using hN' n (le_of_max_le_right hn)
  have h2 : |∑ i ∈ Ico N n, w n i * x i| ≤ C * δ := by
    calc |∑ i ∈ Ico N n, w n i * x i|
        ≤ ∑ i ∈ Ico N n, |w n i * x i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Ico N n, w n i * δ := by
          apply sum_le_sum
          intro i hi
          rw [abs_mul, abs_of_nonneg (hw n i)]
          have := hN i (mem_Ico.1 hi).1
          rw [Real.dist_eq, sub_zero] at this
          exact mul_le_mul_of_nonneg_left this.le (hw n i)
      _ = (∑ i ∈ Ico N n, w n i) * δ := by rw [sum_mul]
      _ ≤ C * δ := by
          apply mul_le_mul_of_nonneg_right _ hδpos.le
          calc ∑ i ∈ Ico N n, w n i ≤ ∑ i ∈ range n, w n i :=
                sum_le_sum_of_subset_of_nonneg
                  (fun i hi => mem_range.2 (mem_Ico.1 hi).2) (fun i _ _ => hw n i)
            _ ≤ C := hrow n
  have h3 : C * δ < ε / 2 := by
    rw [hδ, mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  calc |∑ i ∈ range N, w n i * x i + ∑ i ∈ Ico N n, w n i * x i|
      ≤ |∑ i ∈ range N, w n i * x i| + |∑ i ∈ Ico N n, w n i * x i| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := add_halves ε

end ConditionedStableLaws
