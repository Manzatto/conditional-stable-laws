import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Deterministic identities for Birkhoff sums

Identities for changes of time indexing, centering, and stopped averages of finite sums.
-/

open Filter
open scoped BigOperators Topology

noncomputable section

namespace ConditionedStableLaws

/-- Sum over observation times `0, ..., n - 1`. -/
def birkhoffSum (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, u i

/-- The average is totalized as zero at `n = 0`; limit statements use `n → ∞`. -/
def birkhoffAverage (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  birkhoffSum u n / (n : ℝ)

@[simp]
theorem birkhoffSum_zero (u : ℕ → ℝ) : birkhoffSum u 0 = 0 := by
  simp [birkhoffSum]

theorem birkhoffSum_succ (u : ℕ → ℝ) (n : ℕ) :
    birkhoffSum u (n + 1) = birkhoffSum u n + u n := by
  simp [birkhoffSum, Finset.sum_range_succ]

/-- Centering each observation subtracts `n` times the centering constant. -/
theorem birkhoffSum_centered (u : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    birkhoffSum (fun i => u i - c) n = birkhoffSum u n - (n : ℝ) * c := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

/-- Separate the first observation from the remaining observations. -/
theorem birkhoffSum_first (u : ℕ → ℝ) (n : ℕ) :
    birkhoffSum u (n + 1) = u 0 + birkhoffSum (fun i => u (i + 1)) n := by
  induction n with
  | zero => simp [birkhoffSum]
  | succ n ih =>
      rw [birkhoffSum_succ, ih, birkhoffSum_succ]
      ring

/-- Replacing times `0, ..., n - 1` with `1, ..., n` changes only endpoints. -/
theorem birkhoffSum_endpoint_difference (u : ℕ → ℝ) (n : ℕ) :
    birkhoffSum u n - birkhoffSum (fun i => u (i + 1)) n = u 0 - u n := by
  have h := birkhoffSum_first u n
  rw [birkhoffSum_succ] at h
  linarith

/-- If every observation after `m` vanishes, the sum through `n` stops at `m`. -/
theorem birkhoffSum_stopped (u : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n)
    (hu : ∀ i, m ≤ i → i < n → u i = 0) :
    birkhoffSum u n = birkhoffSum u m := by
  unfold birkhoffSum
  symm
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro i hin him
  exact hu i (Nat.le_of_not_gt (by simpa using him)) (Finset.mem_range.mp hin)

/-- The stopped-average identity used when the observable vanishes on `Z`. -/
theorem birkhoffAverage_stopped (u : ℕ → ℝ) {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : m ≤ n)
    (hu : ∀ i, m ≤ i → i < n → u i = 0) :
    birkhoffAverage u n = ((m : ℝ) / (n : ℝ)) * birkhoffAverage u m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold birkhoffAverage
  rw [birkhoffSum_stopped u hmn hu]
  field_simp

/-- Counts visits along a deterministic path, with a predicate for each time. -/
def visitCount (p : ℕ → Prop) [DecidablePred p] (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if p i then 1 else 0

theorem visitCount_first (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    visitCount p (n + 1) =
      (if p 0 then 1 else 0) + visitCount (fun i => p (i + 1)) n := by
  induction n with
  | zero =>
      simp only [visitCount, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
        Finset.range_zero, Finset.sum_empty, Nat.add_zero]
  | succ n ih =>
      simp only [visitCount, Finset.sum_range_succ] at *
      omega

/-- Starting inside every target contributes exactly one additional visit. -/
theorem visitCount_first_of_mem (p : ℕ → Prop) [DecidablePred p]
    (hp : p 0) (n : ℕ) :
    visitCount p (n + 1) = 1 + visitCount (fun i => p (i + 1)) n := by
  rw [visitCount_first]
  simp [hp]

/-- The deterministic endpoint estimate used in changes of time indexing. -/
theorem normalized_endpoint_bound (u : ℕ → ℝ) (n : ℕ) (K a : ℝ)
    (ha : 0 < a) (hu : ∀ i, |u i| ≤ K) :
    |birkhoffSum u n / a - birkhoffSum (fun i => u (i + 1)) n / a| ≤
      2 * K / a := by
  rw [← sub_div, birkhoffSum_endpoint_difference, abs_div, abs_of_pos ha]
  apply div_le_div_of_nonneg_right _ ha.le
  calc
    |u 0 - u n| ≤ |u 0| + |u n| := by
      simpa [sub_eq_add_neg] using abs_add_le (u 0) (-u n)
    _ ≤ 2 * K := by linarith [hu 0, hu n]

/-- A fixed contribution vanishes after division by a diverging normalization. -/
theorem constant_div_tendsto_zero (c : ℝ) {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => c / a n) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).mul (tendsto_inv_atTop_zero.comp ha)
  simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using h

/-- Removing a fixed finite prefix is harmless after diverging normalization. -/
theorem birkhoffSum_fixed_prefix_tendsto_zero (u : ℕ → ℝ) (k : ℕ)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => birkhoffSum u k / a n) atTop (𝓝 0) :=
  constant_div_tendsto_zero (birkhoffSum u k) ha

/-- Endpoint reindexing is negligible once the final endpoint is negligible. -/
theorem normalized_endpoint_tendsto_zero (u : ℕ → ℝ) {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop)
    (hend : Tendsto (fun n => u n / a n) atTop (𝓝 0)) :
    Tendsto
      (fun n => birkhoffSum u n / a n -
        birkhoffSum (fun i => u (i + 1)) n / a n) atTop (𝓝 0) := by
  have h := (constant_div_tendsto_zero (u 0) ha).sub hend
  simpa only [← sub_div, birkhoffSum_endpoint_difference, sub_self] using h

end ConditionedStableLaws
