import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Summing short gaps inside clusters

A gap `k : Fin q` represents the time gap `k.val + 1`. The geometric return estimate is summed over
all such gaps, then over cluster starts.
-/

open Filter Finset
open scoped BigOperators Topology
noncomputable section

namespace ConditionedStableLaws.ClusterGapSums

/-- The sum of rare-event and geometric short-return errors for one gap. -/
def clusterEpsilon (q : ℕ) (p C θ δ : ℝ) : ℝ :=
  (q : ℝ) * p + C * δ / (1 - θ)

/-- Truncating the nonnegative geometric series gives the uniform gap bound. -/
theorem geometric_sum_le (q : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∑ k : Fin q, θ ^ k.val ≤ 1 / (1 - θ) := by
  have hs := hasSum_geometric_of_lt_one hθ0 hθ1
  have h := hs.summable.sum_le_tsum (range q) (fun k _ => pow_nonneg hθ0 k)
  rw [hs.tsum_eq] at h
  simpa [Fin.sum_univ_eq_sum_range, one_div] using h

/-- Exact expansion of the sum over every internal gap vector. -/
theorem sum_gap_products (q s : ℕ) (p C θ δ : ℝ) :
    (∑ g : Fin s → Fin q, p * ∏ i, (p + C * θ ^ (g i).val * δ)) =
      p * (∑ k : Fin q, (p + C * θ ^ k.val * δ)) ^ s := by
  rw [← mul_sum, Fintype.sum_pow]

/-- Summing a single-cluster return bound over its internal gap vectors. -/
theorem sum_gap_products_le (q s : ℕ) {p C θ δ : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : 0 ≤ δ) :
    (∑ g : Fin s → Fin q, p * ∏ i, (p + C * θ ^ (g i).val * δ)) ≤
      p * clusterEpsilon q p C θ δ ^ s := by
  rw [sum_gap_products]
  apply mul_le_mul_of_nonneg_left _ hp
  apply pow_le_pow_left₀ (sum_nonneg (fun k _ => by positivity))
  calc
    (∑ k : Fin q, (p + C * θ ^ k.val * δ)) =
        (q : ℝ) * p + C * δ * ∑ k : Fin q, θ ^ k.val := by
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ (q : ℝ) * p + C * δ * (1 / (1 - θ)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left (geometric_sum_le q hθ0 hθ1)
        (mul_nonneg hC hδ)) _
    _ = clusterEpsilon q p C θ δ := by unfold clusterEpsilon; ring

/-- A cluster probability may be inserted by its pointwise return bound. -/
theorem sum_cluster_le (q s : ℕ) {p C θ δ : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (π : (Fin s → Fin q) → ℝ)
    (hπ : ∀ g, π g ≤ p * ∏ i, (p + C * θ ^ (g i).val * δ)) :
    (∑ g, π g) ≤ p * clusterEpsilon q p C θ δ ^ s :=
  (sum_le_sum (fun g _ => hπ g)).trans (sum_gap_products_le q s hp hC hθ0 hθ1 hδ)

/-- The summed probability of independent blocks factorizes exactly. -/
theorem sum_cluster_products (q c : ℕ) (s : Fin c → ℕ)
    (π : ∀ j, (Fin (s j) → Fin q) → ℝ) :
    (∑ g : ∀ j, Fin (s j) → Fin q, ∏ j, π j (g j)) =
      ∏ j, ∑ h, π j h := (Fintype.prod_sum π).symm

/-- A fixed pattern of `c` clusters with `s j` internal gaps contributes this bound. -/
theorem sum_cluster_products_le (q c : ℕ) (s : Fin c → ℕ) {p C θ δ : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (π : ∀ j, (Fin (s j) → Fin q) → ℝ) (hπ0 : ∀ j g, 0 ≤ π j g)
    (hπ : ∀ j g, π j g ≤ p * ∏ i, (p + C * θ ^ (g i).val * δ)) :
    (∑ g : ∀ j, Fin (s j) → Fin q, ∏ j, π j (g j)) ≤
      p ^ c * clusterEpsilon q p C θ δ ^ (∑ j, s j) := by
  rw [sum_cluster_products]
  calc
    (∏ j, ∑ h, π j h) ≤ ∏ j, p * clusterEpsilon q p C θ δ ^ s j := by
      apply prod_le_prod₀ (fun j _ => sum_nonneg (fun g _ => hπ0 j g))
      intro j hj
      exact sum_cluster_le q (s j) hp hC hθ0 hθ1 hδ (π j) (hπ j)
    _ = p ^ c * clusterEpsilon q p C θ δ ^ (∑ j, s j) := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]
      simp

/-- There are at most `n^c` choices of cluster starts. Summing over all of them
is a valid upper bound even though some placements overlap or leave the time window. -/
theorem sum_cluster_placements_le (n q c : ℕ) (s : Fin c → ℕ) {p C θ δ : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (π : ∀ j, (Fin (s j) → Fin q) → ℝ) (hπ0 : ∀ j g, 0 ≤ π j g)
    (hπ : ∀ j g, π j g ≤ p * ∏ i, (p + C * θ ^ (g i).val * δ)) :
    (∑ _t : Fin c → Fin n, ∑ g : ∀ j, Fin (s j) → Fin q, ∏ j, π j (g j)) ≤
      ((n : ℝ) * p) ^ c * clusterEpsilon q p C θ δ ^ (∑ j, s j) := by
  calc
    _ ≤ ∑ _t : Fin c → Fin n, p ^ c * clusterEpsilon q p C θ δ ^ (∑ j, s j) :=
      sum_le_sum (fun _ _ => sum_cluster_products_le q c s hp hC hθ0 hθ1 hδ π hπ0 hπ)
    _ = _ := by simp [mul_pow, mul_assoc]

/-- Restricting to any injectively encoded set of valid configurations only reduces the nonnegative
placement bound. -/
theorem sum_encoded_configurations_le {T : Type*} [Fintype T]
    (n q c : ℕ) (s : Fin c → ℕ)
    (encode : T ↪ ((Fin c → Fin n) × (∀ j, Fin (s j) → Fin q)))
    {p C θ δ : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (π : ∀ j, (Fin (s j) → Fin q) → ℝ) (hπ0 : ∀ j g, 0 ≤ π j g)
    (hπ : ∀ j g, π j g ≤ p * ∏ i, (p + C * θ ^ (g i).val * δ))
    (w : T → ℝ) (hw : ∀ t, w t ≤ ∏ j, π j ((encode t).2 j)) :
    (∑ t, w t) ≤ ((n : ℝ) * p) ^ c * clusterEpsilon q p C θ δ ^ (∑ j, s j) := by
  classical
  let f : ((Fin c → Fin n) × (∀ j, Fin (s j) → Fin q)) → ℝ :=
    fun z => ∏ j, π j (z.2 j)
  calc
    (∑ t, w t) ≤ ∑ t, f (encode t) := sum_le_sum (fun t _ => hw t)
    _ = ∑ z ∈ univ.image encode, f z :=
      (sum_image (fun _ _ _ _ h => encode.injective h)).symm
    _ ≤ ∑ z, f z := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun z _ _ => prod_nonneg (fun j _ => hπ0 j _))
    _ = ∑ _t : Fin c → Fin n, ∑ g : ∀ j, Fin (s j) → Fin q, ∏ j, π j (g j) :=
      Fintype.sum_prod_type _
    _ ≤ _ := sum_cluster_placements_le n q c s hp hC hθ0 hθ1 hδ π hπ0 hπ

/-- The short-gap error vanishes under the two small-target limits. -/
theorem clusterEpsilon_tendsto_zero (q : ℕ → ℕ) (p δ : ℕ → ℝ) (C θ rate : ℝ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 rate))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => clusterEpsilon (q n) (p n) C θ (δ n)) atTop (𝓝 0) := by
  have hqp : Tendsto (fun n : ℕ => (q n : ℝ) * p n) atTop (𝓝 0) := by
    have h := hq.mul hp
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  simpa [clusterEpsilon] using hqp.add ((hδ.const_mul C).div_const (1 - θ))

/-- Any fixed pattern containing an internal gap has vanishing total bound. -/
theorem cluster_placement_bound_tendsto_zero (q : ℕ → ℕ) (p δ : ℕ → ℝ)
    (C θ rate : ℝ) (c s : ℕ) (hs : 0 < s)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 rate))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((n : ℝ) * p n) ^ c *
      clusterEpsilon (q n) (p n) C θ (δ n) ^ s) atTop (𝓝 0) := by
  simpa [zero_pow (Nat.ne_of_gt hs)] using
    (hp.pow c).mul ((clusterEpsilon_tendsto_zero q p δ C θ rate hq hp hδ).pow s)

/-- Summing finitely many order and cluster-size patterns preserves the
vanishing close-configuration contribution. -/
theorem finite_cluster_contribution_tendsto_zero {J : Type*} [Fintype J]
    (q : ℕ → ℕ) (p δ : ℕ → ℝ) (C θ rate : ℝ) (c s : J → ℕ)
    (hs : ∀ j, 0 < s j)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 rate))
    (hδ : Tendsto δ atTop (𝓝 0))
    (W : ℕ → J → ℝ) (hW0 : ∀ n j, 0 ≤ W n j)
    (hW : ∀ n j, W n j ≤ ((n : ℝ) * p n) ^ c j *
      clusterEpsilon (q n) (p n) C θ (δ n) ^ s j) :
    Tendsto (fun n => ∑ j, W n j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ∑ j, ((n : ℝ) * p n) ^ c j *
      clusterEpsilon (q n) (p n) C θ (δ n) ^ s j) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ (fun j _ =>
      cluster_placement_bound_tendsto_zero q p δ C θ rate (c j) (s j) (hs j) hq hp hδ)
  exact squeeze_zero (fun n => sum_nonneg (fun j _ => hW0 n j))
    (fun n => sum_le_sum (fun j _ => hW n j)) hlim

end ConditionedStableLaws.ClusterGapSums
