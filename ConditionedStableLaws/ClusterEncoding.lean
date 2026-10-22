import ConditionedStableLaws.ClusterGapSums

/-!
# Encoding ordered observations by cluster starts and short gaps

For a fixed set `S` of short adjacent gaps, a strictly ordered time tuple is encoded by its first
time, the times just after the other gaps, and the short gaps minus one. This is an injection,
including the time-window constraints; the full coordinate space gives a larger nonnegative sum.
-/

open Finset
open scoped BigOperators
noncomputable section

namespace ConditionedStableLaws.ClusterEncoding

/-- `S` lists adjacent gaps required to lie in `1,...,q`.
There are `r+1` observations in the time window `0,...,n-1`. -/
def Configuration (n q r : ℕ) (S : Finset (Fin r)) :=
  {t : Fin (r + 1) → Fin n // StrictMono t ∧
    ∀ i ∈ S, (t i.succ).val ≤ (t i.castSucc).val + q}

instance (n q r : ℕ) (S : Finset (Fin r)) : Fintype (Configuration n q r S) :=
  inferInstanceAs (Fintype {_t : Fin (r + 1) → Fin n // _})

/-- The gap coordinate is the true positive gap minus one. -/
def gap {n q r : ℕ} {S : Finset (Fin r)} (t : Configuration n q r S)
    (i : S) : Fin q :=
  ⟨(t.val i.val.succ).val - (t.val i.val.castSucc).val - 1, by
    have hlt : (t.val i.val.castSucc).val < (t.val i.val.succ).val :=
      t.property.1 Fin.castSucc_lt_succ
    have hle := t.property.2 i.val i.property
    omega⟩

/-- First time, remaining cluster starts, and short internal gaps. -/
def coordinates {n q r : ℕ} {S : Finset (Fin r)} (t : Configuration n q r S) :
    Fin n × ((↥Sᶜ → Fin n) × (↥S → Fin q)) :=
  (t.val 0, (fun i => t.val i.val.succ, gap t))

/-- The start and gap data uniquely recover every observation time. -/
theorem coordinates_injective {n q r : ℕ} {S : Finset (Fin r)} :
    Function.Injective (coordinates (n := n) (q := q) (r := r) (S := S)) := by
  intro t u h
  apply Subtype.ext
  funext i
  induction i using Fin.induction with
  | zero => exact congrArg Prod.fst h
  | succ i ih =>
      by_cases hi : i ∈ S
      · have hg := congrArg (fun z : Fin n × ((↥Sᶜ → Fin n) × (↥S → Fin q)) =>
          (z.2.2 ⟨i, hi⟩).val) h
        have ht : (t.val i.castSucc).val < (t.val i.succ).val :=
          t.property.1 Fin.castSucc_lt_succ
        have hu : (u.val i.castSucc).val < (u.val i.succ).val :=
          u.property.1 Fin.castSucc_lt_succ
        have hp := congrArg Fin.val ih
        apply Fin.ext
        change (t.val i.succ).val - (t.val i.castSucc).val - 1 =
          (u.val i.succ).val - (u.val i.castSucc).val - 1 at hg
        omega
      · exact congrArg (fun z : Fin n × ((↥Sᶜ → Fin n) × (↥S → Fin q)) =>
          z.2.1 ⟨i, mem_compl.mpr hi⟩) h

/-- The injection explicitly keeps every cluster start and every short gap. -/
def encoding {n q r : ℕ} {S : Finset (Fin r)} :
    Configuration n q r S ↪ (Fin n × ((↥Sᶜ → Fin n) × (↥S → Fin q))) :=
  ⟨coordinates, coordinates_injective⟩

/-- Exact size of the larger, unconstrained coordinate space. -/
theorem card_coordinates (n q r : ℕ) (S : Finset (Fin r)) :
    Fintype.card (Fin n × ((↥Sᶜ → Fin n) × (↥S → Fin q))) =
      n ^ (1 + (r - S.card)) * q ^ S.card := by
  simp [pow_add, mul_assoc]

/-- The fixed-pattern count bound follows from the injection. -/
theorem card_configuration_le (n q r : ℕ) (S : Finset (Fin r)) :
    Fintype.card (Configuration n q r S) ≤ n ^ (1 + (r - S.card)) * q ^ S.card := by
  rw [← card_coordinates]
  exact Fintype.card_le_of_injective _ coordinates_injective

/-- A weighted version of the encoding bound. Each cluster start contributes
`p`, and each short gap contributes its own nonnegative return factor. -/
theorem sum_configuration_weight_le (n q r : ℕ) (S : Finset (Fin r))
    (p : ℝ) (hp : 0 ≤ p) (a : Fin q → ℝ) (ha : ∀ k, 0 ≤ a k)
    (w : Configuration n q r S → ℝ)
    (hw : ∀ t, w t ≤ p ^ (1 + (r - S.card)) * ∏ i : S, a (gap t i)) :
    (∑ t, w t) ≤ ((n : ℝ) * p) ^ (1 + (r - S.card)) * (∑ k, a k) ^ S.card := by
  classical
  let f : (Fin n × ((↥Sᶜ → Fin n) × (↥S → Fin q))) → ℝ :=
    fun z => p ^ (1 + (r - S.card)) * ∏ i : S, a (z.2.2 i)
  have hsum : (∑ g : S → Fin q, ∏ i, a (g i)) = (∑ k, a k) ^ S.card := by
    rw [← Fintype.prod_sum]
    simp
  calc
    (∑ t, w t) ≤ ∑ t, f (coordinates t) := sum_le_sum (fun t _ => hw t)
    _ = ∑ z ∈ univ.image coordinates, f z :=
      (sum_image (fun _ _ _ _ h => coordinates_injective h)).symm
    _ ≤ ∑ z, f z := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun z _ _ => mul_nonneg (pow_nonneg hp _) (prod_nonneg (fun i _ => ha _)))
    _ = ((n : ℝ) * p) ^ (1 + (r - S.card)) * (∑ k, a k) ^ S.card := by
      simp only [f, Fintype.sum_prod_type]
      simp_rw [← mul_sum, hsum]
      simp only [sum_const, card_univ, Fintype.card_fin, Fintype.card_fun,
        Fintype.card_coe, card_compl, nsmul_eq_mul, Nat.cast_pow, mul_pow, pow_add, pow_one]
      ring

/-- Apply the encoding to the geometric short-return bound. -/
theorem sum_configuration_return_bound (n q r : ℕ) (S : Finset (Fin r))
    {p C θ δ : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (w : Configuration n q r S → ℝ)
    (hw : ∀ t, w t ≤ p ^ (1 + (r - S.card)) *
      ∏ i : S, (p + C * θ ^ (gap t i).val * δ)) :
    (∑ t, w t) ≤ ((n : ℝ) * p) ^ (1 + (r - S.card)) *
      ClusterGapSums.clusterEpsilon q p C θ δ ^ S.card := by
  have hs : (∑ k : Fin q, (p + C * θ ^ k.val * δ)) ≤
      ClusterGapSums.clusterEpsilon q p C θ δ := by
    calc
      _ = (q : ℝ) * p + C * δ * ∑ k : Fin q, θ ^ k.val := by
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [mul_sum]
        congr 1
        apply sum_congr rfl
        intro i hi
        ring
      _ ≤ (q : ℝ) * p + C * δ * (1 / (1 - θ)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left
          (ClusterGapSums.geometric_sum_le q hθ0 hθ1) (mul_nonneg hC hδ)) _
      _ = ClusterGapSums.clusterEpsilon q p C θ δ := by
        unfold ClusterGapSums.clusterEpsilon
        ring
  apply (sum_configuration_weight_le n q r S p hp
    (fun k => p + C * θ ^ k.val * δ) (fun k => by positivity) w hw).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sum_nonneg (fun k _ => by positivity)) hs S.card) (by positivity)

/-- Ordered observation times containing at least one short adjacent gap. -/
def BadConfiguration (n q r : ℕ) :=
  {t : Fin (r + 1) → Fin n // StrictMono t ∧
    ∃ i : Fin r, (t i.succ).val ≤ (t i.castSucc).val + q}

instance (n q r : ℕ) : Fintype (BadConfiguration n q r) :=
  inferInstanceAs (Fintype {_t : Fin (r + 1) → Fin n // _})

/-- The short-gap pattern of an ordered time tuple. -/
def shortPattern {n q r : ℕ} (t : BadConfiguration n q r) : Finset (Fin r) :=
  univ.filter (fun i => (t.val i.succ).val ≤ (t.val i.castSucc).val + q)

theorem shortPattern_nonempty {n q r : ℕ} (t : BadConfiguration n q r) :
    (shortPattern t).Nonempty := by
  obtain ⟨i, hi⟩ := t.property.2
  exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩

/-- Regard the tuple as a configuration in its own short-gap pattern. -/
def patterned {n q r : ℕ} (t : BadConfiguration n q r) :
    Configuration n q r (shortPattern t) :=
  ⟨t.val, t.property.1, fun _ hi => (mem_filter.mp hi).2⟩

/-- Encoding by the nonempty pattern does not identify distinct tuples. -/
def patternEncoding {n q r : ℕ} : BadConfiguration n q r ↪
    (Σ S : {S : Finset (Fin r) // S.Nonempty}, Configuration n q r S.val) where
  toFun t := ⟨⟨shortPattern t, shortPattern_nonempty t⟩, patterned t⟩
  inj' := by
    intro t u h
    apply Subtype.ext
    exact congrArg (fun z : Σ S : {S : Finset (Fin r) // S.Nonempty},
      Configuration n q r S.val => z.2.val) h

/-- Sum every ordered close tuple using its canonical nonempty pattern. The right side is a fixed
finite sum of the cluster bounds. -/
theorem sum_bad_configuration_le (n q r : ℕ)
    {p C θ δ : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (w : BadConfiguration n q r → ℝ)
    (hw : ∀ t, w t ≤ p ^ (1 + (r - (shortPattern t).card)) *
      ∏ i : shortPattern t, (p + C * θ ^ (gap (patterned t) i).val * δ)) :
    (∑ t, w t) ≤ ∑ S : {S : Finset (Fin r) // S.Nonempty},
      ((n : ℝ) * p) ^ (1 + (r - S.val.card)) *
        ClusterGapSums.clusterEpsilon q p C θ δ ^ S.val.card := by
  classical
  let f : (Σ S : {S : Finset (Fin r) // S.Nonempty}, Configuration n q r S.val) → ℝ :=
    fun z => p ^ (1 + (r - z.1.val.card)) *
      ∏ i : z.1.val, (p + C * θ ^ (gap z.2 i).val * δ)
  calc
    (∑ t, w t) ≤ ∑ t, f (patternEncoding t) := sum_le_sum (fun t _ => hw t)
    _ = ∑ z ∈ univ.image patternEncoding, f z :=
      (sum_image (fun _ _ _ _ h => patternEncoding.injective h)).symm
    _ ≤ ∑ z, f z := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun z _ _ => by dsimp [f]; positivity)
    _ = ∑ S : {S : Finset (Fin r) // S.Nonempty},
        ∑ t : Configuration n q r S.val, f ⟨S, t⟩ := Fintype.sum_sigma _
    _ ≤ _ := by
      apply sum_le_sum
      intro S hS
      exact sum_configuration_return_bound n q r S.val hp hC hθ0 hθ1 hδ
        (fun t => f ⟨S, t⟩) (fun _ => le_rfl)

/-- The summed weight of ordered close tuples tends to zero under rare-event scaling and the uniform
small-target return bound. -/
theorem sum_bad_configuration_tendsto_zero (r : ℕ) (q : ℕ → ℕ) (p δ : ℕ → ℝ)
    (C θ rate : ℝ) (hp0 : ∀ n, 0 ≤ p n) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hδ0 : ∀ n, 0 ≤ δ n)
    (hq : Filter.Tendsto (fun n : ℕ => (q n : ℝ) / n) Filter.atTop (nhds 0))
    (hp : Filter.Tendsto (fun n : ℕ => (n : ℝ) * p n) Filter.atTop (nhds rate))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (w : ∀ n, BadConfiguration n (q n) r → ℝ) (hw0 : ∀ n t, 0 ≤ w n t)
    (hw : ∀ n t, w n t ≤ (p n) ^ (1 + (r - (shortPattern t).card)) *
      ∏ i : shortPattern t, (p n + C * θ ^ (gap (patterned t) i).val * δ n)) :
    Filter.Tendsto (fun n => ∑ t, w n t) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun n : ℕ =>
      ∑ S : {S : Finset (Fin r) // S.Nonempty},
        ((n : ℝ) * p n) ^ (1 + (r - S.val.card)) *
          ClusterGapSums.clusterEpsilon (q n) (p n) C θ (δ n) ^ S.val.card)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum univ (fun (S : {S : Finset (Fin r) // S.Nonempty}) _ =>
      ClusterGapSums.cluster_placement_bound_tendsto_zero q p δ C θ rate
        (1 + (r - S.val.card)) S.val.card (card_pos.mpr S.property) hq hp hδ)
  exact squeeze_zero (fun n => sum_nonneg (fun t _ => hw0 n t))
    (fun n => sum_bad_configuration_le n (q n) r (hp0 n) hC hθ0 hθ1 (hδ0 n) (w n) (hw n))
    hlim

end ConditionedStableLaws.ClusterEncoding
