import ConditionedStableLaws.OrderedPathEvents

/-!
# Positive bounds for excluded rare-event configurations

Long-gap geometric errors are absorbed into an inflated one-point mass. The inflation vanishes after
multiplication by the time horizon. Short gaps keep the one-step small-target factor, so the cluster
encoding can sum them.
-/

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal Topology BigOperators
noncomputable section
namespace ConditionedStableLaws.ExcludedChainBounds

/-- A harmless inflation absorbing the uniformly small long-gap errors. -/
def inflatedMass (q : ℕ) (p C θ δ : ℝ) : ℝ := p + C * θ^(q - 1) * δ

/-- The first/long-gap factor is an inflated mass; a short gap retains its
additional geometric return error. -/
def gapFactor (q : ℕ) (p C θ δ : ℝ) (m : ℕ) : ℝ :=
  if m ≤ q then inflatedMass q p C θ δ + C * θ^(m - 1) * δ else inflatedMass q p C θ δ

theorem inflatedMass_nonneg (q : ℕ) {p C θ δ : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) : 0 ≤ inflatedMass q p C θ δ := by
  unfold inflatedMass
  positivity

theorem gapFactor_nonneg (q m : ℕ) {p C θ δ : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) : 0 ≤ gapFactor q p C θ δ m := by
  unfold gapFactor
  split <;> dsimp [inflatedMass] <;> positivity

theorem long_return_le_inflatedMass (q m : ℕ) {p C θ δ : ℝ}
    (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ) (hm : q ≤ m) :
    p + C * θ^(m - 1) * δ ≤ inflatedMass q p C θ δ := by
  unfold inflatedMass
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ1 (Nat.sub_le_sub_right hm 1)) hC) hδ

theorem return_le_gapFactor (q m : ℕ) {p C θ δ : ℝ}
    (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ) :
    p + C * θ^(m - 1) * δ ≤ gapFactor q p C θ δ m := by
  unfold gapFactor
  split
  · unfold inflatedMass
    have : 0 ≤ C * θ^(q-1) * δ := by positivity
    linarith
  · rename_i hm
    exact long_return_le_inflatedMass q m hC hθ0 hθ1 hδ (Nat.le_of_lt (Nat.lt_of_not_ge hm))

/-- Exact product decomposition into one mass per cluster and one factor per
short adjacent gap. -/
theorem product_short_long (r q : ℕ) (g : Fin r → ℕ) (p C θ δ : ℝ) :
    let S := univ.filter (fun i => g i ≤ q)
    inflatedMass q p C θ δ * (∏ i, gapFactor q p C θ δ (g i)) =
      inflatedMass q p C θ δ ^ (1 + (r - S.card)) *
        ∏ i : S, (inflatedMass q p C θ δ + C * θ^(g i.val - 1) * δ) := by
  dsimp only
  let S := univ.filter (fun i => g i ≤ q)
  have he : univ.filter (fun i => ¬g i ≤ q) = Sᶜ := by ext i; simp [S]
  simp only [gapFactor, prod_ite, he, prod_const, card_compl, Fintype.card_fin]
  have hs : (∏ i ∈ univ.filter (fun i => g i ≤ q),
      (inflatedMass q p C θ δ + C * θ^(g i - 1) * δ)) =
      ∏ i : S, (inflatedMass q p C θ δ + C * θ^(g i.val - 1) * δ) := by
    exact Finset.prod_subtype S (fun _ => Iff.rfl) _
  rw [hs]
  simp only [pow_add, pow_one]
  ring

/-- Inflation does not alter the rare-event mass limit when the cutoff makes
the first-gap error negligible after multiplication by the horizon. -/
theorem inflatedMass_scaled_tendsto (q : ℕ → ℕ) (p δ : ℕ → ℝ) (C θ rate : ℝ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ)*p n) atTop (𝓝 rate))
    (herror : Tendsto (fun n : ℕ => (n : ℝ)*θ^(q n-1)*δ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ)*inflatedMass (q n) (p n) C θ (δ n)) atTop (𝓝 rate) := by
  have hh := hp.add (herror.const_mul C)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr
  intro n
  unfold inflatedMass
  ring

end ConditionedStableLaws.ExcludedChainBounds

namespace ConditionedStableLaws.CanonicalChain
open StandingHypothesis OrderedPathEvents PositiveConditioning ExcludedChainBounds
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)
local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

/-- An ordered close-tuple event has the cluster-pattern product bound. The inputs are
one-step-smoothed return bounds derived from the spectral data. -/
theorem conditioned_ordered_close_bound
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State)
    (U : Set M) (p C₀ θ δ B a : ℝ)
    (hp : 0 ≤ p) (hC : 0 ≤ C₀) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ)
    (hB : 0 ≤ B) (ha : 0 < a)
    (hlower : ∀ y ∈ U, a ≤ (d.weight y).toReal)
    (hupper : ∀ m y, (d.rate.toReal)⁻¹ ^ m * ((C.killedTransition ^ m) y).real univ ≤ B)
    (hfirst : ∀ m, ((d.kernel ^ (m+1)) x).real (Subtype.val ⁻¹' U) ≤ p+C₀*θ^m*δ)
    (hreturn : ∀ m, ∀ y : d.State, y.val ∈ U →
      ((d.kernel ^ (m+1)) y).real (Subtype.val ⁻¹' U) ≤ p+C₀*θ^m*δ)
    (n q r : ℕ) (hq : 1 ≤ q) (t : ClusterEncoding.BadConfiguration n q r)
    (hinterior : q ≤ (t.val 0).val)
    (hden : (d.weight x.val).toReal / 2 ≤
      (d.rate.toReal)⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ)
    (A : Fin (r+1) → Set M) (hA : ∀ i, MeasurableSet (A i)) (hAU : ∀ i, A i ⊆ U) :
    (C.conditionedMeasure x.val n).real {ω | ∀ i, ω (t.val i).val ∈ Option.some '' A i} ≤
      (2*B/a) * inflatedMass q p C₀ θ δ ^ (1 + (r - (ClusterEncoding.shortPattern t).card)) *
        ∏ i : ClusterEncoding.shortPattern t,
          (inflatedMass q p C₀ θ δ + C₀*θ^(ClusterEncoding.gap (ClusterEncoding.patterned t) i).val*δ) := by
  let times : Fin (r+1) → ℕ := fun i => (t.val i).val
  have ht : StrictMono times := t.property.1
  let w := timeWord times A
  let tail := List.ofFn (fun i : Fin r => (times i.succ - times i.castSucc, A i.succ))
  have hwm : ∀ z ∈ w, MeasurableSet z.2 := forall_timeWord_targets times A _ hA
  have hws : ∀ z ∈ w, z.2 ⊆ U := forall_timeWord_targets times A (fun S => S ⊆ U) hAU
  have htailm : ∀ z ∈ tail, MeasurableSet z.2 := by
    intro z hz
    rcases List.mem_ofFn.mp hz with ⟨i, rfl⟩
    exact hA i.succ
  have htails : ∀ z ∈ tail, z.2 ⊆ U := by
    intro z hz
    rcases List.mem_ofFn.mp hz with ⟨i, rfl⟩
    exact hAU i.succ
  have hfp : ((d.kernel ^ times 0) x).real (Subtype.val ⁻¹' U) ≤ inflatedMass q p C₀ θ δ := by
    have hh := hfirst (times 0 - 1)
    rw [Nat.sub_add_cancel (hq.trans hinterior)] at hh
    exact hh.trans (long_return_le_inflatedMass q (times 0) hC hθ0 hθ1 hδ hinterior)
  have hret : ∀ z ∈ tail, ∀ y : d.State, y.val ∈ U →
      ((d.kernel ^ z.1) y).real (Subtype.val ⁻¹' U) ≤ gapFactor q p C₀ θ δ z.1 := by
    intro z hz y hy
    rcases List.mem_ofFn.mp hz with ⟨i, rfl⟩
    have hgap : 1 ≤ times i.succ - times i.castSucc :=
      Nat.sub_pos_of_lt (ht Fin.castSucc_lt_succ)
    have hh := hreturn (times i.succ - times i.castSucc - 1) y hy
    rw [Nat.sub_add_cancel hgap] at hh
    exact hh.trans (return_le_gapFactor q _ hC hθ0 hθ1 hδ)
  have hprodBound := doob_event_product_le d x U (A 0) (hA 0) (hAU 0) (times 0)
    tail htailm htails (inflatedMass q p C₀ θ δ) (gapFactor q p C₀ θ δ)
    (fun m => gapFactor_nonneg q m hp hC hθ0 hδ) hfp hret
  have hword : w = (times 0, A 0) :: tail := timeWord_eq times A
  rw [← hword] at hprodBound
  have hprodBound' : (QProcessLimit.pathMeasure d.kernel x).real (doobEvent d w) ≤
      inflatedMass q p C₀ θ δ * ∏ i : Fin r, gapFactor q p C₀ θ δ (times i.succ-times i.castSucc) := by
    simpa only [tail, List.map_ofFn, List.prod_ofFn, Function.comp_def] using hprodBound
  have hend : PathMixing.totalTime (PathMixing.indicatorObservations w) +
      (n - times (Fin.last r)) = n := by
    rw [totalTime_timeWord times ht.monotone A]
    exact Nat.add_sub_of_le (t.val (Fin.last r)).isLt.le
  have hdom := C.conditioned_targets_le_doob d x U w hwm (timeWord_ne_nil times A) hws
    (n - times (Fin.last r)) B a hB ha hlower (hupper _) (by simpa only [hend] using hden)
  rw [hend, pathEvent_timeWord times ht.monotone A] at hdom
  have hb := hdom.trans (mul_le_mul_of_nonneg_left hprodBound' (by positivity : 0 ≤ 2*B/a))
  have hS : univ.filter (fun i : Fin r => times i.succ-times i.castSucc ≤ q) =
      ClusterEncoding.shortPattern t := by
    ext i
    simp only [ClusterEncoding.shortPattern, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [times]
    omega
  have hpatt := product_short_long r q (fun i => times i.succ-times i.castSucc) p C₀ θ δ
  dsimp only at hpatt
  rw [hS] at hpatt
  rw [hpatt] at hb
  simpa only [ClusterEncoding.gap, ClusterEncoding.patterned, times, mul_assoc] using hb

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.CanonicalChain
open EndpointTrimming SortedConfigurations ExcludedChainBounds
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Labelled joint-event weights after deleting the endpoint strips. -/
def trimmedTargetWeight (x : M) (n q k : ℕ) (A : Fin k → Set M) (t : Fin k → Fin n) : ℝ :=
  if t ∈ boundaryConfigurations n k q then 0 else
    if Function.Injective t then
      (C.conditionedMeasure x n).real {ω | ∀ i, ω (t i).val ∈ Option.some '' A i}
    else 0

theorem trimmedTargetWeight_nonneg (x : M) (n q k : ℕ) (A : Fin k → Set M) (t : Fin k → Fin n) :
    0 ≤ C.trimmedTargetWeight x n q k A t := by
  unfold trimmedTargetWeight
  split <;> positivity

/-- The labelled weights are exactly the mixed-factorial-event weights of the Option-valued trimmed
canonical coordinates. -/
theorem trimmedTargetWeight_eq_mixed {J : Type*} [Fintype J]
    (x : M) (n q : ℕ) (U : J → Set M) (r : J → ℕ)
    (t : Fin (∑ j, r j) → Fin n) :
    C.trimmedTargetWeight x n q (∑ j, r j)
      (fun i => U ((factorialSlotsEquiv r).symm i).1) t =
      mixedFactorialEventWeight (C.conditionedMeasure x n)
        (trimmedObservations q (fun i : Fin n => fun ω : Path M => ω i.val))
        (liftedTargets (fun j => Option.some '' U j)) r t := by
  by_cases ht : t ∈ boundaryConfigurations n (∑ j, r j) q
  · rw [mixedWeight_eq_zero_of_boundary _ q _ _ r t ht]
    simp [trimmedTargetWeight, ht]
  · rw [mixedWeight_eq_of_not_boundary _ q _ _ r t ht]
    simp only [trimmedTargetWeight, ht, ↓reduceIte, mixedFactorialEventWeight]
    congr 1
    apply congrArg (C.conditionedMeasure x n).real
    ext ω
    change (∀ i, ω (t i).val ∈ Option.some '' U ((factorialSlotsEquiv r).symm i).1) ↔
      ∀ a : Σ j, Fin (r j), ω (t (factorialSlotsEquiv r a)).val ∈ Option.some '' U a.1
    constructor
    · intro hh a
      simpa using hh (factorialSlotsEquiv r a)
    · intro hh i
      simpa using hh ((factorialSlotsEquiv r).symm i)

/-- All additional excluded endpoint terms are zero for the trimmed weights, so the close-tuple sum
is the full excluded sum. -/
theorem sum_excluded_trimmedTargetWeight (x : M) (n q k : ℕ) (A : Fin k → Set M) :
    (∑ t ∈ excludedConfigurations n k q, C.trimmedTargetWeight x n q k A t) =
      ∑ t ∈ badConfigurations n k q, C.trimmedTargetWeight x n q k A t := by
  symm
  apply Finset.sum_subset Finset.subset_union_left
  intro t ht hnot
  have hb := (Finset.mem_union.mp ht).resolve_left hnot
  simp only [trimmedTargetWeight, hb, ↓reduceIte]

local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

/-- A finite-n excluded-configuration bound for trimmed canonical paths. The finite sorted-tuple
encoding is applied to probabilities. Long-gap errors are kept inside the explicitly inflated mass.
-/
theorem sum_excluded_trimmedTargetWeight_le
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State)
    (U : Set M) (p C₀ θ δ B a : ℝ)
    (hp : 0 ≤ p) (hC : 0 ≤ C₀) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (hB : 0 ≤ B) (ha : 0 < a)
    (hlower : ∀ y ∈ U, a ≤ (d.weight y).toReal)
    (hupper : ∀ m y, (d.rate.toReal)⁻¹ ^ m * ((C.killedTransition ^ m) y).real univ ≤ B)
    (hfirst : ∀ m, ((d.kernel ^ (m+1)) x).real (Subtype.val ⁻¹' U) ≤ p+C₀*θ^m*δ)
    (hreturn : ∀ m, ∀ y : d.State, y.val ∈ U →
      ((d.kernel ^ (m+1)) y).real (Subtype.val ⁻¹' U) ≤ p+C₀*θ^m*δ)
    (n q k : ℕ) (hq : 1 ≤ q) (hk : 0 < k)
    (hden : (d.weight x.val).toReal / 2 ≤
      (d.rate.toReal)⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ)
    (A : Fin k → Set M) (hA : ∀ i, MeasurableSet (A i)) (hAU : ∀ i, A i ⊆ U) :
    (∑ t ∈ excludedConfigurations n k q, C.trimmedTargetWeight x.val n q k A t) ≤
      (2*B/a) * (k.factorial : ℝ) *
        ∑ S : {S : Finset (Fin (k-1)) // S.Nonempty},
          ((n : ℝ) * inflatedMass q p C₀ θ δ) ^ (1 + (k-1-S.val.card)) *
            ClusterGapSums.clusterEpsilon q (inflatedMass q p C₀ θ δ) C₀ θ δ ^ S.val.card := by
  cases k with
  | zero => omega
  | succ r =>
      let p' := inflatedMass q p C₀ θ δ
      let D := 2*B/a
      let W : ClusterEncoding.BadConfiguration n q r → ℝ := fun t =>
        p' ^ (1 + (r - (ClusterEncoding.shortPattern t).card)) *
          ∏ i : ClusterEncoding.shortPattern t,
            (p' + C₀*θ^(ClusterEncoding.gap (ClusterEncoding.patterned t) i).val*δ)
      have hp' : 0 ≤ p' := inflatedMass_nonneg q hp hC hθ0 hδ
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hW : ∀ t, 0 ≤ W t := fun t => by dsimp [W]; positivity
      rw [C.sum_excluded_trimmedTargetWeight]
      have hbound := sum_finset_bad_le_factorial_mul n q r (fun t => D*W t)
        (fun t => mul_nonneg hD (hW t)) (C.trimmedTargetWeight x.val n q (r+1) A)
        (fun t ht => by simp [trimmedTargetWeight, ht])
      have hsorted : ∀ e : Bad n q r,
          C.trimmedTargetWeight x.val n q (r+1) A e.val ≤ D*W (sortedBad e) := by
        intro e
        by_cases hbd : (e.val : Fin (r+1) → Fin n) ∈ boundaryConfigurations n (r+1) q
        · simp only [trimmedTargetWeight, hbd, ↓reduceIte]
          exact mul_nonneg hD (hW _)
        · have hno : ∀ i, e.val i ∉ boundaryTimes n q := by
            simpa only [boundaryConfigurations, Finset.mem_filter, Finset.mem_univ, true_and,
              not_exists] using hbd
          let A' : Fin (r+1) → Set M := fun i => A ((rank e.val).symm i)
          have hs (i : Fin (r+1)) : (sortedBad e).val i = e.val ((rank e.val).symm i) := by
            change (sorted e.val).val i = _
            simpa only [Equiv.apply_symm_apply] using sorted_rank e.val ((rank e.val).symm i)
          have hinterior : q ≤ ((sortedBad e).val 0).val := by
            rw [hs]
            have hh := hno ((rank e.val).symm 0)
            simp only [boundaryTimes, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hh
            exact Nat.le_of_not_gt hh.1
          have hevent : {ω : Path M | ∀ i, ω (e.val i).val ∈ Option.some '' A i} =
              {ω : Path M | ∀ i, ω ((sortedBad e).val i).val ∈ Option.some '' A' i} := by
            ext ω
            simp only [Set.mem_ofPred_eq, hs, A']
            constructor
            · intro hh i
              exact hh ((rank e.val).symm i)
            · intro hh i
              have hhi := hh (rank e.val i)
              simpa only [Equiv.symm_apply_apply] using hhi
          have hb := C.conditioned_ordered_close_bound d x U p C₀ θ δ B a hp hC hθ0 hθ1.le hδ
            hB ha hlower hupper hfirst hreturn n q r hq (sortedBad e) hinterior hden A'
            (fun i => hA _) (fun i => hAU _)
          simp only [trimmedTargetWeight, hbd, ↓reduceIte, e.val.injective, hevent]
          simpa only [D, W, p', mul_assoc] using hb
      have hh := hbound hsorted
      rw [← Finset.mul_sum] at hh
      have hs := ClusterEncoding.sum_bad_configuration_le n q r hp' hC hθ0 hθ1 hδ W
        (fun _ => le_rfl)
      calc
        _ ≤ ((r+1).factorial : ℝ) * (D * ∑ t, W t) := hh
        _ ≤ ((r+1).factorial : ℝ) * (D * ∑ S : {S : Finset (Fin r) // S.Nonempty},
            ((n : ℝ)*p') ^ (1+(r-S.val.card)) *
              ClusterGapSums.clusterEpsilon q p' C₀ θ δ ^ S.val.card) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hD) (by positivity)
        _ = _ := by simp only [Nat.add_sub_cancel]; dsimp [D, p']; ring

end ConditionedStableLaws.CanonicalChain
