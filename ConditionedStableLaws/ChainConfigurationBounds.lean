import ConditionedStableLaws.ExcludedChainBounds

/-!
# Vanishing excluded configurations for conditioned paths

The close-tuple probabilities are canonical conditioned probabilities. Their vanishing follows from
one-step target smallness, the spectral gap, and first-order rare-event scaling. Endpoint strips
have been deleted exactly.
-/

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal Topology BigOperators
noncomputable section
namespace ConditionedStableLaws.ExcludedChainBounds

/-- Explicit finite-pattern upper bound, including the long-gap inflation. -/
def excludedBound (k n q : ℕ) (p C θ δ D : ℝ) : ℝ :=
  D * (k.factorial : ℝ) *
    ∑ S : {S : Finset (Fin (k-1)) // S.Nonempty},
      ((n : ℝ) * inflatedMass q p C θ δ) ^ (1 + (k-1-S.val.card)) *
        ClusterGapSums.clusterEpsilon q (inflatedMass q p C θ δ) C θ δ ^ S.val.card

/-- Every nonempty short-gap pattern contains a factor tending to zero. -/
theorem excludedBound_tendsto_zero (k : ℕ) (q : ℕ → ℕ) (p δ : ℕ → ℝ)
    (C θ D rate : ℝ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ) / n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 rate))
    (hδ : Tendsto δ atTop (𝓝 0))
    (herror : Tendsto (fun n : ℕ => (n : ℝ)*θ^(q n-1)*δ n) atTop (𝓝 0)) :
    Tendsto (fun n => excludedBound k n (q n) (p n) C θ (δ n) D) atTop (𝓝 0) := by
  have hp' := inflatedMass_scaled_tendsto q p δ C θ rate hp herror
  have hh : Tendsto (fun n : ℕ =>
      ∑ S : {S : Finset (Fin (k-1)) // S.Nonempty},
        ((n : ℝ) * inflatedMass (q n) (p n) C θ (δ n)) ^ (1 + (k-1-S.val.card)) *
          ClusterGapSums.clusterEpsilon (q n) (inflatedMass (q n) (p n) C θ (δ n))
            C θ (δ n) ^ S.val.card) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ (fun (S : {S : Finset (Fin (k-1)) // S.Nonempty}) _ =>
      ClusterGapSums.cluster_placement_bound_tendsto_zero q
        (fun n => inflatedMass (q n) (p n) C θ (δ n)) δ C θ rate
        (1 + (k-1-S.val.card)) S.val.card (card_pos.mpr S.property) hq hp' hδ)
  simpa only [excludedBound, mul_zero] using hh.const_mul (D * (k.factorial : ℝ))

end ConditionedStableLaws.ExcludedChainBounds

namespace ConditionedStableLaws.CanonicalChain
open EndpointTrimming ExcludedChainBounds StandingHypothesis ConditionalMixing
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)
local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

/-- A sequence of excluded joint-event sums vanishes from one-point return bounds and rare-event
scaling. All finite-chain estimates are only required eventually. -/
theorem sum_excluded_trimmedTargetWeight_tendsto_zero
    (d : DoobTransform.EigenData C.killedTransition) (x : d.State)
    (U : ℕ → Set M) (p δ : ℕ → ℝ) (q : ℕ → ℕ) (k : ℕ) (hk : 0 < k)
    (C₀ θ B a rate : ℝ) (hC : 0 ≤ C₀) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hB : 0 ≤ B) (ha : 0 < a)
    (hp0 : ∀ᶠ n in atTop, 0 ≤ p n) (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hq1 : ∀ᶠ n in atTop, 1 ≤ q n)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, a ≤ (d.weight y).toReal)
    (hupper : ∀ m y, (d.rate.toReal)⁻¹ ^ m * ((C.killedTransition ^ m) y).real univ ≤ B)
    (hfirst : ∀ᶠ n in atTop, ∀ m,
      ((d.kernel ^ (m+1)) x).real (Subtype.val ⁻¹' U n) ≤ p n+C₀*θ^m*δ n)
    (hreturn : ∀ᶠ n in atTop, ∀ m, ∀ y : d.State, y.val ∈ U n →
      ((d.kernel ^ (m+1)) y).real (Subtype.val ⁻¹' U n) ≤ p n+C₀*θ^m*δ n)
    (hden : ∀ᶠ n in atTop, (d.weight x.val).toReal / 2 ≤
      (d.rate.toReal)⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ)*p n) atTop (𝓝 rate))
    (hδ : Tendsto δ atTop (𝓝 0))
    (herror : Tendsto (fun n : ℕ => (n : ℝ)*θ^(q n-1)*δ n) atTop (𝓝 0))
    (A : ℕ → Fin k → Set M) (hA : ∀ n i, MeasurableSet (A n i))
    (hAU : ∀ n i, A n i ⊆ U n) :
    Tendsto (fun n => ∑ t ∈ excludedConfigurations n k (q n),
      C.trimmedTargetWeight x.val n (q n) k (A n) t) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    sum_nonneg (fun t _ => C.trimmedTargetWeight_nonneg x.val n (q n) k (A n) t))) _
    (excludedBound_tendsto_zero k q p δ C₀ θ (2*B/a) rate hq hp hδ herror)
  filter_upwards [hp0, hδ0, hq1, hlower, hfirst, hreturn, hden] with n hpn hδn hqn hln hfn hrn hdn
  exact C.sum_excluded_trimmedTargetWeight_le d x (U n) (p n) C₀ θ (δ n) B a hpn hC hθ0 hθ1
    hδn hB ha hln hupper hfn hrn n (q n) k hqn hk hdn (A n) (hA n) (hAU n)

/-- Exact identification of the excluded sum used by the mixed-factorial moment criterion with the
labelled canonical event sum. -/
theorem sum_excluded_trimmed_mixed_eq {J : Type*} [Fintype J]
    (x : M) (n q : ℕ) (U : J → Set M) (r : J → ℕ) :
    (∑ t ∈ excludedConfigurations n (∑ j, r j) q,
      mixedFactorialEventWeight (C.conditionedMeasure x n)
        (trimmedObservations q (fun i : Fin n => fun ω : Path M => ω i.val))
        (liftedTargets (fun j => Option.some '' U j)) r t) =
      ∑ t ∈ excludedConfigurations n (∑ j, r j) q,
        C.trimmedTargetWeight x n q (∑ j, r j)
          (fun i => U ((factorialSlotsEquiv r).symm i).1) t := by
  apply sum_congr rfl
  intro t _
  exact (C.trimmedTargetWeight_eq_mixed x n q U r t).symm

variable [MetricSpace M] [CompactSpace M] [BorelSpace M] {ρ : Measure M}

/-- Under H and the spectral package, the aggregate of all excluded trimmed configurations vanishes.
The only asymptotic inputs concern the target mass, one-step target probability, and the scalar
cutoff. -/
theorem conditioned_excluded_sum_tendsto_zero
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (μ : Measure M) (hμρ : μ ≪ ρ)
    (hmean : ∀ v, s.mean v = ∫ y, v y ∂μ)
    (hleft : ∀ v, s.mean (((d.rate.toReal)⁻¹ • h.transitionOperator) v) = s.mean v)
    (x : d.State) (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᶠ n in atTop, ∀ y ∈ U n, a ≤ (d.weight y).toReal)
    (δ : ℕ → ℝ) (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hsmall : ∀ᶠ n in atTop, ∀ y, (C.killedTransition y).real (U n) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (q : ℕ → ℕ) (rate : ℝ)
    (hq1 : ∀ᶠ n in atTop, 1 ≤ q n)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/n) atTop (𝓝 0))
    (hp : Tendsto (fun n : ℕ => (n : ℝ)*(μ.withDensity d.weight).real (U n)) atTop (𝓝 rate))
    (herror : Tendsto (fun n : ℕ => (n : ℝ)*s.decay^(q n-1)*δ n) atTop (𝓝 0))
    (k : ℕ) (hk : 0 < k) (A : ℕ → Fin k → Set M)
    (hA : ∀ n i, MeasurableSet (A n i)) (hAU : ∀ n i, A n i ⊆ U n) :
    Tendsto (fun n => ∑ t ∈ excludedConfigurations n k (q n),
      C.trimmedTargetWeight x.val n (q n) k (A n) t) atTop (𝓝 0) := by
  obtain ⟨R, _hR0, hRt, hR⟩ := h.weight_bounded d s.eigenvector s.eigenvector_ae
  have hweight : ∀ y, (d.weight y).toReal ≤ R.toReal := fun y => ENNReal.toReal_mono hRt (hR y)
  have hx : 0 < (d.weight x.val).toReal := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  let ηstar := min a (d.weight x.val).toReal
  have hηstar : 0 < ηstar := lt_min ha hx
  let C₀ := max s.constant ‖1-rankOne s.mean s.eigenvector‖ *
    (d.rate.toReal)⁻¹ * R.toReal / ηstar
  have hC : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hden : ∀ᶠ n in atTop, (d.weight x.val).toReal / 2 ≤
      (d.rate.toReal)⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ := by
    have hh := (tendsto_order.mp (s.normalized_survival_tendstoUniformly.tendsto_at x.val)).1
      _ (half_lt_self hx)
    filter_upwards [hh] with n hn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, Measure.real,
      toKilledKernel_kernel] using hn.le
  have hreturn : ∀ᶠ n in atTop, ∀ m, ∀ y : d.State, ηstar ≤ (d.weight y.val).toReal →
      ((d.kernel ^ (m+1)) y).real (Subtype.val ⁻¹' U n) ≤
        (μ.withDensity d.weight).real (U n)+C₀*s.decay^m*δ n := by
    filter_upwards [hδ0, hsmall] with n hδn hsmalln m y hy
    exact h.doob_short_return d μ hμρ s.mean hmean s.eigenvector s.eigenvector_ae
      (U n) (hU n) (weightedTargetVector s.eigenvector (U n) (hU n))
      (weightedTargetVector_ae s.eigenvector (U n) (hU n) _ s.eigenvector_ae) (hleft _)
      R.toReal (δ n) ηstar s.constant s.decay ENNReal.toReal_nonneg hδn hηstar
      s.constant_nonneg s.decay_nonneg hweight hsmalln s.gap m y hy
  apply C.sum_excluded_trimmedTargetWeight_tendsto_zero d x U
    (fun n => (μ.withDensity d.weight).real (U n)) δ q k hk C₀ s.decay s.survivalBound a rate
    hC s.decay_nonneg s.decay_lt_one s.survivalBound_nonneg ha
    (Eventually.of_forall fun _ => measureReal_nonneg) hδ0 hq1 hlower
  · intro m y
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, Measure.real,
      toKilledKernel_kernel] using s.normalized_survival_real_le m y
  · filter_upwards [hreturn] with n hn m
    exact hn m x (min_le_right _ _)
  · filter_upwards [hreturn, hlower] with n hn hln m y hy
    exact hn m y ((min_le_left _ _).trans (hln y.val hy))
  · exact hden
  · exact hq
  · exact hp
  · exact hδ
  · exact herror
  · exact hA
  · exact hAU

end ConditionedStableLaws.CanonicalChain
