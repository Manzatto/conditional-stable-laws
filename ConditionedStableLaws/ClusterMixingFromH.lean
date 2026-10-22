import ConditionedStableLaws.StationaryClusters
import ConditionedStableLaws.HypothesisSpectralGap
import ConditionedStableLaws.EigenmeasureDensity
import ConditionedStableLaws.L2Compactness

/-!
# Cluster mixing under Hypothesis H

The separated-cluster mixing estimate with the spectral gap obtained from H: there is `θ ∈ [0,1)`
such that for every `x ∈ M \ Z` the conditioned probability of the cluster events equals the product
of the stationary `Q`-cluster probabilities `∏ π_ℓ` up to `Kₓ(c, r) θ^q`, uniformly in the observed
sets (any `[0,1]`-valued observables, in particular indicators), the gaps inside the clusters and
the positions of the clusters; `c` is the number of clusters and `Kₓ` depends only on `x`, `c` and
the total number of internal observations.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.CanonicalChain

open ClusterMixing ConditionalMixing StandingHypothesis PathMixing StationaryClusters

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  (C : CanonicalChain M) {ρ : Measure M}

local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

/-- **Cluster mixing**, with the spectral gap derived from H. -/
theorem conditioned_cluster_mixing_of_H (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ x : d.State, ∃ Kx : ℕ → ℕ → ℝ,
      ∀ (w : List (ℕ × Block (Lp ℝ ∞ ρ))) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞),
        (∀ p ∈ flatten w, Measurable (f p.2)) → (∀ p ∈ flatten w, ∀ y, f p.2 y ≤ 1) →
        (∀ p ∈ flatten w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2) →
        ∀ t m : ℕ, (∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) → 1 ≤ t ∧ m ≤ t →
          |(∫ ω, (pathProduct (liftObservations
              ((1, fun _ => 1) :: (flatten w).map (fun p => (p.1, f p.2)))) ω).toReal
            ∂C.conditionedMeasure x.val (((flatten w).map Prod.fst).sum + t + 1)) -
              (w.map fun p => clusterExpectation d μ p.2 f).prod| ≤
            Kx w.length (w.map fun p => p.2.internal.length).sum * θ ^ m := by
  have : IsProbabilityMeasure ρ := h.reference_probability
  obtain ⟨s', hmean⟩ := h.exists_survivalGapData_with_mean d s.continuous_weight μ hleft hnorm
  have hμρ : μ ≪ ρ := h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft
  set r := d.rate.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  set Pi0 := rankOne s'.mean s'.eigenvector with hPi0_def
  set U := max 1 (‖Pi0‖ + s'.constant) with hU_def
  have hU : 1 ≤ U := le_max_left _ _
  have hP : ‖Pi0‖ ≤ U := (le_add_of_nonneg_right s'.constant_nonneg).trans (le_max_right _ _)
  have hQ : ∀ n, 1 ≤ n → ‖(r⁻¹ • h.transitionOperator) ^ n‖ ≤ U := by
    intro n hn
    have h1 := norm_le_norm_add_norm_sub' ((r⁻¹ • h.transitionOperator) ^ n) Pi0
    have h2 := s'.gap n hn
    have h3 : s'.constant * s'.decay ^ n ≤ s'.constant :=
      mul_le_of_le_one_right s'.constant_nonneg
        (pow_le_one₀ s'.decay_nonneg s'.decay_lt_one.le)
    refine le_trans ?_ (le_max_right _ _)
    linarith
  refine ⟨s'.decay, s'.decay_nonneg, s'.decay_lt_one, fun x => ?_⟩
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  set one : Lp ℝ ∞ ρ := (memLp_top_const (μ := ρ) (1 : ℝ)).toLp _ with hone_def
  have hone_rep : (one : M → ℝ) =ᵐ[ρ] fun _ => 1 := (memLp_top_const (1 : ℝ)).coeFn_toLp
  have hone : s'.mean one = 1 := by
    rw [hmean, integral_congr_ae (hμρ.ae_eq hone_rep)]; simp
  have ha : 0 < h.stepEvaluation r⁻¹ x.val s'.eigenvector := by
    rw [h.stepEvaluation_apply]
    have h1 : ∫ y, s'.eigenvector y ∂C.toKilledKernel.kernel x.val =
        ∫ y, (d.weight y).toReal ∂C.toKilledKernel.kernel x.val :=
      integral_congr_ae ((h.absolutelyContinuous x.val).ae_eq s'.eigenvector_ae)
    have h2 := L2Compactness.kint_eta (K := C.toKilledKernel) d x.val
    rw [h1]
    change 0 < r⁻¹ * KernelLp.kint C.toKilledKernel.kernel
      (L2Compactness.eta (K := C.toKilledKernel) d) x.val
    rw [h2]
    change 0 < r⁻¹ * (r * (d.weight x.val).toReal)
    have := ENNReal.toReal_pos x.property (d.weight_ne_top _)
    positivity
  set ev := h.stepEvaluation r⁻¹ x.val with hev_def
  refine ⟨fun c i => (2 / ev s'.eigenvector) * ‖ev‖ * s'.constant * ‖one‖ *
    ((c + 1 : ℝ) * U ^ (c + 1) + (‖s'.mean‖ * ‖s'.eigenvector‖) ^ c) * U ^ i,
    fun w f hfm hfb hrep t m htimes ht => ?_⟩
  have hb := C.conditioned_cluster_mixing_uniform h d μ hμρ hnorm s'.mean hmean s'.eigenvector one
    s'.eigenvector_ae x.val hx hone hone_rep ha w f hfm hfb hrep t m U s'.constant s'.decay hU
    s'.constant_nonneg s'.decay_nonneg s'.decay_lt_one.le hP hQ (fun n hn => s'.gap n hn)
    htimes ht
  refine hb.trans (le_of_eq ?_)
  simp only [hev_def]
  ring

end ConditionedStableLaws.CanonicalChain
