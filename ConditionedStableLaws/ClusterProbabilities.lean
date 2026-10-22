import ConditionedStableLaws.ShortReturns
import ConditionedStableLaws.ClusterGapSums

/-!
# Probabilities of short clusters

The Markov product identity bounds a simultaneous target event by its initial target mass times the
successive return bounds. This gives the probability input to the finite gap sums.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace ConditionedStableLaws.ClusterProbabilities
open PathMixing StationaryClusters
variable {M : Type*} [MeasurableSpace M]

/-- Kernel powers of a Markov kernel remain Markov. -/
theorem markov_power (K : Kernel M M) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (K ^ n) := by
  induction n with
  | zero =>
      change IsMarkovKernel (Kernel.id : Kernel M M)
      infer_instance
  | succ n ih =>
      have := ih
      rw [pow_succ]
      change IsMarkovKernel ((K ^ n) ∘ₖ K)
      infer_instance

/-- A nested target word retains one return factor per internal gap. -/
theorem kernelWord_targets_le (K : Kernel M M) [IsMarkovKernel K]
    (U : Set M) (w : List (ℕ × Set M))
    (hw : ∀ p ∈ w, MeasurableSet p.2) (hsub : ∀ p ∈ w, p.2 ⊆ U)
    (b : ℕ → ℝ≥0∞)
    (hreturn : ∀ p ∈ w, ∀ x ∈ U, (K ^ p.1) x U ≤ b p.1)
    (x : M) (hx : x ∈ U) :
    PathMixing.kernelWord K (indicatorObservations w) (fun _ => 1) x ≤
      (w.map (fun p => b p.1)).prod := by
  induction w generalizing x with
  | nil => simp [indicatorObservations, PathMixing.kernelWord]
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      have hA := hw (n, A) (by simp)
      have hwm : ∀ p ∈ w, MeasurableSet p.2 := fun p hp => hw p (by simp [hp])
      have hws : ∀ p ∈ w, p.2 ⊆ U := fun p hp => hsub p (by simp [hp])
      have hwr : ∀ p ∈ w, ∀ x ∈ U, (K ^ p.1) x U ≤ b p.1 :=
        fun p hp => hreturn p (by simp [hp])
      change (∫⁻ y, A.indicator (fun _ => 1) y *
        PathMixing.kernelWord K (indicatorObservations w) (fun _ => 1) y ∂(K ^ n) x) ≤
        b n * (w.map (fun p => b p.1)).prod
      calc
        _ ≤ ∫⁻ y, A.indicator (fun _ => (w.map (fun p => b p.1)).prod) y ∂(K ^ n) x := by
          apply lintegral_mono
          intro y
          by_cases hy : y ∈ A
          · simp only [indicator_of_mem hy, one_mul]
            exact ih hwm hws hwr y (hsub (n, A) (by simp) hy)
          · simp [hy]
        _ = (w.map (fun p => b p.1)).prod * (K ^ n) x A := by
          rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ]
        _ ≤ (w.map (fun p => b p.1)).prod * b n := by
          exact mul_le_mul' le_rfl ((measure_mono (hsub (n, A) (by simp))).trans
            (hreturn (n, A) (by simp) x hx))
        _ = _ := mul_comm _ _

/-- The probability of a cluster event under an arbitrary initial law. Only one-time Markov return
bounds are inputs. -/
theorem initial_cluster_measure_le (K : Kernel M M) [IsMarkovKernel K]
    (ν : Measure M) (U A : Set M) (hA : MeasurableSet A) (hAU : A ⊆ U)
    (w : List (ℕ × Set M)) (hw : ∀ p ∈ w, MeasurableSet p.2)
    (hsub : ∀ p ∈ w, p.2 ⊆ U) (b : ℕ → ℝ≥0∞)
    (hreturn : ∀ p ∈ w, ∀ x ∈ U, (K ^ p.1) x U ≤ b p.1) :
    initialPathMeasure K ν (targetEvent ((0, A) :: w)) ≤
      ν U * (w.map (fun p => b p.1)).prod := by
  have hwm : ∀ p ∈ (0, A) :: w, MeasurableSet p.2 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hA
    · exact hw p hp
  have hpath := lintegral_initial_pathProduct K ν
    (indicatorObservations ((0, A) :: w)) (measurable_indicatorObservations _ hwm)
  simp_rw [pathProduct_target_indicators] at hpath
  rw [lintegral_indicator (measurableSet_targetEvent _ hwm), lintegral_one,
    Measure.restrict_apply_univ] at hpath
  rw [hpath]
  have hkernel (x : M) :
      PathMixing.kernelWord K (indicatorObservations ((0, A) :: w)) (fun _ => 1) x =
        A.indicator (fun _ => 1) x *
          PathMixing.kernelWord K (indicatorObservations w) (fun _ => 1) x := by
    change (∫⁻ y, A.indicator (fun _ => 1) y *
      PathMixing.kernelWord K (indicatorObservations w) (fun _ => 1) y ∂(K ^ 0) x) = _
    change (∫⁻ y, A.indicator (fun _ => 1) y *
      PathMixing.kernelWord K (indicatorObservations w) (fun _ => 1) y ∂Measure.dirac x) = _
    exact lintegral_dirac' _ ((measurable_const.indicator hA).mul
      (measurable_kernelWord K _ (measurable_indicatorObservations _ hw) _ measurable_const))
  simp_rw [hkernel]
  calc
    _ ≤ ∫⁻ x, A.indicator (fun _ => (w.map (fun p => b p.1)).prod) x ∂ν := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · simp only [indicator_of_mem hx, one_mul]
        exact kernelWord_targets_le K U w hw hsub b hreturn x (hAU hx)
      · simp [hx]
    _ = (w.map (fun p => b p.1)).prod * ν A := by
      rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ (w.map (fun p => b p.1)).prod * ν U := mul_le_mul' le_rfl (measure_mono hAU)
    _ = _ := mul_comm _ _


/-- Real-valued version of the exact Markov cluster bound. -/
theorem initial_cluster_real_le (K : Kernel M M) [IsMarkovKernel K]
    (ν : Measure M) [IsFiniteMeasure ν]
    (U A : Set M) (hA : MeasurableSet A) (hAU : A ⊆ U)
    (w : List (ℕ × Set M)) (hw : ∀ p ∈ w, MeasurableSet p.2)
    (hsub : ∀ p ∈ w, p.2 ⊆ U) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hreturn : ∀ p ∈ w, ∀ x ∈ U, ((K ^ p.1) x).real U ≤ b p.1) :
    (initialPathMeasure K ν).real (targetEvent ((0, A) :: w)) ≤
      ν.real U * (w.map (fun p => b p.1)).prod := by
  have hret : ∀ p ∈ w, ∀ x ∈ U, (K ^ p.1) x U ≤ ENNReal.ofReal (b p.1) := by
    intro p hp x hx
    have := markov_power K p.1
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hreturn p hp x hx)
  have hn := initial_cluster_measure_le K ν U A hA hAU w hw hsub
    (fun n => ENNReal.ofReal (b n)) hret
  have hprod : (w.map (fun p => ENNReal.ofReal (b p.1))).prod =
      ENNReal.ofReal ((w.map (fun p => b p.1)).prod) := by
    clear hw hsub hreturn hret hn
    induction w with
    | nil => simp
    | cons p w ih =>
      simp only [List.map_cons, List.prod_cons, ih, ENNReal.ofReal_mul (hb p.1)]
  rw [hprod] at hn
  have hnreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top) hn
  have hpos : 0 ≤ (w.map (fun p => b p.1)).prod := by
    apply List.prod_nonneg
    intro a ha
    rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
    exact hb p.1
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos] using hnreal


/-- Restriction to the live subtype preserves every ambient weighted target
mass: the complement of the live set has density zero. -/
theorem weightedInitial_apply {K : Kernel M M} [IsSFiniteKernel K]
    (d : DoobTransform.EigenData K) (μ : Measure M) (U : Set M) (hU : MeasurableSet U) :
    d.weightedInitial μ (Subtype.val ⁻¹' U) = (μ.withDensity d.weight) U := by
  unfold DoobTransform.EigenData.weightedInitial
  rw [d.live_embedding.comap_apply]
  have himage : (Subtype.val : d.State → M) '' (Subtype.val ⁻¹' U) = U ∩ d.liveSet := by
    ext y
    simp only [mem_image, mem_preimage, mem_inter_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.property⟩
    · rintro ⟨hy, hlive⟩
      exact ⟨⟨y, hlive⟩, hy, rfl⟩
  rw [himage, withDensity_apply _ (hU.inter d.measurableSet_liveSet), withDensity_apply _ hU,
    ← lintegral_indicator (hU.inter d.measurableSet_liveSet), ← lintegral_indicator hU]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ U
  · by_cases hlive : y ∈ d.liveSet
    · simp [hy, hlive]
    · have hz : d.weight y = 0 := by simpa [DoobTransform.EigenData.liveSet] using hlive
      simp [hy, hlive, hz]
  · simp [hy]

/-- A stationary Doob cluster coefficient is bounded by the initial weighted target mass times the
return probabilities. -/
theorem doob_cluster_le {K : Kernel M M} [IsSFiniteKernel K]
    (d : DoobTransform.EigenData K) (μ : Measure M)
    (hnorm : ∫⁻ y, d.weight y ∂μ = 1) (U : Set M) (hU : MeasurableSet U)
    (b : ClusterMixing.Block (Set M))
    (hb : ∀ p ∈ (0, b.first) :: b.internal, MeasurableSet p.2)
    (hsub : ∀ p ∈ (0, b.first) :: b.internal, p.2 ⊆ U)
    (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (hreturn : ∀ p ∈ b.internal, ∀ x : d.State, x.val ∈ U →
      ((d.kernel ^ p.1) x).real (Subtype.val ⁻¹' U) ≤ R p.1) :
    clusterExpectation d μ b (fun A => A.indicator (fun _ => 1)) ≤
      (μ.withDensity d.weight).real U * (b.internal.map (fun p => R p.1)).prod := by
  have : IsProbabilityMeasure (d.weightedInitial μ) := d.isProbabilityMeasure_weightedMeasure μ hnorm
  rw [clusterExpectation_indicators d μ b hb]
  let w := b.internal.map (fun p => (p.1, (Subtype.val : d.State → M) ⁻¹' p.2))
  have hwm : ∀ p ∈ w, MeasurableSet p.2 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (hb q (by simp [hq])).preimage measurable_subtype_coe
  have hws : ∀ p ∈ w, p.2 ⊆ (Subtype.val : d.State → M) ⁻¹' U := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact preimage_mono (hsub q (by simp [hq]))
  have hwr : ∀ p ∈ w, ∀ x ∈ (Subtype.val : d.State → M) ⁻¹' U,
      ((d.kernel ^ p.1) x).real (Subtype.val ⁻¹' U) ≤ R p.1 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact hreturn q hq
  have hh := initial_cluster_real_le d.kernel (d.weightedInitial μ) (Subtype.val ⁻¹' U)
    (Subtype.val ⁻¹' b.first) ((hb (0, b.first) (by simp)).preimage measurable_subtype_coe)
    (preimage_mono (hsub (0, b.first) (by simp))) w hwm hws R hR hwr
  have hmass : (d.weightedInitial μ).real (Subtype.val ⁻¹' U) = (μ.withDensity d.weight).real U :=
    congrArg ENNReal.toReal (weightedInitial_apply d μ U hU)
  rw [hmass] at hh
  simpa only [DoobTransform.EigenData.stationaryPathMeasure, clusterEvent, List.map_cons,
    w, List.map_map, Function.comp_def] using hh


/-- A cluster with prescribed labels and an independently varying vector of
short positive gaps. `s` counts internal gaps, hence the cluster has size `s+1`. -/
def gapBlock {s q : ℕ} (A : Set M) (B : Fin s → Set M) (g : Fin s → Fin q) :
    ClusterMixing.Block (Set M) where
  first := A
  internal := List.ofFn (fun i => ((g i).val + 1, B i))

/-- Summing cluster probabilities over every internal short-gap vector produces a small factor for
each extra point in the cluster. -/
theorem sum_doob_clusters_le {K : Kernel M M} [IsSFiniteKernel K]
    (d : DoobTransform.EigenData K) (μ : Measure M)
    (hnorm : ∫⁻ y, d.weight y ∂μ = 1) (U : Set M) (hU : MeasurableSet U)
    (q s : ℕ) (A : Set M) (B : Fin s → Set M)
    (hA : MeasurableSet A) (hB : ∀ i, MeasurableSet (B i))
    (hAU : A ⊆ U) (hBU : ∀ i, B i ⊆ U)
    (C θ δ : ℝ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : 0 ≤ δ)
    (hreturn : ∀ n : ℕ, ∀ x : d.State, x.val ∈ U →
      ((d.kernel ^ (n + 1)) x).real (Subtype.val ⁻¹' U) ≤
        (μ.withDensity d.weight).real U + C * θ^n * δ) :
    (∑ g : Fin s → Fin q, clusterExpectation d μ (gapBlock A B g)
      (fun S => S.indicator (fun _ => 1))) ≤
      (μ.withDensity d.weight).real U *
        ClusterGapSums.clusterEpsilon q ((μ.withDensity d.weight).real U) C θ δ ^ s := by
  apply ClusterGapSums.sum_cluster_le q s (measureReal_nonneg) hC hθ0 hθ1 hδ
  intro g
  have hm : ∀ p ∈ (0, (gapBlock A B g).first) :: (gapBlock A B g).internal,
      MeasurableSet p.2 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hA
    · rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
      exact hB i
  have hs : ∀ p ∈ (0, (gapBlock A B g).first) :: (gapBlock A B g).internal,
      p.2 ⊆ U := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hAU
    · rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
      exact hBU i
  have hr : ∀ p ∈ (gapBlock A B g).internal, ∀ x : d.State, x.val ∈ U →
      ((d.kernel ^ p.1) x).real (Subtype.val ⁻¹' U) ≤
        (μ.withDensity d.weight).real U + C * θ^(p.1 - 1) * δ := by
    intro p hp x hx
    rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
    simpa using hreturn (g i).val x hx
  have hh := doob_cluster_le d μ hnorm U hU (gapBlock A B g) hm hs
    (fun n => (μ.withDensity d.weight).real U + C * θ^(n - 1) * δ)
    (fun n => add_nonneg measureReal_nonneg (by positivity)) hr
  simpa [gapBlock, List.map_ofFn, List.prod_ofFn] using hh

end ConditionedStableLaws.ClusterProbabilities

namespace ConditionedStableLaws.StandingHypothesis
open ConditionalMixing ClusterMixing StationaryClusters ClusterProbabilities
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- The stationary short-cluster estimate derived from H and explicit spectral eigen-data. The small
factor is the one-step target bound `δ`. Every internal gap is arbitrary and positive; every marked
target may be a subset of the common shrinking target. -/
theorem HypothesisH.stationary_cluster_short_return_bound (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel)
    (μ : Measure M) (hμρ : μ ≪ ρ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (η : Lp ℝ ∞ ρ) (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal)
    (U : Set M) (hU : MeasurableSet U) (f : Lp ℝ ∞ ρ)
    (hrep : f =ᵐ[ρ] U.indicator (fun y => (d.weight y).toReal))
    (hleft : mean (((d.rate.toReal)⁻¹ • h.transitionOperator) f) = mean f)
    (B δ ηstar A θ : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hηstar : 0 < ηstar)
    (hA : 0 ≤ A) (hθ : 0 ≤ θ)
    (hweight : ∀ y, (d.weight y).toReal ≤ B)
    (hlower : ∀ y ∈ U, ηstar ≤ (d.weight y).toReal)
    (hsmall : ∀ y, (K.kernel y).real U ≤ δ)
    (hgap : ∀ n : ℕ, 1 ≤ n →
      ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n - rankOne mean η‖ ≤ A * θ^n)
    (b : Block (Set M))
    (hb : ∀ p ∈ (0, b.first) :: b.internal, MeasurableSet p.2)
    (hsub : ∀ p ∈ (0, b.first) :: b.internal, p.2 ⊆ U)
    (htime : ∀ p ∈ b.internal, 1 ≤ p.1) :
    clusterExpectation d μ b (fun S => S.indicator (fun _ => 1)) ≤
      (μ.withDensity d.weight).real U * (b.internal.map (fun p =>
        (μ.withDensity d.weight).real U +
          (max A ‖1 - rankOne mean η‖ * (d.rate.toReal)⁻¹ * B / ηstar) * θ^(p.1 - 1) * δ)).prod := by
  apply doob_cluster_le d μ hnorm U hU b hb hsub
    (fun n => (μ.withDensity d.weight).real U +
      (max A ‖1 - rankOne mean η‖ * (d.rate.toReal)⁻¹ * B / ηstar) * θ^(n - 1) * δ)
    (fun _ => add_nonneg measureReal_nonneg (by positivity))
  intro p hp x hx
  have hh := h.doob_short_return d μ hμρ mean hmean η hη U hU f hrep hleft
    B δ ηstar A θ hB hδ hηstar hA hθ hweight hsmall hgap (p.1 - 1) x (hlower x.val hx)
  rwa [Nat.sub_add_cancel (htime p hp)] at hh


/-- The complete summed short-cluster estimate under the explicit spectral input. -/
theorem HypothesisH.sum_stationary_clusters_le (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel)
    (μ : Measure M) (hμρ : μ ≪ ρ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (η : Lp ℝ ∞ ρ) (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal)
    (hleft : ∀ v, mean (((d.rate.toReal)⁻¹ • h.transitionOperator) v) = mean v)
    (U : Set M) (hU : MeasurableSet U)
    (B δ ηstar A θ : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hηstar : 0 < ηstar)
    (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hweight : ∀ y, (d.weight y).toReal ≤ B)
    (hlower : ∀ y ∈ U, ηstar ≤ (d.weight y).toReal)
    (hsmall : ∀ y, (K.kernel y).real U ≤ δ)
    (hgap : ∀ n : ℕ, 1 ≤ n →
      ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n - rankOne mean η‖ ≤ A * θ^n)
    (q s : ℕ) (A₀ : Set M) (targets : Fin s → Set M)
    (hA₀ : MeasurableSet A₀) (hTargets : ∀ i, MeasurableSet (targets i))
    (hA₀U : A₀ ⊆ U) (hTargetsU : ∀ i, targets i ⊆ U) :
    let C := max A ‖1 - rankOne mean η‖ * (d.rate.toReal)⁻¹ * B / ηstar
    (∑ g : Fin s → Fin q, clusterExpectation d μ (gapBlock A₀ targets g)
      (fun S => S.indicator (fun _ => 1))) ≤
      (μ.withDensity d.weight).real U *
        ClusterGapSums.clusterEpsilon q ((μ.withDensity d.weight).real U) C θ δ ^ s := by
  dsimp only
  apply sum_doob_clusters_le d μ hnorm U hU q s A₀ targets hA₀ hTargets hA₀U hTargetsU
    _ θ δ (by positivity) hθ0 hθ1 hδ
  intro n x hx
  exact h.doob_short_return d μ hμρ mean hmean η hη U hU (weightedTargetVector η U hU)
    (weightedTargetVector_ae η U hU _ hη) (hleft _) B δ ηstar A θ
    hB hδ hηstar hA hθ0 hweight hsmall hgap n x (hlower x.val hx)

end ConditionedStableLaws.StandingHypothesis
