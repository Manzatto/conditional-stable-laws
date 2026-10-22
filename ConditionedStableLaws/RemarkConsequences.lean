import ConditionedStableLaws.QProcessDefinition
import ConditionedStableLaws.TheoremF
import ConditionedStableLaws.WeightedLp
import ConditionedStableLaws.PoissonProcessConvergence

/-!
# Consequences of the remarks

The Q-process avoids the escaping set at every time, simultaneously almost surely. Integer-valued
limiting Poisson counts are independent. Finite-time counts need not be independent: mutually
exclusive positive-probability events give an explicit obstruction. The integrability comparison
gives conditional LLN conclusions, including the case in which the weight is bounded away from zero.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section
namespace ConditionedStableLaws

namespace CanonicalChain
open StandingHypothesis
variable {M : Type*} [MeasurableSpace M] {C : CanonicalChain M}

/-- The Q-process stays in its state space at all times on one event of full
probability, rather than merely on a separate event at each time. -/
theorem IsQProcess.ae_always_stays {S : Set M} {Q : M → Measure (Path M)}
    (hQ : C.IsQProcess S Q) {x : M} (hx : x ∈ S) :
    ∀ᵐ ω ∂Q x, ∀ n : ℕ, ω n ∈ Option.some '' S :=
  ae_all_iff.mpr (hQ.stays x hx)

/-- The single event of staying in the live state space forever has probability one. -/
theorem IsQProcess.always_stays_eq_one {S : Set M} {Q : M → Measure (Path M)}
    (hQ : C.IsQProcess S Q) (hS : MeasurableSet S) {x : M} (hx : x ∈ S) :
    Q x {ω | ∀ n : ℕ, ω n ∈ Option.some '' S} = 1 := by
  have := hQ.isProbability x hx
  apply (mem_ae_iff_prob_eq_one ?_).mp (hQ.ae_always_stays hx)
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    (measurableEmbedding_some_state.measurableSet_image' hS).preimage (measurable_pi_apply n)

/-- In particular, every finite survival event has Q-probability one. -/
theorem IsQProcess.survival_eq_one {S : Set M} {Q : M → Measure (Path M)}
    (hQ : C.IsQProcess S Q) {x : M} (hx : x ∈ S) (n : ℕ) :
    Q x (survival n) = 1 := by
  have := hQ.isProbability x hx
  have hs : ∀ᵐ ω ∂Q x, ω ∈ survival n := by
    filter_upwards [hQ.ae_always_stays hx] with ω hω
    intro k _
    obtain ⟨y, _, hy⟩ := hω k
    rw [← hy]
    exact Option.some_ne_none y
  exact (mem_ae_iff_prob_eq_one (measurableSet_survival n)).mp hs

/-- The coordinate transition law of a Q-process assigns zero mass to the escaping set. -/
theorem IsQProcess.escaping_marginal_eq_zero {K : Kernel M M}
    {Q : M → Measure (Path M)}
    (hQ : C.IsQProcess (survivingSet K) Q) {x : M}
    (hx : x ∈ survivingSet K) (n : ℕ) :
    Q x {ω | ω n ∈ Option.some '' escapingSet K} = 0 := by
  have hz : ∀ᵐ ω ∂Q x, ω ∉ {ω | ω n ∈ Option.some '' escapingSet K} := by
    filter_upwards [hQ.stays x hx n] with ω hω hbad
    obtain ⟨y, hy, he⟩ := hω
    obtain ⟨z, hz, he'⟩ := hbad
    have : z = y := Option.some.inj (he'.trans he.symm)
    subst z
    exact hy hz
  simpa only [Set.mem_ofPred_eq, not_not] using (ae_iff.mp hz)

/-- **The Q-process under H.** The Q-process exists; it gives probability one to every finite
survival event, zero mass to the escaping set at every time, and probability one to staying in the
surviving set at all times. -/
theorem exists_qProcess_never_escapes [MetricSpace M] [CompactSpace M] [BorelSpace M]
    {ρ : Measure M} (h : HypothesisH ρ C.toKilledKernel) :
    ∃ Q : M → Measure (Path M), C.IsQProcess (survivingSet C.killedTransition) Q ∧
      ∀ x ∈ survivingSet C.killedTransition,
        (∀ n : ℕ, Q x (survival n) = 1) ∧
        (∀ n : ℕ, Q x {ω | ω n ∈ Option.some '' escapingSet C.killedTransition} = 0) ∧
        Q x {ω | ∀ n : ℕ, ω n ∈ Option.some '' survivingSet C.killedTransition} = 1 := by
  obtain ⟨d, hlive, hQ⟩ := h.exists_isQProcess (C := C)
  refine ⟨C.doobQ d, hQ, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · exact fun n => hQ.survival_eq_one hx n
  · exact fun n => hQ.escaping_marginal_eq_zero hx n
  · apply hQ.always_stays_eq_one _ hx
    rw [← hlive]
    exact d.measurableSet_liveSet

end CanonicalChain

namespace IsPoissonRandomMeasure
variable {Ω : Type*} [MeasurableSpace Ω] {N : RandomPointMeasure Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {υ : Measure ExtremeState}

/-- The natural-valued limiting Poisson counts on disjoint sets are independent, including
finite-intensity sets of intensity zero. -/
theorem independent_countOn (hN : IsPoissonRandomMeasure N P υ)
    (k : ℕ) (A : Fin k → Set ExtremeState) (hA : ∀ j, MeasurableSet (A j))
    (hd : Pairwise fun i j => Disjoint (A i) (A j))
    (hf : ∀ j, υ (A j) ≠ ∞) :
    iIndepFun (fun j ω => (N.toFun ω).countOn (A j)) P :=
  (hN.independent_counts k A hA hd hf).comp
    (fun (_ : Fin k) (x : ℝ≥0∞) => ⌊x.toReal⌋₊)
    (fun _ => measurable_id.ennreal_toReal.nat_floor)

end IsPoissonRandomMeasure

/-- Two mutually exclusive positive-probability values obstruct independence. This applies, in
particular, to the two one-observation counts of disjoint targets. -/
theorem not_indepFun_of_disjoint_positive_values
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    {P : Measure Ω} {X : Ω → A} {Y : Ω → B} (a : A) (b : B)
    (hx : P (X ⁻¹' {a}) ≠ 0) (hy : P (Y ⁻¹' {b}) ≠ 0)
    (hd : Disjoint (X ⁻¹' {a}) (Y ⁻¹' {b})) : ¬ IndepFun X Y P := by
  intro hi
  have hh := hi.measure_inter_preimage_eq_mul {a} {b}
    (measurableSet_singleton a) (measurableSet_singleton b)
  rw [Set.disjoint_iff_inter_eq_empty.mp hd, measure_empty] at hh
  exact (mul_ne_zero hx hy) hh.symm

/-- Finite empirical counts in two disjoint sets need not be independent: with one random
observation and positive probabilities of both targets they are necessarily dependent. -/
theorem not_independent_single_observation_counts
    {Ω A : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → A) {U V : Set A} (hd : Disjoint U V)
    (hU : P (X ⁻¹' U) ≠ 0) (hV : P (X ⁻¹' V) ≠ 0) :
    ¬ IndepFun
      (fun ω => (visitTimes (fun _ : Fin 1 => X ω) U).card)
      (fun ω => (visitTimes (fun _ : Fin 1 => X ω) V).card) P := by
  classical
  have he (S : Set A) :
      (fun ω => (visitTimes (fun _ : Fin 1 => X ω) S).card) ⁻¹' {1} = X ⁻¹' S := by
    ext ω
    by_cases hx : X ω ∈ S <;> simp [visitTimes, hx]
  apply not_indepFun_of_disjoint_positive_values 1 1
  · rwa [he]
  · rwa [he]
  · rw [he, he]
    exact hd.preimage X

namespace RefinedLLN
open StandingHypothesis CanonicalChain
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
    {ρ : Measure M} (C : CanonicalChain M)

/-- If the eigenfunction is bounded away from zero, L1(nu) suffices for the conditional-mean LLN
because it implies L1(mu). -/
theorem lln_L1_of_weight_bounded_below (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (a : ℝ≥0∞) (ha : a ≠ 0) (hat : a ≠ ∞)
    (hlower : ∀ᵐ y ∂μ, a ≤ d.weight y)
    {f : M → ℝ} (hf : Measurable f)
    (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0)
    (hfi : Integrable f (μ.withDensity d.weight)) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M),
      Tendsto (fun n : ℕ => ∫ ω, |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω -
        ∫ y, f y ∂μ.withDensity d.weight| ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
  have hμ : Integrable f μ := by
    rw [← memLp_one_iff_integrable] at hfi ⊢
    exact hfi.of_measure_le_smul (by simpa using ha)
      (measure_le_weighted_of_weight_ge ha hat hlower)
  exact lln_L1 C h d s hlive μ hleft hnorm hf hZ hμ

end RefinedLLN
end ConditionedStableLaws
