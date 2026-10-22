import ConditionedStableLaws.LabelledTargetMixing

/-!
Probabilities of interior separated configurations factorize, with an explicit geometric error
uniform in their times and measurable labels.
-/
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 800000
namespace ConditionedStableLaws.SeparatedChainBounds
open StandingHypothesis ConditionalMixing
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M} (h : HypothesisH ρ K)
  (d : DoobTransform.EigenData K.kernel) (s : SurvivalGapData h d)

def powerBound : ℝ := 1 + ‖rankOne s.mean s.eigenvector‖ + s.constant

theorem powerBound_one_le : 1 ≤ powerBound h d s := by
  dsimp [powerBound]
  linarith [norm_nonneg (rankOne s.mean s.eigenvector), s.constant_nonneg]

theorem projection_norm_le : ‖rankOne s.mean s.eigenvector‖ ≤ powerBound h d s := by
  dsimp [powerBound]
  linarith [s.constant_nonneg]

theorem power_norm_le (n : ℕ) (hn : 1 ≤ n) :
    ‖((d.rate.toReal)⁻¹ • h.transitionOperator)^n‖ ≤ powerBound h d s := by
  have hθ : s.decay^n ≤ 1 := pow_le_one₀ s.decay_nonneg s.decay_lt_one.le
  have hh := norm_add_le (((d.rate.toReal)⁻¹ • h.transitionOperator)^n -
    rankOne s.mean s.eigenvector) (rankOne s.mean s.eigenvector)
  rw [sub_add_cancel] at hh
  have hb := (s.gap n hn).trans (mul_le_of_le_one_right s.constant_nonneg hθ)
  dsimp [powerBound]
  linarith

/-- The all-orders constant depends on the order and fixed starting point,
not on the targets or their observation times. -/
def mixingConstant (x : M) (k : ℕ) : ℝ :=
  (2 / (d.weight x).toReal) * ‖h.stepEvaluation (d.rate.toReal)⁻¹ x‖ * s.constant * ‖s.one‖ *
    ((k+1 : ℝ) * powerBound h d s ^ (k+1) + (‖s.mean‖*‖s.eigenvector‖)^k)

theorem mixingConstant_nonneg (x : M) (k : ℕ) : 0 ≤ mixingConstant h d s x k := by
  have : 0 ≤ powerBound h d s := zero_le_one.trans (powerBound_one_le h d s)
  have := s.constant_nonneg
  dsimp [mixingConstant]
  positivity

end ConditionedStableLaws.SeparatedChainBounds

namespace ConditionedStableLaws.CanonicalChain
open StandingHypothesis ConditionalMixing LabelledTargetMixing SeparatedChainBounds OrderedPathEvents
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Sorted observation times in the interior, with all adjacent gaps separated, have the product of
their stationary target masses as the main term. -/
theorem conditioned_ordered_separated_mixing
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (μ : Measure M) (hμρ : μ ≪ ρ) (hmean : ∀ v, s.mean v = ∫ y, v y ∂μ)
    (x : d.State) (N q r : ℕ) (hq : 2 ≤ q)
    (times : Fin (r+1) → Fin N) (htimes : StrictMono times)
    (hinterior : ∀ i, q ≤ (times i).val ∧ (times i).val + q ≤ N)
    (hgaps : ∀ i : Fin r, q < (times i.succ).val - (times i.castSucc).val)
    (hsmall : ‖h.stepEvaluation (d.rate.toReal)⁻¹ x.val‖ * s.constant * s.decay^(q-1) * ‖s.one‖ ≤
      (d.weight x.val).toReal / 2)
    (A : Fin (r+1) → Set M) (hA : ∀ i, MeasurableSet (A i)) :
    |(C.conditionedMeasure x.val N).real {ω | ∀ i, ω (times i).val ∈ Option.some '' A i} -
      ∏ i, (μ.withDensity d.weight).real (A i)| ≤
      mixingConstant h d s x.val (r+1) * s.decay^(q-1) := by
  let τ : Fin (r+1) → ℕ := fun i => (times i).val
  have hτ : StrictMono τ := fun i j hij => htimes hij
  let w : List (ℕ × Fin (r+1)) := List.ofFn (fun i : Fin r => (τ i.succ-τ i.castSucc, i.succ))
  have hfirst : 1 ≤ τ 0 := by have := (hinterior 0).1; dsimp [τ]; omega
  have ht : 1 ≤ N-τ (Fin.last r) ∧ q-1 ≤ N-τ (Fin.last r) := by
    have := (hinterior (Fin.last r)).2
    dsimp [τ] at *
    omega
  have heval : h.stepEvaluation (d.rate.toReal)⁻¹ x.val s.eigenvector = (d.weight x.val).toReal := by
    rw [← h.smoothedOperator_apply]
    exact h.smoothed_eigenvector d s.eigenvector s.eigenvector_ae x.val
  have hx : 0 < h.stepEvaluation (d.rate.toReal)⁻¹ x.val s.eigenvector := by
    rw [heval]
    exact ENNReal.toReal_pos x.property (d.weight_ne_top _)
  have hword : ∀ p ∈ ((τ 0-1, 0)::w), 1 ≤ p.1 ∧ q-1 ≤ p.1 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · have := (hinterior 0).1
      dsimp [τ] at *
      omega
    · rcases List.mem_ofFn.mp hp with ⟨i,rfl⟩
      have := hgaps i
      dsimp [τ]
      omega
  have hh := C.conditioned_labelled_event_mixing h d μ hμρ s.mean hmean s.eigenvector s.one
    s.eigenvector_ae x.val s.mean_one s.one_ae hx (τ 0-1) 0 w A hA
    (N-τ (Fin.last r)) (q-1) (powerBound h d s) s.constant s.decay
    (powerBound_one_le h d s) s.constant_nonneg s.decay_nonneg s.decay_lt_one.le
    (projection_norm_le h d s) (power_norm_le h d s) s.gap hword ht (by rwa [heval])
  have htime : τ 0-1+(w.map Prod.fst).sum+(N-τ (Fin.last r))+1 = N := by
    have he := first_add_sum_gaps r τ hτ.monotone
    have hlast := (times (Fin.last r)).isLt
    have hsum : (w.map Prod.fst).sum = ∑ i : Fin r, (τ i.succ-τ i.castSucc) := by
      simp [w, List.map_ofFn, List.sum_ofFn]
    rw [hsum]
    dsimp [τ] at *
    omega
  have hw : setWord A ((τ 0-1+1, 0)::w) = timeWord τ A := by
    rw [Nat.sub_add_cancel hfirst, timeWord_eq]
    simp [setWord, w, List.map_ofFn, Function.comp_def]
  have hprod : (((τ 0-1, 0)::w).map fun p => (μ.withDensity d.weight).real (A p.2)).prod =
      ∏ i, (μ.withDensity d.weight).real (A i) := by
    simp only [List.map_cons, List.prod_cons, w, List.map_ofFn, List.prod_ofFn, Function.comp_def]
    exact (Fin.prod_univ_succ (fun i : Fin (r+1) => (μ.withDensity d.weight).real (A i))).symm
  rw [htime, hw, pathEvent_timeWord τ hτ.monotone A, hprod, heval] at hh
  norm_num only [w, List.length_ofFn, mixingConstant, Nat.cast_add, Nat.cast_one,
    Nat.add_assoc, add_assoc] at hh ⊢
  exact hh

/-- Sorting only permutes the target labels and leaves their product unchanged. This is the
separated-event estimate for factorial moments. -/
theorem conditioned_separated_trimmedWeight_mixing
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (μ : Measure M) (hμρ : μ ≪ ρ) (hmean : ∀ v, s.mean v = ∫ y, v y ∂μ)
    (x : d.State) (N q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    (t : Fin k → Fin N) (ht : t ∈ interiorSeparatedConfigurations N k q)
    (hsmall : ‖h.stepEvaluation (d.rate.toReal)⁻¹ x.val‖ * s.constant * s.decay^(q-1) * ‖s.one‖ ≤
      (d.weight x.val).toReal / 2)
    (A : Fin k → Set M) (hA : ∀ i, MeasurableSet (A i)) :
    |C.trimmedTargetWeight x.val N q k A t - ∏ i, (μ.withDensity d.weight).real (A i)| ≤
      mixingConstant h d s x.val k * s.decay^(q-1) := by
  cases k with
  | zero => omega
  | succ r =>
      obtain ⟨hsep,hint⟩ := (mem_interiorSeparatedConfigurations_iff t).mp ht
      have hinj : Function.Injective t := by
        intro i j hij
        by_contra hne
        exact hsep i j hne (by simp [CloseTimes, hij])
      let e : Fin (r+1) ↪ Fin N := ⟨t,hinj⟩
      let times := (SortedConfigurations.sorted e).val
      let A' : Fin (r+1) → Set M := fun i => A ((SortedConfigurations.rank e).symm i)
      have hs (i : Fin (r+1)) : times i = t ((SortedConfigurations.rank e).symm i) := by
        simpa only [Equiv.apply_symm_apply, times, e, Function.Embedding.coeFn_mk] using
          SortedConfigurations.sorted_rank e ((SortedConfigurations.rank e).symm i)
      have htimes : StrictMono times := (SortedConfigurations.sorted e).property
      have hinterior : ∀ i, q ≤ (times i).val ∧ (times i).val+q ≤ N := by
        intro i
        rw [hs]
        exact hint _
      have hgaps : ∀ i : Fin r, q < (times i.succ).val-(times i.castSucc).val := by
        intro i
        have hne : (SortedConfigurations.rank e).symm i.castSucc ≠
            (SortedConfigurations.rank e).symm i.succ := by
          apply (SortedConfigurations.rank e).symm.injective.ne
          exact ne_of_lt Fin.castSucc_lt_succ
        have hc := hsep _ _ hne
        change ¬(_ ≤ _+q ∧ _ ≤ _+q) at hc
        rw [← hs, ← hs] at hc
        have hm : (times i.castSucc).val < (times i.succ).val := htimes Fin.castSucc_lt_succ
        omega
      have hevent : {ω : Path M | ∀ i, ω (t i).val ∈ Option.some '' A i} =
          {ω : Path M | ∀ i, ω (times i).val ∈ Option.some '' A' i} := by
        ext ω
        simp only [Set.mem_ofPred_eq, hs, A']
        constructor
        · intro hh i
          exact hh ((SortedConfigurations.rank e).symm i)
        · intro hh i
          have hh' := hh (SortedConfigurations.rank e i)
          simpa only [Equiv.symm_apply_apply] using hh'
      have hprod : (∏ i, (μ.withDensity d.weight).real (A' i)) =
          ∏ i, (μ.withDensity d.weight).real (A i) :=
        Equiv.prod_comp (SortedConfigurations.rank e).symm
          (fun i => (μ.withDensity d.weight).real (A i))
      have hnoboundary : t ∉ boundaryConfigurations N (r+1) q := by
        have hnot := (mem_sdiff.mp ht).2
        exact fun hb => hnot (mem_union_right _ hb)
      have hh := C.conditioned_ordered_separated_mixing h d s μ hμρ hmean x N q r hq
        times htimes hinterior hgaps hsmall A' (fun i => hA _)
      rw [hprod, ← hevent] at hh
      simpa only [trimmedTargetWeight, hnoboundary, hinj, ↓reduceIte] using hh

end ConditionedStableLaws.CanonicalChain
