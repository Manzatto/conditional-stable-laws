import ConditionedStableLaws.CemeteryBridge

/-!
# Killed-kernel powers and canonical survival conditioning

The Ionescu–Tulcea canonical path law and powers of the killed kernel. All transition and survival
identities are derived from the absorbing Markov kernel.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace ConditionedStableLaws

noncomputable section

variable {M : Type*} [MeasurableSpace M]

/-- Pushing a measure forward before applying a kernel is the same as
pulling back the kernel's source. -/
theorem kernel_comp_map_measure {A B D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace D]
    (κ : Kernel B D) (μ : Measure A) (f : A → B) (hf : Measurable f) :
    κ ∘ₘ μ.map f = (κ.comap f hf) ∘ₘ μ := by
  ext S hS
  rw [Measure.bind_apply hS κ.aemeasurable,
    Measure.bind_apply hS (κ.comap f hf).aemeasurable,
    lintegral_map (κ.measurable_coe hS) hf]
  rfl

/-- For an integrand vanishing at the cemetery, only the pullback to the live
states contributes to its lower integral. No finiteness assumption is needed. -/
theorem lintegral_eq_live_comap (μ : Measure (Option M)) (f : Option M → ℝ≥0∞)
    (hzero : f none = 0) :
    (∫⁻ z, f z ∂μ) = ∫⁻ y : M, f (some y) ∂μ.comap Option.some := by
  rw [← measurableEmbedding_some_state.lintegral_map f,
    measurableEmbedding_some_state.map_comap]
  symm
  apply setLIntegral_eq_of_support_subset
  intro z hz
  cases z with
  | none => exact False.elim (hz hzero)
  | some y => exact ⟨y, rfl⟩

namespace CanonicalChain

variable (C : CanonicalChain M)

/-- The canonical trajectory construction gives the exact joint distribution
of the past and the next observation. -/
theorem pathMeasure_past_next (x : M) (n : ℕ) :
    (C.pathMeasure x).map (Preorder.frestrictLe n) ⊗ₘ C.historyKernel n =
      (C.pathMeasure x).map (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- The coordinate marginals of the canonical path law follow the original
Markov transition kernel. -/
theorem pathMeasure_map_succ (x : M) (n : ℕ) :
    (C.pathMeasure x).map (fun ω => ω (n + 1)) =
      C.transition ∘ₘ (C.pathMeasure x).map (fun ω => ω n) := by
  have h := congrArg (fun μ => μ.snd) (C.pathMeasure_past_next x n)
  rw [Measure.snd_compProd] at h
  have hmap : ((C.pathMeasure x).map
      (fun ω => (Preorder.frestrictLe n ω, ω (n + 1)))).snd =
      (C.pathMeasure x).map (fun ω => ω (n + 1)) := by
    rw [Measure.snd, Measure.map_map measurable_snd]
    · rfl
    · exact (Preorder.measurable_frestrictLe n).prod (measurable_pi_apply (n + 1))
  rw [hmap] at h
  rw [← h, historyKernel, ← kernel_comp_map_measure]
  congr 1
  rw [Measure.map_map
    (g := fun ω : (i : Finset.Iic n) → Option M => ω ⟨n, by simp⟩)
    (measurable_pi_apply _) (Preorder.measurable_frestrictLe n)]
  rfl

/-- Absorption ensures that pulling a measure back to live states commutes
with one transition, provided the transition on the live side is killed. -/
theorem live_comap_transition_comp (μ : Measure (Option M)) :
    (C.transition ∘ₘ μ).comap Option.some =
      C.killedTransition ∘ₘ μ.comap Option.some := by
  ext A hA
  have hsome : MeasurableSet (Option.some '' A) :=
    measurableEmbedding_some_state.measurableSet_image' hA
  rw [measurableEmbedding_some_state.comap_apply,
    Measure.bind_apply hsome C.transition.aemeasurable,
    Measure.bind_apply hA C.killedTransition.aemeasurable]
  simp_rw [C.killedTransition_apply _ A hA]
  apply lintegral_eq_live_comap
  rw [C.absorbing, Measure.dirac_apply' _ hsome]
  simp

/-- The live-state part of the time-n marginal is exactly the n-step killed
transition law, including n = 0. -/
theorem pathMeasure_marginal_comap (x : M) (n : ℕ) :
    ((C.pathMeasure x).map (fun ω => ω n)).comap Option.some =
      (C.killedTransition ^ n) x := by
  induction n with
  | zero =>
      rw [C.pathMeasure_initial]
      change (Measure.dirac (some x)).comap Option.some = Measure.dirac x
      rw [← Measure.map_dirac' measurable_some_state]
      exact measurableEmbedding_some_state.comap_map _
  | succ n ih =>
      rw [C.pathMeasure_map_succ, C.live_comap_transition_comp, ih, pow_succ']
      rfl

/-- Exact killed-kernel formula for every measurable live-state target and
every finite time, derived from the canonical path construction. -/
theorem killedTransition_pow_apply (x : M) (n : ℕ) (A : Set M)
    (hA : MeasurableSet A) :
    (C.killedTransition ^ n) x A =
      C.pathMeasure x {ω | ω n ∈ Option.some '' A} := by
  have hsome : MeasurableSet ((Option.some : M → Option M) '' A) :=
    measurableEmbedding_some_state.measurableSet_image' hA
  rw [← C.pathMeasure_marginal_comap x n,
    measurableEmbedding_some_state.comap_apply,
    Measure.map_apply (f := fun ω : Path M => ω n) (measurable_pi_apply n) hsome]
  rfl

/-- At every fixed step, the canonical path stays in the cemetery after
reaching it, almost surely. This follows from the joint past/next law. -/
theorem ae_absorbing_step (x : M) (n : ℕ) :
    ∀ᵐ ω ∂C.pathMeasure x, ω n = none → ω (n + 1) = none := by
  let p : ((i : Finset.Iic n) → Option M) × Option M → Prop :=
    fun z => z.1 ⟨n, by simp⟩ = none → z.2 = none
  have hp : MeasurableSet {z | p z} := by
    apply MeasurableSet.imp
    · exact measurableSet_cemetery.preimage ((measurable_pi_apply _).comp measurable_fst)
    · exact measurableSet_cemetery.preimage measurable_snd
  have hprod : ∀ᵐ z ∂((C.pathMeasure x).map (Preorder.frestrictLe n) ⊗ₘ
      C.historyKernel n), p z := by
    apply Measure.ae_compProd_of_ae_ae hp
    apply Eventually.of_forall
    intro ω
    change ∀ᵐ y ∂C.historyKernel n ω, ω ⟨n, by simp⟩ = none → y = none
    by_cases hlast : ω ⟨n, by simp⟩ = none
    · rw [C.historyKernel_of_last_none n ω hlast]
      filter_upwards [(ae_dirac_iff measurableSet_cemetery).2 (by rfl)] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall (fun _ h => False.elim (hlast h))
  rw [C.pathMeasure_past_next] at hprod
  exact ae_of_ae_map
    ((Preorder.measurable_frestrictLe n).prod (measurable_pi_apply (n + 1))).aemeasurable
    hprod

/-- A single full-measure set of canonical paths has the absorbing property
simultaneously for every pair of observation times. -/
theorem ae_absorbing (x : M) :
    ∀ᵐ ω ∂C.pathMeasure x, ∀ m n : ℕ, m ≤ n → ω m = none → ω n = none := by
  have hsteps : ∀ᵐ ω ∂C.pathMeasure x, ∀ n : ℕ,
      ω n = none → ω (n + 1) = none :=
    ae_all_iff.2 (fun n => C.ae_absorbing_step x n)
  filter_upwards [hsteps] with ω hω
  intro m n hmn hm
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ n _ ih => exact hω n ih

/-- For canonical absorbing paths, survival through n is almost surely
equivalent to being alive at time n. -/
theorem ae_mem_survival_iff (x : M) (n : ℕ) :
    ∀ᵐ ω ∂C.pathMeasure x, ω ∈ survival n ↔ ω n ≠ none := by
  filter_upwards [C.ae_absorbing x] with ω hω
  constructor
  · intro hs
    exact hs n le_rfl
  · intro hn k hk hkilled
    exact hn (hω k n hk hkilled)

/-- Survival identity: total killed-kernel mass equals the survival probability under the canonical
path law. -/
theorem pathMeasure_survival (x : M) (n : ℕ) :
    C.pathMeasure x (survival n) = (C.killedTransition ^ n) x univ := by
  rw [C.killedTransition_pow_apply x n univ MeasurableSet.univ]
  apply measure_congr
  apply eventuallyEqSet_iff.2
  filter_upwards [C.ae_mem_survival_iff x n] with ω hω
  simpa only [Set.mem_ofPred_eq, Set.image_univ, live_states_eq_cemetery_compl,
    Set.mem_compl_iff, Set.mem_singleton_iff] using hω

/-- Every power of the killed transition kernel is again a subprobability
law, as follows from its path-law interpretation. -/
theorem killedTransition_pow_mass_le_one (x : M) (n : ℕ) :
    (C.killedTransition ^ n) x univ ≤ 1 := by
  rw [← C.pathMeasure_survival x n]
  exact prob_le_one

/-- All survival denominators are positive when the initial state lies
outside the eventually escaping set of the killed kernel. -/
theorem pathMeasure_survival_pos (x : M)
    (hx : x ∈ StandingHypothesis.survivingSet C.killedTransition) (n : ℕ) :
    0 < C.pathMeasure x (survival n) := by
  cases n with
  | zero =>
      rw [C.pathMeasure_survival_zero]
      exact zero_lt_one
  | succ n =>
      rw [C.pathMeasure_survival]
      exact (StandingHypothesis.mem_survivingSet_iff C.killedTransition x).1 hx
        (n + 1) (by omega)

/-- Survival conditioning is a probability law for every horizon and every
nonescaping initial state, with positivity proved from the killed kernel. -/
theorem conditionedMeasure_isProbability_of_surviving (x : M)
    (hx : x ∈ StandingHypothesis.survivingSet C.killedTransition) (n : ℕ) :
    IsProbabilityMeasure (C.conditionedMeasure x n) :=
  C.conditionedMeasure_isProbability x n (C.pathMeasure_survival_pos x hx n).ne'

/-- The endpoint law under survival conditioning is the normalized killed marginal. The identity
also holds when the survival event has mass zero, both sides being zero. -/
theorem conditionedMeasure_endpoint (x : M) (n : ℕ) (A : Set M)
    (hA : MeasurableSet A) :
    C.conditionedMeasure x n {ω | ω n ∈ Option.some '' A} =
      ((C.killedTransition ^ n) x univ)⁻¹ * (C.killedTransition ^ n) x A := by
  have hinter : survival n ∩ {ω : Path M | ω n ∈ Option.some '' A} =ᵐ[C.pathMeasure x]
      {ω : Path M | ω n ∈ Option.some '' A} := by
    apply eventuallyEqSet_iff.2
    filter_upwards [C.ae_mem_survival_iff x n] with ω hω
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨hω.2 ?_, h⟩
      obtain ⟨y, _, hy⟩ := h
      intro hnone
      have hbad : (some y : Option M) = none := hy.trans hnone
      cases hbad
  rw [C.conditionedMeasure_apply, C.pathMeasure_survival, measure_congr hinter,
    ← C.killedTransition_pow_apply x n A hA]

/-- Measure-valued form of the conditioned endpoint law on live states. -/
theorem conditionedMeasure_marginal_comap (x : M) (n : ℕ) :
    ((C.conditionedMeasure x n).map (fun ω => ω n)).comap Option.some =
      ((C.killedTransition ^ n) x univ)⁻¹ • (C.killedTransition ^ n) x := by
  ext A hA
  have hsome : MeasurableSet ((Option.some : M → Option M) '' A) :=
    measurableEmbedding_some_state.measurableSet_image' hA
  rw [measurableEmbedding_some_state.comap_apply,
    Measure.map_apply (f := fun ω : Path M => ω n) (measurable_pi_apply n) hsome,
    Measure.smul_apply, smul_eq_mul]
  exact C.conditionedMeasure_endpoint x n A hA

end CanonicalChain

end

end ConditionedStableLaws
