import ConditionedStableLaws.ConditionedCesaro

/-!
# Existence and uniqueness of the quasi-ergodic probability

The definition quantifies over every bounded measurable real observable and requires the
survival-conditioned Birkhoff-average limit for almost every initial state under the candidate law.
Under H, existence holds with convergence at every nonescaping initial state. Uniqueness also rules
out candidates charging the finite-extinction set.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws.CanonicalChain
noncomputable section
open StandingHypothesis
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- The quasi-ergodic property, using the canonical path law and its survival conditioning. -/
def IsQuasiErgodic (ν : Measure M) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ f : M → ℝ, Measurable f →
    (∃ B : ℝ, ∀ y, |f y| ≤ B) → ∀ᵐ x ∂ν,
      Tendsto (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ * pathBirkhoffSum f n ω
        ∂C.conditionedMeasure x n) atTop (𝓝 (∫ y, f y ∂ν))

/-- No quasi-ergodic probability can charge states whose survival becomes
impossible at a finite horizon. This follows by testing the constant one. -/
theorem IsQuasiErgodic.ae_surviving {ν : Measure M} (hq : C.IsQuasiErgodic ν) :
    ∀ᵐ x ∂ν, x ∈ survivingSet C.killedTransition := by
  have : IsProbabilityMeasure ν := hq.1
  have hlim := hq.2 (fun _ => 1) measurable_const ⟨1, by simp⟩
  filter_upwards [hlim] with x hx
  by_contra hxs
  have hz : x ∈ escapingSet C.killedTransition := by
    simpa only [survivingSet, mem_compl_iff, not_not] using hxs
  obtain ⟨k, _hk, hkzero⟩ := hz
  have hpath : C.pathMeasure x (survival k) = 0 := by
    rw [C.pathMeasure_survival]
    exact hkzero
  have hevent : ∀ᶠ n : ℕ in atTop, C.conditionedMeasure x n = 0 :=
    eventually_atTop.2 ⟨k, fun n hn => by
      exact ProbabilityTheory.cond_eq_zero_of_meas_eq_zero
        (le_zero_iff.mp ((C.survival_probability_antitone x hn).trans_eq hpath))⟩
  have hzero : Tendsto (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ * pathBirkhoffSum (fun _ => 1) n ω
      ∂C.conditionedMeasure x n) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    simp [hn]
  have hbad := tendsto_nhds_unique hzero hx
  simp at hbad

variable [MetricSpace M] [CompactSpace M] [BorelSpace M] {ρ : Measure M}

/-- H produces an absolutely continuous quasi-ergodic probability, with
convergence at every nonescaping starting state and every bounded observable. -/
theorem exists_pointwise_quasiErgodic_probability (h : HypothesisH ρ C.toKilledKernel) :
    ∃ ν : ProbabilityMeasure M,
      (ν : Measure M) ≪ ρ ∧ C.IsQuasiErgodic ν ∧
      ∀ x ∈ survivingSet C.killedTransition, ∀ f : M → ℝ, Measurable f →
        (∃ B : ℝ, ∀ y, |f y| ≤ B) →
        Tendsto (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ * pathBirkhoffSum f n ω
          ∂C.conditionedMeasure x n) atTop (𝓝 (∫ y, f y ∂(ν : Measure M))) := by
  obtain ⟨d, _hdr, _hc, hlive, μ, hleft, hnorm, hlim⟩ :=
    C.exists_pointwise_quasiErgodic_eigenData h
  let ν := (μ : Measure M).withDensity d.weight
  have hprob : IsProbabilityMeasure ν := ⟨by
    change (μ : Measure M).withDensity d.weight univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa using hnorm⟩
  have ha : ∀ᵐ x ∂ν, x ∈ survivingSet C.killedTransition := by
    rw [ae_withDensity_iff d.measurable_weight]
    exact ae_of_all _ (fun x hx => hlive ▸ hx)
  refine ⟨⟨ν, hprob⟩, ?_, ⟨hprob, ?_⟩, hlim⟩
  · exact (withDensity_absolutelyContinuous _ _).trans
      (h.eigenmeasure_absolutelyContinuous μ d.rate_ne_zero hleft)
  · intro f hfm hfb
    filter_upwards [ha] with x hx
    exact hlim x hx f hfm hfb

/-- Under H the quasi-ergodic probability, in the almost-everywhere sense, is unique; candidates
need not have full support. -/
theorem exists_unique_quasiErgodic (h : HypothesisH ρ C.toKilledKernel) :
    ∃! ν : Measure M, C.IsQuasiErgodic ν := by
  obtain ⟨ν, _hac, hq, hlim⟩ := C.exists_pointwise_quasiErgodic_probability h
  refine ⟨ν, hq, ?_⟩
  intro ν' hq'
  have : IsProbabilityMeasure ν' := hq'.1
  have ha := hq'.ae_surviving C
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hfb : ∃ B : ℝ, ∀ y, |f y| ≤ B := ⟨‖f‖, fun y => by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y⟩
  have hf := hq'.2 f f.continuous.measurable hfb
  obtain ⟨x, hxs, hxf⟩ := (ha.and hf).exists
  exact tendsto_nhds_unique hxf (hlim x hxs f f.continuous.measurable hfb)

end
end ConditionedStableLaws.CanonicalChain
