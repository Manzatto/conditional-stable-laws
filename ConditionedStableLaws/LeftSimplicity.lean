import ConditionedStableLaws.RealSimplicity

/-!
# Uniqueness of positive left eigenmeasures

Subtracting the rank-one eigenprojection removes the simple eigenvalue.
The Fredholm alternative then shows that every left eigenfunctional is a
multiple of the given one. Applying this to integration gives uniqueness
of the quasi-stationary probability measure.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws.LeftSimplicity
noncomputable section

/-- A simple eigenvalue with a normalized left eigenfunctional has a
one-dimensional left eigenspace. Compactness supplies the needed surjectivity
through the Fredholm alternative. -/
theorem left_eigenfunctional_eq_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : IsCompactOperator T) {r : ℝ} (hr : r ≠ 0)
    (η : E) (ℓ : E →L[ℝ] ℝ) (hℓη : ℓ η = 1)
    (hℓT : ∀ f, ℓ (T f) = r * ℓ f)
    (hsimple : ∀ f, T f = r • f → ∃ c : ℝ, f = c • η)
    (φ : E →L[ℝ] ℝ) (hφT : ∀ f, φ (T f) = r * φ f) :
    ∀ f, φ f = φ η * ℓ f := by
  let R : E →L[ℝ] E := T - ℓ.smulRight (r • η)
  have hcompact : IsCompactOperator R := by
    apply hT.sub
    exact (isCompactOperator_of_locallyCompactSpace_dom ℓ).continuous_comp
      (continuous_id.smul continuous_const)
  have hno : ¬ Module.End.HasEigenvalue (R : Module.End ℝ E) r := by
    intro he
    obtain ⟨f, hf⟩ := he.exists_hasEigenvector
    have hRf : R f = r • f := hf.apply_eq_smul
    have hlf : ℓ f = 0 := by
      have hi := congrArg ℓ hRf
      change ℓ (T f - ℓ f • (r • η)) = ℓ (r • f) at hi
      simp only [map_sub, map_smul, hℓT, hℓη, smul_eq_mul, mul_one] at hi
      have hz : r * ℓ f = 0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_left hr
    have hTf : T f = r • f := by
      change T f - ℓ f • (r • η) = r • f at hRf
      simpa only [hlf, zero_smul, sub_zero] using hRf
    obtain ⟨c, hc⟩ := hsimple f hTf
    have hc0 : c = 0 := by
      rw [hc, map_smul, hℓη, smul_eq_mul, mul_one] at hlf
      exact hlf
    exact hf.2 (by rw [hc, hc0, zero_smul])
  have hres := (hcompact.hasEigenvalue_or_mem_resolventSet hr).resolve_left hno
  have hsurj : Function.Surjective (r • (1 : E →L[ℝ] E) - R) := by
    rw [spectrum.mem_resolventSet_iff] at hres
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp ?_).2
    simpa only [Algebra.algebraMap_eq_smul_one] using hres
  let ψ : E →L[ℝ] ℝ := φ - φ η • ℓ
  have hψη : ψ η = 0 := by simp [ψ, hℓη]
  have hψT (f : E) : ψ (T f) = r * ψ f := by
    simp only [ψ, sub_apply, smul_apply, smul_eq_mul, hφT, hℓT]
    ring
  have hψR (f : E) : ψ (R f) = r * ψ f := by
    change ψ (T f - ℓ f • (r • η)) = _
    simp only [map_sub, map_smul, hψη, smul_eq_mul, mul_zero, sub_zero, hψT]
  intro f
  obtain ⟨g, hg⟩ := hsurj f
  have hz : ψ f = 0 := by
    rw [← hg]
    change ψ (r • g - R g) = 0
    simp only [map_sub, map_smul, smul_eq_mul, hψR, sub_self]
  exact sub_eq_zero.mp hz

variable {M : Type*} [MeasurableSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]

/-- Integration against a finite measure as a continuous linear functional
on bounded continuous real functions. -/
def integralFunctional (μ : Measure M) [IsFiniteMeasure μ] : (M →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous {
    toFun f := ∫ x, f x ∂μ
    map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
    map_smul' c f := integral_smul c f
  } (μ.real univ) (fun f => f.norm_integral_le_mul_norm μ)

theorem integralFunctional_apply (μ : Measure M) [IsFiniteMeasure μ] (f : M →ᵇ ℝ) :
    integralFunctional μ f = ∫ x, f x ∂μ := rfl

end
end ConditionedStableLaws.LeftSimplicity

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Two same-rate probability eigenmeasures coincide, using the right eigenfunction and real
simplicity from H2. -/
theorem HypothesisH.left_probability_eigenmeasure_unique_of_eigenfunction
    (h : HypothesisH ρ K) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r)
    (hμ : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
    (hν : K.kernel ∘ₘ ν = ENNReal.ofReal r • ν)
    (η : M →ᵇ ℝ) (hηne : η ≠ 0) (hηpos : ∀ x, 0 ≤ η x)
    (hηeq : h.continuousKernelOperator η = r • η) : μ = ν := by
  let Iμ := LeftSimplicity.integralFunctional μ
  let Iν := LeftSimplicity.integralFunctional ν
  let a : ℝ := Iμ η
  have ha : 0 < a := h.real_eigenfunction_integral_pos μ hr hμ η hηne hηpos hηeq
  let ℓ : (M →ᵇ ℝ) →L[ℝ] ℝ := a⁻¹ • Iμ
  have hℓη : ℓ η = 1 := inv_mul_cancel₀ ha.ne'
  have hℓT (f : M →ᵇ ℝ) : ℓ (h.continuousKernelOperator f) = r * ℓ f := by
    change a⁻¹ * (∫ x, h.continuousKernelOperator f x ∂μ) = r * (a⁻¹ * ∫ x, f x ∂μ)
    rw [h.integral_continuousKernelOperator_of_eigenmeasure μ hr.le hμ]
    ring
  have hνT (f : M →ᵇ ℝ) : Iν (h.continuousKernelOperator f) = r * Iν f :=
    h.integral_continuousKernelOperator_of_eigenmeasure ν hr.le hν f
  have hfun := LeftSimplicity.left_eigenfunctional_eq_smul
    h.continuousKernelOperator h.continuousKernelOperator_isCompact hr.ne' η ℓ hℓη hℓT
    (fun f hf => h.real_eigenfunction_eq_smul μ hr hμ η hηne hηpos hηeq f hf) Iν hνT
  have hc : Iν η * a⁻¹ = 1 := by
    have hh := hfun 1
    change (∫ x, (1 : M →ᵇ ℝ) x ∂ν) = Iν η * (a⁻¹ * (∫ x, (1 : M →ᵇ ℝ) x ∂μ)) at hh
    simpa using hh.symm
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hh := hfun f
  change (∫ x, f x ∂ν) = Iν η * (a⁻¹ * ∫ x, f x ∂μ) at hh
  rw [← mul_assoc, hc, one_mul] at hh
  exact hh.symm

/-- The standing assumptions imply existence and uniqueness of the quasi-stationary probability
measure. Different candidate rates are first identified by the positive eigenfunction pairing. -/
theorem HypothesisH.exists_unique_quasiStationary (h : HypothesisH ρ K) :
    ∃! μ : ProbabilityMeasure M, IsQuasiStationary K.kernel (μ : Measure M) := by
  obtain ⟨r, hr, hrone, η, hη, hnorm, heq, μ, hμ⟩ := h.exists_positive_eigenpair_and_eigenmeasure
  have hne : η ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; norm_num)
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  refine ⟨μ, ⟨inferInstance, ENNReal.ofReal r, ENNReal.ofReal_pos.mpr hr, ?_, hμ⟩, ?_⟩
  · exact (ENNReal.ofReal_le_ofReal hrone).trans_eq (by simp)
  · intro ν hν
    obtain ⟨s, hs, hsone, hνleft⟩ := hν.2
    have hst : s ≠ ∞ := ne_of_lt (hsone.trans_lt ENNReal.one_lt_top)
    have hrs := h.quasiStationary_rates_unique μ ν hr0 ENNReal.ofReal_ne_top hs.ne' hst hμ hνleft
    have hνr : K.kernel ∘ₘ (ν : Measure M) = ENNReal.ofReal r • (ν : Measure M) := by rwa [hrs]
    apply Subtype.ext
    exact (h.left_probability_eigenmeasure_unique_of_eigenfunction μ ν hr hμ hνr η hne hη heq).symm

/-- Uniqueness for the measure-valued definition of quasi-stationarity. -/
theorem HypothesisH.quasiStationary_unique (h : HypothesisH ρ K)
    (μ ν : Measure M) (hμ : IsQuasiStationary K.kernel μ) (hν : IsQuasiStationary K.kernel ν) : μ = ν := by
  let μp : ProbabilityMeasure M := ⟨μ, hμ.1⟩
  let νp : ProbabilityMeasure M := ⟨ν, hν.1⟩
  have hp : μp = νp := h.exists_unique_quasiStationary.unique hμ hν
  exact congrArg (fun p : ProbabilityMeasure M => (p : Measure M)) hp

end
end ConditionedStableLaws.StandingHypothesis
