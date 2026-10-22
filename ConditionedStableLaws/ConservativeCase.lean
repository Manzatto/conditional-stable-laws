import ConditionedStableLaws.SpectralSurvival

/-!
# The case without killing

Conservative killed kernels have unit survival probability at every time.
The canonical conditional path laws are then exactly the original laws.
For normalized spectral data, the eigenvalue and eigenfunction are both one,
so the quasi-ergodic weight does not change the eigenmeasure.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws
noncomputable section

variable {M : Type*} [MeasurableSpace M]

theorem kernel_pow_univ_of_conservative (K : Kernel M M)
    (hK : ∀ x, K x univ = 1) (n : ℕ) (x : M) : (K ^ n) x univ = 1 := by
  have : IsMarkovKernel K := ⟨fun x => ⟨hK x⟩⟩
  have hp : ∀ n : ℕ, IsMarkovKernel (K ^ n) := by
    intro n
    induction n with
    | zero => change IsMarkovKernel (Kernel.id : Kernel M M); infer_instance
    | succ n ih =>
        have := ih
        rw [pow_succ]
        change IsMarkovKernel ((K ^ n) ∘ₖ K)
        infer_instance
  have := hp n
  exact measure_univ

theorem eigenvalue_eq_one_of_conservative (K : Kernel M M)
    (hK : ∀ x, K x univ = 1) (μ : Measure M) [IsProbabilityMeasure μ]
    {rate : ℝ≥0∞} (heigen : K ∘ₘ μ = rate • μ) : rate = 1 := by
  have : IsMarkovKernel K := ⟨fun x => ⟨hK x⟩⟩
  rw [eigenvalue_eq_survival_mass K μ heigen]
  exact measure_univ

namespace CanonicalChain
variable (C : CanonicalChain M)

theorem survival_probability_eq_one_of_conservative
    (hK : ∀ x, C.killedTransition x univ = 1) (x : M) (n : ℕ) :
    C.pathMeasure x (survival n) = 1 := by
  rw [C.pathMeasure_survival]
  exact kernel_pow_univ_of_conservative C.killedTransition hK n x

/-- Survival conditioning changes no events when there is no killing. -/
theorem conditionedMeasure_eq_of_conservative
    (hK : ∀ x, C.killedTransition x univ = 1) (x : M) (n : ℕ) :
    C.conditionedMeasure x n = C.pathMeasure x := by
  have hs := C.survival_probability_eq_one_of_conservative hK x n
  have hae : ∀ᵐ ω ∂C.pathMeasure x, ω ∈ survival n := by
    rw [ae_iff]
    change C.pathMeasure x (survival n)ᶜ = 0
    rw [measure_compl (measurableSet_survival n) (measure_ne_top _ _),
      measure_univ, hs, tsub_self]
  change (C.pathMeasure x (survival n))⁻¹ • (C.pathMeasure x).restrict (survival n) = _
  rw [hs, inv_one, one_smul, Measure.restrict_eq_self_of_ae_mem hae]

/-- With no killing the canonical path never reaches the cemetery, almost surely. -/
theorem ae_always_live_of_conservative
    (hK : ∀ x, C.killedTransition x univ = 1) (x : M) :
    ∀ᵐ ω ∂C.pathMeasure x, ∀ n : ℕ, ω n ≠ none := by
  have hsurv : ∀ n : ℕ, ∀ᵐ ω ∂C.pathMeasure x, ω ∈ survival n := by
    intro n
    rw [← C.conditionedMeasure_eq_of_conservative hK x n]
    exact C.ae_survival_conditionedMeasure x n
  filter_upwards [ae_all_iff.mpr hsurv] with ω hω
  intro n
  exact hω n n le_rfl

end CanonicalChain

namespace StandingHypothesis
variable [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M} {h : HypothesisH ρ K}
  {d : DoobTransform.EigenData K.kernel}

/-- The normalized continuous survival eigenfunction is identically one in the conservative case;
this uses the survival limit from the gap. -/
theorem SurvivalGapData.weight_eq_one_of_conservative (s : SurvivalGapData h d)
    (hK : ∀ x, K.kernel x univ = 1) (μ : Measure M) [IsProbabilityMeasure μ]
    (heigen : K.kernel ∘ₘ μ = d.rate • μ) (x : M) : d.weight x = 1 := by
  have hr := eigenvalue_eq_one_of_conservative K.kernel hK μ heigen
  have ht := s.normalized_survival_tendstoUniformly.tendsto_at x
  simp only [hr, inv_one, one_pow, one_mul,
    kernel_pow_univ_of_conservative K.kernel hK, ENNReal.toReal_one] at ht
  have hx : (d.weight x).toReal = 1 := tendsto_nhds_unique ht tendsto_const_nhds
  calc
    d.weight x = ENNReal.ofReal (d.weight x).toReal := (ENNReal.ofReal_toReal (d.weight_ne_top x)).symm
    _ = 1 := by rw [hx]; simp

theorem SurvivalGapData.weightedMeasure_eq_of_conservative (s : SurvivalGapData h d)
    (hK : ∀ x, K.kernel x univ = 1) (μ : Measure M) [IsProbabilityMeasure μ]
    (heigen : K.kernel ∘ₘ μ = d.rate • μ) : μ.withDensity d.weight = μ := by
  have hw : d.weight = fun _ => 1 := funext (s.weight_eq_one_of_conservative hK μ heigen)
  rw [hw, withDensity_const, one_smul]

end StandingHypothesis
end
end ConditionedStableLaws
