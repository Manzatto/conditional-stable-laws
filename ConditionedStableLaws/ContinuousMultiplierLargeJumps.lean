import ConditionedStableLaws.StableLawSmall

/-!
A large-jump probability bound from the Poisson count limit.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
noncomputable section

namespace ConditionedStableLaws.ContinuousMultiplier
open StandingHypothesis CanonicalChain NormalizationBridge AnnularPoissonClouds StableLawSmall

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- The probability of a jump above `R Bₙ` is eventually at most `2 R⁻ᵅ`.
There is no restriction `α < 1`: this follows from the count theorem. -/
theorem large_jump_eventually (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (R : ℝ≥0) (hR : 0 < R) :
    ∀ᶠ n in atTop, (C.conditionedMeasure x.val n).real
      {ω | ∃ j : ℕ, j < n ∧ (R : ℝ) * positivePowerScale
        (volumeConstant * (d.weight x₀).toReal * m x₀) (dimension / β) n <
          zeroExtension (singularObservable x₀ β) (ω j)} < 2 * (R : ℝ) ^ (-(dimension / β)) := by
  set α := dimension / β
  have hα : 0 < α := div_pos hadm.1.1 hβ
  set Cc := volumeConstant * (d.weight x₀).toReal * m x₀
  have hC : 0 < Cc := mul_pos (mul_pos hadm.1.2.1
    (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  set f := singularObservable x₀ β
  have hfm : Measurable f := measurable_singularObservable x₀ β
  have hfpos : ∀ y, 0 < f y := singularObservable_pos x₀ β
  set B := positivePowerScale Cc α
  have hB : ∀ n, 0 < B n := positivePowerScale_pos hC
  set P : ℕ → Measure (Path M) := fun n => C.liveConditionedProbabilityMeasure d x n
  set Q := powerLaw α hα
  set N : ℕ → RandomPointMeasure (Path M) := fun n => pathEmpirical f hfm hfpos n (B n) (hB n)
  set A : Set ExtremeState := Ioc (TruncatedPointIntegrals.endpoint R hR) ⊤
  have hlt : TruncatedPointIntegrals.endpoint R hR < (⊤ : ExtremeState) := by
    refine lt_of_le_of_ne le_top fun heq => ?_
    exact ENNReal.coe_ne_top (congrArg Subtype.val heq)
  have hc1 := C.poisson_interval_counts_of_admissibility h d hc μ hleft hnorm
    m hm hm0 hμ x hadm hx₀ hβ 1 (fun _ => TruncatedPointIntegrals.endpoint R hR)
    (fun _ => ⊤) (fun _ => hlt) (fun i j hij => absurd (Subsingleton.elim i j) hij)
  have hlim := tendsto_prob_of_tendstoInDistribution_nat hc1 {v | 1 ≤ v 0}
  have hfin : powerIntensity α A ≠ ∞ := by
    refine ne_top_of_le_ne_top (powerIntensity_tail_lt_top hα R hR).ne
      (measure_mono fun y hy => ?_)
    exact le_of_lt hy.1
  have hQ : Q.real {ω | 1 ≤ (randomMeasure.toFun ω).countOn A} ≤ (R : ℝ) ^ (-α) := by
    have hb := prob_count_pos_le (powerIntensity_tail_lt_top hα) measurableSet_Ioc hfin
    rw [powerIntensity_real_Ioc_top hα _ ENNReal.coe_ne_top] at hb
    exact hb
  have hpos : 0 < (R : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by exact_mod_cast hR) _
  have hbound : ∀ᶠ n in atTop, (P n).real {ω | 1 ≤ ((N n).toFun ω).countOn A} <
      2 * (R : ℝ) ^ (-α) :=
    hlim.eventually (gt_mem_nhds (show Q.real _ < 2 * (R : ℝ) ^ (-α) by
      change Q.real {ω | 1 ≤ (randomMeasure.toFun ω).countOn A} < _
      linarith))
  filter_upwards [hbound] with n hn
  apply lt_of_le_of_lt (measureReal_mono ?_) hn
  rintro ω ⟨j, hj, hlarge⟩
  set y : Fin n → ℝ := fun i => positiveExtension f (ω i) / B n
  have hy (i : Fin n) : 0 < y i := div_pos (positiveExtension_pos hfpos _) (hB n)
  change 1 ≤ (LocallyFinitePointMeasure.empirical
    (fun i => ⟨ENNReal.ofReal (y i), ENNReal.ofReal_pos.mpr (hy i)⟩)).countOn A
  apply one_le_countOn_empirical _ measurableSet_Ioc (i := ⟨j, hj⟩)
  apply (mem_Ioc_top hR (hy ⟨j, hj⟩)).mpr
  apply (lt_div_iff₀ (hB n)).mpr
  cases he : ω j with
  | none =>
    simp only [he, zeroExtension_none] at hlarge
    exact (not_lt_of_ge (mul_nonneg R.coe_nonneg (hB n).le) hlarge).elim
  | some z => simpa only [he, zeroExtension_some, positiveExtension] using hlarge

end ConditionedStableLaws.ContinuousMultiplier
