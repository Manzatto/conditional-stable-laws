import ConditionedStableLaws.ContinuousMultiplier

/-!
# Continuous multipliers in the positive stable range

For `0 < α < 1`, the multiplier error is negligible without centering. The approximation is proved
under the changing conditioned laws, starting from the singular-observable law.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ConditionedStableLaws.ContinuousMultiplier

noncomputable section

open CanonicalChain NormalizationBridge StandingHypothesis AnnularPoissonClouds

section Pathwise
variable {M : Type*}

theorem path_sub (f g : M → ℝ) (n : ℕ) (ω : Path M) :
    pathBirkhoffSum (fun x => f x - g x) n ω =
      pathBirkhoffSum f n ω - pathBirkhoffSum g n ω := by
  unfold pathBirkhoffSum birkhoffSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases hω : ω j <;> simp [zeroExtension, hω]

theorem path_nonneg {f : M → ℝ} (hf : ∀ x, 0 ≤ f x) (n : ℕ) (ω : Path M) :
    0 ≤ pathBirkhoffSum f n ω := by
  unfold pathBirkhoffSum birkhoffSum
  apply Finset.sum_nonneg
  intro j _
  cases ω j <;> simp [zeroExtension, hf]

variable [MetricSpace M]

theorem path_residual_eq (x₀ : M) (β : ℝ) (g : M → ℝ) (n : ℕ) (ω : Path M) :
    pathBirkhoffSum (residual x₀ β g) n ω =
      pathBirkhoffSum (observable x₀ β g) n ω -
        g x₀ * pathBirkhoffSum (singularObservable x₀ β) n ω := by
  have hfun : residual x₀ β g = fun x => observable x₀ β g x - g x₀ * singularObservable x₀ β x := by
    funext x
    exact (observable_sub_center x₀ β g x).symm
  rw [hfun, path_sub, SmallJumpMoment.pathBirkhoffSum_const_mul]

end Pathwise

section Distribution

variable {M Ω' : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Ω']
  (P : ℕ → Measure (Path M)) [∀ n, IsProbabilityMeasure (P n)]
  (Q : Measure Ω') [IsProbabilityMeasure Q]

/-- Multiplication by a continuous function preserves an uncentered limit
whenever `n/B_n → 0`. The multiplier is evaluated at the singularity. -/
theorem uncentered_multiplier {x₀ : M} {β : ℝ} (hβ : 0 < β) {g : M → ℝ}
    (hg : Continuous g) {B : ℕ → ℝ} (hB : ∀ n, 0 < B n)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) / B n) atTop (𝓝 0)) {Z : Ω' → ℝ}
    (hlim : TendstoInDistribution
      (fun n ω => (B n)⁻¹ * pathBirkhoffSum (singularObservable x₀ β) n ω) atTop Z P Q) :
    TendstoInDistribution
      (fun n ω => (B n)⁻¹ * pathBirkhoffSum (observable x₀ β g) n ω) atTop
      (fun ω => g x₀ * Z ω) P Q := by
  let X : ℕ → Path M → ℝ := fun n ω => (B n)⁻¹ * pathBirkhoffSum (singularObservable x₀ β) n ω
  let Y : ℕ → Path M → ℝ := fun n ω => (B n)⁻¹ * pathBirkhoffSum (observable x₀ β g) n ω
  have hXm (n : ℕ) : Measurable (X n) :=
    (measurable_pathBirkhoffSum (measurable_singularObservable x₀ β) n).const_mul _
  have hYm (n : ℕ) : Measurable (Y n) :=
    (measurable_pathBirkhoffSum (measurable_observable x₀ β hg) n).const_mul _
  have hnear := probability_negligible_of_relative_bound P Q hXm hlim ha
    (R := fun n ω => Y n ω - g x₀ * X n ω) (by
      intro ε hε
      obtain ⟨K, hK, hb⟩ := residual_bound hβ hg hε
      refine ⟨K, hK, fun n ω => ?_⟩
      have hpath := path_residual_bound hK hb n ω
      have hX0 : 0 ≤ X n ω := mul_nonneg (inv_nonneg.mpr (hB n).le)
        (path_nonneg (fun z => (singularObservable_pos x₀ β z).le) n ω)
      have hid : Y n ω - g x₀ * X n ω = (B n)⁻¹ * pathBirkhoffSum (residual x₀ β g) n ω := by
        rw [path_residual_eq]
        dsimp [Y, X]
        ring
      rw [hid, abs_mul, abs_of_pos (inv_pos.mpr (hB n)), abs_of_nonneg hX0]
      calc
        _ ≤ (B n)⁻¹ * (ε * pathBirkhoffSum (singularObservable x₀ β) n ω + n * K) :=
          mul_le_mul_of_nonneg_left hpath (inv_nonneg.mpr (hB n).le)
        _ = _ := by dsimp [X]; ring)
  have hscaled := hlim.continuous_comp (g := fun z : ℝ => g x₀ * z)
    (continuous_const.mul continuous_id)
  exact tendstoInDistribution_of_varying_probability_approximation P Q Y
    (fun n ω => g x₀ * X n ω) (fun ω => g x₀ * Z ω) hYm
    (fun n => (hXm n).const_mul _) hscaled hnear

end Distribution

/-- `n/B_n → 0` in the uncentered stable range. -/
theorem nat_div_positivePowerScale_tendsto_zero {Cc α : ℝ} (hC : 0 < Cc)
    (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) / positivePowerScale Cc α n) atTop (𝓝 0) := by
  have he : 0 < 1 / α - 1 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hα).mpr
    simpa using hα1
  have hh := ((tendsto_rpow_neg_atTop he).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (Cc ^ (1 / α))⁻¹
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [positivePowerScale_eventually_eq Cc α, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  simp only [Function.comp_apply]
  rw [show -(1 / α - 1) = 1 - 1 / α by ring, Real.rpow_sub hn', Real.rpow_one,
    hn, powerScale, Real.mul_rpow hC.le hn'.le]
  ring

section Chain

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Continuous multipliers for `0 < α < 1`, before rescaling by `|g(x₀)|`. The hypotheses are those
of the stable law plus continuity of the multiplier. -/
theorem stable_law_small_multiplier (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (m : M → ℝ) (hm : Integrable m ρ) (hm0 : ∀ y, 0 ≤ m y)
    (hμ : μ = ρ.withDensity (fun y => ENNReal.ofReal (m y)))
    (x : d.State) {x₀ : M} {dimension volumeConstant β : ℝ}
    (hadm : IsAdmissibleAt ρ m x₀ dimension volumeConstant)
    (hx₀ : d.weight x₀ ≠ 0) (hβ : 0 < β) (hα1 : dimension / β < 1)
    {g : M → ℝ} (hg : Continuous g) :
    TendstoInDistribution
      (fun n ω => (positivePowerScale (volumeConstant * (d.weight x₀).toReal * m x₀)
        (dimension / β) n)⁻¹ * pathBirkhoffSum (observable x₀ β g) n ω) atTop
      (fun ω => g x₀ * positiveIntegral ω)
      (fun n => (C.liveConditionedProbabilityMeasure d x n : Measure (Path M)))
      (powerLaw (dimension / β) (div_pos hadm.1.1 hβ)) := by
  have hC : 0 < volumeConstant * (d.weight x₀).toReal * m x₀ :=
    mul_pos (mul_pos hadm.1.2.1 (ENNReal.toReal_pos hx₀ (d.weight_ne_top _))) hadm.2.1
  exact uncentered_multiplier _ _ hβ hg (positivePowerScale_pos hC)
    (nat_div_positivePowerScale_tendsto_zero hC (div_pos hadm.1.1 hβ) hα1)
    (StableLawSmall.stable_law_small C h d s hlive μ hleft hnorm m hm hm0 hμ x hadm hx₀ hβ hα1)

end Chain
end
end ConditionedStableLaws.ContinuousMultiplier
