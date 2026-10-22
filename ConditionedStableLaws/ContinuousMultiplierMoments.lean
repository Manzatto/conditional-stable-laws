import ConditionedStableLaws.ContinuousMultiplierSmall
import ConditionedStableLaws.CompensationAsymptotics

/-!
# Vanishing centered arrays for the continuous-multiplier extension

Quantitative consequences of the conditional second-moment estimate, for signed observables.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ConditionedStableLaws.ContinuousMultiplier

noncomputable section
open CanonicalChain StandingHypothesis SecondMoment

section Chain
variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- A signed, bounded triangular array with vanishing sup norms and vanishing
scaled second moments gives negligible centered sums under the conditioned laws. -/
theorem centered_array_negligible (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : d.State) (q : ℕ → M → ℝ) (hq : ∀ n, Measurable (q n))
    (G : ℕ → ℝ) (hG0 : ∀ n, 0 ≤ G n) (hqG : ∀ n y, |q n y| ≤ G n)
    (hG : Tendsto G atTop (𝓝 0))
    (hμq : Tendsto (fun n : ℕ => (n : ℝ) * ∫ y, q n y ^ 2 ∂μ) atTop (𝓝 0))
    (hνq : Tendsto (fun n : ℕ => (n : ℝ) * ∫ y, q n y ^ 2 ∂μ.withDensity d.weight)
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (C.conditionedMeasure x.val n).real {ω | ε <
        |pathBirkhoffSum (q n) n ω - n * ∫ y, q n y ∂μ.withDensity d.weight|})
      atTop (𝓝 0) := by
  let ν := μ.withDensity d.weight
  have : IsProbabilityMeasure ν :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]⟩
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  have hP (n : ℕ) : IsProbabilityMeasure (C.conditionedMeasure x.val n) :=
    C.conditionedMeasure_isProbability_of_surviving x.val hx n
  obtain ⟨K, hK, hmain⟩ := conditional_sum_second_moment C h d s hlive μ hleft hnorm x
  let c : ℕ → ℝ := fun n => ∫ y, q n y ∂ν
  let qc : ℕ → M → ℝ := fun n y => q n y - c n
  let Y : ℕ → Path M → ℝ := fun n ω => pathBirkhoffSum (q n) n ω - n * c n
  have hcb (n : ℕ) : |c n| ≤ G n := abs_integral_le_of_prob (hqG n)
  have hqc (n : ℕ) : Measurable (qc n) := (hq n).sub_const _
  have hqcb (n : ℕ) (y : M) : |qc n y| ≤ 2 * G n := by
    exact (abs_sub _ _).trans (by linarith [hqG n y, hcb n])
  have hc2 (n : ℕ) : c n ^ 2 ≤ ∫ y, q n y ^ 2 ∂ν := by
    have hh := sq_integral_mul_le (ν := ν) (u := q n) (v := fun _ => 1)
      (hq n) measurable_const (hqG n) (V := 1) (fun _ => by simp)
    simpa [c] using hh
  have hqcmean (n : ℕ) : ∫ y, qc n y ∂ν = 0 := by
    rw [show qc n = fun y => q n y - c n from rfl,
      integral_sub (integrable_of_bdd (hq n) (hqG n)) (integrable_const _),
      integral_const, probReal_univ, one_smul]
    exact sub_self _
  have hmoment (n : ℕ) : ∫ y, qc n y ^ 2 ∂μ ≤
      2 * ∫ y, q n y ^ 2 ∂μ + 2 * ∫ y, q n y ^ 2 ∂ν := by
    calc
      _ ≤ ∫ y, (2 * q n y ^ 2 + 2 * c n ^ 2) ∂μ :=
        integral_mono (integrable_of_bdd ((hqc n).pow_const 2) (sq_bdd (hqcb n)))
          (((integrable_of_bdd ((hq n).pow_const 2) (sq_bdd (hqG n))).const_mul 2).add
            (integrable_const _)) (fun y => by dsimp [qc]; nlinarith [sq_nonneg (q n y + c n)])
      _ = 2 * ∫ y, q n y ^ 2 ∂μ + 2 * c n ^ 2 := by
        rw [integral_add ((integrable_of_bdd ((hq n).pow_const 2) (sq_bdd (hqG n))).const_mul 2)
          (integrable_const _), integral_const_mul, integral_const, probReal_univ, one_smul]
      _ ≤ _ := by linarith [hc2 n]
  have hYmoment (n : ℕ) : ∫ ω, Y n ω ^ 2 ∂C.conditionedMeasure x.val n ≤
      K * (2 * ((n : ℝ) * ∫ y, q n y ^ 2 ∂μ) +
        2 * ((n : ℝ) * ∫ y, q n y ^ 2 ∂ν) + 4 * G n ^ 2) := by
    have heq : ∫ ω, Y n ω ^ 2 ∂C.conditionedMeasure x.val n =
        ∫ ω, pathBirkhoffSum (qc n) n ω ^ 2 ∂C.conditionedMeasure x.val n := by
      apply integral_congr_ae
      filter_upwards [C.ae_survival_conditionedMeasure x.val n] with ω hω
      rw [show qc n = fun y => q n y - c n from rfl,
        SmallJumpMoment.pathBirkhoffSum_sub_const _ _ hω]
    rw [heq]
    apply (hmain (qc n) (hqc n) (2 * G n) (mul_nonneg (by norm_num) (hG0 n)) (hqcb n) (hqcmean n) n).trans
    apply mul_le_mul_of_nonneg_left _ hK
    have hh := mul_le_mul_of_nonneg_left (hmoment n) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  have hupper : Tendsto (fun n : ℕ => K *
      (2 * ((n : ℝ) * ∫ y, q n y ^ 2 ∂μ) +
        2 * ((n : ℝ) * ∫ y, q n y ^ 2 ∂ν) + 4 * G n ^ 2)) atTop (𝓝 0) := by
    simpa using (((hμq.const_mul 2).add (hνq.const_mul 2)).add
      ((hG.pow 2).const_mul 4)).const_mul K
  have hYlim : Tendsto (fun n => ∫ ω, Y n ω ^ 2 ∂C.conditionedMeasure x.val n)
      atTop (𝓝 0) := squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _)
        hYmoment hupper
  intro ε hε
  have hcheb (n : ℕ) : (C.conditionedMeasure x.val n).real {ω | ε < |Y n ω|} ≤
      (∫ ω, Y n ω ^ 2 ∂C.conditionedMeasure x.val n) / ε ^ 2 := by
    have := hP n
    have hYm : Measurable (Y n) := (measurable_pathBirkhoffSum (hq n) n).sub_const _
    have hYb (ω : Path M) : |Y n ω| ≤ 2 * n * G n := by
      have hp : |pathBirkhoffSum (q n) n ω| ≤ n * G n := by
        unfold pathBirkhoffSum birkhoffSum
        calc
          _ ≤ ∑ j ∈ Finset.range n, |zeroExtension (q n) (ω j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ Finset.range n, G n := Finset.sum_le_sum fun j _ =>
            abs_zeroExtension_le (hG0 n) (hqG n) _
          _ = n * G n := by simp
      have hc := mul_le_mul_of_nonneg_left (hcb n) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      calc
        _ ≤ |pathBirkhoffSum (q n) n ω| + |(n : ℝ) * c n| := abs_sub _ _
        _ ≤ 2 * n * G n := by rw [abs_mul, Nat.abs_cast]; nlinarith
    have hint := integrable_of_bdd (ν := C.conditionedMeasure x.val n)
      (hYm.pow_const 2) (sq_bdd hYb)
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun ω => sq_nonneg (Y n ω)) hint (ε ^ 2)
    have hmono : (C.conditionedMeasure x.val n).real {ω | ε < |Y n ω|} ≤
        (C.conditionedMeasure x.val n).real {ω | ε ^ 2 ≤ Y n ω ^ 2} := by
      apply measureReal_mono
      intro ω hω
      change ε ^ 2 ≤ Y n ω ^ 2
      rw [← sq_abs (Y n ω)]
      exact pow_le_pow_left₀ hε.le (le_of_lt hω) 2
      exact measure_ne_top _ _
    rw [le_div_iff₀ (sq_pos_of_pos hε)]
    nlinarith [hmono, hmark]
  exact squeeze_zero (fun _ => measureReal_nonneg) hcheb
    (by simpa using hYlim.div_const (ε ^ 2))

end Chain
end
end ConditionedStableLaws.ContinuousMultiplier
