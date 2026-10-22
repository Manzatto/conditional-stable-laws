import ConditionedStableLaws.ContinuousMultiplierCompensation
import ConditionedStableLaws.MultiplierReflection

/-! Absolute-value centering for a continuous multiplier at tail exponent one. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
noncomputable section
namespace ConditionedStableLaws.ContinuousMultiplier
open MultiplierReflection SmallJumpMoment NormalizationBridge SecondMoment

section Bounds
variable {M : Type*} {f r : M → ℝ}

theorem absTrunc_sub_cut_shell_bound
    (hf : ∀ y, 0 ≤ f y) {B η K lo hi : ℝ}
    (hB : 0 < B) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2)
    (hK : K ≤ η * B) (hlo : lo ≤ 1) (hhi : 1 ≤ hi)
    (hloeq : (1 + η) * lo + η = 1) (hhieq : (1 - η) * hi - η = 1)
    (hr : ∀ y, |r y| ≤ η * f y + K) (y : M) :
    |absTrunc (fun z => f z + r z) B y - cut f (fun z => f z + r z) B y| ≤
      {z | lo * B < f z ∧ f z ≤ hi * B}.indicator (fun _ => 2 * B) y := by
  have hsum : |f y + r y| ≤ (1 + η) * f y + K := by
    have hb := abs_add_le (f y) (r y)
    rw [abs_of_nonneg (hf y)] at hb
    linarith [hr y]
  have hlowersum : (1 - η) * f y - K ≤ f y + r y := by
    have hh := neg_abs_le (r y)
    linarith [hr y]
  by_cases hs : lo * B < f y ∧ f y ≤ hi * B
  · rw [indicator_of_mem (show y ∈ {z | lo * B < f z ∧ f z ≤ hi * B} from hs)]
    by_cases habs : |f y + r y| ≤ B <;> by_cases hcut : f y ≤ B
    · simp [absTrunc, cut, habs, hcut, hB.le]
    · simp only [absTrunc, cut, indicator_of_mem (show y ∈ {z | |f z + r z| ≤ B} from habs),
        indicator_of_notMem (show y ∉ {z | f z ≤ B} from hcut), sub_zero]
      linarith
    · simp only [absTrunc, cut, indicator_of_notMem
        (show y ∉ {z | |f z + r z| ≤ B} from habs),
        indicator_of_mem (show y ∈ {z | f z ≤ B} from hcut), zero_sub, abs_neg]
      have hh := mul_le_mul_of_nonneg_left hcut (show 0 ≤ 1 + η by linarith)
      have he := mul_le_mul_of_nonneg_right hηsmall hB.le
      nlinarith
    · simp [absTrunc, cut, habs, hcut, hB.le]
  · rw [indicator_of_notMem (show y ∉ {z | lo * B < f z ∧ f z ≤ hi * B} from hs)]
    by_cases hbelow : f y ≤ lo * B
    · have hcut : f y ≤ B := hbelow.trans (by nlinarith)
      have hh := mul_le_mul_of_nonneg_left hbelow (show 0 ≤ 1 + η by linarith)
      have he : (1 + η) * (lo * B) + η * B = B := by nlinarith [congrArg (fun t => t * B) hloeq]
      have habs : |f y + r y| ≤ B := by linarith
      simp [absTrunc, cut, hcut, habs]
    · have habove : hi * B < f y := lt_of_not_ge (fun hy => hs ⟨lt_of_not_ge hbelow, hy⟩)
      have hcut : ¬f y ≤ B := by nlinarith
      have hh := mul_lt_mul_of_pos_left habove (show 0 < 1 - η by linarith)
      have he : (1 - η) * (hi * B) - η * B = B := by nlinarith [congrArg (fun t => t * B) hhieq]
      have habs : ¬|f y + r y| ≤ B := by linarith [le_abs_self (f y + r y)]
      simp [absTrunc, cut, hcut, habs]

end Bounds
section Integrals
variable {M : Type*} [MeasurableSpace M] (ν : Measure M) [IsProbabilityMeasure ν]
  {f r : M → ℝ}

theorem measurable_absTrunc {q : M → ℝ} (hq : Measurable q) (B : ℝ) :
    Measurable (absTrunc q B) :=
  hq.indicator (measurableSet_le (continuous_abs.measurable.comp hq) measurable_const)

omit [MeasurableSpace M] in
theorem abs_absTrunc_le {q : M → ℝ} {B : ℝ} (hB : 0 ≤ B) (y : M) :
    |absTrunc q B y| ≤ B := by
  by_cases hy : |q y| ≤ B <;> simp [absTrunc, hy, hB]

theorem integral_absTrunc_sub_cut_shell_bound
    (hfm : Measurable f) (hrm : Measurable r) (hf : ∀ y, 0 ≤ f y)
    {B η K lo hi : ℝ} (hB : 0 < B) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (hK0 : 0 ≤ K)
    (hK : K ≤ η * B) (hlo : lo ≤ 1) (hhi : 1 ≤ hi)
    (hloeq : (1 + η) * lo + η = 1) (hhieq : (1 - η) * hi - η = 1)
    (hr : ∀ y, |r y| ≤ η * f y + K) :
    |(∫ y, absTrunc (fun z => f z + r z) B y ∂ν) -
        ∫ y, cut f (fun z => f z + r z) B y ∂ν| ≤
      2 * B * ν.real {y | lo * B < f y ∧ f y ≤ hi * B} := by
  have ha : Integrable (absTrunc (fun z => f z + r z) B) ν :=
    integrable_of_bdd (ν := ν) (measurable_absTrunc (hfm.add hrm) B) (abs_absTrunc_le hB.le)
  have hq : ∀ y, |f y + r y| ≤ (1 + η) * f y + K := fun y => by
    have hh := abs_add_le (f y) (r y)
    rw [abs_of_nonneg (hf y)] at hh
    linarith [hr y]
  have hcut : Integrable (cut f (fun y => f y + r y) B) ν := by
    apply integrable_of_bdd (measurable_cut hfm (hfm.add hrm) B)
    exact abs_cut_le (show 0 ≤ 1 + η by linarith) hK0 hB.le hq
  have hset : MeasurableSet {y | lo * B < f y ∧ f y ≤ hi * B} :=
    (measurableSet_lt measurable_const hfm).inter (measurableSet_le hfm measurable_const)
  rw [← integral_sub ha hcut]
  have hb := norm_integral_le_of_norm_le
    (f := fun y => absTrunc (fun z => f z + r z) B y - cut f (fun z => f z + r z) B y)
    ((integrable_const (2 * B)).indicator hset)
    (ae_of_all ν fun y => by
      simpa only [Real.norm_eq_abs] using
        absTrunc_sub_cut_shell_bound hf hB hη hηsmall hK hlo hhi hloeq hhieq hr y)
  rw [integral_indicator hset, setIntegral_const, smul_eq_mul] at hb
  simpa only [Real.norm_eq_abs, mul_comm] using hb

/-- At exponent one, using the absolute size of the perturbed observable
instead of the original cutoff changes the normalized centering by `o(1)`.
The proof derives a shrinking-shell estimate from the original tail. -/
theorem absolute_center_difference_tendsto
    (hfm : Measurable f) (hrm : Measurable r) (hf : ∀ y, 0 ≤ f y)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |r y| ≤ η * f y + K)
    {Cc : ℝ} (hC : 0 < Cc)
    (htail : Tendsto (fun t : ℝ => ν.real {y | t < f y} /
      (Cc * t ^ (-(1 : ℝ)))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) / positivePowerScale Cc 1 n *
      ((∫ y, absTrunc (fun z => f z + r z) (positivePowerScale Cc 1 n) y ∂ν) -
        ∫ y, cut f (fun z => f z + r z) (positivePowerScale Cc 1 n) y ∂ν))
      atTop (𝓝 0) := by
  let B := positivePowerScale Cc 1
  have hB : ∀ n, 0 < B n := positivePowerScale_pos hC
  let F : ℝ → ℝ := fun η => 2 * (((1 - η) / (1 + η))⁻¹ - ((1 + η) / (1 - η))⁻¹)
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt F 0 := by dsimp [F]; fun_prop (disch := norm_num)
    simpa [F] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hchoose : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η ∧ η < 1 / 2 ∧ F η < ε := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds,
      hF.eventually_lt_const hε] with η hη hηsmall hnear
    exact ⟨hη, hηsmall, hnear⟩
  obtain ⟨η, hη, hηsmall, hFη⟩ := hchoose.exists
  have hp : 0 < 1 + η := by linarith
  have hm : 0 < 1 - η := by linarith
  let lo := (1 - η) / (1 + η)
  let hi := (1 + η) / (1 - η)
  have hlo0 : 0 < lo := div_pos hm hp
  have hhi0 : 0 < hi := div_pos hp hm
  have hlo : lo ≤ 1 := (div_le_one hp).mpr (by linarith)
  have hhi : 1 ≤ hi := (one_le_div hm).mpr (by linarith)
  have hloeq : (1 + η) * lo + η = 1 := by dsimp [lo]; field_simp; ring
  have hhieq : (1 - η) * hi - η = 1 := by dsimp [hi]; field_simp; ring
  obtain ⟨K, hK0, hKr⟩ := hr η hη
  have hK : ∀ᶠ n in atTop, K ≤ η * B n :=
    ((positivePowerScale_tendsto_atTop hC one_pos).const_mul_atTop hη).eventually_ge_atTop K
  have htailLo := CompensationAsymptotics.scaled_tail hC one_pos htail hlo0
  have htailHi := CompensationAsymptotics.scaled_tail hC one_pos htail hhi0
  have hshell : Tendsto (fun n : ℕ => 2 * ((n : ℝ) *
      ν.real {y | lo * B n < f y ∧ f y ≤ hi * B n})) atTop (𝓝 (F η)) := by
    have ht := (htailLo.sub htailHi).const_mul 2
    simp only [Real.rpow_neg_one] at ht
    apply ht.congr
    intro n
    have he : {y | lo * B n < f y ∧ f y ≤ hi * B n} =
        {y | B n * lo < f y} \ {y | B n * hi < f y} := by
      ext y
      simp only [mem_ofPred_eq, Set.mem_sdiff, not_lt, mul_comm]
    rw [he, measureReal_sdiff]
    · ring
    · intro y hy
      change B n * lo < f y
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hlo.trans hhi) (hB n).le) hy
    · exact measurableSet_lt measurable_const hfm
  filter_upwards [hK, hshell.eventually_lt_const hFη] with n hn hnear
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (hB n).le)]
  have hb := integral_absTrunc_sub_cut_shell_bound ν hfm hrm hf (hB n)
    hη.le hηsmall.le hK0 hn hlo hhi hloeq hhieq hKr
  calc
    _ ≤ (n : ℝ) / B n * (2 * B n * ν.real {y | lo * B n < f y ∧ f y ≤ hi * B n}) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg (Nat.cast_nonneg n) (hB n).le)
    _ = 2 * ((n : ℝ) * ν.real {y | lo * B n < f y ∧ f y ≤ hi * B n}) := by
      field_simp [(hB n).ne']
    _ < ε := hnear

/-- The centering correction in the form used with the centered residual sum. -/
theorem absolute_center_residual_tendsto
    (hfm : Measurable f) (hrm : Measurable r) (hf : ∀ y, 0 ≤ f y)
    (hr : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |r y| ≤ η * f y + K)
    {Cc : ℝ} (hC : 0 < Cc)
    (htail : Tendsto (fun t : ℝ => ν.real {y | t < f y} /
      (Cc * t ^ (-(1 : ℝ)))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) / positivePowerScale Cc 1 n *
      ((∫ y, absTrunc (fun z => f z + r z) (positivePowerScale Cc 1 n) y ∂ν) -
        (∫ y, trunc f (positivePowerScale Cc 1 n) y ∂ν) -
        ∫ y, cut f r (positivePowerScale Cc 1 n) y ∂ν)) atTop (𝓝 0) := by
  apply (absolute_center_difference_tendsto ν hfm hrm hf hr hC htail).congr
  intro n
  obtain ⟨K, hK0, hKr⟩ := hr 1 one_pos
  have hB := positivePowerScale_pos hC (α := (1 : ℝ)) n
  have hfi : Integrable (trunc f (positivePowerScale Cc 1 n)) ν :=
    integrable_of_bdd (measurable_trunc hfm _)
      (fun y => by rw [abs_of_nonneg (trunc_nonneg hf _ y)]; exact trunc_le hB.le y)
  have hri : Integrable (cut f r (positivePowerScale Cc 1 n)) ν :=
    integrable_of_bdd (measurable_cut hfm hrm _) (abs_cut_le zero_le_one hK0 hB.le hKr)
  have he : cut f (fun z => f z + r z) (positivePowerScale Cc 1 n) =
      fun y => trunc f (positivePowerScale Cc 1 n) y + cut f r (positivePowerScale Cc 1 n) y := by
    funext y
    by_cases hy : f y ≤ positivePowerScale Cc 1 n <;> simp [cut, trunc, hy]
  rw [he, integral_add hfi hri]
  ring

end Integrals
end ConditionedStableLaws.ContinuousMultiplier
