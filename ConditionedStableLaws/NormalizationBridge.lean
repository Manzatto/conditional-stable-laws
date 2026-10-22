import ConditionedStableLaws.PoissonProcessConvergence
import ConditionedStableLaws.RareTargetNormalization

/-!
# Normalized live targets and their power-intensity rates

The cemetery extension is eventually below every positive lower endpoint. Finite and infinite upper
endpoints are treated explicitly. All targets are preimages of the normalized observation used in
the empirical process.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
noncomputable section

namespace ConditionedStableLaws.NormalizationBridge

/-- A positive normalization at every index, agreeing with the stable normalization for n>0. -/
def positivePowerScale (C α : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else powerScale C α n

theorem positivePowerScale_pos {C α : ℝ} (hC : 0 < C) (n : ℕ) :
    0 < positivePowerScale C α n := by
  unfold positivePowerScale
  split_ifs with hn
  · norm_num
  · exact powerScale_pos hC (Nat.pos_of_ne_zero hn)

theorem positivePowerScale_eventually_eq (C α : ℝ) :
    ∀ᶠ n in atTop, positivePowerScale C α n = powerScale C α n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact ite_eq_right (Nat.ne_of_gt hn)

theorem positivePowerScale_tendsto_atTop {C α : ℝ} (hC : 0 < C) (hα : 0 < α) :
    Tendsto (positivePowerScale C α) atTop atTop :=
  (powerScale_tendsto_atTop hC hα).congr' (by
    filter_upwards [positivePowerScale_eventually_eq C α] with n hn using hn.symm)

variable {M : Type*}

/-- The live-state preimage of the normalized observation. -/
def normalizedTarget (f : M → ℝ) (hf : ∀ x, 0 < f x) (B : ℕ → ℝ)
    (hB : ∀ n, 0 < B n) (n : ℕ) (a b : ExtremeState) : Set M :=
  (RandomPointMeasure.normalizedObservation f hf (B n) (hB n)) ⁻¹' Ioc a b

theorem measurableSet_normalizedTarget [MeasurableSpace M] (f : M → ℝ)
    (hm : Measurable f) (hf : ∀ x, 0 < f x) (B : ℕ → ℝ) (hB : ∀ n, 0 < B n)
    (n : ℕ) (a b : ExtremeState) : MeasurableSet (normalizedTarget f hf B hB n a b) :=
  (RandomPointMeasure.measurable_normalizedObservation hm hf _ _) measurableSet_Ioc

theorem lower_toReal_pos {a b : ExtremeState} (hab : a < b) : 0 < a.val.toReal :=
  ENNReal.toReal_pos a.property.ne' (ne_top_of_lt hab)

/-- Finite endpoints give the exact real half-open observation interval. -/
theorem normalizedTarget_eq_finite (f : M → ℝ) (hf : ∀ x, 0 < f x)
    (B : ℕ → ℝ) (hB : ∀ n, 0 < B n) (n : ℕ) (a b : ExtremeState)
    (ha : a.val ≠ ∞) (hb : b.val ≠ ∞) :
    normalizedTarget f hf B hB n a b =
      {x | a.val.toReal * B n < f x ∧ f x ≤ b.val.toReal * B n} := by
  ext x
  change (a.val < ENNReal.ofReal (f x / B n) ∧ ENNReal.ofReal (f x / B n) ≤ b.val) ↔ _
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb]
  rw [ENNReal.ofReal_lt_ofReal_iff (div_pos (hf x) (hB n)),
    ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
    lt_div_iff₀ (hB n), div_le_iff₀ (hB n)]
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, mem_ofPred_eq]

/-- An infinite upper endpoint gives exactly the strict observation tail. -/
theorem normalizedTarget_eq_top (f : M → ℝ) (hf : ∀ x, 0 < f x)
    (B : ℕ → ℝ) (hB : ∀ n, 0 < B n) (n : ℕ) (a : ExtremeState) (ha : a.val ≠ ∞) :
    normalizedTarget f hf B hB n a ⊤ = {x | a.val.toReal * B n < f x} := by
  ext x
  change (a.val < ENNReal.ofReal (f x / B n) ∧ ENNReal.ofReal (f x / B n) ≤ ∞) ↔ _
  simp only [le_top, and_true]
  rw [← ENNReal.ofReal_toReal ha, ENNReal.ofReal_lt_ofReal_iff (div_pos (hf x) (hB n)),
    lt_div_iff₀ (hB n)]
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, mem_ofPred_eq]

/-- Every target lies in its lower tail, including top upper endpoints. -/
theorem normalizedTarget_subset_tail (f : M → ℝ) (hf : ∀ x, 0 < f x)
    (B : ℕ → ℝ) (hB : ∀ n, 0 < B n) (n : ℕ) (a b : ExtremeState) (ha : a.val ≠ ∞) :
    normalizedTarget f hf B hB n a b ⊆ {x | a.val.toReal * B n < f x} := by
  intro x hx
  have hx' : a.val < ENNReal.ofReal (f x / B n) := hx.1
  rw [← ENNReal.ofReal_toReal ha, ENNReal.ofReal_lt_ofReal_iff (div_pos (hf x) (hB n)),
    lt_div_iff₀ (hB n)] at hx'
  exact hx'

/-- Any smaller common positive level contains the target eventually. -/
theorem normalizedTarget_eventually_subset_tail {C α level : ℝ} (hC : 0 < C)
    (f : M → ℝ) (hf : ∀ x, 0 < f x) (a b : ExtremeState) (hab : a < b)
    (hlevel : level ≤ a.val.toReal) :
    ∀ᶠ n in atTop, normalizedTarget f hf (positivePowerScale C α)
      (positivePowerScale_pos hC) n a b ⊆ {x | level * powerScale C α n < f x} := by
  filter_upwards [positivePowerScale_eventually_eq C α] with n hn
  intro x hx
  have h := normalizedTarget_subset_tail f hf _ (positivePowerScale_pos hC) n a b (ne_top_of_lt hab) hx
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlevel (by rw [← hn]; exact (positivePowerScale_pos hC n).le))
    (by simpa only [hn, mem_ofPred_eq] using h)

/-- The scalar-tail envelope holds at every index; at zero its threshold is zero. -/
theorem normalizedTarget_subset_powerTail {C α level : ℝ} (hC : 0 < C) (hα : 0 < α)
    (f : M → ℝ) (hf : ∀ x, 0 < f x) (a b : ExtremeState) (hab : a < b)
    (hlevel : level ≤ a.val.toReal) (n : ℕ) :
    normalizedTarget f hf (positivePowerScale C α) (positivePowerScale_pos hC) n a b ⊆
      {x | level * powerScale C α n < f x} := by
  intro x hx
  by_cases hn : n = 0
  · subst n
    simpa only [powerScale, Nat.cast_zero, mul_zero, Real.zero_rpow (one_div_ne_zero hα.ne'),
      mem_ofPred_eq] using hf x
  · have he : positivePowerScale C α n = powerScale C α n := ite_eq_right hn
    have ht := normalizedTarget_subset_tail f hf _ (positivePowerScale_pos hC) n a b (ne_top_of_lt hab) hx
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlevel (powerScale_pos hC (Nat.pos_of_ne_zero hn)).le)
      (by simpa only [he, mem_ofPred_eq] using ht)

/-- Strict positive intervals have finite positive lower endpoints. -/
theorem powerIntensity_real_Ioc_top {α : ℝ} (hα : 0 < α) (a : ExtremeState) (ha : a.val ≠ ∞) :
    (powerIntensity α).real (Ioc a ⊤) = a.val.toReal ^ (-α) := by
  have hset : Ioc a ⊤ = {y : ExtremeState | ENNReal.ofReal a.val.toReal < y.val} := by
    rw [ENNReal.ofReal_toReal ha]
    ext y
    simp only [mem_Ioc, le_top, and_true, mem_ofPred_eq]
    rfl
  rw [hset, measureReal_def, powerIntensity_Ioi hα (ENNReal.toReal_pos a.property.ne' ha),
    ENNReal.toReal_ofReal (Real.rpow_nonneg ENNReal.toReal_nonneg _)]

/-- Exact interval rates for the normalized targets, including infinity. -/
theorem normalizedTarget_rate [MeasurableSpace M] (ν : Measure M) [IsFiniteMeasure ν]
    (f : M → ℝ) (hm : Measurable f) (hf : ∀ x, 0 < f x)
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (htail : Tendsto (fun t : ℝ => ν.real {x | t < f x} / (C * t ^ (-α))) atTop (𝓝 1))
    (a b : ExtremeState) (hab : a < b) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real (normalizedTarget f hf
      (positivePowerScale C α) (positivePowerScale_pos hC) n a b)) atTop
      (𝓝 ((powerIntensity α).real (Ioc a b))) := by
  have ha : a.val ≠ ∞ := ne_top_of_lt hab
  have ha0 := lower_toReal_pos hab
  by_cases hb : b.val = ∞
  · have hb' : b = ⊤ := Subtype.ext hb
    subst b
    rw [powerIntensity_real_Ioc_top hα a ha]
    apply (normalized_tail_limit hC hα htail ha0).congr'
    filter_upwards [positivePowerScale_eventually_eq C α] with n hn
    rw [normalizedTarget_eq_top f hf _ _ n a ha, hn]
  · have hab' : a.val.toReal ≤ b.val.toReal := ENNReal.toReal_mono hb hab.le
    have hset : Ioc a b = {y : ExtremeState |
        ENNReal.ofReal a.val.toReal < y.val ∧ y.val ≤ ENNReal.ofReal b.val.toReal} := by
      rw [ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
      rfl
    rw [hset]
    apply (normalized_interval_tendsto_powerIntensity hm hC hα ha0 hab' htail).congr'
    filter_upwards [positivePowerScale_eventually_eq C α] with n hn
    rw [normalizedTarget_eq_finite f hf _ _ n a b ha hb, hn]

/-- Once the normalized cemetery mark falls below the lower endpoint, the
path target is exactly the lift of the live-state target. -/
theorem pathNormalization_preimage_eq [MeasurableSpace M]
    (f : M → ℝ) (hf : ∀ x, 0 < f x) (B : ℕ → ℝ) (hB : ∀ n, 0 < B n)
    (n : ℕ) (a b : ExtremeState) (ha : a.val ≠ ∞) (hcem : 1 ≤ a.val.toReal * B n) :
    pathNormalization f hf B hB n ⁻¹' Ioc a b =
      Option.some '' normalizedTarget f hf B hB n a b := by
  ext z
  cases z with
  | none =>
    have hnone : (none : Option M) ∉ Option.some '' normalizedTarget f hf B hB n a b := by simp
    rw [iff_false_right hnone]
    intro hz
    have hl : a.val < ENNReal.ofReal (1 / B n) := hz.1
    rw [← ENNReal.ofReal_toReal ha, ENNReal.ofReal_lt_ofReal_iff (div_pos zero_lt_one (hB n)),
      lt_div_iff₀ (hB n)] at hl
    exact not_lt_of_ge hcem hl
  | some x =>
    have he : pathNormalization f hf B hB n (some x) =
        RandomPointMeasure.normalizedObservation f hf (B n) (hB n) x := rfl
    simp only [mem_preimage, he, mem_image, Option.some.injEq, exists_eq_right, normalizedTarget]

/-- The path preimages eventually equal lifted live targets. -/
theorem pathNormalization_preimage_eventually [MeasurableSpace M]
    (f : M → ℝ) (hf : ∀ x, 0 < f x) {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (a b : ExtremeState) (hab : a < b) :
    ∀ᶠ n in atTop, pathNormalization f hf (positivePowerScale C α) (positivePowerScale_pos hC) n ⁻¹' Ioc a b =
      Option.some '' normalizedTarget f hf (positivePowerScale C α) (positivePowerScale_pos hC) n a b := by
  have ht := (positivePowerScale_tendsto_atTop hC hα).const_mul_atTop (lower_toReal_pos hab)
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with n hn
  exact pathNormalization_preimage_eq f hf _ _ n a b (ne_top_of_lt hab) hn

/-- Preimages preserve disjointness exactly at every index. -/
theorem normalizedTarget_disjoint (f : M → ℝ) (hf : ∀ x, 0 < f x)
    (B : ℕ → ℝ) (hB : ∀ n, 0 < B n) (n : ℕ)
    {a b c d : ExtremeState} (hd : Disjoint (Ioc a b) (Ioc c d)) :
    Disjoint (normalizedTarget f hf B hB n a b) (normalizedTarget f hf B hB n c d) :=
  hd.preimage _

end ConditionedStableLaws.NormalizationBridge
