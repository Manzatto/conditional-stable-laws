import ConditionedStableLaws.VagueSeparation
import ConditionedStableLaws.PointCounts
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurability of counts for the vague topology

Evaluations on compact sets are limits of compactly supported test integrals. Open-set evaluations
follow by compact exhaustion, and interval counts follow by subtraction.
-/

open Filter MeasureTheory Set Classical
open scoped Topology ENNReal NNReal CompactlySupported

namespace ConditionedStableLaws
noncomputable section

namespace LocallyFinitePointMeasure

/-- The real-valued mass of any compact set is measurable for the vague Borel
sigma algebra. Compactly supported Urysohn approximants give the proof. -/
theorem measurable_measureReal_compact {K : Set ExtremeState} (hK : IsCompact K) :
    Measurable (fun ξ : LocallyFinitePointMeasure => ξ.toMeasure.real K) := by
  obtain ⟨f, hKf, _, hfcompact, hfrange⟩ :=
    exists_continuous_one_zero_of_isCompact_of_isGδ hK hK.isClosed.isGδ
      isClosed_empty (disjoint_empty K)
  let g (n : ℕ) : C_c(ExtremeState, ℝ) :=
    ⟨⟨fun x => f x * f x ^ n, f.continuous.mul (f.continuous.pow n)⟩,
      hfcompact.mul_right⟩
  apply measurable_of_tendsto_metrizable
    (fun n => (continuous_testIntegral (g n)).measurable)
  apply tendsto_pi_nhds.mpr
  intro ξ
  have hfi : Integrable f ξ.toMeasure :=
    (⟨f, hfcompact⟩ : C_c(ExtremeState, ℝ)).integrable
  have hdom (n : ℕ) (x : ExtremeState) : ‖g n x‖ ≤ f x := by
    change ‖f x * f x ^ n‖ ≤ f x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfrange x).1
      (pow_nonneg (hfrange x).1 n))]
    have hpow : f x ^ n ≤ 1 := pow_le_one₀ (hfrange x).1 (hfrange x).2
    nlinarith [(hfrange x).1]
  have hpoint (x : ExtremeState) : Tendsto (fun n => g n x) atTop
      (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) := by
    by_cases hx : x ∈ K
    · have hfx : f x = 1 := by simpa [hKf] using hx
      simp [g, hfx, hx]
    · have hfx : f x < 1 := lt_of_le_of_ne (hfrange x).2 (by
        intro heq
        apply hx
        simpa [hKf] using heq)
      simpa [g, hx] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (hfrange x).1 hfx).const_mul (f x)
  have ht := tendsto_integral_of_dominated_convergence f
    (fun n => (g n).continuous.aestronglyMeasurable) hfi
    (fun n => .of_forall (hdom n)) (.of_forall hpoint)
  have hInd : (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂ξ.toMeasure) = ξ.toMeasure.real K := by
    simpa using integral_indicator_const (μ := ξ.toMeasure) (1 : ℝ) hK.isClosed.measurableSet
  rw [hInd] at ht
  convert ht using 1

/-- Compact-set evaluation as an extended nonnegative mass is measurable. -/
theorem measurable_measure_compact {K : Set ExtremeState} (hK : IsCompact K) :
    Measurable (fun ξ : LocallyFinitePointMeasure => ξ.toMeasure K) := by
  have h := ENNReal.measurable_ofReal.comp (measurable_measureReal_compact hK)
  convert h using 1
  ext ξ
  exact (ofReal_measureReal (hK.measure_lt_top (μ := ξ.toMeasure)).ne).symm

/-- Open-set evaluation is measurable, even when its value can be infinite. -/
theorem measurable_measure_open {U : Set ExtremeState} (hU : IsOpen U) :
    Measurable (fun ξ : LocallyFinitePointMeasure => ξ.toMeasure U) := by
  have hσ : IsSigmaCompact U := by
    let : LocallyCompactSpace U := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hKU⟩ := hσ
  apply ENNReal.measurable_of_tendsto
    (fun n => measurable_measure_compact (isCompact_accumulate hK n))
  apply tendsto_pi_nhds.mpr
  intro ξ
  simpa only [hKU] using
    (tendsto_measure_iUnion_accumulate (μ := ξ.toMeasure) (s := K))

/-- The closed positive tail `[a,∞]`. -/
theorem measurable_measure_tail (a : ℝ≥0) (ha : 0 < a) :
    Measurable (fun ξ : LocallyFinitePointMeasure => ξ.toMeasure (extremeTail a)) :=
  measurable_measure_compact (isCompact_extremeTail a ha)

/-- Open positive tails `(a,∞]` are measurable evaluations, including at infinity. -/
theorem measurable_measure_openTail (a : ℝ≥0∞) :
    Measurable (fun ξ : LocallyFinitePointMeasure =>
      ξ.toMeasure {x : ExtremeState | a < x.val}) :=
  measurable_measure_open (isOpen_lt continuous_const continuous_subtype_val)

/-- Evaluation on every interval `(a,b]` is measurable. -/
theorem measurable_measure_interval (a b : ℝ≥0∞) (ha : 0 < a) :
    Measurable (fun ξ : LocallyFinitePointMeasure =>
      ξ.toMeasure {x : ExtremeState | a < x.val ∧ x.val ≤ b}) := by
  by_cases hab : a ≤ b
  · have hsub : {x : ExtremeState | b < x.val} ⊆ {x : ExtremeState | a < x.val} :=
      fun x hx => hab.trans_lt hx
    have hbmeas : MeasurableSet {x : ExtremeState | b < x.val} :=
      (isOpen_lt continuous_const continuous_subtype_val).measurableSet
    have hmeas := (measurable_measure_openTail a).sub (measurable_measure_openTail b)
    convert hmeas using 1
    ext ξ
    simp only [Pi.sub_apply]
    rw [← measure_sdiff hsub hbmeas.nullMeasurableSet]
    · congr 1
      ext x
      simp
    · obtain ⟨δ, hδ0, hδa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha
      exact (lt_of_le_of_lt (measure_mono (fun x hx => (hδa.le.trans hab).trans hx.le))
        (ξ.finite_tail δ (by exact_mod_cast hδ0))).ne
  · have hset : {x : ExtremeState | a < x.val ∧ x.val ≤ b} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun hx hxb => hab (hx.le.trans hxb)
    simp [hset]

/-- A finite evaluation of a point measure, represented as a natural count. -/
def countOn (ξ : LocallyFinitePointMeasure) (A : Set ExtremeState) : ℕ :=
  ⌊ξ.toMeasure.real A⌋₊

/-- The natural count is the mass, with multiplicities. -/
theorem countOn_eq_measure (ξ : LocallyFinitePointMeasure) {A : Set ExtremeState}
    (hA : MeasurableSet A) (hfinite : ξ.toMeasure A < ∞) :
    (ξ.countOn A : ℝ≥0∞) = ξ.toMeasure A := by
  obtain ⟨n, hn⟩ := ξ.atomic.exists_nat_of_apply_lt_top A hA hfinite
  simp [countOn, measureReal_def, hn]

/-- Compact counts are measurable as natural-valued maps. -/
theorem measurable_countOn_compact {K : Set ExtremeState} (hK : IsCompact K) :
    Measurable (fun ξ : LocallyFinitePointMeasure => ξ.countOn K) :=
  (measurable_measureReal_compact hK).nat_floor

/-- The natural-valued count on a positive half-open interval is measurable. -/
theorem measurable_countOn_interval (a b : ℝ≥0∞) (ha : 0 < a) :
    Measurable (fun ξ : LocallyFinitePointMeasure =>
      ξ.countOn {x : ExtremeState | a < x.val ∧ x.val ≤ b}) :=
  ((measurable_measure_interval a b ha).ennreal_toReal).nat_floor

/-- Positive half-open intervals have finite mass, including intervals ending
at infinity. -/
theorem measure_interval_lt_top (ξ : LocallyFinitePointMeasure) (a b : ℝ≥0∞)
    (ha : 0 < a) : ξ.toMeasure {x : ExtremeState | a < x.val ∧ x.val ≤ b} < ∞ := by
  obtain ⟨δ, hδ0, hδa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha
  exact lt_of_le_of_lt (measure_mono (fun x hx => hδa.le.trans hx.1.le))
    (ξ.finite_tail δ (by exact_mod_cast hδ0))

theorem countOn_interval_eq_measure (ξ : LocallyFinitePointMeasure) (a b : ℝ≥0∞)
    (ha : 0 < a) :
    (ξ.countOn {x : ExtremeState | a < x.val ∧ x.val ≤ b} : ℝ≥0∞) =
      ξ.toMeasure {x : ExtremeState | a < x.val ∧ x.val ≤ b} :=
  ξ.countOn_eq_measure ((measurableSet_lt measurable_const measurable_subtype_coe).inter
    (measurableSet_le measurable_subtype_coe measurable_const))
    (ξ.measure_interval_lt_top a b ha)

/-- Joint interval counts are measurable in the product sigma algebra. -/
theorem measurable_intervalCountVector {J : Type*} (a b : J → ℝ≥0∞)
    (ha : ∀ j, 0 < a j) :
    Measurable (fun ξ : LocallyFinitePointMeasure => fun j =>
      ξ.countOn {x : ExtremeState | a j < x.val ∧ x.val ≤ b j}) :=
  Measurable.of_eval fun j => measurable_countOn_interval (a j) (b j) (ha j)

end LocallyFinitePointMeasure

namespace RandomPointMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every random point measure has measurable natural counts on intervals `(a,b]`; this follows from
its vague Borel measurability. -/
theorem measurable_intervalCount (N : RandomPointMeasure Ω) (a b : ℝ≥0∞) (ha : 0 < a) :
    Measurable (fun ω => (N.toFun ω).countOn {x : ExtremeState | a < x.val ∧ x.val ≤ b}) :=
  (LocallyFinitePointMeasure.measurable_countOn_interval a b ha).comp N.measurable

theorem measurable_intervalCountVector {J : Type*} (N : RandomPointMeasure Ω)
    (a b : J → ℝ≥0∞) (ha : ∀ j, 0 < a j) :
    Measurable (fun ω => fun j =>
      (N.toFun ω).countOn {x : ExtremeState | a j < x.val ∧ x.val ≤ b j}) :=
  (LocallyFinitePointMeasure.measurable_intervalCountVector a b ha).comp N.measurable

end RandomPointMeasure
end
end ConditionedStableLaws
