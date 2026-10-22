import ConditionedStableLaws.FiniteCountExample
import ConditionedStableLaws.EmpiricalPaths

/-!
# Dependent finite counts for the singular observable

Positive-dimensional local regularity supplies two disjoint finite mark bands of positive mass. For
the refresh chain these give dependent counts of the singular empirical point measure at horizon
two.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
noncomputable section
namespace ConditionedStableLaws.FiniteCountExample

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [BorelSpace M]
  {ρ : Measure M} [IsProbabilityMeasure ρ]

omit [BorelSpace M] in
/-- Regularity makes every sufficiently large singular mark possible with positive probability. -/
theorem singular_tail_ne_zero_of_regular {x₀ : M} {β d C : ℝ}
    (hβ : 0 < β) (hreg : IsRegularAt ρ x₀ d C) (a : ℝ) :
    ρ {x | a < singularObservable x₀ β x} ≠ 0 := by
  have hh := (tendsto_order.1 (tail_asymptotic_of_regular hβ hreg)).1 0 zero_lt_one
  obtain ⟨t, ht, hta, ht0⟩ :=
    (hh.and ((eventually_gt_atTop a).and (eventually_gt_atTop (0 : ℝ)))).exists
  have hden : 0 < C * t ^ (-(d / β)) :=
    mul_pos hreg.2.1 (Real.rpow_pos_of_pos ht0 _)
  have hpos : 0 < ρ.real {x | t < singularObservable x₀ β x} :=
    (div_pos_iff_of_pos_right hden).mp ht
  have hsub : {x | t < singularObservable x₀ β x} ⊆
      {x | a < singularObservable x₀ β x} := fun _ hx => hta.trans hx
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.toReal_pos_iff.mp hpos).1 (measure_mono hsub))

omit [MetricSpace M] [BorelSpace M] [IsProbabilityMeasure ρ] in
/-- A finite-valued observable with a positive tail has a finite positive-mass
band above the same threshold. -/
theorem exists_positive_band_of_positive_tail {f : M → ℝ} (a : ℝ)
    (ha : ρ {x | a < f x} ≠ 0) :
    ∃ b : ℝ, a < b ∧ ρ {x | a < f x ∧ f x ≤ b} ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz (n : ℕ) : ρ {x | a < f x ∧ f x ≤ a + 1 + (n : ℝ)} = 0 :=
    hn _ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  apply ha
  apply measure_mono_null (t := ⋃ n : ℕ, {x | a < f x ∧ f x ≤ a + 1 + (n : ℝ)})
  · intro x hx
    obtain ⟨n, hn'⟩ := exists_nat_gt (f x - a)
    exact mem_iUnion.mpr ⟨n, hx, by linarith⟩
  · exact measure_iUnion_null hz

omit [BorelSpace M] in
/-- Two adjacent, disjoint finite bands lie above the assigned center value one and both have
positive mass under the reference measure. -/
theorem exists_two_positive_singular_bands {x₀ : M} {β d C : ℝ}
    (hβ : 0 < β) (hreg : IsRegularAt ρ x₀ d C) :
    ∃ b c : ℝ, 2 < b ∧ b < c ∧
      ρ {x | 2 < singularObservable x₀ β x ∧ singularObservable x₀ β x ≤ b} ≠ 0 ∧
      ρ {x | b < singularObservable x₀ β x ∧ singularObservable x₀ β x ≤ c} ≠ 0 := by
  obtain ⟨b, hb, hp⟩ := exists_positive_band_of_positive_tail 2
    (singular_tail_ne_zero_of_regular hβ hreg 2)
  obtain ⟨c, hc, hq⟩ := exists_positive_band_of_positive_tail b
    (singular_tail_ne_zero_of_regular hβ hreg b)
  exact ⟨b, c, hb, hc, hp, hq⟩

/-- A positive finite raw mark, divided by the scale. -/
def scaledEndpoint (a B : ℝ) (ha : 0 < a) (hB : 0 < B) : ExtremeState :=
  ⟨ENNReal.ofReal (a / B), ENNReal.ofReal_pos.mpr (div_pos ha hB)⟩

theorem scaledEndpoint_lt {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (hB : 0 < B) :
    scaledEndpoint a B ha hB < scaledEndpoint b B hb hB ↔ a < b := by
  change ENNReal.ofReal (a / B) < ENNReal.ofReal (b / B) ↔ a < b
  rw [ENNReal.ofReal_lt_ofReal_iff (div_pos hb hB), div_lt_div_iff_of_pos_right hB]

omit [MetricSpace M] [BorelSpace M] in
/-- Evaluation of the normalized empirical measure is the raw visit count for the corresponding
band. The lower endpoint above one also removes the cemetery extension, so the equality holds for
every path. -/
theorem pathEmpirical_countOn_scaled_Ioc (f : M → ℝ) (hm : Measurable f)
    (hf : ∀ x, 0 < f x) (n : ℕ) (B : ℝ) (hB : 0 < B)
    {a b : ℝ} (ha : 1 < a) (hb : 0 < b) (ω : CanonicalChain.Path M) :
    ((pathEmpirical f hm hf n B hB).toFun ω).countOn
      (Ioc (scaledEndpoint a B (zero_lt_one.trans ha) hB) (scaledEndpoint b B hb hB)) =
      (visitTimes (fun i : Fin n => ω i.val) (Option.some '' {x | a < f x ∧ f x ≤ b})).card := by
  classical
  change (LocallyFinitePointMeasure.empirical _).countOn _ = _
  rw [countOn_empirical]
  unfold visitTimes
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (ENNReal.ofReal (a / B) < ENNReal.ofReal (positiveExtension f (ω i.val) / B) ∧
      ENNReal.ofReal (positiveExtension f (ω i.val) / B) ≤ ENNReal.ofReal (b / B)) ↔ _
  rw [ENNReal.ofReal_lt_ofReal_iff (div_pos (positiveExtension_pos hf _) hB),
    ENNReal.ofReal_le_ofReal_iff (div_nonneg hb.le hB.le),
    div_lt_div_iff_of_pos_right hB, div_le_div_iff_of_pos_right hB]
  cases hω : ω i.val with
  | none => simp [positiveExtension, not_lt.mpr ha.le]
  | some x => simp [positiveExtension]

variable [CompactSpace M]

/-- The exact singular point-process counts at horizon two are dependent for two disjoint finite
positive-endpoint intervals. The only chain input is its time-one marginal under the conditioned
path law. -/
theorem singular_two_counts_dependent_of_time_one_law
    (Cchain : CanonicalChain M) (eig : DoobTransform.EigenData Cchain.killedTransition)
    (x₀ : eig.State) {β d C B : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hreg : IsRegularAt ρ x₀.val d C)
    (hlaw : ∀ A : Set M, MeasurableSet A →
      (Cchain.liveConditionedProbabilityMeasure eig x₀ 2 : Measure (CanonicalChain.Path M))
        {ω | ω 1 ∈ Option.some '' A} = ρ A) :
    ∃ a b c : ExtremeState, a < b ∧ b < c ∧ c.val ≠ ∞ ∧
      Disjoint (Ioc a b) (Ioc b c) ∧
      ¬ IndepFun
        (fun ω : CanonicalChain.Path M =>
          ((singularPathEmpirical x₀.val β 2 B hB).toFun ω).countOn (Ioc a b))
        (fun ω : CanonicalChain.Path M =>
          ((singularPathEmpirical x₀.val β 2 B hB).toFun ω).countOn (Ioc b c))
        (Cchain.liveConditionedProbabilityMeasure eig x₀ 2 :
          Measure (CanonicalChain.Path M)) := by
  obtain ⟨b, c, hb, hc, hp, hq⟩ := exists_two_positive_singular_bands hβ hreg
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := hb0.trans hc
  let U : Set M := {x | 2 < singularObservable x₀.val β x ∧ singularObservable x₀.val β x ≤ b}
  let V : Set M := {x | b < singularObservable x₀.val β x ∧ singularObservable x₀.val β x ≤ c}
  have hm := measurable_singularObservable x₀.val β
  have hU : MeasurableSet U := (measurableSet_lt measurable_const hm).inter
    (measurableSet_le hm measurable_const)
  have hV : MeasurableSet V := (measurableSet_lt measurable_const hm).inter
    (measurableSet_le hm measurable_const)
  have hd : Disjoint U V := disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1
  have hxU : x₀.val ∉ U := by simp [U]
  have hxV : x₀.val ∉ V := by simp [V, not_lt.mpr (by linarith : 1 ≤ b)]
  have hnot := Cchain.two_visit_counts_not_independent eig x₀ 2 hd hxU hxV
    (by rwa [hlaw U hU]) (by rwa [hlaw V hV])
  refine ⟨scaledEndpoint 2 B (by norm_num) hB, scaledEndpoint b B hb0 hB,
    scaledEndpoint c B hc0 hB, (scaledEndpoint_lt _ _ _).mpr hb,
    (scaledEndpoint_lt _ _ _).mpr hc, ENNReal.ofReal_ne_top, ?_, ?_⟩
  · exact disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1
  · simpa only [singularPathEmpirical, pathEmpirical_countOn_scaled_Ioc _ _ _ _ _ _
      (by norm_num : (1 : ℝ) < 2) hb0,
      pathEmpirical_countOn_scaled_Ioc _ _ _ _ _ _ (by linarith : 1 < b) hc0] using hnot

/-- A chain satisfying H with dependent finite counts for the singular empirical measure, given
local regularity and the scale. -/
theorem refresh_hypothesisH_and_singular_two_counts_dependent [ρ.IsOpenPosMeasure]
    {x₀ : M} {β d C B : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hreg : IsRegularAt ρ x₀ d C) :
    Nonempty (StandingHypothesis.HypothesisH ρ (refreshChain ρ).toKilledKernel) ∧
    IsAdmissibleAt ρ (fun _ => 1) x₀ d C ∧
    ∃ a b c : ExtremeState, a < b ∧ b < c ∧ c.val ≠ ∞ ∧
      Disjoint (Ioc a b) (Ioc b c) ∧
      ¬ IndepFun
        (fun ω : CanonicalChain.Path M =>
          ((singularPathEmpirical x₀ β 2 B hB).toFun ω).countOn (Ioc a b))
        (fun ω : CanonicalChain.Path M =>
          ((singularPathEmpirical x₀ β 2 B hB).toFun ω).countOn (Ioc b c))
        ((refreshChain ρ).liveConditionedProbabilityMeasure
          (refreshEigenData ρ) (refreshState ρ x₀) 2 : Measure (CanonicalChain.Path M)) := by
  refine ⟨⟨refreshChain_hypothesisH ρ⟩,
    isAdmissibleAt_of_continuousAt (integrable_const 1) hreg zero_lt_one continuousAt_const, ?_⟩
  exact singular_two_counts_dependent_of_time_one_law (refreshChain ρ)
    (refreshEigenData ρ) (refreshState ρ x₀) hβ hB hreg
    (fun A hA => refresh_time_one_probability ρ x₀ 2 A hA)

end ConditionedStableLaws.FiniteCountExample
