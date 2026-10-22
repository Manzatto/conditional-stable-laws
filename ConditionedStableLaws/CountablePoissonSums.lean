import ConditionedStableLaws.PoissonCloudCounts
import ConditionedStableLaws.PoissonConvergence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Countable sums of independent Poisson counts with finite total rate. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem poissonProbabilityMeasure_tendsto {r : ℕ → ℝ≥0} {a : ℝ≥0}
    (hr : Tendsto r atTop (𝓝 a)) :
    Tendsto (fun n => poissonProbabilityMeasure (r n)) atTop (𝓝 (poissonProbabilityMeasure a)) := by
  apply probabilityMeasure_nat_tendsto_of_atoms
  intro k
  change Tendsto (fun n => (poissonMeasure (r n)).real {k}) atTop
    (𝓝 ((poissonMeasure a).real {k}))
  simp_rw [poissonMeasure_real_singleton]
  have ht := NNReal.continuous_coe.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, ← Real.exp_eq_exp_ℝ] using
    ((ht.neg.exp).mul (ht.pow k)).div_const (k.factorial : ℝ)

theorem tendstoInDistribution_of_poisson_laws
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Y : (n : ℕ) → Ω n → ℕ) (r : ℕ → ℝ≥0) (a : ℝ≥0)
    (hY : ∀ n, HasLaw (Y n) (poissonMeasure (r n)) (P n))
    (hr : Tendsto r atTop (𝓝 a)) :
    TendstoInDistribution Y atTop id P (poissonMeasure a) := by
  refine ⟨fun n => (hY n).aemeasurable, aemeasurable_id, ?_⟩
  simpa only [poissonProbabilityMeasure, fun n => (hY n).map_eq, Measure.map_id] using
    poissonProbabilityMeasure_tendsto hr

theorem poisson_finite_sum_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0) (hYm : ∀ n, Measurable (Y n))
    (hY : ∀ n, HasLaw (Y n) (poissonMeasure (r n)) P) (hind : iIndepFun Y P)
    (s : Finset ℕ) :
    HasLaw (fun ω => ∑ i ∈ s, Y i ω) (poissonMeasure (∑ i ∈ s, r i)) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : poissonMeasure 0 = Measure.dirac 0 := by
        apply Measure.ext_of_singleton
        intro n
        rw [poissonMeasure_singleton]
        cases n <;> simp
      simp only [Finset.sum_empty]
      rw [hz]
      exact ⟨measurable_const.aemeasurable, by simp⟩
  | @insert i s hi ih =>
      have hsum : (∑ j ∈ s, Y j) = (fun ω => ∑ j ∈ s, Y j ω) := by
        funext ω
        exact Finset.sum_apply ω s Y
      have ih' : HasLaw (∑ j ∈ s, Y j) (poissonMeasure (∑ j ∈ s, r j)) P := by
        rw [hsum]
        exact ih
      have ht := ((hind.indepFun_finsetSum_of_notMem hYm hi).symm).hasLaw_add_poissonMeasure
        (hY i) ih'
      rw [hsum] at ht
      change HasLaw (fun ω => Y i ω + ∑ j ∈ s, Y j ω)
        (poissonMeasure (r i + ∑ j ∈ s, r j)) P at ht
      simpa only [Finset.sum_insert hi] using ht

/-- Countable superposition preserves the Poisson law when the total rate is finite. Counts are
ENNReal-valued. -/
theorem poisson_countable_sum_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0) (hYm : ∀ n, Measurable (Y n))
    (hY : ∀ n, HasLaw (Y n) (poissonMeasure (r n)) P) (hind : iIndepFun Y P)
    (hr : Summable r) :
    HasLaw (fun ω => ∑' i, (Y i ω : ℝ≥0∞))
      (poissonCountLaw (∑' i, (r i : ℝ≥0∞))) P := by
  let S : ℕ → Ω → ℕ := fun n ω => ∑ i ∈ Finset.range n, Y i ω
  have hS (n : ℕ) : Measurable (S n) := Finset.measurable_sum _ (fun i _ => hYm i)
  have hSlaw (n : ℕ) : HasLaw (S n) (poissonMeasure (∑ i ∈ Finset.range n, r i)) P :=
    poisson_finite_sum_hasLaw P Y r hYm hY hind _
  have hD := (tendstoInDistribution_of_poisson_laws (fun _ => P) S
    (fun n => ∑ i ∈ Finset.range n, r i) (∑' i, r i) hSlaw hr.hasSum.tendsto_sum_nat).continuous_comp
    (g := fun n : ℕ => (n : ℝ≥0∞)) continuous_of_discreteTopology
  have hm : Measurable (fun ω => ∑' i, (Y i ω : ℝ≥0∞)) :=
    Measurable.tsum (fun i => (MeasurableEmbedding.natCast (α := ℝ≥0∞)).measurable.comp (hYm i))
  have hD' : TendstoInDistribution (fun n ω => (S n ω : ℝ≥0∞)) atTop
      (fun ω => ∑' i, (Y i ω : ℝ≥0∞)) (fun _ => P) P := by
    apply tendstoInDistribution_of_ae_tendsto (fun n =>
      ((MeasurableEmbedding.natCast (α := ℝ≥0∞)).measurable.comp (hS n)).aemeasurable) hm.aemeasurable
    apply ae_of_all
    intro ω
    change Tendsto (fun n => ((∑ i ∈ Finset.range n, Y i ω : ℕ) : ℝ≥0∞)) atTop _
    simpa only [Nat.cast_sum] using
      (ENNReal.summable.hasSum (f := fun i => (Y i ω : ℝ≥0∞))).tendsto_sum_nat
  refine ⟨hm.aemeasurable, ?_⟩
  have heq := congrArg (fun μ : ProbabilityMeasure ℝ≥0∞ => (μ : Measure ℝ≥0∞))
    (tendsto_nhds_unique hD'.tendsto hD.tendsto)
  change P.map (fun ω => ∑' i, (Y i ω : ℝ≥0∞)) =
    (poissonMeasure (∑' i, r i)).map (fun n : ℕ => (n : ℝ≥0∞)) at heq
  simpa only [poissonCountLaw, Function.comp_def, id_eq, ← ENNReal.coe_tsum hr,
    ENNReal.toNNReal_coe] using heq

end
end ConditionedStableLaws
