import ConditionedStableLaws.AnnularPoissonClouds
import ConditionedStableLaws.IndependentSuperposition

/-!
Existence of Poisson random measures for every intensity finite on positive tails, including the
infinite power-law intensity.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ConditionedStableLaws.AnnularPoissonClouds
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)

/-- The superposed count has the Poisson law on every finite-intensity measurable region. -/
theorem superposed_count_hasLaw (A : Set ExtremeState) (hA : MeasurableSet A)
    (hf : υ A ≠ ∞) :
    HasLaw (fun ω => (randomMeasure.toFun ω).toMeasure A)
      (poissonCountLaw (υ A)) (law υ hυ) := by
  have hsum : ∑' n, (υ.restrict (annulus n)) A = υ A := by
    rw [← Measure.sum_apply_of_countable, sum_restrict_annulus]
  have hfinite (n : ℕ) : (υ.restrict (annulus n)) A ≠ ∞ := by
    apply ne_top_of_le_ne_top (annulus_measure_lt_top υ hυ n).ne
    rw [Measure.restrict_apply hA]
    exact measure_mono inter_subset_right
  have hr : Summable (fun n => ((υ.restrict (annulus n)) A).toNNReal) :=
    ENNReal.summable_toNNReal_of_tsum_ne_top (by rw [hsum]; exact hf)
  have he : (∑' n, (((υ.restrict (annulus n)) A).toNNReal : ℝ≥0∞)) = υ A := by
    simpa only [ENNReal.coe_toNNReal (hfinite _)] using hsum
  have hp := poisson_countable_sum_hasLaw (law υ hυ)
    (fun n ω => FinitePoissonCloud.count A (ω n))
    (fun n => ((υ.restrict (annulus n)) A).toNNReal)
    (fun n => (FinitePoissonCloud.measurable_count A hA).comp (measurable_pi_apply n))
    (fun n => component_count_hasLaw υ hυ n A hA)
    (independent_component_counts υ hυ A hA) hr
  rw [he] at hp
  apply hp.congr
  filter_upwards [randomMeasure_apply_ae υ hυ] with ω hω
  rw [hω A]
  apply tsum_congr
  intro n
  exact (FinitePoissonCloud.count_eq_mass A (ω n)).symm

/-- Counts of the superposition on disjoint regions are independent. -/
theorem superposed_independent_counts {J : Type*} [Fintype J]
    (A : J → Set ExtremeState) (hA : ∀ j, MeasurableSet (A j))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    iIndepFun (fun j ω => (randomMeasure.toFun ω).toMeasure (A j)) (law υ hυ) := by
  let X : ℕ → J → Sample → ℝ≥0∞ := fun n j ω =>
    (FinitePoissonCloud.pointMeasure (ω n)).toMeasure (A j)
  have hm (n : ℕ) (j : J) : Measurable (X n j) :=
    (measurable_cloud_evaluation (A j) (hA j)).comp (measurable_pi_apply n)
  have hrows : iIndepFun (fun n ω j => X n j ω) (law υ hυ) :=
    iIndepFun_infinitePi (fun _ => Measurable.of_eval
      (fun j => measurable_cloud_evaluation (A j) (hA j)))
  have hwithin (n : ℕ) : iIndepFun (X n) (law υ hυ) := by
    have hi := (FinitePoissonCloud.independent_counts
      (componentIntensity υ hυ n).mass (componentIntensity υ hυ n).normalize A hA hd).comp
      (fun _ => ENNReal.ofReal) (fun _ => measurable_id.ennreal_ofReal)
    have hi' : iIndepFun (fun j ω => (FinitePoissonCloud.pointMeasure ω).toMeasure (A j))
        (componentLaw υ hυ n) := by
      convert hi using 1
      · funext j ω
        simpa only [Function.comp_def, ENNReal.ofReal_natCast] using
          (FinitePoissonCloud.count_eq_mass (A j) ω).symm
      · rfl
    exact independent_pullback (law υ hυ) (componentLaw υ hυ n) (fun ω => ω n)
      (measurable_pi_apply n) ⟨(measurable_pi_apply n).aemeasurable,
        Measure.infinitePi_map_eval (componentLaw υ hυ) n⟩
      _ (fun j => measurable_cloud_evaluation (A j) (hA j)) hi'
  apply (independent_countable_sums (law υ hυ) X hm hrows hwithin).congr
  intro j
  filter_upwards [randomMeasure_apply_ae υ hυ] with ω hω
  exact (hω (A j)).symm

/-- The annular construction is a Poisson random measure with the prescribed
locally finite intensity. -/
theorem isPoissonRandomMeasure :
    IsPoissonRandomMeasure randomMeasure (law υ hυ) υ :=
  ⟨hυ, superposed_count_hasLaw υ hυ,
    fun _ A hA hd _ => superposed_independent_counts υ hυ A hA hd⟩

end
end ConditionedStableLaws.AnnularPoissonClouds

namespace ConditionedStableLaws

/-- Existence for every locally finite intensity, on an explicit countable product probability
space. -/
theorem exists_poisson_random_measure (υ : Measure ExtremeState)
    (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞) :
    ∃ P : Measure AnnularPoissonClouds.Sample, ∃ _ : IsProbabilityMeasure P,
      ∃ N : RandomPointMeasure AnnularPoissonClouds.Sample, IsPoissonRandomMeasure N P υ :=
  ⟨AnnularPoissonClouds.law υ hυ, inferInstance, AnnularPoissonClouds.randomMeasure,
    AnnularPoissonClouds.isPoissonRandomMeasure υ hυ⟩

end ConditionedStableLaws
