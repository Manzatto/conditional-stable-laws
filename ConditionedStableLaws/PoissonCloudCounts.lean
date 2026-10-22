import ConditionedStableLaws.FinitePoissonCloud
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
Poisson count laws for the finite marked-cloud construction.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.FinitePoissonCloud
noncomputable section

def count (A : Set ExtremeState) (ω : Sample) : ℕ :=
  ∑ i : Fin ω.1, A.indicator (fun _ => 1) (ω.2 i)

theorem measurable_count (A : Set ExtremeState) (hA : MeasurableSet A) : Measurable (count A) := by
  apply measurable_of_sigma
  intro n
  change Measurable (fun a : Fin n → ExtremeState => ∑ i, A.indicator (fun _ => (1 : ℕ)) (a i))
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_const.indicator hA).comp (measurable_pi_apply i))

theorem count_eq_mass (A : Set ExtremeState) (ω : Sample) :
    (count A ω : ℝ≥0∞) = (pointMeasure ω).toMeasure A := by
  classical
  rw [pointMeasure, LocallyFinitePointMeasure.empirical_apply]
  simp only [count, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ω.2 i ∈ A <;> simp [hi]

theorem integral_indicator_count (A : Set ExtremeState) (t : ℝ) (ω : Sample) :
    (∫ x, A.indicator (fun _ => t) x ∂(pointMeasure ω).toMeasure) = t * count A ω := by
  classical
  rw [pointMeasure, LocallyFinitePointMeasure.integral_empirical]
  simp only [count, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ω.2 i ∈ A <;> simp [hi]

theorem integral_exp_indicator (ν : ProbabilityMeasure ExtremeState)
    (A : Set ExtremeState) (hA : MeasurableSet A) (t : ℝ) :
    (∫ x, Complex.exp ((A.indicator (fun _ => t) x : ℝ) * Complex.I)
      ∂(ν : Measure ExtremeState)) =
        1 + (ν : Measure ExtremeState).real A * (Complex.exp (t * Complex.I) - 1) := by
  have heq : (fun x => Complex.exp ((A.indicator (fun _ => t) x : ℝ) * Complex.I)) =
      fun x => (1 : ℂ) + A.indicator (fun _ => Complex.exp (t * Complex.I) - 1) x := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [heq, integral_add (integrable_const _)
    ((integrable_const _).indicator hA), integral_const, integral_indicator_const _ hA]
  simp

/-- Every measurable region has a Poisson count, with rate equal to its
finite-cloud intensity. This is thinning derived from the marked-cloud law. -/
theorem count_hasLaw (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (A : Set ExtremeState) (hA : MeasurableSet A) :
    HasLaw (count A) (poissonMeasure (r * ((ν : Measure ExtremeState) A).toNNReal)) (law r ν) := by
  refine ⟨(measurable_count A hA).aemeasurable, ?_⟩
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [Measure.map_map (by fun_prop) (measurable_count A hA)]
  simp only [Function.comp_def]
  have hm : Measurable (fun ω => (count A ω : ℝ)) :=
    (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp (measurable_count A hA)
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_cast_poissonMeasure, charFun_apply_real,
    integral_map hm.aemeasurable (by fun_prop)]
  have he := characteristic_functional r ν (A.indicator (fun _ => t))
    (measurable_const.indicator hA)
  simp_rw [integral_indicator_count A t] at he
  rw [integral_exp_indicator ν A hA t] at he
  calc
    _ = Complex.exp ((r : ℂ) *
        ((1 + (ν : Measure ExtremeState).real A * (Complex.exp (t * Complex.I) - 1)) - 1)) := by
      simpa only [Function.comp_def, Complex.ofReal_mul] using he
    _ = _ := by
      simp only [NNReal.coe_mul, Measure.real_def]
      push_cast
      ring_nf

theorem integral_exp_disjoint {J : Type*} [Fintype J]
    (ν : ProbabilityMeasure ExtremeState) (A : J → Set ExtremeState)
    (hA : ∀ j, MeasurableSet (A j)) (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (t : J → ℝ) :
    (∫ x, Complex.exp ((∑ j, (A j).indicator (fun _ => t j) x : ℝ) * Complex.I)
      ∂(ν : Measure ExtremeState)) =
        1 + ∑ j, (ν : Measure ExtremeState).real (A j) * (Complex.exp (t j * Complex.I) - 1) := by
  classical
  have heq : (fun x => Complex.exp ((∑ j, (A j).indicator (fun _ => t j) x : ℝ) * Complex.I)) =
      fun x => (1 : ℂ) + ∑ j, (A j).indicator (fun _ => Complex.exp (t j * Complex.I) - 1) x := by
    funext x
    by_cases hx : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := hx
      have hout (j : J) (hj : j ≠ i) : x ∉ A j := fun hxj =>
        Set.disjoint_left.mp (hd hj) hxj hi
      rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji; simp [hout j hji]
      · simp
      · intro j _ hji; simp [hout j hji]
      · simp
    · have hout (j : J) : x ∉ A j := fun hj => hx ⟨j,hj⟩
      simp [hout]
  have hint (j : J) : Integrable
      ((A j).indicator (fun _ => Complex.exp (t j * Complex.I) - 1)) (ν : Measure ExtremeState) :=
    (integrable_const _).indicator (hA j)
  rw [heq, integral_add (integrable_const _) (integrable_finsetSum _ (fun j _ => hint j)),
    integral_const, integral_finsetSum _ (fun j _ => hint j)]
  simp_rw [integral_indicator_const _ (hA _)]
  simp

theorem integral_sum_indicator_count {J : Type*} [Fintype J]
    (A : J → Set ExtremeState) (t : J → ℝ) (ω : Sample) :
    (∫ x, ∑ j, (A j).indicator (fun _ => t j) x ∂(pointMeasure ω).toMeasure) =
      ∑ j, t j * count (A j) ω := by
  rw [pointMeasure, LocallyFinitePointMeasure.integral_empirical, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [pointMeasure, LocallyFinitePointMeasure.integral_empirical] using
    integral_indicator_count (A j) (t j) ω

theorem characteristic_disjoint_counts {J : Type*} [Fintype J]
    (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState) (A : J → Set ExtremeState)
    (hA : ∀ j, MeasurableSet (A j)) (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (t : J → ℝ) :
    (∫ ω, Complex.exp ((∑ j, t j * count (A j) ω : ℝ) * Complex.I) ∂law r ν) =
      ∏ j, Complex.exp ((r : ℂ) * (ν : Measure ExtremeState).real (A j) *
        (Complex.exp (t j * Complex.I) - 1)) := by
  have he := characteristic_functional r ν (fun x => ∑ j, (A j).indicator (fun _ => t j) x)
    (Finset.measurable_sum _ (fun j _ => measurable_const.indicator (hA j)))
  simp_rw [integral_sum_indicator_count A t] at he
  rw [integral_exp_disjoint ν A hA hd t] at he
  rw [he, ← Complex.exp_sum]
  congr 1
  rw [add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem charFun_count (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState)
    (A : Set ExtremeState) (hA : MeasurableSet A) (t : ℝ) :
    charFun ((law r ν).map (fun ω => (count A ω : ℝ))) t =
      Complex.exp ((r : ℂ) * (ν : Measure ExtremeState).real A *
        (Complex.exp (t * Complex.I) - 1)) := by
  have hm : Measurable (fun ω => (count A ω : ℝ)) :=
    (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp (measurable_count A hA)
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  have he := characteristic_functional r ν (A.indicator (fun _ => t))
    (measurable_const.indicator hA)
  simp_rw [integral_indicator_count A t] at he
  rw [integral_exp_indicator ν A hA t, add_sub_cancel_left] at he
  simpa only [Complex.ofReal_mul, mul_assoc] using he

/-- Counts in disjoint measurable regions are jointly independent. -/
theorem independent_counts {J : Type*} [Fintype J]
    (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState) (A : J → Set ExtremeState)
    (hA : ∀ j, MeasurableSet (A j)) (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    iIndepFun (fun j ω => (count (A j) ω : ℝ)) (law r ν) := by
  have hm (j : J) : Measurable (fun ω => (count (A j) ω : ℝ)) :=
    (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp (measurable_count (A j) (hA j))
  apply (iIndepFun_iff_charFun_pi (fun j => (hm j).aemeasurable)).mpr
  intro t
  have hmv : Measurable (fun ω => WithLp.toLp 2 (fun j => (count (A j) ω : ℝ))) :=
    (MeasurableEquiv.toLp 2 (J → ℝ)).measurable.comp (Measurable.of_eval hm)
  rw [charFun_apply, integral_map hmv.aemeasurable (by fun_prop)]
  simp_rw [PiLp.inner_apply, Real.inner_apply, charFun_count r ν _ (hA _) (t _)]
  convert characteristic_disjoint_counts r ν A hA hd (fun j => t j) using 1
  congr 1
  funext ω
  simp [mul_comm]

/-- The finite marked cloud is a Poisson random measure. -/
theorem isPoissonRandomMeasure (r : ℝ≥0) (ν : ProbabilityMeasure ExtremeState) :
    IsPoissonRandomMeasure randomPointMeasure (law r ν)
      ((r : ℝ≥0∞) • (ν : Measure ExtremeState)) := by
  have : IsFiniteMeasure ((r : ℝ≥0∞) • (ν : Measure ExtremeState)) :=
    (ν : Measure ExtremeState).smul_finite ENNReal.coe_ne_top
  refine ⟨fun ε _ => measure_lt_top _ _, ?_, ?_⟩
  · intro A hA _
    have hc := (hasLaw_map (P := poissonMeasure (r * ((ν : Measure ExtremeState) A).toNNReal))
      (show AEMeasurable (fun n : ℕ => (n : ℝ≥0∞)) _ by fun_prop)).comp (count_hasLaw r ν A hA)
    have heq : (fun ω => (pointMeasure ω).toMeasure A) =
        (fun n : ℕ => (n : ℝ≥0∞)) ∘ count A := by
      funext ω
      exact (count_eq_mass A ω).symm
    change HasLaw (fun ω => (pointMeasure ω).toMeasure A) _ _
    rw [heq]
    convert hc using 1
    simp [poissonCountLaw, Measure.smul_apply, ENNReal.toNNReal_mul]
  · intro n A hA hd _
    have hi := (independent_counts r ν A hA hd).comp (fun _ => ENNReal.ofReal)
      (fun _ => measurable_id.ennreal_ofReal)
    convert hi using 1
    funext j ω
    change (pointMeasure ω).toMeasure (A j) = ENNReal.ofReal (count (A j) ω : ℝ)
    simpa only [ENNReal.ofReal_natCast] using (count_eq_mass (A j) ω).symm

/-- Existence for every finite intensity, including the zero intensity. -/
theorem exists_for_finite_intensity (υ : Measure ExtremeState) [IsFiniteMeasure υ] :
    ∃ P : Measure Sample, ∃ _ : IsProbabilityMeasure P,
      IsPoissonRandomMeasure randomPointMeasure P υ := by
  have : Nonempty ExtremeState := ⟨⟨1, by simp⟩⟩
  let v : FiniteMeasure ExtremeState := ⟨υ, inferInstance⟩
  have he : (v.mass : ℝ≥0∞) • (v.normalize : Measure ExtremeState) = υ := by
    exact congrArg (fun w : FiniteMeasure ExtremeState => (w : Measure ExtremeState))
      v.self_eq_mass_smul_normalize.symm
  refine ⟨law v.mass v.normalize, inferInstance, ?_⟩
  rw [← he]
  exact isPoissonRandomMeasure v.mass v.normalize

end
end ConditionedStableLaws.FinitePoissonCloud
