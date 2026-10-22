import ConditionedStableLaws.MethodOfMoments
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Convergence of moment generating functions

If the moment generating functions of real laws converge at every real
point to the (everywhere finite) moment generating function of a limit law,
the laws converge weakly. Tightness comes from the exponential moments, a
weak subsequential limit inherits the limiting moment generating function by
the uniform square bound, and complex moment generating functions separate
laws. This is the form of the continuity theorem used for the conditional
central limit theorems.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace ConditionedStableLaws

noncomputable section

theorem tendsto_of_mgf_tendsto (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hi : ∀ n (s : ℝ), Integrable (fun x => Real.exp (s * x)) (μ n : Measure ℝ))
    (_hν : ∀ s : ℝ, Integrable (fun x => Real.exp (s * x)) (ν : Measure ℝ))
    (hm : ∀ s : ℝ, Tendsto (fun n => ∫ x, Real.exp (s * x) ∂(μ n : Measure ℝ)) atTop
      (𝓝 (∫ x, Real.exp (s * x) ∂(ν : Measure ℝ)))) :
    Tendsto μ atTop (𝓝 ν) := by
  -- Tightness from the exponential moments at `±1`.
  have habs (x : ℝ) : ‖x‖ ≤ Real.exp (1 * x) + Real.exp (-1 * x) := by
    rw [Real.norm_eq_abs, one_mul, neg_one_mul]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      linarith [Real.add_one_le_exp x, Real.exp_pos (-x)]
    · rw [abs_of_nonpos hx]
      linarith [Real.add_one_le_exp (-x), Real.exp_pos x]
  obtain ⟨C1, hC1⟩ := (hm 1).bddAbove_range
  obtain ⟨C2, hC2⟩ := (hm (-1)).bddAbove_range
  have hint (n : ℕ) : Integrable (fun x : ℝ => x) (μ n : Measure ℝ) :=
    ((hi n 1).add (hi n (-1))).mono' continuous_id.aestronglyMeasurable
      (Eventually.of_forall fun x => habs x)
  have hnorm (n : ℕ) : (∫ x : ℝ, ‖x‖ ∂(μ n : Measure ℝ)) ≤ C1 + C2 := by
    calc (∫ x : ℝ, ‖x‖ ∂(μ n : Measure ℝ))
        ≤ ∫ x, (Real.exp (1 * x) + Real.exp (-1 * x)) ∂(μ n : Measure ℝ) :=
          integral_mono (hint n).norm ((hi n 1).add (hi n (-1))) habs
      _ = (∫ x, Real.exp (1 * x) ∂(μ n : Measure ℝ)) +
          ∫ x, Real.exp (-1 * x) ∂(μ n : Measure ℝ) := integral_add (hi n 1) (hi n (-1))
      _ ≤ C1 + C2 := add_le_add (hC1 (Set.mem_range_self n)) (hC2 (Set.mem_range_self n))
  have ht := isTight_range_of_norm_integral_bound μ hint hnorm
  have hcompact : IsCompact (closure (Set.range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert ht using 1
    ext P
    simp
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν', _, ms, hms, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self (ns n)))
  -- The subsequential limit has the limiting moment generating function.
  have hmgf (s : ℝ) : Integrable (fun x => Real.exp (s * x)) (ν' : Measure ℝ) ∧
      (∫ x, Real.exp (s * x) ∂(ν' : Measure ℝ)) = ∫ x, Real.exp (s * x) ∂(ν : Measure ℝ) := by
    obtain ⟨C, hC⟩ := (hm (2 * s)).bddAbove_range
    have hsq (y : ℝ) : Real.exp (s * y) ^ 2 = Real.exp (2 * s * y) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h := integral_tendsto_of_weak_tendsto_of_square_bound
      (f := fun x => Real.exp (s * x)) hlim
      ((continuous_const.mul continuous_id).rexp) (fun k => hi (ns (ms k)) s)
      (fun k => (hi (ns (ms k)) (2 * s)).congr (Eventually.of_forall fun y => (hsq y).symm))
      (C := C) (fun k => by
        rw [integral_congr_ae (Eventually.of_forall fun y => hsq y)]
        exact hC (Set.mem_range_self _))
    refine ⟨h.1, tendsto_nhds_unique h.2 ?_⟩
    exact (hm s).comp (hns.comp hms.tendsto_atTop)
  have hmgf_eq : mgf id (ν' : Measure ℝ) = mgf id (ν : Measure ℝ) := by
    funext s
    simp only [mgf, id]
    exact (hmgf s).2
  have hset : integrableExpSet id (ν' : Measure ℝ) = Set.univ := by
    ext s
    simp only [integrableExpSet, id, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (hmgf s).1
  have hc := eqOn_complexMGF_of_mgf hmgf_eq
  rw [hset, interior_univ] at hc
  have heq : (ν' : Measure ℝ) = (ν : Measure ℝ) :=
    Measure.ext_of_complexMGF_id_eq (funext fun z => hc (by simp))
  have : ν' = ν := Subtype.ext heq
  exact ⟨ms, this ▸ hlim⟩

/-- Random-variable form: convergence of the moment generating functions at
every real point gives convergence in distribution. -/
theorem tendstoInDistribution_of_mgf_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω' : Type*} [MeasurableSpace Ω']
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q] (X : (n : ℕ) → Ω n → ℝ) (Y : Ω' → ℝ)
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hY : AEMeasurable Y Q)
    (hi : ∀ n (s : ℝ), Integrable (fun ω => Real.exp (s * X n ω)) (P n))
    (hYi : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * Y ω)) Q)
    (hm : ∀ s : ℝ, Tendsto (fun n => ∫ ω, Real.exp (s * X n ω) ∂P n) atTop
      (𝓝 (∫ ω, Real.exp (s * Y ω) ∂Q))) :
    TendstoInDistribution X atTop Y P Q := by
  refine ⟨hX, hY, ?_⟩
  have hcont (s : ℝ) : Continuous fun x : ℝ => Real.exp (s * x) :=
    (continuous_const.mul continuous_id).rexp
  refine tendsto_of_mgf_tendsto _ _ (fun n s => ?_) (fun s => ?_) (fun s => ?_)
  · exact (integrable_map_measure (hcont s).aestronglyMeasurable (hX n)).2 (hi n s)
  · exact (integrable_map_measure (hcont s).aestronglyMeasurable hY).2 (hYi s)
  · have hmap (n : ℕ) : (∫ x : ℝ, Real.exp (s * x) ∂(P n).map (X n)) =
        ∫ ω, Real.exp (s * X n ω) ∂P n := integral_map (hX n) (hcont s).aestronglyMeasurable
    have hmapY : (∫ x : ℝ, Real.exp (s * x) ∂Q.map Y) = ∫ ω, Real.exp (s * Y ω) ∂Q :=
      integral_map hY (hcont s).aestronglyMeasurable
    simpa only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, hmap, hmapY] using hm s

/-- Convergence to a centred Gaussian law from convergence of the moment
generating functions to `exp(v s²/2)`. -/
theorem tendstoInDistribution_gaussian_of_mgf_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] (X : (n : ℕ) → Ω n → ℝ)
    (hX : ∀ n, AEMeasurable (X n) (P n)) (v : NNReal)
    (hi : ∀ n (s : ℝ), Integrable (fun ω => Real.exp (s * X n ω)) (P n))
    (hm : ∀ s : ℝ, Tendsto (fun n => ∫ ω, Real.exp (s * X n ω) ∂P n) atTop
      (𝓝 (Real.exp (v * s ^ 2 / 2)))) :
    TendstoInDistribution X atTop id P (gaussianReal 0 v) := by
  refine tendstoInDistribution_of_mgf_tendsto P (gaussianReal 0 v) X id hX aemeasurable_id hi
    (fun s => by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) s) (fun s => ?_)
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) s
  simp only [mgf, id, zero_mul, zero_add] at this
  simp only [id]
  rw [this]
  exact hm s

end

end ConditionedStableLaws
