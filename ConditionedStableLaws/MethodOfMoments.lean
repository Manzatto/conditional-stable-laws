import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
# The method of moments on the real line

Moment determinacy means uniqueness among probability measures with all moments.
The proof obtains compactness from moment bounds and transfers moments through
bounded continuous truncations; determinacy is used only to identify a limit.
-/

open Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws

noncomputable section

/-- Every natural power is Bochner integrable. -/
def HasAllRealMoments (μ : Measure ℝ) : Prop :=
  ∀ r : ℕ, Integrable (fun x : ℝ => x ^ r) μ

/-- Uniqueness from moments among probability laws with all moments. -/
def MomentDeterminate (μ : ProbabilityMeasure ℝ) : Prop :=
  HasAllRealMoments (μ : Measure ℝ) ∧
    ∀ ν : ProbabilityMeasure ℝ, HasAllRealMoments (ν : Measure ℝ) →
      (∀ r : ℕ, (∫ x : ℝ, x ^ r ∂(ν : Measure ℝ)) =
        ∫ x : ℝ, x ^ r ∂(μ : Measure ℝ)) → ν = μ

private def momentClip (R y : ℝ) : ℝ := max (-R) (min R y)

private theorem abs_momentClip_le (R y : ℝ) (hR : 0 ≤ R) :
    |momentClip R y| ≤ R := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private theorem momentClip_eq (R y : ℝ) (hy : |y| ≤ R) : momentClip R y = y := by
  rw [abs_le] at hy
  simp [momentClip, min_eq_right hy.2, max_eq_right hy.1]

private theorem abs_momentClip_le_abs (R y : ℝ) (hR : 0 ≤ R) :
    |momentClip R y| ≤ |y| := by
  by_cases hy : |y| ≤ R
  · rw [momentClip_eq R y hy]
  · exact (abs_momentClip_le R y hR).trans (le_of_not_ge hy)

private theorem momentClip_error_le (R y : ℝ) (hR : 0 < R) :
    |y - momentClip R y| ≤ y ^ 2 / R := by
  by_cases hy : |y| ≤ R
  · rw [momentClip_eq R y hy, sub_self, abs_zero]
    positivity
  · have hyR : R < |y| := lt_of_not_ge hy
    by_cases hy0 : 0 ≤ y
    · have hRy : R < y := by simpa [abs_of_nonneg hy0] using hyR
      have hclip : momentClip R y = R := by
        simp [momentClip, min_eq_left hRy.le, max_eq_right (by linarith : -R ≤ R)]
      rw [hclip, abs_of_nonneg (by linarith), le_div_iff₀ hR]
      nlinarith [sq_nonneg (y - R)]
    · have hRy : y < -R := by
        rw [abs_of_neg (lt_of_not_ge hy0)] at hyR
        linarith
      have hclip : momentClip R y = -R := by
        simp [momentClip, min_eq_right (by linarith : y ≤ R), max_eq_left hRy.le]
      rw [hclip, abs_of_neg (by linarith), le_div_iff₀ hR]
      nlinarith [sq_nonneg (y + R)]

private def clippedContinuous (f : ℝ → ℝ) (hf : Continuous f) (R : ℝ) (hR : 0 ≤ R) :
    ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => momentClip R (f x), continuous_const.max (continuous_const.min hf)⟩
    (2 * R) (by
      intro x y
      calc
        dist (momentClip R (f x)) (momentClip R (f y))
            ≤ |momentClip R (f x)| + |momentClip R (f y)| := by
              simpa [Real.dist_eq] using abs_sub (momentClip R (f x)) (momentClip R (f y))
        _ ≤ 2 * R := by linarith [abs_momentClip_le R (f x) hR,
            abs_momentClip_le R (f y) hR])

private theorem momentClip_tendsto (y : ℝ) :
    Tendsto (fun n : ℕ => momentClip (n + 1) y) atTop (𝓝 y) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge |y|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  exact (momentClip_eq (n + 1) y (by linarith)).symm

/-- An integral norm bound survives weak convergence for a continuous function.
This also proves integrability under the limiting law. -/
theorem integrable_limit_of_weak_tendsto
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hμ : Tendsto μ atTop (𝓝 ν)) {f : ℝ → ℝ} (hf : Continuous f)
    (hfi : ∀ n, Integrable f (μ n : Measure ℝ)) {C : ℝ}
    (hC : ∀ n, (∫ x, ‖f x‖ ∂(μ n : Measure ℝ)) ≤ C) :
    Integrable f (ν : Measure ℝ) ∧ (∫ x, ‖f x‖ ∂(ν : Measure ℝ)) ≤ C := by
  let g (R : ℕ) := clippedContinuous f hf (R + 1) (by positivity)
  have hg_le (R : ℕ) (x : ℝ) : ‖g R x‖ ≤ ‖f x‖ :=
    abs_momentClip_le_abs (R + 1) (f x) (by positivity)
  have hg_tend (x : ℝ) : Tendsto (fun R => g R x) atTop (𝓝 (f x)) :=
    momentClip_tendsto (f x)
  have hg_bound (R : ℕ) : (∫ x, ‖g R x‖ ∂(ν : Measure ℝ)) ≤ C := by
    apply le_of_tendsto
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (g R).normComp)
    exact .of_forall fun n => (integral_mono ((g R).integrable (μ := (μ n : Measure ℝ))).norm (hfi n).norm
      (hg_le R)).trans (hC n)
  have hlim : Integrable f (ν : Measure ℝ) := by
    apply integrable_of_tendsto (.of_forall hg_tend)
      (fun R => (g R).continuous.aestronglyMeasurable)
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply liminf_le_of_frequently_le'
    · exact Frequently.of_forall fun R => by
        rw [← ofReal_integral_norm_eq_lintegral_enorm ((g R).integrable (μ := (ν : Measure ℝ)))]
        exact ENNReal.ofReal_le_ofReal (hg_bound R)
  refine ⟨hlim, ?_⟩
  apply le_of_tendsto (tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun R => (g R).continuous.norm.aestronglyMeasurable) hlim.norm
    (fun R => .of_forall fun x => by simpa using hg_le R x)
    (.of_forall fun x => (hg_tend x).norm))
  exact .of_forall hg_bound

private theorem integral_momentClip_error_le {P : Measure ℝ} [IsFiniteMeasure P]
    {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f P)
    (hf2 : Integrable (fun x => f x ^ 2) P) {C R : ℝ}
    (hC : (∫ x, f x ^ 2 ∂P) ≤ C) (hR : 0 < R) :
    |(∫ x, f x ∂P) - ∫ x, momentClip R (f x) ∂P| ≤ C / R := by
  have hgi : Integrable (fun x => momentClip R (f x)) P :=
    (clippedContinuous f hf R hR.le).integrable (μ := P)
  rw [← integral_sub hfi hgi]
  calc
    |∫ x, f x - momentClip R (f x) ∂P|
        ≤ ∫ x, f x ^ 2 / R ∂P :=
      by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_of_norm_le (f := fun x => f x - momentClip R (f x))
            (hf2.div_const R) (.of_forall fun x => momentClip_error_le R (f x) hR)
    _ = (∫ x, f x ^ 2 ∂P) / R := integral_div R _
    _ ≤ C / R := div_le_div_of_nonneg_right hC hR.le

/-- Weak convergence plus a uniform second-moment bound for a continuous
observable implies convergence of its expectations. -/
theorem integral_tendsto_of_weak_tendsto_of_square_bound
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hμ : Tendsto μ atTop (𝓝 ν)) {f : ℝ → ℝ} (hf : Continuous f)
    (hfi : ∀ n, Integrable f (μ n : Measure ℝ))
    (hf2 : ∀ n, Integrable (fun x => f x ^ 2) (μ n : Measure ℝ)) {C : ℝ}
    (hC : ∀ n, (∫ x, f x ^ 2 ∂(μ n : Measure ℝ)) ≤ C) :
    Integrable f (ν : Measure ℝ) ∧
      Tendsto (fun n => ∫ x, f x ∂(μ n : Measure ℝ)) atTop
        (𝓝 (∫ x, f x ∂(ν : Measure ℝ))) := by
  have habs (y : ℝ) : ‖y‖ ≤ 1 + y ^ 2 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
  have hbound (n : ℕ) : (∫ x, ‖f x‖ ∂(μ n : Measure ℝ)) ≤ 1 + C := by
    calc
      _ ≤ ∫ x, 1 + f x ^ 2 ∂(μ n : Measure ℝ) :=
        integral_mono (hfi n).norm ((integrable_const 1).add (hf2 n)) (fun x => habs _)
      _ = 1 + ∫ x, f x ^ 2 ∂(μ n : Measure ℝ) := by
        rw [integral_add (integrable_const 1) (hf2 n)]
        simp
      _ ≤ 1 + C := by linarith [hC n]
  have hνi := (integrable_limit_of_weak_tendsto hμ hf hfi hbound).1
  refine ⟨hνi, ?_⟩
  let g (R : ℕ) := clippedContinuous f hf (R + 1) (by positivity)
  have hB : Tendsto (fun R => ∫ x, g R x ∂(ν : Measure ℝ)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun R => (g R).continuous.aestronglyMeasurable) hνi.norm
      (fun R => .of_forall fun x => abs_momentClip_le_abs (R + 1) (f x) (by positivity))
    exact .of_forall fun x => momentClip_tendsto (f x)
  have hrem : Tendsto (fun R : ℕ => C / (R + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨R, hBR, hCR⟩ := ((Metric.tendsto_nhds.mp hB) (ε / 3) hε3).and
    ((Metric.tendsto_nhds.mp hrem) (ε / 3) hε3) |>.exists
  have hg := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (g R)
  filter_upwards [(Metric.tendsto_nhds.mp hg) (ε / 3) hε3] with n hgn
  simp only [Real.dist_eq, sub_zero] at hBR hCR hgn ⊢
  have herr : |(∫ x, f x ∂(μ n : Measure ℝ)) - ∫ x, g R x ∂(μ n : Measure ℝ)|
      ≤ C / (R + 1) :=
    integral_momentClip_error_le hf (hfi n) (hf2 n) (hC n) (by positivity)
  have htri := abs_add_le
    ((∫ x, f x ∂(μ n : Measure ℝ)) - ∫ x, g R x ∂(μ n : Measure ℝ))
    ((∫ x, g R x ∂(μ n : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ))
  have htri' := abs_add_le
    ((∫ x, g R x ∂(μ n : Measure ℝ)) - ∫ x, g R x ∂(ν : Measure ℝ))
    ((∫ x, g R x ∂(ν : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ))
  simp only [sub_add_sub_cancel] at htri htri'
  linarith [(le_abs_self (C / (R + 1))).trans_lt hCR]

/-- Uniform first absolute moments give tightness of a family of real laws. -/
theorem isTight_range_of_norm_integral_bound (μ : ℕ → ProbabilityMeasure ℝ)
    (hi : ∀ n, Integrable (fun x : ℝ => x) (μ n : Measure ℝ)) {C : ℝ}
    (hC : ∀ n, (∫ x : ℝ, ‖x‖ ∂(μ n : Measure ℝ)) ≤ C) :
    IsTightMeasureSet (Set.range fun n => (μ n : Measure ℝ)) := by
  have hC0 : 0 ≤ C := (integral_nonneg fun x => norm_nonneg x).trans (hC 0)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hδ : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  let R : ℝ := (C + 1) / δ
  have hR : 0 < R := div_pos (by linarith) hδ
  refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (μ n : Measure ℝ)) (.of_forall fun x => norm_nonneg x) (hi n).norm R
  have hsub : (Set.Icc (-R) R)ᶜ ⊆ {x : ℝ | R ≤ ‖x‖} := by
    intro x hx
    have hx' : ¬ |x| ≤ R := by simpa [abs_le, Set.mem_Icc] using hx
    exact (lt_of_not_ge hx').le
  have hreal : (μ n : Measure ℝ).real (Set.Icc (-R) R)ᶜ ≤ δ := by
    have hm := measureReal_mono (μ := (μ n : Measure ℝ)) hsub
    have hmul : R * (δ : ℝ) = C + 1 := by dsimp [R]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hm hR.le, hC n]
  calc
    (μ n : Measure ℝ) (Set.Icc (-R) R)ᶜ
        = ENNReal.ofReal ((μ n : Measure ℝ).real (Set.Icc (-R) R)ᶜ) :=
      (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ε := by simpa using hδε.le

/-- Convergent second moments make the closure of a sequence of real
probability laws compact in the weak topology. -/
theorem compact_closure_of_second_moment_tendsto (μ : ℕ → ProbabilityMeasure ℝ)
    (hi : ∀ n, HasAllRealMoments (μ n : Measure ℝ)) {m : ℝ}
    (hm : Tendsto (fun n => ∫ x : ℝ, x ^ 2 ∂(μ n : Measure ℝ)) atTop (𝓝 m)) :
    IsCompact (closure (Set.range μ)) := by
  obtain ⟨C, hC⟩ := hm.bddAbove_range
  have hnorm (n : ℕ) : (∫ x : ℝ, ‖x‖ ∂(μ n : Measure ℝ)) ≤ 1 + C := by
    calc
      _ ≤ ∫ x : ℝ, 1 + x ^ 2 ∂(μ n : Measure ℝ) := by
        apply integral_mono (by simpa only [pow_one] using (hi n 1).norm)
          ((integrable_const 1).add (hi n 2))
        intro x
        change ‖x‖ ≤ 1 + x ^ 2
        rw [Real.norm_eq_abs]
        nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
      _ = 1 + ∫ x : ℝ, x ^ 2 ∂(μ n : Measure ℝ) := by
        rw [integral_add (integrable_const 1) (hi n 2)]
        simp
      _ ≤ 1 + C := by linarith [hC (Set.mem_range_self n)]
  have ht := isTight_range_of_norm_integral_bound μ (fun n => by simpa using hi n 1) hnorm
  apply isCompact_closure_of_isTightMeasureSet
  convert ht using 1
  ext P
  simp

/-- Each weak subsequential limit has all the prescribed moments. -/
theorem moments_of_weak_tendsto
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hμ : Tendsto μ atTop (𝓝 ν)) (hi : ∀ n, HasAllRealMoments (μ n : Measure ℝ))
    {m : ℕ → ℝ}
    (hm : ∀ r, Tendsto (fun n => ∫ x : ℝ, x ^ r ∂(μ n : Measure ℝ)) atTop (𝓝 (m r))) :
    HasAllRealMoments (ν : Measure ℝ) ∧
      ∀ r, (∫ x : ℝ, x ^ r ∂(ν : Measure ℝ)) = m r := by
  have htransfer (r : ℕ) : Integrable (fun x : ℝ => x ^ r) (ν : Measure ℝ) ∧
      Tendsto (fun n => ∫ x : ℝ, x ^ r ∂(μ n : Measure ℝ)) atTop
        (𝓝 (∫ x : ℝ, x ^ r ∂(ν : Measure ℝ))) := by
    obtain ⟨C, hC⟩ := (hm (r * 2)).bddAbove_range
    apply integral_tendsto_of_weak_tendsto_of_square_bound hμ (continuous_id.pow r)
      (fun n => hi n r) (fun n => by simpa [pow_mul] using hi n (r * 2))
    intro n
    simpa [pow_mul] using hC (Set.mem_range_self n)
  exact ⟨fun r => (htransfer r).1, fun r => tendsto_nhds_unique (htransfer r).2 (hm r)⟩

/-- **The method of moments.** If all moments converge to those of a moment-determinate real
probability law, the laws converge weakly. -/
theorem method_of_moments (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hi : ∀ n, HasAllRealMoments (μ n : Measure ℝ)) (hν : MomentDeterminate ν)
    (hm : ∀ r : ℕ, Tendsto (fun n => ∫ x : ℝ, x ^ r ∂(μ n : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x ^ r ∂(ν : Measure ℝ)))) :
    Tendsto μ atTop (𝓝 ν) := by
  have hcompact := compact_closure_of_second_moment_tendsto μ hi (hm 2)
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν', _, ms, hms, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self (ns n)))
  have hmoment := moments_of_weak_tendsto hlim
    (fun n => hi (ns (ms n))) (fun r => (hm r).comp (hns.comp hms.tendsto_atTop))
  have heq : ν' = ν := hν.2 ν' hmoment.1 hmoment.2
  exact ⟨ms, heq ▸ hlim⟩

/-- Random-variable form of the method of moments, allowing the probability
space and its law to vary with the sequence index. -/
theorem method_of_moments_inDistribution
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : (n : ℕ) → Ω n → ℝ) (Y : Ω' → ℝ)
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hY : AEMeasurable Y Q)
    (hi : ∀ n (r : ℕ), Integrable (fun ω => X n ω ^ r) (P n))
    (hYdet : MomentDeterminate
      (ProbabilityMeasure.map (⟨Q, inferInstance⟩ : ProbabilityMeasure Ω') Y))
    (hm : ∀ r : ℕ, Tendsto (fun n => ∫ ω, X n ω ^ r ∂P n) atTop
      (𝓝 (∫ ω, Y ω ^ r ∂Q))) :
    TendstoInDistribution X atTop Y P Q := by
  refine ⟨hX, hY, ?_⟩
  refine method_of_moments _ _ ?_ hYdet ?_
  · intro n r
    exact (integrable_map_measure (by fun_prop) (hX n)).2 (hi n r)
  · intro r
    have hmap (n : ℕ) : (∫ x : ℝ, x ^ r ∂(P n).map (X n)) =
        ∫ ω, X n ω ^ r ∂P n := integral_map (hX n) (by fun_prop)
    have hmap' : (∫ x : ℝ, x ^ r ∂Q.map Y) = ∫ ω, Y ω ^ r ∂Q :=
      integral_map hY (by fun_prop)
    change Tendsto (fun n => ∫ x : ℝ, x ^ r ∂(P n).map (X n)) atTop
      (𝓝 (∫ x : ℝ, x ^ r ∂Q.map Y))
    simpa only [hmap, hmap'] using hm r

end
end ConditionedStableLaws
