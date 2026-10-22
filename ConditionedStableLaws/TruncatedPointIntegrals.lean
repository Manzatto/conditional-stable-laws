import ConditionedStableLaws.PoissonProcessConvergence
import Mathlib.Order.Interval.Set.Union
import Mathlib.Order.Interval.Set.IsoIoo

/-!
# Truncated jump integrals and interval-count step approximations

All integrals below use the point measure. Finite step sums use interval counts. Their error is
bounded by mesh times the number of points in the truncated interval.
-/

open Filter MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace ConditionedStableLaws.TruncatedPointIntegrals

/-- The sum of jumps in the finite positive interval `(a,b]`. -/
def truncatedIntegral (a b : ExtremeState) (ξ : LocallyFinitePointMeasure) : ℝ :=
  ∫ x in Ioc a b, x.val.toReal ∂ξ.toMeasure

/-- A finite lower-endpoint step sum, expressed in natural counts. -/
def stepSum (a : ℕ → ExtremeState) (k : ℕ) (ξ : LocallyFinitePointMeasure) : ℝ :=
  ∑ i : Fin k, (a i.val).val.toReal * (ξ.countOn (Ioc (a i.val) (a (i.val + 1))) : ℕ)

private def stepFunction (a : ℕ → ExtremeState) (k : ℕ) (x : ExtremeState) : ℝ :=
  ∑ i : Fin k, (Ioc (a i.val) (a (i.val + 1))).indicator (fun _ => (a i.val).val.toReal) x

/-- Monotone adjacent cells stay inside the original interval. -/
theorem cell_subset (a : ℕ → ExtremeState) (ha : Monotone a) (k : ℕ) (i : Fin k) :
    Ioc (a i.val) (a (i.val + 1)) ⊆ Ioc (a 0) (a k) := by
  intro x hx
  exact ⟨(ha (Nat.zero_le _)).trans_lt hx.1, hx.2.trans (ha i.isLt)⟩

/-- The cells of an increasing partition are pairwise disjoint. -/
theorem cells_disjoint (a : ℕ → ExtremeState) (ha : Monotone a) (k : ℕ) :
    Pairwise (fun i j : Fin k => Disjoint (Ioc (a i.val) (a (i.val + 1)))
      (Ioc (a j.val) (a (j.val + 1)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact not_lt_of_ge (hxi.2.trans (ha h)) hxj.1
  · exact not_lt_of_ge (hxj.2.trans (ha h)) hxi.1

/-- Every point of the truncated interval belongs to an adjacent cell. -/
theorem exists_cell (a : ℕ → ExtremeState) (k : ℕ) {x : ExtremeState}
    (hx : x ∈ Ioc (a 0) (a k)) :
    ∃ i : Fin k, x ∈ Ioc (a i.val) (a (i.val + 1)) := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (Ioc_subset_biUnion_Ioc k a hx)
  obtain ⟨hi, hxi⟩ := mem_iUnion.mp hi
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, hxi⟩

/-- On each cell only its own step contributes. -/
private theorem stepFunction_eq (a : ℕ → ExtremeState) (ha : Monotone a) (k : ℕ)
    (i : Fin k) {x : ExtremeState} (hx : x ∈ Ioc (a i.val) (a (i.val + 1))) :
    stepFunction a k x = (a i.val).val.toReal := by
  unfold stepFunction
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (cells_disjoint a ha k hji) hj hx) _
  · simp

/-- Counts on positive intervals equal their finite real masses. -/
theorem countOn_eq_real (ξ : LocallyFinitePointMeasure) (a b : ExtremeState) :
    (ξ.countOn (Ioc a b) : ℝ) = ξ.toMeasure.real (Ioc a b) := by
  have h := congrArg ENNReal.toReal (ξ.countOn_interval_eq_measure a.val b.val a.property)
  change (ξ.countOn (Ioc a b) : ℝ≥0∞).toReal = (ξ.toMeasure (Ioc a b)).toReal at h
  simpa only [ENNReal.toReal_natCast, measureReal_def] using h

/-- The true jump observable is integrable on a finite positive interval. -/
theorem integrableOn_toReal (ξ : LocallyFinitePointMeasure) (a b : ExtremeState)
    (hb : b.val ≠ ∞) : IntegrableOn (fun x : ExtremeState => x.val.toReal) (Ioc a b) ξ.toMeasure := by
  let : IsFiniteMeasure (ξ.toMeasure.restrict (Ioc a b)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact ξ.measure_interval_lt_top a.val b.val a.property⟩
  apply Integrable.of_bound measurable_subtype_coe.ennreal_toReal.aestronglyMeasurable b.val.toReal
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hb hx.2

private theorem integrableOn_stepFunction (ξ : LocallyFinitePointMeasure)
    (a : ℕ → ExtremeState) (k : ℕ) :
    IntegrableOn (stepFunction a k) (Ioc (a 0) (a k)) ξ.toMeasure := by
  let : IsFiniteMeasure (ξ.toMeasure.restrict (Ioc (a 0) (a k))) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact ξ.measure_interval_lt_top (a 0).val (a k).val (a 0).property⟩
  exact integrable_finsetSum _ (fun _ _ => (integrable_const _).indicator measurableSet_Ioc)

/-- The step integral is exactly the finite weighted count sum. -/
theorem integral_stepFunction (ξ : LocallyFinitePointMeasure)
    (a : ℕ → ExtremeState) (ha : Monotone a) (k : ℕ) :
    (∫ x in Ioc (a 0) (a k), stepFunction a k x ∂ξ.toMeasure) = stepSum a k ξ := by
  let : IsFiniteMeasure (ξ.toMeasure.restrict (Ioc (a 0) (a k))) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact ξ.measure_interval_lt_top (a 0).val (a k).val (a 0).property⟩
  unfold stepFunction stepSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator_const _ measurableSet_Ioc, measureReal_restrict_apply measurableSet_Ioc,
      inter_eq_self_of_subset_left (cell_subset a ha k i), smul_eq_mul, countOn_eq_real]
    ring
  · intro i _
    exact (integrable_const _).indicator measurableSet_Ioc

/-- The deterministic mesh bound, with the number of points as its only multiplier. -/
theorem abs_truncatedIntegral_sub_stepSum_le (ξ : LocallyFinitePointMeasure)
    (a : ℕ → ExtremeState) (ha : Monotone a) (k : ℕ) (hb : (a k).val ≠ ∞)
    (mesh : ℝ) (hmesh : ∀ i : Fin k, (a (i.val + 1)).val.toReal - (a i.val).val.toReal ≤ mesh) :
    |truncatedIntegral (a 0) (a k) ξ - stepSum a k ξ| ≤
      mesh * (ξ.countOn (Ioc (a 0) (a k)) : ℝ) := by
  rw [← integral_stepFunction ξ a ha k, truncatedIntegral,
    ← integral_sub (integrableOn_toReal ξ (a 0) (a k) hb) (integrableOn_stepFunction ξ a k),
    ← Real.norm_eq_abs, countOn_eq_real]
  apply norm_setIntegral_le_of_norm_le_const
    (ξ.measure_interval_lt_top (a 0).val (a k).val (a 0).property)
  intro x hx
  obtain ⟨i, hi⟩ := exists_cell a k hx
  rw [stepFunction_eq a ha k i hi, Real.norm_eq_abs]
  have hright : (a (i.val + 1)).val ≠ ∞ := ne_top_of_le_ne_top hb (ha i.isLt)
  have hxfin : x.val ≠ ∞ := ne_top_of_le_ne_top hb hx.2
  have hlo := ENNReal.toReal_mono hxfin hi.1.le
  have hhi := ENNReal.toReal_mono hright hi.2
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  exact (sub_le_sub_right hhi _).trans (hmesh i)

/-- A positive finite endpoint viewed in `(0,∞]`. -/
def endpoint (x : ℝ≥0) (hx : 0 < x) : ExtremeState :=
  ⟨x, ENNReal.coe_pos.mpr hx⟩

/-- Uniform partitions of a fixed finite positive interval. -/
def grid (ε R : ℝ≥0) (hε : 0 < ε) (m i : ℕ) : ExtremeState :=
  endpoint (ε + i * ((R - ε) / (m + 1))) (lt_of_lt_of_le hε (le_add_of_nonneg_right (by positivity)))

theorem grid_monotone (ε R : ℝ≥0) (hε : 0 < ε) (m : ℕ) :
    Monotone (grid ε R hε m) := by
  intro i j hij
  change (↑(ε + i * ((R - ε) / (m + 1))) : ℝ≥0∞) ≤ ↑(ε + j * ((R - ε) / (m + 1)))
  exact_mod_cast add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)) ε

@[simp] theorem grid_zero (ε R : ℝ≥0) (hε : 0 < ε) (m : ℕ) :
    grid ε R hε m 0 = endpoint ε hε := by
  apply Subtype.ext
  simp [grid, endpoint]

@[simp] theorem grid_last (ε R : ℝ≥0) (hε : 0 < ε) (hεR : ε ≤ R) (m : ℕ) :
    grid ε R hε m (m + 1) = endpoint R (hε.trans_le hεR) := by
  apply Subtype.ext
  simp only [grid, endpoint, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel₀ _ (by positivity), add_tsub_cancel_of_le hεR]

theorem grid_step (ε R : ℝ≥0) (hε : 0 < ε) (m i : ℕ) :
    (grid ε R hε m (i + 1)).val.toReal - (grid ε R hε m i).val.toReal =
      ((R - ε) / (m + 1) : ℝ≥0) := by
  simp only [grid, endpoint, ENNReal.coe_toReal, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_natCast, Nat.cast_add, Nat.cast_one, NNReal.coe_one]
  ring

theorem measurable_stepSum (a : ℕ → ExtremeState) (k : ℕ) : Measurable (stepSum a k) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul ((measurable_from_nat (f := fun j : ℕ => (j : ℝ))).comp (LocallyFinitePointMeasure.measurable_countOn_interval
    (a i.val).val (a (i.val + 1)).val (a i.val).property))

theorem mesh_tendsto_zero (ε R : ℝ≥0) :
    Tendsto (fun m : ℕ => (((R - ε) / (m + 1) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
  simpa only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
    NNReal.coe_mul, NNReal.coe_inv, div_eq_mul_inv, one_mul, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((R - ε : ℝ≥0) : ℝ)

theorem stepSum_tendsto (ε R : ℝ≥0) (hε : 0 < ε) (hεR : ε ≤ R)
    (ξ : LocallyFinitePointMeasure) :
    Tendsto (fun m => stepSum (grid ε R hε m) (m + 1) ξ) atTop
      (𝓝 (truncatedIntegral (endpoint ε hε) (endpoint R (hε.trans_le hεR)) ξ)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) _
    ((mesh_tendsto_zero ε R).mul_const (ξ.countOn (Ioc (endpoint ε hε)
      (endpoint R (hε.trans_le hεR))) : ℝ) |>.trans (by simp))
  intro m
  rw [dist_comm, Real.dist_eq]
  have h := abs_truncatedIntegral_sub_stepSum_le ξ (grid ε R hε m)
    (grid_monotone ε R hε m) (m + 1) (by simp [grid_last ε R hε hεR, endpoint])
    (((R - ε) / (m + 1) : ℝ≥0) : ℝ) (fun i => (grid_step ε R hε m i.val).le)
  simpa only [grid_zero, grid_last ε R hε hεR, endpoint] using h

theorem measurable_truncatedIntegral (ε R : ℝ≥0) (hε : 0 < ε) (hεR : ε ≤ R) :
    Measurable (truncatedIntegral (endpoint ε hε) (endpoint R (hε.trans_le hεR))) :=
  measurable_of_tendsto_metrizable (fun m => measurable_stepSum (grid ε R hε m) (m + 1))
    (tendsto_pi_nhds.mpr (stepSum_tendsto ε R hε hεR))

/-- Lower-endpoint sums retain at least the lower endpoint per observed point. -/
theorem lower_mul_count_le_stepSum (ξ : LocallyFinitePointMeasure)
    (a : ℕ → ExtremeState) (ha : Monotone a) (k : ℕ) (hb : (a k).val ≠ ∞) :
    (a 0).val.toReal * (ξ.countOn (Ioc (a 0) (a k)) : ℝ) ≤ stepSum a k ξ := by
  rw [← integral_stepFunction ξ a ha k, countOn_eq_real]
  have hfin := ξ.measure_interval_lt_top (a 0).val (a k).val (a 0).property
  have hc : (a 0).val.toReal * ξ.toMeasure.real (Ioc (a 0) (a k)) =
      ∫ _ in Ioc (a 0) (a k), (a 0).val.toReal ∂ξ.toMeasure := by
    simp [integral_const, smul_eq_mul, mul_comm]
  rw [hc]
  apply integral_mono_ae (integrableOn_const (C := (a 0).val.toReal) hfin.ne) (integrableOn_stepFunction ξ a k)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  obtain ⟨i, hi⟩ := exists_cell a k hx
  rw [stepFunction_eq a ha k i hi]
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top hb (ha (Nat.le_of_lt i.isLt))) (ha (Nat.zero_le _))

theorem truncatedIntegral_nonneg (ξ : LocallyFinitePointMeasure) (a b : ExtremeState) :
    0 ≤ truncatedIntegral a b ξ := integral_nonneg (fun _ => ENNReal.toReal_nonneg)

theorem stepSum_nonneg (ξ : LocallyFinitePointMeasure) (a : ℕ → ExtremeState) (k : ℕ) :
    0 ≤ stepSum a k ξ := Finset.sum_nonneg (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (by positivity))

private theorem integral_lipschitz_dist_le
    {E W : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace W] (F : BoundedContinuousFunction E ℝ) (L : ℝ≥0)
    (hL : LipschitzWith L F) (μ : Measure W) [IsProbabilityMeasure μ]
    (Z Z' : W → E) (hZ : Measurable Z) (hZ' : Measurable Z') (d : ℝ)
    (hd : ∀ ω, dist (Z ω) (Z' ω) ≤ d) :
    |(∫ ω, F (Z ω) ∂μ) - ∫ ω, F (Z' ω) ∂μ| ≤ L * d := by
  have hi (V : W → E) (hV : Measurable V) : Integrable (fun ω => F (V ω)) μ :=
    Integrable.of_bound (F.continuous.measurable.comp hV).aestronglyMeasurable ‖F‖
      (ae_of_all _ (fun ω => F.norm_coe_le_norm (V ω)))
  rw [← integral_sub (hi Z hZ) (hi Z' hZ'), ← Real.norm_eq_abs]
  simpa using
    norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => F (Z ω) - F (Z' ω)) (C := L * d)
      (ae_of_all _ (fun ω => by
        simpa only [Real.dist_eq, Real.norm_eq_abs] using (hL.dist_le_mul (Z ω) (Z' ω)).trans
          (mul_le_mul_of_nonneg_left (hd ω) L.coe_nonneg)))

/-- Uniform deterministic approximation transfers weak convergence, also
when the underlying probability spaces and laws vary with the index. -/
theorem tendstoInDistribution_of_uniform_approximation
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : ∀ n, Ω n → E) (Y : Ω' → E)
    (A : ∀ (_m n : ℕ), Ω n → E) (B : ℕ → Ω' → E)
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hA : ∀ m n, Measurable (A m n)) (hB : ∀ m, Measurable (B m))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hAX : ∀ m n ω, dist (A m n ω) (X n ω) ≤ δ m)
    (hBY : ∀ m ω, dist (B m ω) (Y ω) ≤ δ m)
    (hAB : ∀ m, TendstoInDistribution (A m) atTop (B m) P Q) :
    TendstoInDistribution X atTop Y P Q := by
  refine ⟨fun n => (hX n).aemeasurable, hY.aemeasurable, ?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro f hf ⟨L, hL⟩
  let F : BoundedContinuousFunction E ℝ := ⟨⟨f, hL.continuous⟩, hf⟩
  have hlim m : Tendsto (fun n => ∫ ω, f (A m n ω) ∂P n) atTop
      (𝓝 (∫ ω, f (B m ω) ∂Q)) := by
    exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (fun n => (hA m n).aemeasurable) (hB m).aemeasurable).mp (hAB m) F
  have hmain : Tendsto (fun n => ∫ ω, f (X n ω) ∂P n) atTop
      (𝓝 (∫ ω, f (Y ω) ∂Q)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have ht : Tendsto (fun m => 2 * (L : ℝ) * δ m) atTop (𝓝 0) := by
      simpa using hδ.const_mul (2 * (L : ℝ))
    have hsmall := ht.eventually_lt_const (show 0 < ε / 2 by positivity)
    obtain ⟨m, hm⟩ := hsmall.exists
    filter_upwards [(Metric.tendsto_nhds.mp (hlim m)) (ε / 2) (by positivity)] with n hn
    have h₁ := integral_lipschitz_dist_le F L hL (P n) (A m n) (X n) (hA m n) (hX n) (δ m) (hAX m n)
    have h₂ := integral_lipschitz_dist_le F L hL Q (B m) Y (hB m) hY (δ m) (hBY m)
    have htri := abs_sub_le (∫ ω, f (X n ω) ∂P n) (∫ ω, f (A m n ω) ∂P n)
      (∫ ω, f (Y ω) ∂Q)
    have htri' := abs_sub_le (∫ ω, f (A m n ω) ∂P n) (∫ ω, f (B m ω) ∂Q)
      (∫ ω, f (Y ω) ∂Q)
    change |(∫ ω, f (A m n ω) ∂P n) - ∫ ω, f (X n ω) ∂P n| ≤ L * δ m at h₁
    change |(∫ ω, f (B m ω) ∂Q) - ∫ ω, f (Y ω) ∂Q| ≤ L * δ m at h₂
    rw [abs_sub_comm] at h₁
    rw [Real.dist_eq] at hn ⊢
    linarith
  simpa only [ProbabilityMeasure.coe_mk, integral_map (hY.aemeasurable)
    hL.continuous.aestronglyMeasurable, integral_map (hX _).aemeasurable
    hL.continuous.aestronglyMeasurable] using hmain

/-- The bounded coordinate change used solely to obtain uniform errors. -/
def compactCoordinate : ℝ ≃ₜ Ioo (-1 : ℝ) 1 := (orderIsoIooNegOneOne ℝ).toHomeomorph

@[simp] theorem compactCoordinate_val (x : ℝ) :
    (compactCoordinate x).val = x / (1 + |x|) := by
  unfold compactCoordinate orderIsoIooNegOneOne
  rfl

/-- A relative mesh error becomes a uniform error in bounded coordinates. -/
theorem compactCoordinate_dist_le {x y c d e : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hd : 0 ≤ d) (he : 0 < e) (hcount : e * c ≤ y) (herror : |x - y| ≤ d * c) :
    dist (compactCoordinate x) (compactCoordinate y) ≤ d / e := by
  change |(compactCoordinate x).val - (compactCoordinate y).val| ≤ d / e
  simp only [compactCoordinate_val, abs_of_nonneg hx, abs_of_nonneg hy]
  have hx' : 0 < 1 + x := by linarith
  have hy' : 0 < 1 + y := by linarith
  rw [div_sub_div _ _ hx'.ne' hy'.ne']
  have hnum : x * (1 + y) - (1 + x) * y = x - y := by ring
  rw [hnum, abs_div, abs_of_pos (mul_pos hx' hy')]
  apply (div_le_div_iff₀ (mul_pos hx' hy') he).mpr
  calc
    |x - y| * e ≤ d * c * e := mul_le_mul_of_nonneg_right herror he.le
    _ = d * (e * c) := by ring
    _ ≤ d * y := mul_le_mul_of_nonneg_left hcount hd
    _ ≤ d * ((1 + x) * (1 + y)) := mul_le_mul_of_nonneg_left (by nlinarith) hd

theorem uniform_compactCoordinate_error (ε R : ℝ≥0) (hε : 0 < ε) (hεR : ε ≤ R)
    (m : ℕ) (ξ : LocallyFinitePointMeasure) :
    dist (compactCoordinate (stepSum (grid ε R hε m) (m + 1) ξ))
      (compactCoordinate (truncatedIntegral (endpoint ε hε) (endpoint R (hε.trans_le hεR)) ξ)) ≤
      (((R - ε) / (m + 1) : ℝ≥0) : ℝ) / ε := by
  rw [dist_comm]
  apply compactCoordinate_dist_le (truncatedIntegral_nonneg ξ _ _)
    (stepSum_nonneg ξ _ _) (by positivity) (by exact_mod_cast hε)
  · have h := lower_mul_count_le_stepSum ξ (grid ε R hε m) (grid_monotone ε R hε m)
      (m + 1) (by simp [grid_last ε R hε hεR, endpoint])
    simpa only [grid_zero, grid_last ε R hε hεR, endpoint, ENNReal.coe_toReal] using h
  · have h := abs_truncatedIntegral_sub_stepSum_le ξ (grid ε R hε m)
      (grid_monotone ε R hε m) (m + 1) (by simp [grid_last ε R hε hεR, endpoint])
      (((R - ε) / (m + 1) : ℝ≥0) : ℝ) (fun i => (grid_step ε R hε m i.val).le)
    simpa only [grid_zero, grid_last ε R hε hεR, endpoint] using h

/-- Convergence of all finite joint interval counts implies convergence of the truncated jump
integrals. The probability spaces may vary. This is the jump-truncation implication used after
point-process convergence. -/
theorem tendstoInDistribution_truncatedIntegral
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (N : ∀ n, RandomPointMeasure (Ω n)) (N' : RandomPointMeasure Ω')
    (hcounts : ∀ (k : ℕ) (a b : Fin k → ExtremeState),
      TendstoInDistribution (fun n ω j => ((N n).toFun ω).countOn (Ioc (a j) (b j))) atTop
        (fun ω j => (N'.toFun ω).countOn (Ioc (a j) (b j))) P Q)
    (ε R : ℝ≥0) (hε : 0 < ε) (hεR : ε ≤ R) :
    TendstoInDistribution
      (fun n ω => truncatedIntegral (endpoint ε hε) (endpoint R (hε.trans_le hεR)) ((N n).toFun ω)) atTop
      (fun ω => truncatedIntegral (endpoint ε hε) (endpoint R (hε.trans_le hεR)) (N'.toFun ω)) P Q := by
  have hstep m : TendstoInDistribution
      (fun n ω => stepSum (grid ε R hε m) (m + 1) ((N n).toFun ω)) atTop
      (fun ω => stepSum (grid ε R hε m) (m + 1) (N'.toFun ω)) P Q := by
    exact (hcounts (m + 1) (fun j => grid ε R hε m j.val)
      (fun j => grid ε R hε m (j.val + 1))).continuous_comp
      (g := fun v : Fin (m + 1) → ℕ => ∑ j : Fin (m + 1),
        (grid ε R hε m j.val).val.toReal * (v j : ℝ)) (by fun_prop)
  have hcompact := tendstoInDistribution_of_uniform_approximation P Q
    (fun n ω => compactCoordinate (truncatedIntegral (endpoint ε hε)
      (endpoint R (hε.trans_le hεR)) ((N n).toFun ω)))
    (fun ω => compactCoordinate (truncatedIntegral (endpoint ε hε)
      (endpoint R (hε.trans_le hεR)) (N'.toFun ω)))
    (fun m n ω => compactCoordinate (stepSum (grid ε R hε m) (m + 1) ((N n).toFun ω)))
    (fun m ω => compactCoordinate (stepSum (grid ε R hε m) (m + 1) (N'.toFun ω)))
    (fun n => compactCoordinate.continuous.measurable.comp
      ((measurable_truncatedIntegral ε R hε hεR).comp (N n).measurable))
    (compactCoordinate.continuous.measurable.comp
      ((measurable_truncatedIntegral ε R hε hεR).comp N'.measurable))
    (fun m n => compactCoordinate.continuous.measurable.comp
      ((measurable_stepSum _ _).comp (N n).measurable))
    (fun m => compactCoordinate.continuous.measurable.comp
      ((measurable_stepSum _ _).comp N'.measurable))
    (fun m => (((R - ε) / (m + 1) : ℝ≥0) : ℝ) / ε)
    (by simpa using (mesh_tendsto_zero ε R).div_const (ε : ℝ))
    (fun m n ω => uniform_compactCoordinate_error ε R hε hεR m ((N n).toFun ω))
    (fun m ω => uniform_compactCoordinate_error ε R hε hεR m (N'.toFun ω))
    (fun m => (hstep m).continuous_comp compactCoordinate.continuous)
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
    hcompact.continuous_comp compactCoordinate.symm.continuous

/-- The same jump-truncation result requires only strict disjoint interval
families, as supplied by the Poisson point-process argument. -/
theorem tendstoInDistribution_truncatedIntegral_of_disjoint_counts
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (N : ∀ n, RandomPointMeasure (Ω n)) (N' : RandomPointMeasure Ω')
    (hcounts : ∀ (k : ℕ) (a b : Fin k → ExtremeState), (∀ j, a j < b j) →
      Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      TendstoInDistribution (fun n ω j => ((N n).toFun ω).countOn (Ioc (a j) (b j))) atTop
        (fun ω j => (N'.toFun ω).countOn (Ioc (a j) (b j))) P Q)
    (ε R : ℝ≥0) (hε : 0 < ε) (hεR : ε ≤ R) :
    TendstoInDistribution
      (fun n ω => truncatedIntegral (endpoint ε hε) (endpoint R (hε.trans_le hεR)) ((N n).toFun ω)) atTop
      (fun ω => truncatedIntegral (endpoint ε hε) (endpoint R (hε.trans_le hεR)) (N'.toFun ω)) P Q := by
  apply tendstoInDistribution_truncatedIntegral P Q N N' _ ε R hε hεR
  intro k a b
  obtain ⟨m, l, u, rows, hs, hd, hsum⟩ := IntervalRefinement.exists_count_refinement a b
  have ht := (hcounts m l u hs hd).continuous_comp
    (g := fun v : Fin m → ℕ => fun j : Fin k => ∑ i ∈ rows j, v i) (by fun_prop)
  simpa only [Function.comp_def, ← hsum] using ht

end ConditionedStableLaws.TruncatedPointIntegrals
