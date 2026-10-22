import ConditionedStableLaws.BoundedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Tactic

/-!
# Approximation in probability under changing laws

The conditioned laws vary with the horizon. The bounded-Lipschitz estimate underlying the
converging-together argument, and a version of Slutsky's approximation theorem for changing laws.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ConditionedStableLaws

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded real Lipschitz test function is integrable after any measurable
observation under a probability measure. -/
theorem integrable_bounded_lipschitz_comp
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (F : ℝ → ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) {B : ℝ}
    (hB : ∀ x y, dist (F x) (F y) ≤ B) : Integrable (fun ω => F (X ω)) P := by
  apply Integrable.of_bound (hF.continuous.measurable.comp hX).aestronglyMeasurable
    (|F 0| + B)
  exact Eventually.of_forall fun ω => by
    have h := hB (X ω) 0
    rw [Real.dist_eq] at h
    rw [Real.norm_eq_abs]
    change |F (X ω)| ≤ |F 0| + B
    have := abs_sub_abs_le_abs_sub (F (X ω)) (F 0)
    linarith

/-- A quantitative coupling estimate, using only a common underlying
probability law for the two observations at the given horizon. -/
theorem abs_integral_lipschitz_sub_le
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (F : ℝ → ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) {B : ℝ}
    (hB : ∀ x y, dist (F x) (F y) ≤ B) {ε : ℝ} (hε : 0 < ε) :
    |(∫ ω, F (X ω) ∂P) - ∫ ω, F (Y ω) ∂P| ≤
      ε + B * P.real {ω | ε / (L + 1) < |X ω - Y ω|} := by
  have hB0 : 0 ≤ B := by simpa using hB 0 0
  have hiX := integrable_bounded_lipschitz_comp P X hX F hF hB
  have hiY := integrable_bounded_lipschitz_comp P Y hY F hF hB
  rw [← integral_sub hiX hiY]
  apply (show |∫ ω, F (X ω) - F (Y ω) ∂P| ≤
      ∫ ω, |F (X ω) - F (Y ω)| ∂P from by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (fun ω => F (X ω) - F (Y ω)) (μ := P))).trans
  have hbound : ∀ᵐ ω ∂P, |F (X ω) - F (Y ω)| ≤ B :=
    Eventually.of_forall fun ω => by simpa only [Real.dist_eq] using hB (X ω) (Y ω)
  have hcut := BoundedConvergence.integral_abs_le_cutoff P
    (fun ω => F (X ω) - F (Y ω))
    ((hF.continuous.measurable.comp hX).sub (hF.continuous.measurable.comp hY))
    B ε hε.le hbound
  apply hcut.trans
  apply add_le_add le_rfl (mul_le_mul_of_nonneg_left (measureReal_mono ?_) hB0)
  intro ω hω
  change ε < |F (X ω) - F (Y ω)| at hω
  change ε / (L + 1) < |X ω - Y ω|
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < L + 1)).mpr
  have hLip := hF.dist_le_mul (X ω) (Y ω)
  simp only [Real.dist_eq] at hLip
  nlinarith [abs_nonneg (X ω - Y ω)]

/-- If two real observations become close in probability under changing
probability laws, their bounded-Lipschitz expectations become equal. -/
theorem integral_lipschitz_sub_tendsto_zero
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hnear : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P n).real {ω | ε < |X n ω - Y n ω|}) atTop (𝓝 0))
    (F : ℝ → ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) {B : ℝ}
    (hB : ∀ x y, dist (F x) (F y) ≤ B) :
    Tendsto (fun n => (∫ ω, F (X n ω) ∂P n) - ∫ ω, F (Y n ω) ∂P n)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have htail : Tendsto (fun n => B * (P n).real
      {ω | (ε / 2) / (L + 1) < |X n ω - Y n ω|}) atTop (𝓝 0) := by
    simpa using (hnear ((ε / 2) / (L + 1)) (by positivity)).const_mul B
  filter_upwards [htail.eventually_lt_const (half_pos hε)] with n hn
  have hb := abs_integral_lipschitz_sub_le (P n) (X n) (Y n) (hX n) (hY n)
    F hF hB (half_pos hε)
  rw [Real.dist_eq, sub_zero]
  linarith

/-- Slutsky's approximation theorem with a different conditioning law at each n. -/
theorem tendstoInDistribution_of_varying_probability_approximation
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X Y : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hYZ : TendstoInDistribution Y atTop Z P Q)
    (hnear : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P n).real {ω | ε < |X n ω - Y n ω|}) atTop (𝓝 0)) :
    TendstoInDistribution X atTop Z P Q := by
  refine ⟨fun n => (hX n).aemeasurable, hYZ.aemeasurable_limit, ?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨B, hB⟩ ⟨L, hF⟩
  have hlim := tendsto_iff_forall_lipschitz_integral_tendsto.mp hYZ.tendsto F
    ⟨B, hB⟩ ⟨L, hF⟩
  have hdiff := integral_lipschitz_sub_tendsto_zero P X Y hX hY hnear F hF hB
  have hmapsX (n : ℕ) : ∫ z, F z ∂(P n).map (X n) = ∫ ω, F (X n ω) ∂P n :=
    integral_map (hX n).aemeasurable hF.continuous.aestronglyMeasurable
  have hmapsY (n : ℕ) : ∫ z, F z ∂(P n).map (Y n) = ∫ ω, F (Y n ω) ∂P n :=
    integral_map (hY n).aemeasurable hF.continuous.aestronglyMeasurable
  simp only [ProbabilityMeasure.coe_mk, hmapsY] at hlim
  simpa only [ProbabilityMeasure.coe_mk, hmapsX, sub_add_cancel, zero_add] using hdiff.add hlim

/-- The elementary two-stage approximation principle, with the approximation
parameter chosen before the sequence index. -/
theorem tendsto_of_double_approximation
    (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (z : ℝ)
    (hbc : ∀ k, Tendsto (b k) atTop (𝓝 (c k)))
    (hcz : Tendsto c atTop (𝓝 z))
    (hab : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ᶠ n in atTop, |a n - b k n| < ε) :
    Tendsto a atTop (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨k, hknear, hkz⟩ :=
    ((hab (ε / 3) hthird).and (Metric.tendsto_nhds.mp hcz (ε / 3) hthird)).exists
  filter_upwards [hknear, Metric.tendsto_nhds.mp (hbc k) (ε / 3) hthird] with n hn hnc
  have h1 := abs_sub_le (a n) (b k n) (c k)
  have h2 := abs_sub_le (a n) (c k) z
  simp only [Real.dist_eq] at hkz hnc ⊢
  linarith

/-- The converging-together theorem used after truncating small and large jumps. Both the
observation laws and the approximation errors may vary with n. The approximation hypothesis is an
iterated probability estimate. -/
theorem tendstoInDistribution_of_double_probability_approximation
    {Ω' Ω'' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (R : Measure Ω'') [IsProbabilityMeasure R]
    (X : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (Z : ℕ → Ω' → ℝ) (W : Ω'' → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ k n, Measurable (Y k n))
    (hZ : ∀ k, Measurable (Z k))
    (hYZ : ∀ k, TendstoInDistribution (Y k) atTop (Z k) P Q)
    (hZW : TendstoInDistribution Z atTop W (fun _ => Q) R)
    (hnear : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      (P n).real {ω | ε < |X n ω - Y k n ω|} < δ) :
    TendstoInDistribution X atTop W P R := by
  refine ⟨fun n => (hX n).aemeasurable, hZW.aemeasurable_limit, ?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨B, hB⟩ ⟨L, hF⟩
  have hmapsX (n : ℕ) : ∫ z, F z ∂(P n).map (X n) = ∫ ω, F (X n ω) ∂P n :=
    integral_map (hX n).aemeasurable hF.continuous.aestronglyMeasurable
  have hmapsY (k n : ℕ) : ∫ z, F z ∂(P n).map (Y k n) = ∫ ω, F (Y k n ω) ∂P n :=
    integral_map (hY k n).aemeasurable hF.continuous.aestronglyMeasurable
  have hmapsZ (k : ℕ) : ∫ z, F z ∂Q.map (Z k) = ∫ ω, F (Z k ω) ∂Q :=
    integral_map (hZ k).aemeasurable hF.continuous.aestronglyMeasurable
  have hbc (k : ℕ) : Tendsto (fun n => ∫ ω, F (Y k n ω) ∂P n)
      atTop (𝓝 (∫ ω, F (Z k ω) ∂Q)) := by
    have h := tendsto_iff_forall_lipschitz_integral_tendsto.mp (hYZ k).tendsto F
      ⟨B, hB⟩ ⟨L, hF⟩
    simpa only [ProbabilityMeasure.coe_mk, hmapsY, hmapsZ] using h
  have hcz : Tendsto (fun k => ∫ ω, F (Z k ω) ∂Q) atTop (𝓝 (∫ z, F z ∂R.map W)) := by
    have h := tendsto_iff_forall_lipschitz_integral_tendsto.mp hZW.tendsto F
      ⟨B, hB⟩ ⟨L, hF⟩
    simpa only [ProbabilityMeasure.coe_mk, hmapsZ] using h
  simp only [ProbabilityMeasure.coe_mk, hmapsX]
  apply tendsto_of_double_approximation _ _ _ _ hbc hcz
  intro ε hε
  have hB0 : 0 ≤ B := by simpa using hB 0 0
  have hsmall : B * (ε / (2 * (B + 1))) < ε / 2 := by
    have hd : 0 < 2 * (B + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  filter_upwards [hnear ((ε / 2) / (L + 1)) (ε / (2 * (B + 1)))
    (by positivity) (by positivity)] with k hk
  filter_upwards [hk] with n hn
  have hb := abs_integral_lipschitz_sub_le (P n) (X n) (Y k n) (hX n) (hY k n)
    F hF hB (half_pos hε)
  have hmul := mul_le_mul_of_nonneg_left hn.le hB0
  linarith

end
end ConditionedStableLaws
