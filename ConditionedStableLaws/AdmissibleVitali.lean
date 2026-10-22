import ConditionedStableLaws.RiemannianRegularity
import Mathlib.MeasureTheory.Covering.Vitali

/-! Differentiation from pointwise power-volume regularity, without a sphere-null assumption. -/
open Filter MeasureTheory MeasureTheory.Measure Set Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace ConditionedStableLaws
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  {ρ : Measure M} [IsLocallyFiniteMeasure ρ]

omit [BorelSpace M] [IsLocallyFiniteMeasure ρ] in
/-- Power-volume regularity controls the fourfold ball ratio by a constant depending
only on the dimension, even though the local volume constant depends on the centre. -/
theorem IsRegularAt.eventually_ball_four_mul_le {x : M} {d C : ℝ}
    (hreg : IsRegularAt ρ x d C) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (ball x r) ∧
      ρ.real (ball x (4 * r)) ≤ (4 ^ d + 1) * ρ.real (ball x r) := by
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (ball x r) := by
    filter_upwards [(tendsto_order.1 hreg.2.2).1 0 hreg.2.1,
      self_mem_nhdsWithin] with r hr hrpos
    exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hrpos d)).mp hr
  have hratio := (hreg.tendsto_const_scaled_ball (by norm_num : (0 : ℝ) < 4)).div
    hreg.2.2 hreg.2.1.ne'
  rw [mul_div_cancel_left₀ _ hreg.2.1.ne'] at hratio
  have hratio' : Tendsto (fun r => ρ.real (ball x (4 * r)) / ρ.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (4 ^ d)) := by
    apply hratio.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrd : r ^ d ≠ 0 := (Real.rpow_pos_of_pos hr d).ne'
    dsimp only [Pi.div_apply]
    field_simp
  filter_upwards [hpos, hratio'.eventually_lt_const (lt_add_one (4 ^ d))] with r hr hb
  exact ⟨hr, (div_le_iff₀ hr).mp hb.le⟩

omit [BorelSpace M] in
/-- Local finiteness gives finite measure to all sufficiently small enlarged closed balls. -/
theorem eventually_finite_closedBall_mul (x : M) (a : ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ρ (closedBall x (a * r)) < ∞ := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have ht : Tendsto (fun r : ℝ => a * r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hr.const_mul a
  exact ((tendsto_closedBall_smallSets x).comp ht) (ρ.finiteAt_nhds x).eventually

omit [BorelSpace M] in
/-- The dimension-dependent local doubling estimate required by the Vitali covering theorem. -/
theorem IsRegularAt.eventually_closedBall_doubling {x : M} {d C : ℝ}
    (hreg : IsRegularAt ρ x d C) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ρ (closedBall x (3 * r)) ≤
      ENNReal.ofReal (4 ^ d + 1) * ρ (closedBall x r) := by
  filter_upwards [hreg.eventually_ball_four_mul_le, self_mem_nhdsWithin,
    eventually_finite_closedBall_mul (ρ := ρ) x 4] with r hr hrpos hfin
  change 0 < r at hrpos
  have hfin3 : ρ (closedBall x (3 * r)) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall (by linarith))) hfin).ne
  have hfin1 : ρ (closedBall x r) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall (by linarith))) hfin).ne
  have hfin4b : ρ (ball x (4 * r)) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono ball_subset_closedBall) hfin).ne
  apply (ENNReal.toReal_le_toReal hfin3 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin1)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  calc
    ρ.real (closedBall x (3 * r)) ≤ ρ.real (ball x (4 * r)) :=
      measureReal_mono (h₂ := hfin4b) (closedBall_subset_ball (by linarith))
    _ ≤ (4 ^ d + 1) * ρ.real (ball x r) := hr.2
    _ ≤ (4 ^ d + 1) * ρ.real (closedBall x r) :=
      mul_le_mul_of_nonneg_left (measureReal_mono (h₂ := hfin1) ball_subset_closedBall) (by positivity)

variable [SecondCountableTopology M]

/-- Lebesgue differentiation on the exact open balls appearing in admissibility.
Pointwise power-volume regularity supplies the Vitali covering condition. -/
theorem ae_tendsto_ball_abs_sub_average_locallyIntegrable_of_regular {d : ℝ}
    (hreg : ∀ x : M, ∃ C : ℝ, IsRegularAt ρ x d C)
    {m : M → ℝ} (hm : LocallyIntegrable m ρ) :
    ∀ᵐ x ∂ρ, Tendsto
      (fun r => (∫ y in ball x r, |m y - m x| ∂ρ) / ρ.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let K : ℝ≥0 := ⟨4 ^ d + 1, by positivity⟩
  have hdoub (x : M) : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ρ (closedBall x (3 * r)) ≤ K * ρ (closedBall x r) := by
    obtain ⟨C, hx⟩ := hreg x
    have hK : ENNReal.ofReal (4 ^ d + 1) = (K : ℝ≥0∞) := by
      change ENNReal.ofReal (K : ℝ) = (K : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    simpa only [hK] using hx.eventually_closedBall_doubling
  let v : VitaliFamily ρ := Vitali.vitaliFamily ρ K (fun x => (hdoub x).frequently)
  have ht (x : M) : Tendsto (closedBall x) (𝓝[>] (0 : ℝ)) (v.filterAt x) := by
    apply v.tendsto_filterAt_iff.mpr
    refine ⟨?_, fun ε hε => ?_⟩
    · filter_upwards [hdoub x, self_mem_nhdsWithin] with r hr hrpos
      change IsClosed (closedBall x r) ∧ (interior (closedBall x r)).Nonempty ∧ _
      exact ⟨isClosed_closedBall, (nonempty_ball.mpr hrpos).mono ball_subset_interior_closedBall,
        r, Subset.rfl, hr⟩
    · filter_upwards [(eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr
      exact closedBall_subset_closedBall hr.le
  filter_upwards [v.ae_tendsto_average_norm_sub hm] with x hx
  have hclosed : Tendsto
      (fun r => (∫ y in closedBall x r, |m y - m x| ∂ρ) / ρ.real (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, setAverage_eq, Real.norm_eq_abs,
      smul_eq_mul, div_eq_inv_mul] using hx.comp (ht x)
  obtain ⟨Cx, hxreg⟩ := hreg x
  have hlim := hclosed.const_mul (4 ^ d + 1)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun r => div_nonneg
    (integral_nonneg fun y => abs_nonneg _) measureReal_nonneg) _ hlim
  have hcsmall : Tendsto (closedBall x) (𝓝[>] (0 : ℝ)) (𝓝 x).smallSets :=
    (tendsto_closedBall_smallSets x).mono_left nhdsWithin_le_nhds
  filter_upwards [hxreg.eventually_ball_four_mul_le, self_mem_nhdsWithin,
    eventually_finite_closedBall_mul (ρ := ρ) x 4, hcsmall (hm x).eventually] with r hr hrpos hfin hmi
  change 0 < r at hrpos
  have hfin1 : ρ (closedBall x r) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall (by linarith))) hfin).ne
  have hfin4b : ρ (ball x (4 * r)) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono ball_subset_closedBall) hfin).ne
  have hcpos : 0 < ρ.real (closedBall x r) :=
    hr.1.trans_le (measureReal_mono (h₂ := hfin1) ball_subset_closedBall)
  have hmass : ρ.real (closedBall x r) ≤ (4 ^ d + 1) * ρ.real (ball x r) :=
    (measureReal_mono (h₂ := hfin4b) (closedBall_subset_ball (by linarith : r < 4 * r))).trans hr.2
  have hnum : (∫ y in ball x r, |m y - m x| ∂ρ) ≤
      ∫ y in closedBall x r, |m y - m x| ∂ρ :=
    setIntegral_mono_set ((hmi.sub (integrableOn_const hfin1)).abs)
      (ae_of_all _ fun y => abs_nonneg _) (ae_of_all _ fun _ hy => ball_subset_closedBall hy)
  have hn0 : 0 ≤ ∫ y in closedBall x r, |m y - m x| ∂ρ :=
    integral_nonneg fun y => abs_nonneg _
  calc
    _ ≤ (∫ y in closedBall x r, |m y - m x| ∂ρ) / ρ.real (ball x r) :=
      div_le_div_of_nonneg_right hnum hr.1.le
    _ ≤ _ := by
      rw [← mul_div_assoc, div_le_div_iff₀ hr.1 hcpos]
      nlinarith [mul_le_mul_of_nonneg_left hmass hn0]

/-- Integrable version of the local differentiation theorem. -/
theorem ae_tendsto_ball_abs_sub_average_of_regular {d : ℝ}
    (hreg : ∀ x : M, ∃ C : ℝ, IsRegularAt ρ x d C)
    {m : M → ℝ} (hm : Integrable m ρ) :
    ∀ᵐ x ∂ρ, Tendsto
      (fun r => (∫ y in ball x r, |m y - m x| ∂ρ) / ρ.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ae_tendsto_ball_abs_sub_average_locallyIntegrable_of_regular hreg hm.locallyIntegrable

omit [BorelSpace M] [SecondCountableTopology M] in
/-- The absolute-error condition gives ordinary ball averages using only local integrability. -/
theorem ball_average_tendsto_of_abs_sub_average_local {w : M → ℝ}
    (hw : LocallyIntegrable w ρ) (x : M)
    (hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ρ.real (ball x r))
    (hLeb : Tendsto (fun r => (∫ y in ball x r, |w y - w x| ∂ρ) / ρ.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r => (∫ y in ball x r, w y ∂ρ) / ρ.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (w x)) := by
  have hcsmall : Tendsto (closedBall x) (𝓝[>] (0 : ℝ)) (𝓝 x).smallSets :=
    (tendsto_closedBall_smallSets x).mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hLeb
  filter_upwards [hpos, hcsmall (hw x).eventually,
    hcsmall (ρ.finiteAt_nhds x).eventually] with r hr hwi hfin
  have hbfin : ρ (ball x r) ≠ ∞ := (lt_of_le_of_lt (measure_mono ball_subset_closedBall) hfin).ne
  have hnum := norm_integral_le_integral_norm (μ := ρ.restrict (ball x r))
    (fun y => w y - w x)
  rw [integral_sub (hwi.mono_set ball_subset_closedBall) (integrableOn_const hbfin),
    setIntegral_const, smul_eq_mul, Real.norm_eq_abs] at hnum
  simp only [Real.norm_eq_abs] at hnum ⊢
  have heq : (∫ y in ball x r, w y ∂ρ) / ρ.real (ball x r) - w x =
      ((∫ y in ball x r, w y ∂ρ) - ρ.real (ball x r) * w x) / ρ.real (ball x r) := by field_simp
  rw [heq, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right hnum hr.le

/-- Under the common-dimension regularity condition, an integrable density is admissible
at almost every point where its specified representative is positive. -/
theorem ae_isAdmissiblePoint_of_regular {d : ℝ}
    (hreg : ∀ x : M, ∃ C : ℝ, IsRegularAt ρ x d C)
    {m : M → ℝ} (hm : Integrable m ρ) :
    ∀ᵐ x ∂ρ, 0 < m x → IsAdmissiblePoint ρ m x d := by
  filter_upwards [ae_tendsto_ball_abs_sub_average_of_regular hreg hm] with x hx
  intro hmx
  obtain ⟨C, hC⟩ := hreg x
  exact ⟨C, hC, hmx, hx⟩

/-- Almost every point of a measurable domain has asymptotic density one in ambient balls. -/
theorem ae_tendsto_restrict_ball_ratio_of_regular {d : ℝ}
    (hreg : ∀ x : M, ∃ C : ℝ, IsRegularAt ρ x d C)
    {D : Set M} (hD : MeasurableSet D) :
    ∀ᵐ x ∂ρ.restrict D, Tendsto
      (fun r => (ρ.restrict D).real (ball x r) / ρ.real (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hi : LocallyIntegrable (D.indicator (fun _ : M => (1 : ℝ))) ρ :=
    (locallyIntegrable_const 1).indicator hD
  have hdiff := ae_restrict_of_ae
    (ae_tendsto_ball_abs_sub_average_locallyIntegrable_of_regular hreg hi) (s := D)
  filter_upwards [hdiff, ae_restrict_mem hD] with x hx hxD
  obtain ⟨C, hxreg⟩ := hreg x
  have hpos := hxreg.eventually_ball_four_mul_le.mono fun _ hr => hr.1
  have havg := ball_average_tendsto_of_abs_sub_average_local hi x hpos hx
  rw [indicator_of_mem hxD] at havg
  apply havg.congr
  intro r
  rw [setIntegral_indicator hD, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply measurableSet_ball]

/-- Restriction preserves the ambient volume constant at almost every point of the domain,
including its measure-theoretic boundary. -/
theorem ae_isRegularAt_restrict_of_regular {d : ℝ}
    (hreg : ∀ x : M, ∃ C : ℝ, IsRegularAt ρ x d C)
    {D : Set M} (hD : MeasurableSet D) :
    ∀ᵐ x ∂ρ.restrict D, ∃ C : ℝ, IsRegularAt (ρ.restrict D) x d C := by
  filter_upwards [ae_tendsto_restrict_ball_ratio_of_regular hreg hD] with x hx
  obtain ⟨C, hxreg⟩ := hreg x
  refine ⟨C, hxreg.1, hxreg.2.1, ?_⟩
  have ht := hx.mul hxreg.2.2
  rw [one_mul] at ht
  apply ht.congr'
  filter_upwards [hxreg.eventually_ball_four_mul_le] with r hr
  have hbne := hr.1.ne'
  field_simp

/-- The absolute-error differentiation assertion for a density integrable only on D.
It holds almost everywhere in D, without an interior-point or sphere-null hypothesis. -/
theorem ae_tendsto_ball_abs_sub_average_restrict_of_regular {d : ℝ}
    (hreg : ∀ x : M, ∃ C : ℝ, IsRegularAt ρ x d C)
    {D : Set M} (hD : MeasurableSet D) {m : M → ℝ} (hm : Integrable m (ρ.restrict D)) :
    ∀ᵐ x ∂ρ.restrict D, Tendsto
      (fun r => (∫ y in ball x r, |m y - m x| ∂ρ.restrict D) /
        (ρ.restrict D).real (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi : Integrable (D.indicator m) ρ := (integrable_indicator_iff hD).mpr hm
  have hdiff := ae_restrict_of_ae
    (ae_tendsto_ball_abs_sub_average_of_regular hreg hi) (s := D)
  filter_upwards [hdiff, ae_tendsto_restrict_ball_ratio_of_regular hreg hD,
    ae_restrict_mem hD] with x hx hratio hxD
  rw [indicator_of_mem hxD] at hx
  obtain ⟨C, hxreg⟩ := hreg x
  have ht := hx.div hratio one_ne_zero
  rw [zero_div] at ht
  apply squeeze_zero' (Eventually.of_forall fun r => div_nonneg
    (integral_nonneg fun y => abs_nonneg _) measureReal_nonneg) _ ht
  filter_upwards [hxreg.eventually_ball_four_mul_le,
    (tendsto_order.1 hratio).1 0 zero_lt_one,
    eventually_finite_closedBall_mul (ρ := ρ) x 1] with r hr hrr hfin
  have hbfin : ρ (ball x r) ≠ ∞ := (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
    (by simpa only [one_mul] using hfin)).ne
  have hmass : 0 < (ρ.restrict D).real (ball x r) :=
    (div_pos_iff_of_pos_right hr.1).mp hrr
  have hnum : (∫ y in ball x r, |m y - m x| ∂ρ.restrict D) ≤
      ∫ y in ball x r, |D.indicator m y - m x| ∂ρ := by
    rw [show (∫ y in ball x r, |m y - m x| ∂ρ.restrict D) =
        ∫ y in ball x r, D.indicator (fun z => |m z - m x|) y ∂ρ by
      rw [setIntegral_indicator hD, Measure.restrict_restrict measurableSet_ball]]
    apply integral_mono_of_nonneg (ae_of_all _ fun y => indicator_nonneg
      (fun z _ => abs_nonneg (m z - m x)) y) ((hi.restrict.sub (integrableOn_const hbfin)).abs)
    apply ae_of_all
    intro y
    change D.indicator (fun z => |m z - m x|) y ≤ |D.indicator m y - m x|
    by_cases hy : y ∈ D
    · simp only [indicator_of_mem hy, le_refl]
    · simp only [indicator_of_notMem hy]
      exact abs_nonneg _
  calc
    _ ≤ (∫ y in ball x r, |D.indicator m y - m x| ∂ρ) /
        (ρ.restrict D).real (ball x r) := div_le_div_of_nonneg_right hnum hmass.le
    _ = _ := by
      have hbne := hr.1.ne'
      have hmne := hmass.ne'
      dsimp only [Pi.div_apply]
      field_simp

/-- The complete almost-everywhere admissibility consequence on a measurable domain. -/
theorem ae_isAdmissiblePoint_restrict_of_regular {d : ℝ}
    (hreg : ∀ x : M, ∃ C : ℝ, IsRegularAt ρ x d C)
    {D : Set M} (hD : MeasurableSet D) {m : M → ℝ} (hm : Integrable m (ρ.restrict D)) :
    ∀ᵐ x ∂ρ.restrict D, 0 < m x → IsAdmissiblePoint (ρ.restrict D) m x d := by
  filter_upwards [ae_isRegularAt_restrict_of_regular hreg hD,
    ae_tendsto_ball_abs_sub_average_restrict_of_regular hreg hD hm] with x hx hLeb
  intro hmx
  obtain ⟨C, hC⟩ := hx
  exact ⟨C, hC, hmx, hLeb⟩

end ConditionedStableLaws
