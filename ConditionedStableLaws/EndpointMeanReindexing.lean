import ConditionedStableLaws.EndpointReindexing
import ConditionedStableLaws.RefinedLLNMain

/-! Endpoint control in conditioned mean for the unbounded indexing remark. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
noncomputable section
namespace ConditionedStableLaws

/-- Convergence of Cesàro means forces the individual terms divided by n to vanish. -/
theorem term_div_tendsto_zero_of_cesaro {q : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q i) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => q n / n) atTop (𝓝 0) := by
  have hratio : Tendsto (fun n : ℕ => (n + 1 : ℝ) / n) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop)
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    change 1 + (n : ℝ)⁻¹ = (n + 1 : ℝ) / n
    field_simp
  have hlim := (hratio.mul (h.comp (tendsto_add_atTop_nat 1))).sub h
  simp only [one_mul, sub_self] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hns : (n + 1 : ℝ) ≠ 0 := by positivity
  dsimp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
  simp only [Nat.cast_add, Nat.cast_one, Finset.sum_range_succ]
  field_simp
  ring

namespace CanonicalChain
open StandingHypothesis RefinedLLN
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

/-- Under the hypotheses of the unbounded mean theorem, the final observation divided
by n tends to zero in conditioned mean, for almost every live initial state. -/
theorem conditioned_endpoint_mean_nonneg_of_H
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    {g : M → ℝ} (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (hZ : ∀ z ∈ escapingSet C.killedTransition, g z = 0) (hgi : Integrable g μ) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M),
      (∀ n, Integrable (fun ω : Path M => zeroExtension g (ω n)) (C.conditionedMeasure x.val n)) ∧
      Tendsto (fun n : ℕ => (∫ ω, zeroExtension g (ω n) ∂C.conditionedMeasure x.val n) / n)
        atTop (𝓝 0) := by
  let ν := (μ.withDensity d.weight).comap (Subtype.val : d.State → M)
  let u : M → ℝ := fun y => g y / (d.weight y).toReal
  have hu0 (y : M) : 0 ≤ u y := div_nonneg (hg0 y) ENNReal.toReal_nonneg
  have hum : Measurable u := hg.div d.measurable_weight.ennreal_toReal
  have hgZ (y : M) (hy : d.weight y = 0) : g y = 0 := by
    apply hZ
    have : y ∉ d.liveSet := fun h' => h' hy
    rw [hlive] at this
    simpa [survivingSet] using this
  have hug (y : M) : u y * (d.weight y).toReal = g y := by
    by_cases hy : d.weight y = 0
    · simp [u, hy, hgZ y hy]
    · exact div_mul_cancel₀ _ (ENNReal.toReal_ne_zero.2 ⟨hy, d.weight_ne_top y⟩)
  have hugE (y : M) : d.weight y * ENNReal.ofReal (u y) = ENNReal.ofReal (g y) := by
    rw [← hug y, ENNReal.ofReal_mul (hu0 y), ENNReal.ofReal_toReal (d.weight_ne_top y), mul_comm]
  have hgfin : ∫⁻ y, ENNReal.ofReal (g y) ∂μ ≠ ∞ := hgi.lintegral_lt_top.ne
  have huν : Integrable (fun x : d.State => u x.val) ν := by
    apply integrable_live d μ
    refine integrable_of_lintegral_ne_top hum hu0 ?_
    rw [lintegral_withDensity_eq_lintegral_mul _ d.measurable_weight hum.ennreal_ofReal]
    simp only [Pi.mul_apply, hugE]
    exact hgfin
  have hces := QProcessCesaro.nonneg_kernel_cesaro h d s.continuous_weight μ hleft hnorm
    (hum.comp measurable_subtype_coe) huν (fun y => hu0 y.val)
  have hfinν := ae_live_of_ae d μ
    (ae_lintegral_kernel_pow_ne_top hleft d.rate_ne_top hg.ennreal_ofReal hgfin)
  filter_upwards [hces, hfinν] with x hcx hfx
  let q : ℕ → ℝ := fun n => ∫ y, u y.val ∂(d.kernel ^ n) x
  have hq : Tendsto (fun n : ℕ => q n / n) atTop (𝓝 0) :=
    term_div_tendsto_zero_of_cesaro hcx
  have hη : 0 < (d.weight x.val).toReal := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  have hr : 0 < d.rate.toReal := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  have hD (n : ℕ) : (d.weight x.val).toReal * q n =
      d.rate.toReal⁻¹ ^ n * ∫ y, g y ∂(C.killedTransition ^ n) x.val := by
    have hwfin : ∫⁻ y, ENNReal.ofReal (u y) * d.weight y ∂(C.killedTransition ^ n) x.val ≠ ∞ := by
      simpa only [mul_comm (ENNReal.ofReal (u _)), hugE] using hfx n
    simpa only [hug] using doob_pow_integral d n x hum hu0 hwfin
  let e : ℕ → ℝ := fun n => d.rate.toReal⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ
  have he : Tendsto e atTop (𝓝 (d.weight x.val).toReal) :=
    (s.normalized_survival_tendstoUniformly.tendsto_at x.val).congr
      fun n => normalized_survival_toReal (K := C.toKilledKernel) d n x.val
  have hzm (n : ℕ) : Measurable (fun ω : Path M => zeroExtension g (ω n)) :=
    (measurable_zeroExtension hg).comp (measurable_pi_apply n)
  have hz0 (n : ℕ) (ω : Path M) : 0 ≤ zeroExtension g (ω n) := by
    cases ω n <;> simp [zeroExtension, hg0]
  have hformula (n : ℕ) :
      ∫⁻ ω, ENNReal.ofReal (zeroExtension g (ω n)) ∂C.conditionedMeasure x.val n =
      ((C.killedTransition ^ n) x.val univ)⁻¹ * ∫⁻ y, ENNReal.ofReal (g y) ∂(C.killedTransition ^ n) x.val := by
    simp_rw [ofReal_zeroExtension]
    rw [lintegral_conditioned_single C x.val le_rfl hg.ennreal_ofReal]
    have hu (y : M) : (1 : Kernel M M) y univ = 1 := by
      change Measure.dirac y univ = 1
      simp
    simp only [Nat.sub_self, pow_zero, hu, mul_one]
  have hi (n : ℕ) : Integrable (fun ω : Path M => zeroExtension g (ω n)) (C.conditionedMeasure x.val n) := by
    apply integrable_of_lintegral_ne_top (hzm n) (hz0 n)
    rw [hformula]
    have hp := (C.pathMeasure_survival_pos x.val (d.liveSet_subset_survivingSet x.property) n).ne'
    rw [C.pathMeasure_survival] at hp
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp) (hfx n)
  refine ⟨hi, ?_⟩
  have hlim := (hq.const_mul (d.weight x.val).toReal).div he hη.ne'
  simp only [mul_zero, zero_div] at hlim
  apply hlim.congr
  intro n
  have hreal : (∫ ω, zeroExtension g (ω n) ∂C.conditionedMeasure x.val n) =
      (((C.killedTransition ^ n) x.val).real univ)⁻¹ * ∫ y, g y ∂(C.killedTransition ^ n) x.val := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hz0 n)) (hzm n).aestronglyMeasurable,
      hformula, ENNReal.toReal_mul, ENNReal.toReal_inv,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable]
    rfl
  rw [hreal]
  have hp : (d.rate.toReal⁻¹ ^ n) ≠ 0 := pow_ne_zero _ (inv_ne_zero hr.ne')
  have hd := hD n
  dsimp [e]
  rw [← mul_div_assoc, hd]
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (d.rate.toReal⁻¹ ^ n * (d.rate.toReal⁻¹ ^ n)⁻¹) *
        ((((C.killedTransition ^ n) x.val).real univ)⁻¹ * ∫ y, g y ∂(C.killedTransition ^ n) x.val) * (n : ℝ)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ hp, one_mul]

/-- Both time-indexing conventions satisfy the unbounded conditional L¹ law. The terminal error is
controlled by H and μ-integrability alone. -/
theorem lln_L1_reindexed
    (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hleft : C.killedTransition ∘ₘ μ = d.rate • μ) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    {f : M → ℝ} (hf : Measurable f)
    (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0) (hfi : Integrable f μ) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M),
      Tendsto (fun n : ℕ => ∫ ω, |pathShiftedBirkhoffSum f n ω / n -
        ∫ y, f y ∂μ.withDensity d.weight| ∂C.conditionedMeasure x.val n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫ ω, |pathBirkhoffSum f (n + 1) ω / (n + 1 : ℕ) -
        ∫ y, f y ∂μ.withDensity d.weight| ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
  have hfm : Measurable (fun y => |f y|) := by simpa only [Real.norm_eq_abs] using hf.norm
  have hends := C.conditioned_endpoint_mean_nonneg_of_H h d s hlive μ hleft hnorm
    hfm (fun y => abs_nonneg (f y)) (fun y hy => by rw [hZ y hy, abs_zero]) hfi.abs
  have hbase := RefinedLLN.lln_L1 C h d s hlive μ hleft hnorm hf hZ hfi
  have hfinν := ae_live_of_ae d μ
    (ae_lintegral_kernel_pow_ne_top hleft d.rate_ne_top hfm.ennreal_ofReal
      hfi.abs.lintegral_lt_top.ne)
  filter_upwards [hends, hbase, hfinν] with x hend hlim hfx
  have : ∀ n, IsProbabilityMeasure (C.conditionedMeasure x.val n) := fun n =>
    C.conditionedMeasure_isProbability_of_surviving x.val
      (d.liveSet_subset_survivingSet x.property) n
  let L := ∫ y, f y ∂μ.withDensity d.weight
  let A : ℕ → Path M → ℝ := fun n ω => pathBirkhoffSum f n ω / n
  let E : ℕ → Path M → ℝ := fun n ω => zeroExtension (fun y => |f y|) (ω n) / n
  have hzabs (z : Option M) : zeroExtension (fun y => |f y|) z = |zeroExtension f z| := by
    cases z <;> simp [zeroExtension]
  have hE0 (n : ℕ) (ω : Path M) : 0 ≤ E n ω := by
    dsimp [E]
    rw [hzabs]
    positivity
  have hEi (n : ℕ) : Integrable (E n) (C.conditionedMeasure x.val n) := (hend.1 n).div_const _
  have hElim : Tendsto (fun n => ∫ ω, E n ω ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
    simpa only [E, integral_div] using hend.2
  have hAi (n : ℕ) : Integrable (A n) (C.conditionedMeasure x.val n) := by
    have hgm : Measurable (fun ω : Path M => (n : ℝ)⁻¹ * pathBirkhoffSum (fun y => |f y|) n ω) :=
      (measurable_pathBirkhoffSum hfm n).const_mul _
    have hg0 (ω : Path M) : 0 ≤ (n : ℝ)⁻¹ * pathBirkhoffSum (fun y => |f y|) n ω :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
        ((abs_nonneg (pathBirkhoffSum f n ω)).trans (RefinedLLN.abs_pathBirkhoffSum_le f n ω))
    have hgi : Integrable (fun ω : Path M => (n : ℝ)⁻¹ * pathBirkhoffSum (fun y => |f y|) n ω)
        (C.conditionedMeasure x.val n) := by
      apply integrable_of_lintegral_ne_top hgm hg0
      rw [conditioned_average_eq_ofReal C x.val (d.liveSet_subset_survivingSet x.property)
        n hfm (fun y => abs_nonneg (f y)) hfx]
      exact ENNReal.ofReal_ne_top
    apply hgi.mono' ((measurable_pathBirkhoffSum hf n).div_const _).aestronglyMeasurable
    apply ae_of_all
    intro ω
    simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left
      (RefinedLLN.abs_pathBirkhoffSum_le f n ω) (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hAerr (n : ℕ) : Integrable (fun ω => |A n ω - L|) (C.conditionedMeasure x.val n) :=
    ((hAi n).sub (integrable_const L)).abs
  have hAlim : Tendsto (fun n => ∫ ω, |A n ω - L| ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
    simpa only [A, div_eq_mul_inv, mul_comm] using hlim
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hstart := (constant_div_tendsto_zero |f x.val| hnat)
  have hconst := (constant_div_tendsto_zero |L|
    (hnat.comp (tendsto_add_atTop_nat 1)))
  constructor
  · have hb := (hAlim.add hElim).add hstart
    simp only [add_zero] at hb
    apply squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) (fun n => ?_) hb
    calc
      _ ≤ ∫ ω, (|A n ω - L| + E n ω + |f x.val| / n) ∂C.conditionedMeasure x.val n := by
        apply integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
          (((hAerr n).add (hEi n)).add (integrable_const _))
        filter_upwards [C.ae_initial_conditionedMeasure x.val n] with ω hω
        change |_ - L| ≤ |A n ω - L| + E n ω + _
        have hid : pathShiftedBirkhoffSum f n ω / n - L =
            (A n ω - L) + zeroExtension f (ω n) / n - f x.val / n := by
          have hd := birkhoffSum_endpoint_difference (fun i => zeroExtension f (ω i)) n
          change pathBirkhoffSum f n ω - pathShiftedBirkhoffSum f n ω = _ at hd
          rw [hω, zeroExtension_some] at hd
          dsimp [A]
          linear_combination -(n : ℝ)⁻¹ * hd
        rw [hid]
        calc
          _ ≤ |A n ω - L| + |zeroExtension f (ω n) / n| + |f x.val / n| :=
            (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
          _ = _ := by simp only [E, hzabs, abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      _ = _ := by
        rw [integral_add (f := fun ω => |A n ω - L| + E n ω)
          ((hAerr n).add (hEi n)) (integrable_const _),
          integral_add (hAerr n) (hEi n), integral_const, probReal_univ, one_smul]
  · have hb := (hAlim.add hElim).add hconst
    simp only [add_zero] at hb
    apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun ω => abs_nonneg _) _ hb
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    calc
      _ ≤ ∫ ω, (|A n ω - L| + E n ω + |L| / (n + 1 : ℕ)) ∂C.conditionedMeasure x.val n := by
        apply integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
          (((hAerr n).add (hEi n)).add (integrable_const _))
        apply ae_of_all
        intro ω
        change |_ - L| ≤ |A n ω - L| + E n ω + _
        have hid : pathBirkhoffSum f (n + 1) ω / (n + 1 : ℕ) - L =
            ((n : ℝ) / (n + 1 : ℕ)) * (A n ω - L) +
              zeroExtension f (ω n) / (n + 1 : ℕ) - L / (n + 1 : ℕ) := by
          rw [pathBirkhoffSum_succ]
          dsimp [A]
          push_cast
          field_simp
          ring
        rw [hid]
        have hratio : (n : ℝ) / (n + 1 : ℕ) ≤ 1 := by
          rw [div_le_one hn1]
          exact_mod_cast Nat.le_succ n
        have hratio0 : 0 ≤ (n : ℝ) / (n + 1 : ℕ) := by positivity
        have hb1 : |((n : ℝ) / (n + 1 : ℕ)) * (A n ω - L)| ≤ |A n ω - L| := by
          rw [abs_mul, abs_of_nonneg hratio0]
          exact mul_le_of_le_one_left (abs_nonneg _) hratio
        have hb2 : |zeroExtension f (ω n) / (n + 1 : ℕ)| ≤ E n ω := by
          rw [abs_div, abs_of_pos hn1]
          dsimp [E]
          rw [hzabs]
          exact div_le_div_of_nonneg_left (abs_nonneg _) hn0 (by exact_mod_cast Nat.le_succ n)
        have hb3 : |L / (n + 1 : ℕ)| = |L| / (n + 1 : ℕ) := by rw [abs_div, abs_of_pos hn1]
        exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans
          (add_le_add (add_le_add hb1 hb2) hb3.le))
      _ = _ := by
        rw [integral_add (f := fun ω => |A n ω - L| + E n ω)
          ((hAerr n).add (hEi n)) (integrable_const _),
          integral_add (hAerr n) (hEi n), integral_const, probReal_univ, one_smul]
        rfl

end CanonicalChain
end ConditionedStableLaws
