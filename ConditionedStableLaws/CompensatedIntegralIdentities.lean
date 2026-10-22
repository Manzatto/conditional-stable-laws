import ConditionedStableLaws.CompensatedPoissonIntegral
import ConditionedStableLaws.PoissonLaplace

/-!
Linearity and integral identities for the constructed compensated sums.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem tendstoInMeasure_sub_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X Y : ℕ → Ω → ℝ} {x y : Ω → ℝ}
    (hX : TendstoInMeasure P X atTop x) (hY : TendstoInMeasure P Y atTop y) :
    TendstoInMeasure P (fun n ω => X n ω-Y n ω) atTop (fun ω => x ω-y ω) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro ε hε
  have ht := (hX (ε/2) (half_pos hε)).add (hY (ε/2) (half_pos hε))
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) (fun n => ?_)
  apply (measure_mono (show {ω | ε ≤ dist (X n ω-Y n ω) (x ω-y ω)} ⊆
    {ω | ε/2 ≤ dist (X n ω) (x ω)} ∪ {ω | ε/2 ≤ dist (Y n ω) (y ω)} from ?_)).trans
    (measure_union_le _ _)
  intro ω hω
  by_contra hn
  have ha : dist (X n ω) (x ω) < ε/2 := not_le.mp (fun h => hn (Or.inl h))
  have hb : dist (Y n ω) (y ω) < ε/2 := not_le.mp (fun h => hn (Or.inr h))
  change ε ≤ dist (X n ω-Y n ω) (x ω-y ω) at hω
  rw [Real.dist_eq, show X n ω-Y n ω-(x ω-y ω) = (X n ω-x ω)-(Y n ω-y ω) by ring] at hω
  simp only [Real.dist_eq] at ha hb
  have hh := abs_sub (X n ω-x ω) (Y n ω-y ω)
  linarith

namespace AnnularPoissonClouds

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)

theorem compensatedIntegral_sub_ae
    (f g k : ExtremeState → ℝ) (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    {B : ℝ} (hB : 0 ≤ B) (hfb : ∀ y, ‖f y‖ ≤ B) (hgb : ∀ y, ‖g y‖ ≤ B)
    (hkb : ∀ y, ‖k y‖ ≤ B)
    (hfi : Integrable (fun y => (f y)^2) υ) (hgi : Integrable (fun y => (g y)^2) υ)
    (hki : Integrable (fun y => (k y)^2) υ) (he : ∀ y, k y = f y-g y) :
    compensatedIntegral υ hυ k hk hB hkb =ᵐ[law υ hυ]
      (fun ω => compensatedIntegral υ hυ f hf hB hfb ω -
        compensatedIntegral υ hυ g hg hB hgb ω) := by
  have hterm (i : ℕ) (ω : Sample) : centeredComponent υ k i ω =
      centeredComponent υ f i ω-centeredComponent υ g i ω := by
    have : IsFiniteMeasure (υ.restrict (annulus i)) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact annulus_measure_lt_top υ hυ i⟩
    have hif : Integrable f (υ.restrict (annulus i)) :=
      Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hfb)
    have hig : Integrable g (υ.restrict (annulus i)) :=
      Integrable.of_bound hg.aestronglyMeasurable B (ae_of_all _ hgb)
    simp only [centeredComponent, FinitePoissonCloud.testIntegral_eq_sum, he]
    rw [Finset.sum_sub_distrib, integral_sub hif hig]
    ring
  have hpart (n : ℕ) : CompensatedSeries.partialSum (centeredComponent υ k) n =
      (fun ω => CompensatedSeries.partialSum (centeredComponent υ f) n ω-
        CompensatedSeries.partialSum (centeredComponent υ g) n ω) := by
    funext ω
    simp only [CompensatedSeries.partialSum, hterm, Finset.sum_sub_distrib]
  have htf := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (centered_partialSum_tendsto_eLpNorm υ hυ f hf hB hfb hfi)
  have htg := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (centered_partialSum_tendsto_eLpNorm υ hυ g hg hB hgb hgi)
  have htk := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (centered_partialSum_tendsto_eLpNorm υ hυ k hk hB hkb hki)
  have hparts : CompensatedSeries.partialSum (centeredComponent υ k) =
      (fun n ω => CompensatedSeries.partialSum (centeredComponent υ f) n ω-
        CompensatedSeries.partialSum (centeredComponent υ g) n ω) := funext hpart
  rw [hparts] at htk
  exact tendstoInMeasure_ae_unique htk (tendstoInMeasure_sub_real _ htf htg)

/-- When a nonnegative test is integrable, the L² construction is exactly its Poisson integral minus
its deterministic intensity integral. -/
theorem compensatedIntegral_eq_centered_integral_ae
    (f : ExtremeState → ℝ) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B)
    (hfi : Integrable f υ) (hfsq : Integrable (fun y => (f y)^2) υ) :
    compensatedIntegral υ hυ f hf hB hb =ᵐ[law υ hυ]
      (fun ω => (∫⁻ y, ENNReal.ofReal (f y) ∂(randomMeasure.toFun ω).toMeasure).toReal -
        ∫ y, f y ∂υ) := by
  have hfinite : ∀ᵐ ω ∂law υ hυ,
      (∫⁻ y, ENNReal.ofReal (f y) ∂(randomMeasure.toFun ω).toMeasure) < ∞ :=
    lintegral_lt_top_ae υ hυ _ hf.ennreal_ofReal
      ((lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
        (ae_of_all _ hf0)).mpr hfi).lt_top
  have hmeans : Tendsto (fun n => ∑ i ∈ Finset.range n,
      ∫ y, f y ∂υ.restrict (annulus i)) atTop (𝓝 (∫ y, f y ∂υ)) := by
    have hi : Integrable f (Measure.sum (fun i => υ.restrict (annulus i))) := by
      rwa [sum_restrict_annulus]
    simpa only [sum_restrict_annulus] using (hasSum_integral_measure hi).tendsto_sum_nat
  have ht : ∀ᵐ ω ∂law υ hυ, Tendsto
      (fun n => CompensatedSeries.partialSum (centeredComponent υ f) n ω) atTop
      (𝓝 ((∫⁻ y, ENNReal.ofReal (f y) ∂(randomMeasure.toFun ω).toMeasure).toReal - ∫ y, f y ∂υ)) := by
    filter_upwards [component_testIntegral_tendsto υ hυ f hf hf0 hfinite] with ω hω
    simpa only [CompensatedSeries.partialSum, centeredComponent, Finset.sum_sub_distrib] using hω.sub hmeans
  have htc := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (centered_partialSum_tendsto_eLpNorm υ hυ f hf hB hb hfsq)
  exact tendstoInMeasure_ae_unique htc (tendstoInMeasure_of_tendsto_ae
    (fun n => (Finset.measurable_sum _ (fun i _ => measurable_centeredComponent υ f hf i)).aestronglyMeasurable) ht)

end AnnularPoissonClouds
end
end ConditionedStableLaws
