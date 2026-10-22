import ConditionedStableLaws.QProcessLimit
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# One- and two-time laws of Markov trajectories

For a Markov kernel `K` and the trajectory law `ℙₓ` started at `x`, the law of `Xₘ` is `Kᵐ(x, ·)`
and the law of `(Xᵢ, Xᵢ₊ₘ)` is `Kⁱ(x, ·) ⊗ Kᵐ`. Both follow from the Markov property. Consequently
`E[a(Xᵢ) b(Xᵢ₊ₘ)] = ∫ a (Kᵐ b) dKⁱ(x, ·)` for bounded measurable real `a`, `b`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace ConditionedStableLaws.MarkovPairs

noncomputable section

open QProcessLimit

variable {X : Type*} [MeasurableSpace X] (K : Kernel X X) [IsMarkovKernel K]

theorem isMarkovKernel_pow (n : ℕ) : IsMarkovKernel (K ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel X X); infer_instance
  | succ n ih => rw [Kernel.pow_add, pow_one]; infer_instance

/-- One-time law, nonnegative form. -/
theorem lintegral_single (x : X) (m : ℕ) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (ω m) ∂pathMeasure K x = ∫⁻ y, g y ∂(K ^ m) x := by
  have h := lintegral_history_future K x 0 m (fun _ => 1) measurable_const g hg
  simp only [one_mul, zero_add, historyLaw_zero] at h
  have hmeas : Measurable (fun h : History X 0 => ∫⁻ y, g y ∂(K ^ m) (last 0 h)) :=
    (Measure.measurable_lintegral hg).comp ((K ^ m).measurable.comp (measurable_pi_apply _))
  rw [h, lintegral_dirac' _ hmeas]
  rfl

/-- Two-time law, nonnegative form. -/
theorem lintegral_pair (x : X) (i m : ℕ) {a b : X → ℝ≥0∞} (ha : Measurable a)
    (hb : Measurable b) :
    ∫⁻ ω, a (ω i) * b (ω (i + m)) ∂pathMeasure K x =
      ∫⁻ y, a y * ∫⁻ z, b z ∂(K ^ m) y ∂(K ^ i) x := by
  have hG : Measurable (fun y => ∫⁻ z, b z ∂(K ^ m) y) :=
    (Measure.measurable_lintegral hb).comp (K ^ m).measurable
  have h := lintegral_history_future K x i m (fun h => a (last i h))
    (ha.comp (measurable_pi_apply _)) b hb
  have hmap : ∫⁻ h, a (last i h) * ∫⁻ z, b z ∂(K ^ m) (last i h) ∂historyLaw K x i =
      ∫⁻ ω, a (ω i) * ∫⁻ z, b z ∂(K ^ m) (ω i) ∂pathMeasure K x := by
    unfold historyLaw
    rw [lintegral_map (f := fun h : History X i => a (last i h) * ∫⁻ z, b z ∂(K ^ m) (last i h))
      ((ha.mul hG).comp (measurable_pi_apply _)) (Preorder.measurable_frestrictLe i)]
    rfl
  change ∫⁻ ω, a (last i (Preorder.frestrictLe i ω)) * b (ω (i + m)) ∂pathMeasure K x = _
  rw [h]
  change ∫⁻ h, a (last i h) * ∫⁻ z, b z ∂(K ^ m) (last i h) ∂historyLaw K x i = _
  rw [hmap]
  exact lintegral_single K x i (ha.mul hG)

/-- The law of `Xₘ` under `ℙₓ` is `Kᵐ(x, ·)`. -/
theorem map_single (x : X) (m : ℕ) :
    (pathMeasure K x).map (fun ω => ω m) = (K ^ m) x := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply m) hs]
  have h := lintegral_single K x m (measurable_const.indicator hs : Measurable
    (s.indicator fun _ => (1 : ℝ≥0∞)))
  simp only [lintegral_indicator hs, lintegral_const, one_mul, Measure.restrict_apply_univ] at h
  rw [← h, ← lintegral_indicator_one (hs.preimage (measurable_pi_apply m))]
  rfl

/-- The law of `(Xᵢ, Xᵢ₊ₘ)` under `ℙₓ` is `Kⁱ(x, ·) ⊗ Kᵐ`. -/
theorem map_pair (x : X) (i m : ℕ) :
    (pathMeasure K x).map (fun ω => (ω i, ω (i + m))) = (K ^ i) x ⊗ₘ (K ^ m) := by
  have := isMarkovKernel_pow K i
  have := isMarkovKernel_pow K m
  have hmeas : Measurable (fun ω : ℕ → X => (ω i, ω (i + m))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply (i + m))
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    rw [Measure.map_apply hmeas (hs.prod ht), Measure.compProd_apply_prod hs ht]
    have h := lintegral_pair K x i m (measurable_const.indicator hs : Measurable
      (s.indicator fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator ht : Measurable
      (t.indicator fun _ => (1 : ℝ≥0∞)))
    have hl : ∫⁻ ω, s.indicator (fun _ => (1 : ℝ≥0∞)) (ω i) *
        t.indicator (fun _ => (1 : ℝ≥0∞)) (ω (i + m)) ∂pathMeasure K x =
        pathMeasure K x ((fun ω : ℕ → X => (ω i, ω (i + m))) ⁻¹' s ×ˢ t) := by
      rw [← lintegral_indicator_one ((hs.prod ht).preimage hmeas)]
      apply lintegral_congr
      intro ω
      by_cases h1 : ω i ∈ s <;> by_cases h2 : ω (i + m) ∈ t <;>
        simp [Set.indicator, h1, h2]
    have hr : ∫⁻ y, s.indicator (fun _ => (1 : ℝ≥0∞)) y *
        ∫⁻ z, t.indicator (fun _ => (1 : ℝ≥0∞)) z ∂(K ^ m) y ∂(K ^ i) x =
        ∫⁻ y in s, (K ^ m) y t ∂(K ^ i) x := by
      rw [← lintegral_indicator hs]
      apply lintegral_congr
      intro y
      have hlt : ∫⁻ z, t.indicator (fun _ => (1 : ℝ≥0∞)) z ∂(K ^ m) y = (K ^ m) y t :=
        lintegral_indicator_one ht
      by_cases hy : y ∈ s
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul, hlt]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
    rw [← hl, h, hr]
  · rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ, measure_univ,
      measure_univ]

/-- `E[a(Xᵢ) b(Xᵢ₊ₘ)] = ∫ a(y) ∫ b dKᵐ(y) dKⁱ(x, dy)` for bounded measurable `a`, `b`. -/
theorem integral_pair (x : X) (i m : ℕ) {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (hA : ∀ y, |a y| ≤ A) (hB : ∀ y, |b y| ≤ B) :
    ∫ ω, a (ω i) * b (ω (i + m)) ∂pathMeasure K x =
      ∫ y, a y * ∫ z, b z ∂(K ^ m) y ∂(K ^ i) x := by
  have := isMarkovKernel_pow K i
  have := isMarkovKernel_pow K m
  have hmeas : Measurable (fun ω : ℕ → X => (ω i, ω (i + m))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply (i + m))
  have hf : Measurable (fun p : X × X => a p.1 * b p.2) :=
    (ha.comp measurable_fst).mul (hb.comp measurable_snd)
  have hint : Integrable (fun p : X × X => a p.1 * b p.2) ((K ^ i) x ⊗ₘ (K ^ m)) := by
    refine Integrable.of_bound hf.aestronglyMeasurable (A * B) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hA _) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hA p.1))
  calc ∫ ω, a (ω i) * b (ω (i + m)) ∂pathMeasure K x
      = ∫ p, a p.1 * b p.2 ∂(pathMeasure K x).map (fun ω => (ω i, ω (i + m))) :=
        (integral_map hmeas.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ p, a p.1 * b p.2 ∂((K ^ i) x ⊗ₘ (K ^ m)) := by rw [map_pair]
    _ = ∫ y, ∫ z, a y * b z ∂(K ^ m) y ∂(K ^ i) x := Measure.integral_compProd hint
    _ = ∫ y, a y * ∫ z, b z ∂(K ^ m) y ∂(K ^ i) x := by
        congr 1
        funext y
        exact integral_const_mul _ _

/-- `E[a(Xₘ)] = ∫ a dKᵐ(x, ·)`. -/
theorem integral_single (x : X) (m : ℕ) {a : X → ℝ} (ha : Measurable a) :
    ∫ ω, a (ω m) ∂pathMeasure K x = ∫ y, a y ∂(K ^ m) x := by
  rw [← map_single K x m, integral_map (measurable_pi_apply m).aemeasurable
    ha.aestronglyMeasurable]

end

end ConditionedStableLaws.MarkovPairs
