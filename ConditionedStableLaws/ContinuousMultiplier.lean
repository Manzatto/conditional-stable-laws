import ConditionedStableLaws.StableLawSmall
import ConditionedStableLaws.SmallJumpMoment
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Continuous multipliers of the singular observable

The observable `f_β g` for a continuous multiplier `g`. The estimates below follow from continuity
at the singularity and compactness.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ConditionedStableLaws.ContinuousMultiplier

noncomputable section

variable {M : Type*} [MetricSpace M]

/-- The observable `f_β g` with a continuous multiplier `g`. -/
def observable (x₀ : M) (β : ℝ) (g : M → ℝ) : M → ℝ :=
  fun x => singularObservable x₀ β x * g x

/-- The difference from the constant multiplier `g(x₀)`. -/
def residual (x₀ : M) (β : ℝ) (g : M → ℝ) : M → ℝ :=
  fun x => singularObservable x₀ β x * (g x - g x₀)

@[simp] theorem observable_sub_center (x₀ : M) (β : ℝ) (g : M → ℝ) (x : M) :
    observable x₀ β g x - g x₀ * singularObservable x₀ β x = residual x₀ β g x := by
  unfold observable residual
  ring

/-- Outside any fixed ball, the singular observable is bounded. The bound also
covers the finite convention at the centre. -/
theorem singular_le_off_ball {x₀ : M} {β r : ℝ} (hβ : 0 < β) (hr : 0 < r)
    {x : M} (hx : r ≤ dist x x₀) : singularObservable x₀ β x ≤ r ^ (-β) := by
  have hne : x ≠ x₀ := by rintro rfl; simp at hx; linarith
  simp only [singularObservable, ite_eq_right hne]
  exact Real.rpow_le_rpow_of_nonpos hr hx (neg_nonpos.mpr hβ.le)

/-- Every continuous multiplier error is an arbitrarily small multiple of
`f_β`, up to a bounded remainder. The bounded remainder is global and deterministic. -/
theorem residual_bound [CompactSpace M] {x₀ : M} {β : ℝ} (hβ : 0 < β) {g : M → ℝ}
    (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
      |residual x₀ β g x| ≤ ε * singularObservable x₀ β x + K := by
  obtain ⟨r, hr, hlocal⟩ := Metric.continuousAt_iff.mp hg.continuousAt ε hε
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hg.sub continuous_const).continuousOn : ContinuousOn (fun x => g x - g x₀) univ)
  have hD0 : 0 ≤ D := (norm_nonneg (g x₀ - g x₀)).trans (hD x₀ (mem_univ _))
  refine ⟨D * r ^ (-β), mul_nonneg hD0 (Real.rpow_nonneg hr.le _), fun x => ?_⟩
  have hf0 := (singularObservable_pos x₀ β x).le
  rw [residual, abs_mul, abs_of_nonneg hf0]
  by_cases hx : dist x x₀ < r
  · have hsmall : |g x - g x₀| ≤ ε := by
      simpa only [Real.dist_eq] using (hlocal hx).le
    calc
      singularObservable x₀ β x * |g x - g x₀| ≤ singularObservable x₀ β x * ε :=
        mul_le_mul_of_nonneg_left hsmall hf0
      _ ≤ ε * singularObservable x₀ β x + D * r ^ (-β) := by
        nlinarith [mul_nonneg hD0 (Real.rpow_nonneg hr.le (-β))]
  · have hlarge := singular_le_off_ball hβ hr (le_of_not_gt hx)
    have hgb : |g x - g x₀| ≤ D := by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hD x (mem_univ _)
    calc
      singularObservable x₀ β x * |g x - g x₀| ≤ r ^ (-β) * D :=
        mul_le_mul hlarge hgb (abs_nonneg _) (Real.rpow_nonneg hr.le _)
      _ ≤ ε * singularObservable x₀ β x + D * r ^ (-β) := by nlinarith

section Measurable

variable [MeasurableSpace M] [BorelSpace M]

theorem measurable_observable (x₀ : M) (β : ℝ) {g : M → ℝ} (hg : Continuous g) :
    Measurable (observable x₀ β g) :=
  (measurable_singularObservable x₀ β).mul hg.measurable

theorem measurable_residual (x₀ : M) (β : ℝ) {g : M → ℝ} (hg : Continuous g) :
    Measurable (residual x₀ β g) :=
  (measurable_singularObservable x₀ β).mul (hg.measurable.sub measurable_const)

omit [MetricSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The pathwise remainder estimate, including paths that have already been killed. -/
theorem path_residual_bound {f r : M → ℝ} {ε K : ℝ} (hK : 0 ≤ K)
    (hr : ∀ x, |r x| ≤ ε * f x + K) (n : ℕ)
    (ω : CanonicalChain.Path M) :
    |pathBirkhoffSum r n ω| ≤
      ε * pathBirkhoffSum f n ω + n * K := by
  unfold pathBirkhoffSum birkhoffSum
  calc
    _ ≤ ∑ j ∈ Finset.range n, |zeroExtension r (ω j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, (ε * zeroExtension f (ω j) + K) := by
      apply Finset.sum_le_sum
      intro j _
      cases ω j with
      | none => simpa only [zeroExtension, abs_zero, mul_zero, zero_add] using hK
      | some x => exact hr x
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp

end Measurable

section Tightness

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
  (Q : Measure Ω') [IsProbabilityMeasure Q]

omit [MetricSpace M] in
/-- A convergent sequence of real laws is uniformly bounded in probability. -/
theorem bounded_in_probability {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ n, Measurable (X n)) (hlim : TendstoInDistribution X atTop Z P Q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ n, (P n).real {ω | R < |X n ω|} < δ := by
  let μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨(P n).map (X n), inferInstance⟩
  let μlim : ProbabilityMeasure ℝ := ⟨Q.map Z, inferInstance⟩
  have hcompact : IsCompact (insert μlim (range μs)) := hlim.tendsto.isCompact_insert_range
  have htight := isTightMeasureSet_of_isCompact_closure
    (S := insert μlim (range μs)) (by rwa [hcompact.isClosed.closure_eq])
  obtain ⟨K, hK, hmass⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
    (ENNReal.ofReal (δ / 2)) (ENNReal.ofReal_pos.mpr (half_pos hδ))
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun n => ?_⟩
  have hset : {z : ℝ | max R 1 < |z|} ⊆ Kᶜ := by
    intro z hz hzK
    have hb : |z| ≤ R := by simpa only [Real.norm_eq_abs, id_eq] using hR z hzK
    exact not_lt_of_ge (hb.trans (le_max_left _ _)) hz
  have hmeas : (P n) {ω | max R 1 < |X n ω|} ≤ ENNReal.ofReal (δ / 2) := by
    have hm := hmass (μs n) ⟨μs n, mem_insert_of_mem _ (mem_range_self n), rfl⟩
    calc
      _ = ((μs n : ProbabilityMeasure ℝ) : Measure ℝ) {z | max R 1 < |z|} := by
        change _ = (P n).map (X n) {z | max R 1 < |z|}
        rw [Measure.map_apply (hX n) (measurableSet_lt measurable_const continuous_abs.measurable)]
        rfl
      _ ≤ (μs n : Measure ℝ) Kᶜ := measure_mono hset
      _ ≤ _ := hm
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeas
  rw [ENNReal.toReal_ofReal (half_pos hδ).le] at hr
  exact hr.trans_lt (half_lt_self hδ)

omit [MetricSpace M] in
/-- An error bounded by an arbitrarily small multiple of a tight observation,
plus a deterministic vanishing term, is negligible under the varying laws. -/
theorem probability_negligible_of_relative_bound {X R : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ n, Measurable (X n)) (hlim : TendstoInDistribution X atTop Z P Q)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    (hbound : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧
      ∀ n ω, |R n ω| ≤ η * |X n ω| + K * a n) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P n).real {ω | ε < |R n ω|}) atTop (𝓝 0) := by
  intro ε hε
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨L, hL, htail⟩ := bounded_in_probability P Q hX hlim hδ
  obtain ⟨K, hK, hb⟩ := hbound (ε / (2 * L)) (by positivity)
  have hsmall : ∀ᶠ n in atTop, K * a n < ε / 2 := by
    have hh : Tendsto (fun n => K * a n) atTop (𝓝 0) := by simpa using ha.const_mul K
    exact hh.eventually_lt_const (half_pos hε)
  filter_upwards [hsmall] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  apply lt_of_le_of_lt (measureReal_mono ?_) (htail n)
  intro ω hω
  change L < |X n ω|
  by_contra hc
  have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hc)
    (show 0 ≤ ε / (2 * L) by positivity)
  have heq : ε / (2 * L) * L = ε / 2 := by field_simp
  rw [heq] at hmul
  have hb' := hb n ω
  change ε < |R n ω| at hω
  linarith

end Tightness

end
end ConditionedStableLaws.ContinuousMultiplier
