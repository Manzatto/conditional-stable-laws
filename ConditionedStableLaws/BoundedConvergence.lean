import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Bounded convergence with changing probability measures

The conditional probabilities depend on the conditioning horizon, so dominated convergence under a
single fixed measure does not directly apply. Uniform boundedness and convergence in probability
imply convergence in mean even when the probability measure changes with the sequence index.
-/

open MeasureTheory Filter
open scoped Topology

namespace ConditionedStableLaws

namespace BoundedConvergence

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An eventual exponential tail bound implies convergence in probability, even for changing
underlying measures. Only the tail estimates themselves are needed. -/
theorem tendsto_in_probability_of_exponential_bound
    (μ : ℕ → Measure Ω) (Y : ℕ → Ω → ℝ) {a K : ℝ} (ha : 0 < a)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (μ n).real {x | ε < |Y n x|} ≤ K * Real.exp (-(a * ε ^ 2 * n))) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {x | ε < |Y n x|}) atTop (𝓝 0) := by
  intro ε hε
  have hscale : Tendsto (fun n : ℕ => a * ε ^ 2 * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos ha (sq_pos_of_pos hε))
  have he : Tendsto (fun n : ℕ => K * Real.exp (-(a * ε ^ 2 * n)))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale).const_mul K
  exact squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) (hbound ε hε) he

/-- Splitting at a positive threshold bounds the mean by the threshold plus
the uniform bound times the probability of exceeding that threshold. -/
theorem integral_abs_le_cutoff
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (B ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ᵐ x ∂μ, |Y x| ≤ B) :
    (∫ x, |Y x| ∂μ) ≤ ε + B * μ.real {x | ε < |Y x|} := by
  classical
  have habs : Measurable (fun x => |Y x|) := by
    simpa only [Real.norm_eq_abs] using hY.norm
  have hs : MeasurableSet {x | ε < |Y x|} :=
    measurableSet_lt measurable_const habs
  have hYint : Integrable (fun x => |Y x|) μ :=
    Integrable.of_bound habs.aestronglyMeasurable B (by simpa using hbound)
  have hI : Integrable ({x | ε < |Y x|}.indicator (fun _ => B)) μ :=
    (integrable_const B).indicator hs
  calc
    (∫ x, |Y x| ∂μ) ≤
        ∫ x, ε + {x | ε < |Y x|}.indicator (fun _ => B) x ∂μ := by
      apply integral_mono_ae hYint ((integrable_const ε).add hI)
      filter_upwards [hbound] with x hx
      change |Y x| ≤ ε + {x | ε < |Y x|}.indicator (fun _ => B) x
      by_cases hmem : x ∈ {x | ε < |Y x|}
      · rw [Set.indicator_of_mem hmem]
        linarith
      · rw [Set.indicator_of_notMem hmem, add_zero]
        exact le_of_not_gt hmem
    _ = ε + B * μ.real {x | ε < |Y x|} := by
      rw [integral_add (integrable_const ε) hI, integral_indicator_const B hs]
      simp [mul_comm]

/-- Uniformly bounded convergence in probability implies convergence of the
absolute first moment, for an arbitrary sequence of probability measures. -/
theorem tendsto_integral_abs_of_bounded_in_probability
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (B : ℝ)
    (hbound : ∀ n, ∀ᵐ x ∂μ n, |Y n x| ≤ B)
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {x | ε < |Y n x|}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |Y n x| ∂μ n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have htail : Tendsto (fun n => B * (μ n).real {x | ε / 2 < |Y n x|})
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hprob (ε / 2) hhalf)
  have hsmall : ∀ᶠ n in atTop, B * (μ n).real {x | ε / 2 < |Y n x|} < ε / 2 :=
    (tendsto_order.1 htail).2 (ε / 2) hhalf
  filter_upwards [hsmall] with n hn
  have hnonneg : 0 ≤ ∫ x, |Y n x| ∂μ n := integral_nonneg (fun x => abs_nonneg _)
  have hcut := integral_abs_le_cutoff (μ n) (Y n) (hY n) B (ε / 2)
    hhalf.le (hbound n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

/-- Markov's inequality for the strict absolute-value tail, in real-valued
measure notation. Finite measures suffice; normalization is not required. -/
theorem tail_le_integral_abs_div
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ)
    (hY : Integrable Y μ) (ε : ℝ) (hε : 0 < ε) :
    μ.real {x | ε < |Y x|} ≤ (∫ x, |Y x| ∂μ) / ε := by
  have hYabs : Integrable (fun x => |Y x|) μ := by
    simpa only [Real.norm_eq_abs] using hY.norm
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => abs_nonneg (Y x))) hYabs ε
  calc
    μ.real {x | ε < |Y x|} ≤ μ.real {x | ε ≤ |Y x|} :=
      measureReal_mono (by
        intro x hx
        change ε < |Y x| at hx
        exact hx.le)
    _ ≤ (∫ x, |Y x| ∂μ) / ε := by
      apply (le_div_iff₀ hε).2
      simpa only [mul_comm] using hmarkov

/-- Convergence in absolute first moment implies convergence in probability,
also when the underlying finite measures vary with the sequence index. -/
theorem tendsto_in_probability_of_integral_abs
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Integrable (Y n) (μ n))
    (hmean : Tendsto (fun n => ∫ x, |Y n x| ∂μ n) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {x | ε < |Y n x|}) atTop (𝓝 0) := by
  intro ε hε
  apply squeeze_zero (fun n => measureReal_nonneg)
    (fun n => tail_le_integral_abs_div (μ n) (Y n) (hY n) ε hε)
  simpa using hmean.div_const ε

/-- Under a common almost-everywhere bound, convergence in probability and
convergence in absolute first moment are equivalent for changing probability
measures. -/
theorem bounded_probability_iff_integral_abs
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (B : ℝ)
    (hbound : ∀ n, ∀ᵐ x ∂μ n, |Y n x| ≤ B) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {x | ε < |Y n x|}) atTop (𝓝 0)) ↔
      Tendsto (fun n => ∫ x, |Y n x| ∂μ n) atTop (𝓝 0) := by
  constructor
  · exact tendsto_integral_abs_of_bounded_in_probability μ Y hY B hbound
  · apply tendsto_in_probability_of_integral_abs μ Y
    intro n
    exact Integrable.of_bound (hY n).aestronglyMeasurable B (by simpa using hbound n)

end BoundedConvergence

end ConditionedStableLaws
