import ConditionedStableLaws.AnnularCompensation
import ConditionedStableLaws.CompensatedSeries

/-!
Construction of compensated Poisson integrals as L² limits.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.AnnularPoissonClouds
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)
  (f : ExtremeState → ℝ) (hf : Measurable f)
  {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B)

/-- The L² sum of centered integrals of the independent annular clouds. -/
def compensatedIntegral : Sample → ℝ :=
  CompensatedSeries.sumVariable (law υ hυ) (centeredComponent υ f)
    (centeredComponent_memLp υ hυ f hf hB hb)

theorem measurable_compensatedIntegral :
    Measurable (compensatedIntegral υ hυ f hf hB hb) :=
  CompensatedSeries.measurable_sumVariable _ _ _

theorem compensatedIntegral_memLp :
    MemLp (compensatedIntegral υ hυ f hf hB hb) 2 (law υ hυ) :=
  CompensatedSeries.memLp_sumVariable _ _ _

variable (hfi : Integrable (fun x => (f x)^2) υ)

include hfi

theorem centered_partialSum_tendsto_eLpNorm :
    Tendsto (fun n => eLpNorm
      (CompensatedSeries.partialSum (centeredComponent υ f) n -
        compensatedIntegral υ hυ f hf hB hb) 2 (law υ hυ)) atTop (𝓝 0) :=
  CompensatedSeries.partialSum_tendsto_eLpNorm _ _ _
    (independent_centeredComponents υ hυ f hf) (centeredComponent_mean υ hυ f hf hB hb)
    (centeredComponent_second_moments_hasSum υ hυ f hf hB hb hfi).summable

theorem centered_partialSum_tendstoInDistribution :
    TendstoInDistribution (CompensatedSeries.partialSum (centeredComponent υ f)) atTop
      (compensatedIntegral υ hυ f hf hB hb) (fun _ => law υ hυ) (law υ hυ) :=
  CompensatedSeries.partialSum_tendstoInDistribution _ _ _
    (independent_centeredComponents υ hυ f hf) (centeredComponent_mean υ hυ f hf hB hb)
    (centeredComponent_second_moments_hasSum υ hυ f hf hB hb hfi).summable

theorem compensatedIntegral_mean :
    (∫ ω, compensatedIntegral υ hυ f hf hB hb ω ∂law υ hυ) = 0 :=
  CompensatedSeries.sumVariable_mean _ _ _
    (independent_centeredComponents υ hυ f hf) (centeredComponent_mean υ hυ f hf hB hb)
    (centeredComponent_second_moments_hasSum υ hυ f hf hB hb hfi).summable

/-- The Poisson isometry, with its exact intensity integral. -/
theorem compensatedIntegral_second_moment :
    (∫ ω, (compensatedIntegral υ hυ f hf hB hb ω)^2 ∂law υ hυ) =
      ∫ x, (f x)^2 ∂υ := by
  rw [compensatedIntegral, CompensatedSeries.sumVariable_secondMoment _ _ _
    (independent_centeredComponents υ hυ f hf) (centeredComponent_mean υ hυ f hf hB hb)
    (centeredComponent_second_moments_hasSum υ hυ f hf hB hb hfi).summable]
  exact (centeredComponent_second_moments_hasSum υ hυ f hf hB hb hfi).tsum_eq

theorem compensatedIntegral_tail_second_moment (k : ℕ) :
    (∫ ω, (compensatedIntegral υ hυ f hf hB hb ω -
      CompensatedSeries.partialSum (centeredComponent υ f) k ω)^2 ∂law υ hυ) =
      ∑' n, ∫ x, (f x)^2 ∂υ.restrict (annulus (n + k)) := by
  rw [compensatedIntegral, CompensatedSeries.tail_secondMoment _ _ _
    (independent_centeredComponents υ hυ f hf) (centeredComponent_mean υ hυ f hf hB hb)
    (centeredComponent_second_moments_hasSum υ hυ f hf hB hb hfi).summable]
  simp_rw [centeredComponent_second_moment υ hυ f hf hB hb]

end
end ConditionedStableLaws.AnnularPoissonClouds
