import Mathlib.Probability.CramerWold
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Weak convergence with probability measures depending on `n`, as after conditioning on survival, and
the Cramér–Wold device. The proof uses Lévy's convergence theorem.
-/

open Filter MeasureTheory RealInnerProductSpace
open scoped Topology

namespace ConditionedStableLaws

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
  {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- Convergence of expectations of bounded continuous test functions agrees with weak convergence of
the pushforward probability measures. -/
theorem weak_convergence_iff_testFunctions
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    {X : ℕ → Ω → S} {Z : Ω' → S}
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hZ : AEMeasurable Z P') :
    TendstoInDistribution X atTop Z P P' ↔
      ∀ f : BoundedContinuousFunction S ℝ,
        Tendsto (fun n => ∫ ω, f (X n ω) ∂P n) atTop (𝓝 (∫ ω, f (Z ω) ∂P')) :=
  tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hX hZ

/-- Cramér–Wold with changing underlying measures, needed for conditioned laws. -/
theorem cramerWold_varyingMeasures
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hZ : AEMeasurable Z P') :
    TendstoInDistribution X atTop Z P P' ↔
      ∀ u : E, TendstoInDistribution (fun n ω => ⟪X n ω, u⟫) atTop
        (fun ω => ⟪Z ω, u⟫) P P' := by
  constructor
  · intro h u
    exact h.continuous_comp (continuous_id.inner continuous_const)
  · intro h
    refine .of_tendsto_charFun hX hZ fun u => ?_
    rw [charFun_map_eq_charFun_map_inner_one hZ]
    refine ((h u).tendsto_charFun 1).congr fun n => ?_
    rw [charFun_map_eq_charFun_map_inner_one (hX n)]

/-- Coordinate-sum form of the Cramér–Wold device, for any dimension including zero. -/
theorem cramerWold_coordinates {k : ℕ}
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)} {Z : Ω' → EuclideanSpace ℝ (Fin k)}
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hZ : AEMeasurable Z P') :
    TendstoInDistribution X atTop Z P P' ↔
      ∀ u : EuclideanSpace ℝ (Fin k),
        TendstoInDistribution (fun n ω => ∑ j, u j * X n ω j) atTop
          (fun ω => ∑ j, u j * Z ω j) P P' := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial] using cramerWold_varyingMeasures hX hZ

end ConditionedStableLaws
