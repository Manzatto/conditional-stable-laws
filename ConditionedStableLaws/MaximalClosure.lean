import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Real

/-!
# Passing almost-everywhere convergence through maximal approximations

Borel–Cantelli turns summable maximal approximation errors into a uniform approximation in the time
index, almost everywhere. This closure argument is used with the kernel maximal inequality and
rapidly converging `L¹` truncations.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace ConditionedStableLaws.MaximalClosure

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem tendsto_ae_of_maximal_approximation
    (F : ℕ → X → ℝ) (G : ℕ → ℕ → X → ℝ) (b L : ℕ → ℝ) (a : ℝ)
    (hb : Tendsto b atTop (𝓝 0)) (hL : Tendsto L atTop (𝓝 a))
    (hG : ∀ j, ∀ᵐ x ∂ν, Tendsto (fun n => G j n x) atTop (𝓝 (L j)))
    (hmax : (∑' j, ν {x | ∃ n, b j < |F n x - G j n x|}) ≠ ∞) :
    ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 a) := by
  filter_upwards [ae_eventually_notMem hmax, ae_all_iff.2 hG] with x hx hGx
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hb' : ∀ᶠ j in atTop, b j < ε / 3 :=
    (tendsto_order.1 hb).2 _ (by linarith)
  have hL' : ∀ᶠ j in atTop, |L j - a| < ε / 3 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.1 hL) (ε / 3) (by linarith)
  obtain ⟨j, hj, hbj, hLj⟩ := (hx.and (hb'.and hL')).exists
  have hdiff (n : ℕ) : |F n x - G j n x| ≤ b j :=
    le_of_not_gt (fun hn => hj ⟨n, hn⟩)
  have hGj : ∀ᶠ n in atTop, |G j n x - L j| < ε / 3 := by
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.1 (hGx j)) (ε / 3) (by linarith)
  filter_upwards [hGj] with n hn
  rw [Real.dist_eq]
  have htriangle : |F n x - a| ≤
      |F n x - G j n x| + |G j n x - L j| + |L j - a| := by
    calc
      |F n x - a| = |(F n x - G j n x) + (G j n x - L j) + (L j - a)| := by
        congr 1
        ring
      _ ≤ _ := (abs_add_le ((F n x - G j n x) + (G j n x - L j)) (L j - a)).trans
        (add_le_add (abs_add_le (F n x - G j n x) (G j n x - L j)) le_rfl)
  linarith [hdiff n]

end ConditionedStableLaws.MaximalClosure
