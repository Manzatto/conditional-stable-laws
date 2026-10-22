import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.IsBounded
import Mathlib.Tactic

/-! A strict complex spectral-radius bound gives an exponential bound for
all powers, by Gelfand's formula. -/

open Filter Set
open scoped Topology ENNReal NNReal

namespace ConditionedStableLaws.SpectralPowerBound
noncomputable section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The powers of an element admit a geometric bound at some strictly
smaller rate than any given strict upper bound for its spectral radius. -/
theorem exists_geometric_bound (a : A) {r : ℝ} (hr : 0 < r)
    (hspec : spectralRadius ℂ a < ENNReal.ofReal r) :
    ∃ q : ℝ, 0 < q ∧ q < r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖a^n‖ ≤ C*q^n := by
  have hfinite : spectralRadius ℂ a ≠ ∞ := ne_top_of_lt (hspec.trans_le (le_top))
  have hsr : (spectralRadius ℂ a).toReal < r := by
    have he := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hspec
    rwa [ENNReal.toReal_ofReal hr.le] at he
  obtain ⟨q, hsq, hqr⟩ := exists_between hsr
  have hq : 0 < q := ENNReal.toReal_nonneg.trans_lt hsq
  have ht : Tendsto (fun n : ℕ => ‖a^n‖ ^ (1/(n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a).toReal) := by
    have hlim := (ENNReal.tendsto_toReal hfinite).comp
      (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a)
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using hlim
  have hroot : ∀ᶠ n : ℕ in atTop, ‖a^n‖ ^ (1/(n : ℝ)) ≤ q :=
    (ht.eventually (gt_mem_nhds hsq)).mono (fun _ hn => hn.le)
  have hratio : ∀ᶠ n : ℕ in atTop, ‖a^n‖ / q^n ≤ 1 := by
    filter_upwards [hroot, eventually_ge_atTop 1] with n hn hnone
    have hb := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg (a^n)) _) hn n
    rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) (by omega)] at hb
    exact (div_le_one (pow_pos hq n)).mpr hb
  obtain ⟨C, hC⟩ := (isBoundedUnder_of_eventually_le hratio).bddAbove_range
  refine ⟨q, hq, hqr, max C 0, le_max_right _ _, fun n => ?_⟩
  exact (div_le_iff₀ (pow_pos hq n)).mp ((hC (mem_range_self n)).trans (le_max_left _ _))

end
end ConditionedStableLaws.SpectralPowerBound
