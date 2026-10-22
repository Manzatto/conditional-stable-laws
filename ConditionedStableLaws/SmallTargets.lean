import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
The compact-family argument for uniformly small targets. Compactness and continuity of the
transition densities in L¹ imply uniform absolute continuity of their integrals.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ConditionedStableLaws

noncomputable section

variable {Y : Type*} [MeasurableSpace Y] {ρ : Measure Y}

/-- Integrating on an arbitrary set is a contraction from real L¹ to ℝ. -/
theorem abs_setIntegral_sub_le_L1_dist (f g : Lp ℝ 1 ρ) (s : Set Y) :
    |(∫ y in s, f y ∂ρ) - ∫ y in s, g y ∂ρ| ≤ dist f g := by
  have hf := L1.integrable_coeFn f
  have hg := L1.integrable_coeFn g
  calc
    |(∫ y in s, f y ∂ρ) - ∫ y in s, g y ∂ρ|
        = ‖∫ y in s, f y - g y ∂ρ‖ := by
          rw [integral_sub hf.restrict hg.restrict, Real.norm_eq_abs]
    _ ≤ ∫ y in s, ‖f y - g y‖ ∂ρ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖f y - g y‖ ∂ρ :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hf.sub hg).norm
    _ = dist f g := by
      simpa only [dist_eq_norm] using (L1.dist_eq_integral_dist f g).symm

/-- A compact family of L¹ functions has integrals uniformly tending to zero on sets whose measures
tend to zero. -/
theorem uniform_small_sets_of_isCompact_L1 {K : Set (Lp ℝ 1 ρ)}
    (hK : IsCompact K) (U : ℕ → Set Y)
    (hU : Tendsto (fun n => ρ (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ f ∈ K, |∫ y in U n, f y ∂ρ| < ε := by
  intro ε hε
  obtain ⟨t, _htK, ht, hcover⟩ := hK.finite_cover_balls (half_pos hε)
  have hcenters : ∀ g ∈ t, ∀ᶠ n in atTop,
      |∫ y in U n, g y ∂ρ| < ε / 2 := by
    intro g _hg
    have hlim := (L1.integrable_coeFn g).tendsto_setIntegral_nhds_zero hU
    exact hlim.abs.eventually_lt_const (by simpa using half_pos hε)
  have hall : ∀ᶠ n in atTop, ∀ g ∈ t,
      |∫ y in U n, g y ∂ρ| < ε / 2 :=
    (Filter.eventually_all_finite ht).2 hcenters
  filter_upwards [hall] with n hn
  intro f hf
  obtain ⟨g, hgt, hfg⟩ := Set.mem_iUnion₂.mp (hcover hf)
  have hdist : dist f g < ε / 2 := hfg
  calc
    |∫ y in U n, f y ∂ρ|
        ≤ |(∫ y in U n, f y ∂ρ) - ∫ y in U n, g y ∂ρ|
          + |∫ y in U n, g y ∂ρ| := by
            simpa only [sub_add_cancel] using
              abs_add_le ((∫ y in U n, f y ∂ρ) - ∫ y in U n, g y ∂ρ)
                (∫ y in U n, g y ∂ρ)
    _ ≤ dist f g + |∫ y in U n, g y ∂ρ| :=
      add_le_add (abs_setIntegral_sub_le_L1_dist f g (U n)) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hdist (hn g hgt)
    _ = ε := add_halves ε

/-- Continuous L¹ densities indexed by a compact state space satisfy the uniform small-target
estimate, in epsilon/eventually form. Positivity or a probability normalization of the densities is
not needed. -/
theorem uniform_small_targets_of_continuous_L1
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (κ : M → Lp ℝ 1 ρ) (hκ : Continuous κ) (U : ℕ → Set Y)
    (hU : Tendsto (fun n => ρ (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x : M, |∫ y in U n, κ x y ∂ρ| < ε := by
  intro ε hε
  have hK : IsCompact (Set.range κ) := isCompact_range hκ
  filter_upwards [uniform_small_sets_of_isCompact_L1 hK U hU ε hε] with n hn x
  exact hn (κ x) (Set.mem_range_self x)

end

end ConditionedStableLaws
