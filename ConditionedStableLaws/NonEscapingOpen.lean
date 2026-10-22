import ConditionedStableLaws.EigenfunctionSupport
import ConditionedStableLaws.KernelSmallTargets

/-!
# The nonescaping region is open before any spectral construction

Finite-time extinction makes the escaping region forward invariant. H2 then
forces a positive one-step probability of staying in the nonescaping region.
H1 makes that probability continuous, proving openness without an eigenpair.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M]

/-- Nonescaping points have positive survival mass also at time zero. -/
theorem surviving_power_mass_pos (K : Kernel M M) {x : M}
    (hx : x ∈ survivingSet K) (n : ℕ) : 0 < (K^n) x univ := by
  cases n with
  | zero => simp [show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply]
  | succ n => exact (mem_survivingSet_iff K x).mp hx (n + 1) (by omega)

/-- A point that is certain to be extinct by a finite horizon cannot jump
into a point that survives every finite horizon. -/
theorem escaping_no_jump_to_surviving (K : Kernel M M) {x : M}
    (hx : x ∈ escapingSet K) : K x (survivingSet K) = 0 := by
  obtain ⟨n, hn, hmass⟩ := hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hint : (∫⁻ y, (K^m) y univ ∂K x) = 0 := by
    rw [pow_succ] at hmass
    change ((K^m) ∘ₖ K) x univ = 0 at hmass
    rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ] at hmass
    exact hmass
  have hae : ∀ᵐ y ∂K x, (K^m) y univ = 0 :=
    (lintegral_eq_zero_iff ((K^m).measurable_coe MeasurableSet.univ)).mp hint
  apply measure_mono_null (t := {y | (K^m) y univ ≠ 0})
  · intro y hy
    exact (surviving_power_mass_pos K hy m).ne'
  · exact ae_iff.mp hae

/-- The escaping set remains invariant under every kernel power. -/
theorem escaping_power_no_return (K : Kernel M M) (n : ℕ) {x : M}
    (hx : x ∈ escapingSet K) : (K^n) x (survivingSet K) = 0 := by
  exact kernel_pow_preserves_set K (escapingSet K) (measurableSet_escapingSet K)
    (fun _ h => escaping_no_jump_to_surviving K h) n x hx

variable [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Irreducibility forces a nonescaping point to place positive one-step
mass on the nonescaping region. Otherwise every later return is impossible. -/
theorem HypothesisH.one_step_surviving_pos (h : HypothesisH ρ K)
    {x : M} (hx : x ∈ survivingSet K.kernel) : 0 < K.kernel x (survivingSet K.kernel) := by
  have hrel : RelativelyOpen (survivingSet K.kernel) (survivingSet K.kernel) :=
    ⟨univ, isOpen_univ, by simp⟩
  obtain ⟨n, hn, hreach⟩ := h.irreducible x hx _ hrel ⟨x, hx⟩
  by_contra hnot
  have hz : K.kernel x (survivingSet K.kernel) = 0 := le_antisymm (le_of_not_gt hnot) bot_le
  have hae : ∀ᵐ y ∂K.kernel x, y ∈ escapingSet K.kernel := by
    exact hz
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have heq : (K.kernel^(m+1)) x (survivingSet K.kernel) = 0 := by
    rw [pow_succ]
    change ((K.kernel^m) ∘ₖ K.kernel) x (survivingSet K.kernel) = 0
    rw [Kernel.comp_apply' _ _ _ (measurableSet_survivingSet K.kernel)]
    calc
      _ = ∫⁻ _ : M, 0 ∂K.kernel x := by
        apply lintegral_congr_ae
        filter_upwards [hae] with y hy
        exact escaping_power_no_return K.kernel m hy
      _ = 0 := by simp
  exact hreach.ne' heq

/-- The one-step surviving mass characterizes the whole nonescaping region,
not merely the set of points surviving one step. -/
theorem HypothesisH.one_step_surviving_pos_iff (h : HypothesisH ρ K) (x : M) :
    0 < K.kernel x (survivingSet K.kernel) ↔ x ∈ survivingSet K.kernel := by
  constructor
  · intro hp
    by_contra hnot
    have hx : x ∈ escapingSet K.kernel := by simpa only [survivingSet, mem_compl_iff,
      not_not] using hnot
    exact hp.ne' (escaping_no_jump_to_surviving K.kernel hx)
  · exact h.one_step_surviving_pos

/-- H1 and H2 imply openness of `M \\ Z` before any eigenfunction is known. -/
theorem HypothesisH.isOpen_survivingSet (h : HypothesisH ρ K) :
    IsOpen (survivingSet K.kernel) := by
  have hcont : Continuous (fun x => (K.kernel x (survivingSet K.kernel)).toReal) := by
    simp_rw [h.kernel_real_eq_integral _ _ (measurableSet_survivingSet K.kernel)]
    exact continuous_setIntegral_of_continuous_L1 h.continuous_density _
  have heq : survivingSet K.kernel = {x | 0 < (K.kernel x (survivingSet K.kernel)).toReal} := by
    ext x
    constructor
    · intro hx
      exact ENNReal.toReal_pos (h.one_step_surviving_pos hx).ne'
        (measure_ne_top (K.kernel x) _)
    · intro hp
      change 0 < (K.kernel x (survivingSet K.kernel)).toReal at hp
      apply (h.one_step_surviving_pos_iff x).mp
      apply pos_iff_ne_zero.mpr
      intro hz
      simp only [hz, ENNReal.toReal_zero, lt_self_iff_false] at hp
  rw [heq]
  exact isOpen_lt continuous_const hcont

theorem HypothesisH.isClosed_escapingSet (h : HypothesisH ρ K) :
    IsClosed (escapingSet K.kernel) := by
  simpa only [survivingSet, compl_compl] using h.isOpen_survivingSet.isClosed_compl

end
end ConditionedStableLaws.StandingHypothesis
