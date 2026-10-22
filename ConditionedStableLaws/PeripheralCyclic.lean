import ConditionedStableLaws.PeripheralModulus
import Mathlib.GroupTheory.OrderOfElement

/-!
# Cyclic phase fibers

Strong Feller continuity makes phase fibers of peripheral eigenfunctions open in the surviving set.
Irreducibility then forces the phase of the eigenvalue to have finite multiplicative order. These
fibers form a finite Borel cyclic partition, and H3 forces its length to be one.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStableLaws.ComplexIntegral
noncomputable section

theorem phase_pow (z : ℂ) (n : ℕ) : phase (z^n) = (phase z)^n := by
  induction n with
  | zero => simp [phase]
  | succ n ih => rw [pow_succ, phase_mul, ih, pow_succ]

theorem measurable_phase : Measurable phase :=
  measurable_id.div (Complex.continuous_ofReal.measurable.comp measurable_norm)

end
end ConditionedStableLaws.ComplexIntegral

namespace ConditionedStableLaws.StandingHypothesis
noncomputable section
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- The live states with a specified complex eigenfunction phase. -/
def phaseFiber (K : KilledKernel M) (f : M →ᵇ ℂ) (a : ℂ) : Set M :=
  {x | x ∈ survivingSet K.kernel ∧ ComplexIntegral.phase (f x) = a}

omit [CompactSpace M] in
theorem measurableSet_phaseFiber (f : M →ᵇ ℂ) (a : ℂ) :
    MeasurableSet (phaseFiber K f a) :=
  (measurableSet_survivingSet K.kernel).inter (measurableSet_eq_fun
    (ComplexIntegral.measurable_phase.comp f.continuous.measurable) measurable_const)

theorem HypothesisH.continuous_kernel_real_mass (h : HypothesisH ρ K)
    (A : Set M) (hA : MeasurableSet A) : Continuous (fun x => (K.kernel x A).toReal) := by
  simp_rw [h.kernel_real_eq_integral _ _ hA]
  exact continuous_setIntegral_of_continuous_L1 h.continuous_density A

variable (h : HypothesisH ρ K) (μ : Measure M) [IsProbabilityMeasure μ]
  {r : ℝ} (hr : 0 < r) (hleft : K.kernel ∘ₘ μ = ENNReal.ofReal r • μ)
  (f : M →ᵇ ℂ) (hf : f ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
  (heq : ∀ x, (∫ y, f y ∂K.kernel x) = z * f x)

include h μ hr hleft hf hz heq

/-- Every surviving transition lands in the prescribed phase fiber. -/
theorem HypothesisH.kernel_pow_phaseFiber_eq_surviving (n : ℕ) {x : M}
    (hx : x ∈ survivingSet K.kernel) :
    (K.kernel^n) x (phaseFiber K f ((ComplexIntegral.phase z)^n * ComplexIntegral.phase (f x))) =
      (K.kernel^n) x (survivingSet K.kernel) := by
  apply measure_congr
  filter_upwards [h.complex_eigenfunction_phase_transport μ hr hleft f hf hz heq n hx] with y hy
  apply propext
  change (y ∈ survivingSet K.kernel ∧ _) ↔ y ∈ survivingSet K.kernel
  exact ⟨And.left, fun hys => ⟨hys, by simpa only [ComplexIntegral.phase_pow] using hy hys⟩⟩

/-- Positive transition mass into a phase fiber determines the source phase. -/
theorem HypothesisH.phase_eq_of_kernel_pow_phaseFiber_pos (n : ℕ) {x : M}
    (hx : x ∈ survivingSet K.kernel) {a : ℂ}
    (ha : 0 < (K.kernel^n) x (phaseFiber K f a)) :
    a = (ComplexIntegral.phase z)^n * ComplexIntegral.phase (f x) := by
  by_contra hne
  have hae : ∀ᵐ y ∂(K.kernel^n) x, y ∉ phaseFiber K f a := by
    filter_upwards [h.complex_eigenfunction_phase_transport μ hr hleft f hf hz heq n hx] with y hy
    intro hym
    exact hne (hym.2.symm.trans (by simpa only [ComplexIntegral.phase_pow] using hy hym.1))
  exact ha.ne' (by simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hae)

/-- H1 opens every phase fiber, even though the surviving set need not be compact. -/
theorem HypothesisH.isOpen_phaseFiber (a : ℂ) : IsOpen (phaseFiber K f a) := by
  let u := ComplexIntegral.phase z
  have hu : u ≠ 0 := norm_ne_zero_iff.mp (by
    rw [ComplexIntegral.norm_phase (norm_pos_iff.mp (hz ▸ hr))]
    norm_num)
  have heqset : phaseFiber K f a = survivingSet K.kernel ∩
      {x | 0 < (K.kernel x (phaseFiber K f (u*a))).toReal} := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hm := h.kernel_pow_phaseFiber_eq_surviving μ hr hleft f hf hz heq 1 hx.1
      simp only [pow_one, hx.2] at hm
      change 0 < (K.kernel x (phaseFiber K f (ComplexIntegral.phase z*a))).toReal
      rw [hm]
      exact ENNReal.toReal_pos (h.one_step_surviving_pos hx.1).ne' (measure_ne_top _ _)
    · rintro ⟨hx, hpos⟩
      refine ⟨hx, ?_⟩
      have hm : 0 < K.kernel x (phaseFiber K f (u*a)) := by
        exact (ENNReal.toReal_pos_iff).mp hpos |>.1
      have hp := h.phase_eq_of_kernel_pow_phaseFiber_pos μ hr hleft f hf hz heq 1 hx
        (by simpa only [pow_one] using hm)
      simp only [pow_one] at hp
      exact (mul_left_cancel₀ hu hp).symm
  rw [heqset]
  exact h.isOpen_survivingSet.inter (isOpen_lt continuous_const
    (h.continuous_kernel_real_mass _ (measurableSet_phaseFiber f (u*a))))

/-- Irreducibility returns to an open phase fiber and hence gives finite
multiplicative order of the peripheral phase. -/
theorem HypothesisH.peripheral_phase_finite_order :
    IsOfFinOrder (ComplexIntegral.phase z) := by
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  let A := phaseFiber K f (ComplexIntegral.phase (f x))
  have hA : RelativelyOpen A (survivingSet K.kernel) :=
    ⟨A, h.isOpen_phaseFiber μ hr hleft f hf hz heq _, (inter_eq_right.mpr (fun _ hy => hy.1)).symm⟩
  obtain ⟨n, hn, hpos⟩ := h.irreducible x hx A hA ⟨x, hx, rfl⟩
  have hp := h.phase_eq_of_kernel_pow_phaseFiber_pos μ hr hleft f hf hz heq n hx hpos
  have hfx : ComplexIntegral.phase (f x) ≠ 0 := norm_ne_zero_iff.mp (by
    rw [ComplexIntegral.norm_phase
      (h.complex_eigenfunction_ne_zero_on_surviving μ hr hleft f hf hz heq hx)]
    norm_num)
  have hpow : (ComplexIntegral.phase z)^n = 1 := by
    apply mul_right_cancel₀ hfx
    simpa only [one_mul] using hp.symm
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, by omega, hpow⟩

/-- All forward phase iterates occur as phases of live states. -/
theorem HypothesisH.phase_forward_orbit_nonempty {x : M}
    (hx : x ∈ survivingSet K.kernel) (n : ℕ) :
    (phaseFiber K f ((ComplexIntegral.phase z)^n * ComplexIntegral.phase (f x))).Nonempty := by
  induction n with
  | zero => exact ⟨x, hx, by simp⟩
  | succ n ih =>
    obtain ⟨y, hylive, hyphase⟩ := ih
    have hm := h.kernel_pow_phaseFiber_eq_surviving μ hr hleft f hf hz heq 1 hylive
    simp only [pow_one, hyphase, ← mul_assoc, ← pow_succ'] at hm
    exact nonempty_of_measure_ne_zero (by rw [hm]; exact (h.one_step_surviving_pos hylive).ne')

/-- H3 excludes all nontrivial peripheral phases. -/
theorem HypothesisH.peripheral_phase_eq_one : ComplexIntegral.phase z = 1 := by
  let u := ComplexIntegral.phase z
  let v := u⁻¹
  have hu : u ≠ 0 := norm_ne_zero_iff.mp (by
    rw [ComplexIntegral.norm_phase (norm_pos_iff.mp (hz ▸ hr))]
    norm_num)
  have hv : v ≠ 0 := inv_ne_zero hu
  have hvorder : IsOfFinOrder v := by
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp
      (h.peripheral_phase_finite_order μ hr hleft f hf hz heq)
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by
      change u⁻¹^n = 1
      rw [inv_pow, hpow, inv_one]⟩
  let k := orderOf v
  have hk : 0 < k := hvorder.orderOf_pos
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero h.surviving_mass_pos.ne'
  let p := ComplexIntegral.phase (f x₀)
  have hp : p ≠ 0 := norm_ne_zero_iff.mp (by
    rw [ComplexIntegral.norm_phase
      (h.complex_eigenfunction_ne_zero_on_surviving μ hr hleft f hf hz heq hx₀)]
    norm_num)
  let C : Fin k → Set M := fun i => phaseFiber K f (v^i.val * p)
  have hCmeas (i : Fin k) : MeasurableSet (C i) := measurableSet_phaseFiber _ _
  have hCne (i : Fin k) : (C i).Nonempty := by
    have hne := h.phase_forward_orbit_nonempty μ hr hleft f hf hz heq hx₀ (k-i.val)
    have hpow : u^(k-i.val) = v^i.val := by
      have he := inv_pow_sub₀ hv (Nat.le_of_lt i.isLt)
      simpa only [v, inv_inv, show u⁻¹ ^ k = 1 from pow_orderOf_eq_one v,
        inv_one, one_mul] using he
    change (phaseFiber K f (v^i.val * p)).Nonempty
    rwa [← hpow]
  have hCdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro y hiy hjy
    apply hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf i.isLt j.isLt
    exact mul_right_cancel₀ hp (hiy.2.symm.trans hjy.2)
  have hCunion : (⋃ i, C i) = survivingSet K.kernel := by
    apply subset_antisymm
    · intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact hi.1
    · intro y hy
      let A := phaseFiber K f p
      have hA : RelativelyOpen A (survivingSet K.kernel) :=
        ⟨A, h.isOpen_phaseFiber μ hr hleft f hf hz heq _,
          (inter_eq_right.mpr (fun _ hx => hx.1)).symm⟩
      obtain ⟨n, _, hn⟩ := h.irreducible y hy A hA ⟨x₀, hx₀, rfl⟩
      have hphase := h.phase_eq_of_kernel_pow_phaseFiber_pos μ hr hleft f hf hz heq n hy hn
      have hreverse : ComplexIntegral.phase (f y) = v^n * p := by
        change p = u^n * ComplexIntegral.phase (f y) at hphase
        rw [hphase, ← mul_assoc, ← mul_pow]
        simp [v, inv_mul_cancel₀ hu]
      apply mem_iUnion.mpr
      refine ⟨⟨n % k, Nat.mod_lt n hk⟩, hy, ?_⟩
      change ComplexIntegral.phase (f y) = v^(n % orderOf v) * p
      rw [pow_mod_orderOf, hreverse]
  have hCcycle (i : Fin k) : {x | x ∈ survivingSet K.kernel ∧ 0 < K.kernel x (C i)} ⊆
      C (cyclicNext hk i) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hphase := h.phase_eq_of_kernel_pow_phaseFiber_pos μ hr hleft f hf hz heq 1 hy.1
      (by simpa only [pow_one] using hy.2)
    simp only [pow_one] at hphase
    have hreverse : ComplexIntegral.phase (f y) = v^(i.val+1) * p := by
      change v^i.val * p = u * ComplexIntegral.phase (f y) at hphase
      calc
        ComplexIntegral.phase (f y) = v * (v^i.val * p) := by
          rw [hphase, ← mul_assoc]
          simp [v, inv_mul_cancel₀ hu]
        _ = v^(i.val+1) * p := by rw [pow_succ']; ring
    change ComplexIntegral.phase (f y) = v^((i.val+1) % orderOf v) * p
    rw [pow_mod_orderOf, hreverse]
  have hkone := h.aperiodic k hk C hCmeas hCne hCdisjoint hCunion hCcycle
  have hvone : v = 1 := orderOf_eq_one_iff.mp hkone
  have huone := congrArg (fun w : ℂ => w⁻¹) hvone
  simpa only [v, inv_inv, inv_one] using huone

/-- Under the full H, every complex peripheral eigenvalue is the positive leading eigenvalue. This
is the aperiodic spectral exclusion step. -/
theorem HypothesisH.complex_peripheral_eigenvalue_eq : z = (r : ℂ) := by
  have hp := h.peripheral_phase_eq_one μ hr hleft f hf hz heq
  have he := ComplexIntegral.phase_mul_norm z
  rw [hp, one_mul, hz] at he
  exact he.symm

omit μ hr hleft hf hz heq in
/-- Peripheral exclusion under H alone. -/
theorem HypothesisH.exists_eigenpair_peripheral_exclusion :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ η : M →ᵇ ℝ,
      (∀ x, 0 ≤ η x) ∧ ‖η‖ = 1 ∧ h.continuousKernelOperator η = r • η ∧
      ∀ (f : M →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ, ‖z‖ = r →
        (∀ x, (∫ y, f y ∂K.kernel x) = z * f x) → z = (r : ℂ) := by
  obtain ⟨r, hr, hrone, η, hη, hnorm, heq, μ, hleft⟩ := h.exists_positive_eigenpair_and_eigenmeasure
  exact ⟨r, hr, hrone, η, hη, hnorm, heq,
    fun f hf z hz heq => h.complex_peripheral_eigenvalue_eq μ hr hleft f hf hz heq⟩

end
end ConditionedStableLaws.StandingHypothesis
