import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-!
# Killed kernels and the standing Hypothesis H

Hypothesis H on a compact metric state space with its Borel sigma algebra. A killed kernel is
represented on the surviving state space itself, so its mass may be less than one. `HypothesisH`
supplies the L¹ density from (H1), positivity/reachability from (H2), and the Borel cyclic-partition
condition from (H3).
-/

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace ConditionedStableLaws

namespace StandingHypothesis

noncomputable section

variable {M : Type*} [MeasurableSpace M]

/-- The transition kernel restricted to the states before absorption. -/
structure KilledKernel (M : Type*) [MeasurableSpace M] where
  kernel : Kernel M M
  mass_le_one : ∀ x, kernel x univ ≤ 1

instance (K : KilledKernel M) : IsFiniteKernel K.kernel where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, K.mass_le_one⟩

/-- Points with zero survival probability at some positive time (`Z`). -/
def escapingSet (K : Kernel M M) : Set M :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ (K ^ n) x univ = 0}

/-- Points with positive survival probability at every finite positive time. -/
def survivingSet (K : Kernel M M) : Set M := (escapingSet K)ᶜ

theorem escapingSet_eq_union (K : Kernel M M) :
    escapingSet K = ⋃ n : ℕ, {x | (K ^ (n + 1)) x univ = 0} := by
  ext x
  constructor
  · rintro ⟨n, hn, hx⟩
    cases n with
    | zero => omega
    | succ n => exact mem_iUnion.2 ⟨n, hx⟩
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    exact ⟨n + 1, by omega, hn⟩

/-- Eventual escaping is a measurable condition, since time is countable. -/
theorem measurableSet_escapingSet (K : Kernel M M) : MeasurableSet (escapingSet K) := by
  rw [escapingSet_eq_union]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_eq_fun ((K ^ (n + 1)).measurable_coe MeasurableSet.univ)
    measurable_const

theorem measurableSet_survivingSet (K : Kernel M M) : MeasurableSet (survivingSet K) :=
  (measurableSet_escapingSet K).compl

/-- Outside `Z`, every positive-time survival mass is strictly positive.
One-step positivity alone would not suffice for this equivalence. -/
theorem mem_survivingSet_iff (K : Kernel M M) (x : M) :
    x ∈ survivingSet K ↔ ∀ n : ℕ, 1 ≤ n → 0 < (K ^ n) x univ := by
  simp only [survivingSet, mem_compl_iff, escapingSet, mem_ofPred_eq, not_exists,
    not_and, pos_iff_ne_zero]

theorem one_step_survival_pos (K : Kernel M M) {x : M} (hx : x ∈ survivingSet K) :
    0 < K x univ := by
  simpa using (mem_survivingSet_iff K x).1 hx 1 (by omega)

/-- Successor modulo a nonzero partition length, as used in (H3). -/
def cyclicNext {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

section Topology

variable [MetricSpace M]

/-- A subset is relatively open in `S` if it is the intersection of `S` with
an ambient open set. -/
def RelativelyOpen (A S : Set M) : Prop :=
  ∃ U : Set M, IsOpen U ∧ A = S ∩ U

/-- Hypothesis H, with chosen density data. The reference measure is a fully supported Borel
probability measure. -/
structure HypothesisH (ρ : Measure M) (K : KilledKernel M)
    [CompactSpace M] [BorelSpace M] where
  reference_probability : IsProbabilityMeasure ρ
  reference_fullSupport : ρ.IsOpenPosMeasure
  density : M → Lp ℝ 1 ρ
  density_nonneg : ∀ x, ∀ᵐ y ∂ρ, 0 ≤ density x y
  kernel_eq_integral : ∀ x (A : Set M), MeasurableSet A →
    K.kernel x A = ENNReal.ofReal (∫ y in A, density x y ∂ρ)
  continuous_density : Continuous density
  surviving_mass_pos : 0 < ρ (survivingSet K.kernel)
  irreducible : ∀ x, x ∈ survivingSet K.kernel → ∀ A : Set M,
    RelativelyOpen A (survivingSet K.kernel) → A.Nonempty →
      ∃ n : ℕ, 1 ≤ n ∧ 0 < (K.kernel ^ n) x A
  aperiodic : ∀ (k : ℕ) (hk : 0 < k) (C : Fin k → Set M),
    (∀ i, MeasurableSet (C i)) →
    (∀ i, (C i).Nonempty) →
    Pairwise (fun i j => Disjoint (C i) (C j)) →
    (⋃ i, C i) = survivingSet K.kernel →
    (∀ i, {x | x ∈ survivingSet K.kernel ∧ 0 < K.kernel x (C i)} ⊆
      C (cyclicNext hk i)) →
    k = 1

variable [CompactSpace M] [BorelSpace M] {ρ : Measure M} {K : KilledKernel M}

/-- The density equation in (H1) entails the asserted absolute continuity. -/
theorem HypothesisH.absolutelyContinuous (h : HypothesisH ρ K) (x : M) :
    K.kernel x ≪ ρ := by
  intro A hA
  have hnull : ρ (toMeasurable ρ A) = 0 := by
    simpa only [measure_toMeasurable] using hA
  have hKnull : K.kernel x (toMeasurable ρ A) = 0 := by
    rw [h.kernel_eq_integral x _ (measurableSet_toMeasurable ρ A),
      Measure.restrict_eq_zero.2 hnull]
    simp
  exact measure_mono_null (subset_toMeasurable ρ A) hKnull

/-- Compactness upgrades (H1) to uniform continuity in the L¹ metric. -/
theorem HypothesisH.uniformContinuous_density (h : HypothesisH ρ K) :
    UniformContinuous h.density :=
  CompactSpace.uniformContinuous_of_continuous h.continuous_density

/-- The density representation identifies the real-valued transition mass. -/
theorem HypothesisH.kernel_real_eq_integral (h : HypothesisH ρ K) (x : M)
    (A : Set M) (hA : MeasurableSet A) :
    (K.kernel x A).toReal = ∫ y in A, h.density x y ∂ρ := by
  rw [h.kernel_eq_integral x A hA]
  apply ENNReal.toReal_ofReal
  exact integral_nonneg_of_ae (ae_restrict_of_ae (h.density_nonneg x))

end Topology

end

end StandingHypothesis

end ConditionedStableLaws
