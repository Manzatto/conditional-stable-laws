import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Bases
import Mathlib.Tactic

/-!
# Locally finite point measures on (0,∞]

The state space includes infinity. Point measures are measures with an at most countable unit-Dirac
representation, finite on every positive tail. The vague topology is the initial topology of
integration against all continuous compactly supported real functions.
-/

open Filter MeasureTheory Set Classical
open scoped Topology ENNReal NNReal BigOperators CompactlySupported

namespace ConditionedStableLaws

noncomputable section

/-- The extended positive half-line, with its subtype topology and Borel sigma algebra. -/
abbrev ExtremeState := {y : ℝ≥0∞ // 0 < y}

instance : SecondCountableTopology ExtremeState :=
  TopologicalSpace.secondCountableTopology_induced ExtremeState ℝ≥0∞ Subtype.val

/-- The compact positive tail `[ε,∞]`. -/
def extremeTail (ε : ℝ≥0) : Set ExtremeState := {y | (ε : ℝ≥0∞) ≤ y.val}

/-- Positive tails are compact in the stated topology, including the point at infinity. -/
theorem isCompact_extremeTail (ε : ℝ≥0) (hε : 0 < ε) : IsCompact (extremeTail ε) := by
  rw [Subtype.isCompact_iff]
  have heq : Subtype.val '' extremeTail ε = Set.Ici (ε : ℝ≥0∞) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
      exact ⟨⟨y, hε'.trans_le hy⟩, hy, rfl⟩
  rw [heq]
  exact isClosed_Ici.isCompact

/-- The tail condition is also necessary for ordinary local finiteness. -/
theorem finite_extremeTail_of_locallyFinite (μ : Measure ExtremeState)
    [IsLocallyFiniteMeasure μ] (ε : ℝ≥0) (hε : 0 < ε) : μ (extremeTail ε) < ∞ :=
  (isCompact_extremeTail ε hε).measure_lt_top

/-- An at most countable sum of unit Dirac measures, allowing repeated atoms. -/
def IsPointMeasure (μ : Measure ExtremeState) : Prop :=
  ∃ (J : Type) (_ : Countable J) (a : J → ExtremeState),
    μ = Measure.sum (fun j => Measure.dirac (a j))

/-- The space `M_p((0,∞])` of locally finite point measures. -/
structure LocallyFinitePointMeasure where
  toMeasure : Measure ExtremeState
  atomic : IsPointMeasure toMeasure
  finite_tail : ∀ ε : ℝ≥0, 0 < ε → toMeasure (extremeTail ε) < ∞

namespace LocallyFinitePointMeasure

@[ext]
theorem ext {ξ ζ : LocallyFinitePointMeasure} (h : ξ.toMeasure = ζ.toMeasure) : ξ = ζ := by
  cases ξ
  cases ζ
  cases h
  rfl

/-- Finiteness on positive tails implies the usual local finiteness of a measure. -/
instance locallyFinite (ξ : LocallyFinitePointMeasure) : IsLocallyFiniteMeasure ξ.toMeasure := by
  constructor
  intro y
  obtain ⟨ε, hε, hεy⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp y.property
  have hεpos : 0 < ε := by exact_mod_cast hε
  refine ⟨{z : ExtremeState | (ε : ℝ≥0∞) < z.val},
    (isOpen_lt continuous_const continuous_subtype_val).mem_nhds hεy, ?_⟩
  exact lt_of_le_of_lt
    (measure_mono (show {z : ExtremeState | (ε : ℝ≥0∞) < z.val} ⊆ extremeTail ε
      from fun z hz => show (ε : ℝ≥0∞) ≤ z.val from (show (ε : ℝ≥0∞) < z.val from hz).le))
    (ξ.finite_tail ε hεpos)

/-- Compactly supported continuous test functions are integrable here. -/
theorem integrable_test (ξ : LocallyFinitePointMeasure) (f : C_c(ExtremeState, ℝ)) :
    Integrable f ξ.toMeasure := f.integrable

/-- All test-function integrals, used to define the vague topology. -/
def testIntegrals (ξ : LocallyFinitePointMeasure) : C_c(ExtremeState, ℝ) → ℝ :=
  fun f => ∫ y, f y ∂ξ.toMeasure

/-- The vague topology, induced by the complete family of C_c test integrals. -/
instance : TopologicalSpace LocallyFinitePointMeasure :=
  TopologicalSpace.induced testIntegrals inferInstance

instance : MeasurableSpace LocallyFinitePointMeasure := borel LocallyFinitePointMeasure

instance : BorelSpace LocallyFinitePointMeasure := ⟨rfl⟩

/-- Topological convergence is precisely convergence of every C_c integral. -/
theorem tendsto_iff_test_integrals {I : Type*} {l : Filter I}
    {ξ : I → LocallyFinitePointMeasure} {ζ : LocallyFinitePointMeasure} :
    Tendsto ξ l (𝓝 ζ) ↔ ∀ f : C_c(ExtremeState, ℝ),
      Tendsto (fun i => ∫ y, f y ∂(ξ i).toMeasure) l (𝓝 (∫ y, f y ∂ζ.toMeasure)) := by
  change Tendsto ξ l (@nhds _ (TopologicalSpace.induced testIntegrals _) ζ) ↔ _
  rw [nhds_induced, Filter.tendsto_comap_iff]
  exact tendsto_pi_nhds

theorem continuous_testIntegral (f : C_c(ExtremeState, ℝ)) :
    Continuous (fun ξ : LocallyFinitePointMeasure => ∫ y, f y ∂ξ.toMeasure) :=
  (continuous_apply f).comp
    (show Continuous testIntegrals from continuous_induced_dom)

/-- The finite empirical point measure with one unit atom at each observation. -/
def empirical {n : ℕ} (a : Fin n → ExtremeState) : LocallyFinitePointMeasure where
  toMeasure := Measure.sum (fun i => Measure.dirac (a i))
  atomic := ⟨Fin n, inferInstance, a, rfl⟩
  finite_tail := by
    intro ε _hε
    rw [Measure.sum_apply_of_countable, tsum_fintype]
    exact ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _

theorem empirical_apply {n : ℕ} (a : Fin n → ExtremeState) (A : Set ExtremeState) :
    (empirical a).toMeasure A = ∑ i : Fin n, if a i ∈ A then (1 : ℝ≥0∞) else 0 := by
  classical
  simp [empirical, Measure.dirac_apply, Set.indicator]

/-- Evaluation is the number of observations falling in the selected set. -/
theorem empirical_apply_eq_card {n : ℕ} (a : Fin n → ExtremeState) (A : Set ExtremeState) :
    (empirical a).toMeasure A = ((Finset.univ.filter fun i => a i ∈ A).card : ℝ≥0∞) := by
  classical
  rw [empirical_apply]
  simp only [← Finset.sum_boole]

@[simp]
theorem empirical_univ {n : ℕ} (a : Fin n → ExtremeState) :
    (empirical a).toMeasure Set.univ = n := by
  simp [empirical_apply]

/-- Integrating any real test function against an empirical measure is a finite sum. -/
theorem integral_empirical {n : ℕ} (a : Fin n → ExtremeState) (f : ExtremeState → ℝ) :
    ∫ y, f y ∂(empirical a).toMeasure = ∑ i : Fin n, f (a i) := by
  change (∫ y, f y ∂Measure.sum (fun i => Measure.dirac (a i))) = _
  rw [Measure.sum_fintype, integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i _hi
    exact integrable_dirac (by simp)

/-- The finite empirical construction is continuous for the vague topology. -/
theorem continuous_empirical (n : ℕ) :
    Continuous (empirical : (Fin n → ExtremeState) → LocallyFinitePointMeasure) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  change Continuous (fun a : Fin n → ExtremeState => ∫ y, f y ∂(empirical a).toMeasure)
  simp_rw [integral_empirical]
  exact continuous_finsetSum _ fun i _ => f.continuous.comp (continuous_apply i)

theorem measurable_empirical (n : ℕ) :
    Measurable (empirical : (Fin n → ExtremeState) → LocallyFinitePointMeasure) :=
  (continuous_empirical n).measurable

end LocallyFinitePointMeasure

/-- A random point measure is measurable into the Borel sigma algebra of the vague topology. -/
structure RandomPointMeasure (Ω : Type*) [MeasurableSpace Ω] where
  toFun : Ω → LocallyFinitePointMeasure
  measurable : Measurable toFun

namespace RandomPointMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measurable finite collections of observations give random point measures. -/
def empirical {n : ℕ} (a : Fin n → Ω → ExtremeState) (ha : ∀ i, Measurable (a i)) :
    RandomPointMeasure Ω where
  toFun ω := LocallyFinitePointMeasure.empirical (fun i => a i ω)
  measurable := (LocallyFinitePointMeasure.measurable_empirical n).comp (Measurable.of_eval ha)

/-- Convert a positive finite observation and positive scale into a point of `(0,∞]`. -/
def normalizedObservation (f : Ω → ℝ) (hf : ∀ ω, 0 < f ω) (B : ℝ) (hB : 0 < B)
    (ω : Ω) : ExtremeState :=
  ⟨ENNReal.ofReal (f ω / B), ENNReal.ofReal_pos.mpr (div_pos (hf ω) hB)⟩

theorem measurable_normalizedObservation {f : Ω → ℝ} (hm : Measurable f)
    (hf : ∀ ω, 0 < f ω) (B : ℝ) (hB : 0 < B) :
    Measurable (normalizedObservation f hf B hB) := by
  apply Measurable.subtype_mk
  exact ENNReal.measurable_ofReal.comp (hm.div_const B)

/-- The normalized empirical point measure of positive real observations. For the singular
observable this is `Σ_{j<n} δ_{fβ(Xj)/Bn}`. -/
def normalizedEmpirical {n : ℕ} (f : Fin n → Ω → ℝ)
    (hm : ∀ i, Measurable (f i)) (hf : ∀ i ω, 0 < f i ω) (B : ℝ) (hB : 0 < B) :
    RandomPointMeasure Ω :=
  empirical (fun i => normalizedObservation (f i) (hf i) B hB)
    (fun i => measurable_normalizedObservation (hm i) (hf i) B hB)

theorem normalizedEmpirical_apply {n : ℕ} (f : Fin n → Ω → ℝ)
    (hm : ∀ i, Measurable (f i)) (hf : ∀ i ω, 0 < f i ω) (B : ℝ) (hB : 0 < B)
    (ω : Ω) (A : Set ExtremeState) :
    ((normalizedEmpirical f hm hf B hB).toFun ω).toMeasure A =
      ∑ i : Fin n, if normalizedObservation (f i) (hf i) B hB ω ∈ A
        then (1 : ℝ≥0∞) else 0 :=
  LocallyFinitePointMeasure.empirical_apply _ _

end RandomPointMeasure

end

end ConditionedStableLaws
