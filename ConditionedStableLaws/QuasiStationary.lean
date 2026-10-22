import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

/-!
# Quasi-stationarity and normalized surviving marginals

The measure eigenidentity is equivalent to invariance of the normalized surviving marginal at every
positive integer time. Here the marginal is the composition `(K^n) ∘ₘ μ` of a kernel and a measure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace ConditionedStableLaws

variable {M : Type*} [MeasurableSpace M]

/-- The unnormalized surviving marginal after `n` killed transitions. -/
def killedMarginal (K : Kernel M M) (μ : Measure M) (n : ℕ) : Measure M :=
  (K ^ n : Kernel M M) ∘ₘ μ

/-- Normalize a measure by its total mass. Probability claims below require
strictly positive finite mass. -/
def normalizedMeasure (ν : Measure M) : Measure M :=
  (ν univ)⁻¹ • ν

/-- The marginal obtained by normalizing the surviving mass at time `n`. -/
def conditionedMarginal (K : Kernel M M) (μ : Measure M) (n : ℕ) : Measure M :=
  normalizedMeasure (killedMarginal K μ n)

/-- A probability eigenmeasure of the killed kernel with a positive rate at most one. -/
def IsQuasiStationary (K : Kernel M M) (μ : Measure M) : Prop :=
  IsProbabilityMeasure μ ∧
    ∃ rate : ℝ≥0∞, 0 < rate ∧ rate ≤ 1 ∧ K ∘ₘ μ = rate • μ

/-- Iterating a one-step eigenmeasure identity gives the kernel powers. -/
theorem killedMarginal_of_eigenmeasure (K : Kernel M M) (μ : Measure M)
    {rate : ℝ≥0∞} (heigen : K ∘ₘ μ = rate • μ) (n : ℕ) :
    killedMarginal K μ n = rate ^ n • μ := by
  unfold killedMarginal
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [show (1 : Kernel M M) = Kernel.id from rfl]
      simp
  | succ n ih =>
      rw [pow_succ']
      rw [show K * K ^ n = K ∘ₖ (K ^ n) from rfl]
      rw [← Measure.comp_assoc, ih, Measure.comp_smul, heigen, smul_smul, pow_succ]

/-- The surviving mass of a probability eigenmeasure is the power of its rate. -/
theorem killedMarginal_mass_of_eigenmeasure (K : Kernel M M) (μ : Measure M)
    [IsProbabilityMeasure μ] {rate : ℝ≥0∞} (heigen : K ∘ₘ μ = rate • μ) (n : ℕ) :
    killedMarginal K μ n univ = rate ^ n := by
  rw [killedMarginal_of_eigenmeasure K μ heigen n]
  simp

/-- The eigenvalue equals the one-step surviving mass. -/
theorem eigenvalue_eq_survival_mass (K : Kernel M M) (μ : Measure M)
    [IsProbabilityMeasure μ] {rate : ℝ≥0∞} (heigen : K ∘ₘ μ = rate • μ) :
    rate = (K ∘ₘ μ) univ := by
  have h := killedMarginal_mass_of_eigenmeasure K μ heigen 1
  simpa [killedMarginal] using h.symm

/-- In particular a fixed probability eigenmeasure has a unique eigenvalue. -/
theorem quasiStationary_rate_unique (K : Kernel M M) (μ : Measure M)
    [IsProbabilityMeasure μ] {rate κ : ℝ≥0∞}
    (hrate : K ∘ₘ μ = rate • μ) (hκ : K ∘ₘ μ = κ • μ) : rate = κ := by
  rw [eigenvalue_eq_survival_mass K μ hrate, eigenvalue_eq_survival_mass K μ hκ]

/-- Normalization recovers any probability measure multiplied by finite positive mass. -/
theorem normalizedMeasure_smul_probability (μ : Measure M) [IsProbabilityMeasure μ]
    {a : ℝ≥0∞} (ha₀ : a ≠ 0) (hatop : a ≠ ∞) :
    normalizedMeasure (a • μ) = μ := by
  simp [normalizedMeasure, smul_smul, ENNReal.inv_mul_cancel ha₀ hatop]

/-- Normalizing finite positive mass produces a probability measure. -/
theorem normalizedMeasure_isProbability (ν : Measure M)
    (hν₀ : ν univ ≠ 0) (hνtop : ν univ ≠ ∞) :
    IsProbabilityMeasure (normalizedMeasure ν) := by
  constructor
  simp [normalizedMeasure, ENNReal.inv_mul_cancel hν₀ hνtop]

/-- Normalized-measure equality is equivalent to the corresponding mass-scaled equality. -/
theorem normalizedMeasure_eq_iff (ν μ : Measure M)
    (hν₀ : ν univ ≠ 0) (hνtop : ν univ ≠ ∞) :
    normalizedMeasure ν = μ ↔ ν = ν univ • μ := by
  constructor
  · intro h
    calc
      ν = ν univ • normalizedMeasure ν := by
        rw [normalizedMeasure, smul_smul, ENNReal.mul_inv_cancel hν₀ hνtop, one_smul]
      _ = ν univ • μ := by rw [h]
  · intro h
    have h' := congrArg (fun τ : Measure M => (ν univ)⁻¹ • τ) h
    simpa only [normalizedMeasure, smul_smul, ENNReal.inv_mul_cancel hν₀ hνtop,
      one_smul] using h'

/-- Every surviving marginal of a probability eigenmeasure normalizes to the
original measure, including at time zero. -/
theorem conditionedMarginal_of_eigenmeasure (K : Kernel M M) (μ : Measure M)
    [IsProbabilityMeasure μ] {rate : ℝ≥0∞} (hrate₀ : 0 < rate) (hratetop : rate ≠ ∞)
    (heigen : K ∘ₘ μ = rate • μ) (n : ℕ) :
    conditionedMarginal K μ n = μ := by
  rw [conditionedMarginal, killedMarginal_of_eigenmeasure K μ heigen n]
  exact normalizedMeasure_smul_probability μ
    (ENNReal.pow_pos hrate₀ n).ne' (ENNReal.pow_ne_top hratetop)

/-- A killed transition cannot increase the total mass of a probability measure. -/
theorem one_step_survival_mass_le_one (K : Kernel M M) (μ : Measure M)
    [IsProbabilityMeasure μ] (hK : ∀ x, K x univ ≤ 1) :
    (K ∘ₘ μ) univ ≤ 1 := by
  rw [Measure.bind_apply MeasurableSet.univ K.aemeasurable]
  calc
    ∫⁻ x, K x univ ∂μ ≤ ∫⁻ _ : M, 1 ∂μ := lintegral_mono hK
    _ = 1 := by simp

/-- One-step normalized invariance, with positive survival, is precisely
quasi-stationarity for a killed kernel. -/
theorem isQuasiStationary_iff_one_step (K : Kernel M M) (μ : Measure M)
    (hK : ∀ x, K x univ ≤ 1) :
    IsQuasiStationary K μ ↔ IsProbabilityMeasure μ ∧
      0 < (K ∘ₘ μ) univ ∧ conditionedMarginal K μ 1 = μ := by
  constructor
  · rintro ⟨hμ, rate, hrate₀, hrate₁, heigen⟩
    have : IsProbabilityMeasure μ := hμ
    have hratetop : rate ≠ ∞ := (hrate₁.trans_lt ENNReal.one_lt_top).ne
    refine ⟨hμ, ?_, conditionedMarginal_of_eigenmeasure K μ hrate₀ hratetop heigen 1⟩
    rwa [← eigenvalue_eq_survival_mass K μ heigen]
  · rintro ⟨hμ, hmass, hcond⟩
    have : IsProbabilityMeasure μ := hμ
    have hle := one_step_survival_mass_le_one K μ hK
    have hfinite : (K ∘ₘ μ) univ ≠ ∞ := (hle.trans_lt ENNReal.one_lt_top).ne
    refine ⟨hμ, (K ∘ₘ μ) univ, hmass, hle, ?_⟩
    apply (normalizedMeasure_eq_iff _ μ hmass.ne' hfinite).mp
    simpa [conditionedMarginal, killedMarginal] using hcond

/-- Equivalence with invariance of all normalized surviving marginals at
positive times, including the positivity required for conditioning. -/
theorem isQuasiStationary_iff_all_marginals (K : Kernel M M) (μ : Measure M)
    (hK : ∀ x, K x univ ≤ 1) :
    IsQuasiStationary K μ ↔ IsProbabilityMeasure μ ∧
      ∀ n : ℕ, 1 ≤ n →
        0 < killedMarginal K μ n univ ∧ conditionedMarginal K μ n = μ := by
  constructor
  · rintro ⟨hμ, rate, hrate₀, hrate₁, heigen⟩
    have : IsProbabilityMeasure μ := hμ
    refine ⟨hμ, fun n _ => ⟨?_, ?_⟩⟩
    · rw [killedMarginal_mass_of_eigenmeasure K μ heigen n]
      exact ENNReal.pow_pos hrate₀ n
    · exact conditionedMarginal_of_eigenmeasure K μ hrate₀
        (hrate₁.trans_lt ENNReal.one_lt_top).ne heigen n
  · rintro ⟨hμ, hall⟩
    apply (isQuasiStationary_iff_one_step K μ hK).mpr
    obtain ⟨hpos, hcond⟩ := hall 1 le_rfl
    exact ⟨hμ, by simpa [killedMarginal] using hpos, hcond⟩

end ConditionedStableLaws
