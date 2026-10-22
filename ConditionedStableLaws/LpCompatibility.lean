import ConditionedStableLaws.Cited.Interpolation

/-!
# Algebra of compatible operator pairs

Compatibility (agreement almost everywhere on common functions) is preserved by composition, powers,
sums and scalar multiples. On a finite measure space an operator on `Lᵖ` compatible with an operator
on `Lᵖ⁰`, `p₀ ≤ p`, is uniquely determined by it.
-/

open MeasureTheory
open scoped ENNReal

namespace ConditionedStableLaws.LpCompatibility

open Cited

variable {M : Type*} [MeasurableSpace M] {μ : Measure M}

section General

variable {p₀ q₀ r₀ p₁ q₁ r₁ : ℝ≥0∞}
  [Fact (1 ≤ p₀)] [Fact (1 ≤ q₀)] [Fact (1 ≤ r₀)]
  [Fact (1 ≤ p₁)] [Fact (1 ≤ q₁)] [Fact (1 ≤ r₁)]

theorem symm {A₀ : Lp ℝ p₀ μ →L[ℝ] Lp ℝ q₀ μ} {A₁ : Lp ℝ p₁ μ →L[ℝ] Lp ℝ q₁ μ}
    (h : LpCompatible A₀ A₁) : LpCompatible A₁ A₀ :=
  fun f₁ f₀ hf => (h f₀ f₁ hf.symm).symm

theorem comp {A₀ : Lp ℝ r₀ μ →L[ℝ] Lp ℝ q₀ μ} {A₁ : Lp ℝ r₁ μ →L[ℝ] Lp ℝ q₁ μ}
    {B₀ : Lp ℝ p₀ μ →L[ℝ] Lp ℝ r₀ μ} {B₁ : Lp ℝ p₁ μ →L[ℝ] Lp ℝ r₁ μ}
    (hA : LpCompatible A₀ A₁) (hB : LpCompatible B₀ B₁) :
    LpCompatible (A₀.comp B₀) (A₁.comp B₁) :=
  fun f₀ f₁ hf => hA _ _ (hB f₀ f₁ hf)

theorem add {A₀ B₀ : Lp ℝ p₀ μ →L[ℝ] Lp ℝ q₀ μ} {A₁ B₁ : Lp ℝ p₁ μ →L[ℝ] Lp ℝ q₁ μ}
    (hA : LpCompatible A₀ A₁) (hB : LpCompatible B₀ B₁) :
    LpCompatible (A₀ + B₀) (A₁ + B₁) := by
  intro f₀ f₁ hf
  filter_upwards [Lp.coeFn_add (A₀ f₀) (B₀ f₀), Lp.coeFn_add (A₁ f₁) (B₁ f₁),
    hA f₀ f₁ hf, hB f₀ f₁ hf] with x h0 h1 ha hb
  simp only [add_apply, h0, h1, Pi.add_apply, ha, hb]

theorem smul (r : ℝ) {A₀ : Lp ℝ p₀ μ →L[ℝ] Lp ℝ q₀ μ} {A₁ : Lp ℝ p₁ μ →L[ℝ] Lp ℝ q₁ μ}
    (hA : LpCompatible A₀ A₁) : LpCompatible (r • A₀) (r • A₁) := by
  intro f₀ f₁ hf
  filter_upwards [Lp.coeFn_smul r (A₀ f₀), Lp.coeFn_smul r (A₁ f₁), hA f₀ f₁ hf]
    with x h0 h1 ha
  simp only [smul_apply, h0, h1, Pi.smul_apply, ha]

theorem neg {A₀ : Lp ℝ p₀ μ →L[ℝ] Lp ℝ q₀ μ} {A₁ : Lp ℝ p₁ μ →L[ℝ] Lp ℝ q₁ μ}
    (hA : LpCompatible A₀ A₁) : LpCompatible (-A₀) (-A₁) := by
  intro f₀ f₁ hf
  filter_upwards [Lp.coeFn_neg (A₀ f₀), Lp.coeFn_neg (A₁ f₁), hA f₀ f₁ hf] with x h0 h1 ha
  simp only [neg_apply, h0, h1, Pi.neg_apply, ha]

theorem sub {A₀ B₀ : Lp ℝ p₀ μ →L[ℝ] Lp ℝ q₀ μ} {A₁ B₁ : Lp ℝ p₁ μ →L[ℝ] Lp ℝ q₁ μ}
    (hA : LpCompatible A₀ A₁) (hB : LpCompatible B₀ B₁) :
    LpCompatible (A₀ - B₀) (A₁ - B₁) := by
  simpa only [sub_eq_add_neg] using add hA (neg hB)

theorem one : LpCompatible (1 : Lp ℝ p₀ μ →L[ℝ] Lp ℝ p₀ μ) (1 : Lp ℝ p₁ μ →L[ℝ] Lp ℝ p₁ μ) :=
  fun _ _ hf => hf

theorem pow {A₀ : Lp ℝ p₀ μ →L[ℝ] Lp ℝ p₀ μ} {A₁ : Lp ℝ p₁ μ →L[ℝ] Lp ℝ p₁ μ}
    (hA : LpCompatible A₀ A₁) (n : ℕ) : LpCompatible (A₀ ^ n) (A₁ ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact comp ih hA

end General

/-- On a finite measure space, operators on `Lᵖ` compatible with the same
operator on `Lᵖ⁰`, `p₀ ≤ p`, coincide. -/
theorem eq_of_compatible [IsFiniteMeasure μ] {p₀ q₀ p q : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ q₀)] [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p₀ ≤ p)
    {T : Lp ℝ p₀ μ →L[ℝ] Lp ℝ q₀ μ} {A B : Lp ℝ p μ →L[ℝ] Lp ℝ q μ}
    (hA : LpCompatible A T) (hB : LpCompatible B T) : A = B := by
  ext1 f
  have hf : MemLp (f : M → ℝ) p₀ μ := (Lp.memLp f).mono_exponent hp
  apply Lp.ext
  exact (hA f (hf.toLp _) hf.coeFn_toLp.symm).trans (hB f (hf.toLp _) hf.coeFn_toLp.symm).symm

end ConditionedStableLaws.LpCompatibility
