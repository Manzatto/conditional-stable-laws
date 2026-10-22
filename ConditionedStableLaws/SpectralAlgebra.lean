import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Algebraic part of the spectral decomposition

Starting with a linear functional `μ`, a vector `η` with `μ η = 1`, and left/right eigenvector
identities for a linear operator `P`, we prove the projection, annihilation and positive-power
identities. No topology, measure space or spectral radius is needed.
-/

namespace ConditionedStableLaws

namespace SpectralAlgebra

section Ring

variable {A : Type*} [Ring A]

/-- A positive power of an element annihilating `p` still annihilates `p`. -/
theorem positive_power_mul_eq_zero (r p : A) (hrp : r * p = 0) (n : ℕ) :
    r ^ (n + 1) * p = 0 := by
  induction n with
  | zero => simpa using hrp
  | succ n ih =>
      rw [pow_succ', mul_assoc, ih, mul_zero]

/-- A projection and a mutually annihilating remainder have no mixed terms
in any positive power. This statement works in a noncommutative ring. -/
theorem projection_add_remainder_pow (p r : A) (hpp : p * p = p)
    (hpr : p * r = 0) (hrp : r * p = 0) (n : ℕ) :
    (p + r) ^ (n + 1) = p + r ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, add_mul, mul_add, mul_add, hpp, hpr,
        positive_power_mul_eq_zero r p hrp n, add_zero, zero_add]
      exact congrArg (fun a => p + a) (pow_succ r (n + 1)).symm

/-- The remainder obtained by subtracting an invariant projection is
annihilated on both sides by the projection. -/
theorem projection_sub_annihilation (q p : A) (hpp : p * p = p)
    (hpq : p * q = p) (hqp : q * p = p) :
    p * (q - p) = 0 ∧ (q - p) * p = 0 := by
  constructor
  · rw [mul_sub, hpq, hpp, sub_self]
  · rw [sub_mul, hqp, hpp, sub_self]

/-- The positive-power formula for an operator and an invariant projection. -/
theorem operator_pow_eq_projection_add (q p : A) (hpp : p * p = p)
    (hpq : p * q = p) (hqp : q * p = p) (n : ℕ) (hn : 1 ≤ n) :
    q ^ n = p + (q - p) ^ n := by
  have hq : q = p + (q - p) := by abel
  obtain ⟨hpr, hrp⟩ := projection_sub_annihilation q p hpp hpq hqp
  cases n with
  | zero => omega
  | succ k =>
      calc
        q ^ (k + 1) = (p + (q - p)) ^ (k + 1) := congrArg (fun a => a ^ (k + 1)) hq
        _ = p + (q - p) ^ (k + 1) :=
          projection_add_remainder_pow p (q - p) hpp hpr hrp k

end Ring

section LinearMaps

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The map `Π f = μ(f) • η`. -/
def rankOne (μ : E →ₗ[K] K) (η : E) : Module.End K E where
  toFun f := μ f • η
  map_add' f g := by simp [add_smul]
  map_smul' c f := by simp [mul_smul]

@[simp]
theorem rankOne_apply (μ : E →ₗ[K] K) (η f : E) :
    rankOne μ η f = μ f • η := rfl

/-- Normalization of the left/right eigenvectors makes `Π` idempotent. -/
theorem rankOne_idempotent (μ : E →ₗ[K] K) (η : E) (hμη : μ η = 1) :
    rankOne μ η * rankOne μ η = rankOne μ η := by
  ext f
  simp [Module.End.mul_apply, hμη]

/-- The left eigenvector relation for the normalized operator gives `ΠQ = Π`. -/
theorem rankOne_mul_operator (μ : E →ₗ[K] K) (η : E) (Q : Module.End K E)
    (hμQ : ∀ f, μ (Q f) = μ f) :
    rankOne μ η * Q = rankOne μ η := by
  ext f
  simp [Module.End.mul_apply, hμQ]

/-- The right eigenvector relation for the normalized operator gives `QΠ = Π`. -/
theorem operator_mul_rankOne (μ : E →ₗ[K] K) (η : E) (Q : Module.End K E)
    (hQη : Q η = η) :
    Q * rankOne μ η = rankOne μ η := by
  ext f
  simp [Module.End.mul_apply, hQη]

/-- The algebraic spectral decomposition, from the normalization and the left/right eigenvector
relations. -/
theorem normalized_spectral_decomposition
    (μ : E →ₗ[K] K) (η : E) (Q : Module.End K E)
    (hμη : μ η = 1) (hμQ : ∀ f, μ (Q f) = μ f) (hQη : Q η = η) :
    let pi := rankOne μ η
    let R := Q - pi
    pi * pi = pi ∧ pi * R = 0 ∧ R * pi = 0 ∧
      ∀ n : ℕ, 1 ≤ n → Q ^ n = pi + R ^ n := by
  dsimp only
  have hpp := rankOne_idempotent μ η hμη
  have hpq := rankOne_mul_operator μ η Q hμQ
  have hqp := operator_mul_rankOne μ η Q hQη
  obtain ⟨hpr, hrp⟩ := projection_sub_annihilation Q (rankOne μ η) hpp hpq hqp
  exact ⟨hpp, hpr, hrp, operator_pow_eq_projection_add Q (rankOne μ η) hpp hpq hqp⟩

/-- Rescaling an operator by a nonzero eigenvalue fixes its right eigenvector. -/
theorem normalized_operator_fixes_eigenvector
    (P : Module.End K E) (η : E) (eigenvalue : K) (hne : eigenvalue ≠ 0)
    (hPη : P η = eigenvalue • η) :
    (eigenvalue⁻¹ • P) η = η := by
  simp [hPη, smul_smul, hne]

/-- Rescaling an operator by a nonzero eigenvalue fixes its left eigenvector. -/
theorem functional_normalized_operator
    (P : Module.End K E) (μ : E →ₗ[K] K) (eigenvalue : K) (hne : eigenvalue ≠ 0)
    (hμP : ∀ f, μ (P f) = eigenvalue * μ f) (f : E) :
    μ ((eigenvalue⁻¹ • P) f) = μ f := by
  simp [hμP, hne]

/-- The identities with `Q = λ⁻¹ P`, from the unnormalized left and right eigenvector identities. -/
theorem spectral_decomposition_algebra
    (P : Module.End K E) (μ : E →ₗ[K] K) (η : E) (eigenvalue : K)
    (hne : eigenvalue ≠ 0) (hμη : μ η = 1)
    (hPη : P η = eigenvalue • η) (hμP : ∀ f, μ (P f) = eigenvalue * μ f) :
    let Q := eigenvalue⁻¹ • P
    let pi := rankOne μ η
    let R := Q - pi
    pi * pi = pi ∧ pi * R = 0 ∧ R * pi = 0 ∧
      ∀ n : ℕ, 1 ≤ n → Q ^ n = pi + R ^ n := by
  exact normalized_spectral_decomposition μ η (eigenvalue⁻¹ • P) hμη
    (functional_normalized_operator P μ eigenvalue hne hμP)
    (normalized_operator_fixes_eigenvector P η eigenvalue hne hPη)

/-- Applying the operator identity to a vector gives the main term `η μ(f)`
and the exact remainder, before any analytic estimate is invoked. -/
theorem normalized_power_apply
    (μ : E →ₗ[K] K) (η : E) (Q : Module.End K E)
    (hμη : μ η = 1) (hμQ : ∀ f, μ (Q f) = μ f) (hQη : Q η = η)
    (n : ℕ) (hn : 1 ≤ n) (f : E) :
    (Q ^ n) f = μ f • η + ((Q - rankOne μ η) ^ n) f := by
  have h := (normalized_spectral_decomposition μ η Q hμη hμQ hQη).2.2.2 n hn
  exact congrArg (fun T : Module.End K E => T f) h

/-- The remainder has zero `μ`-mean. -/
theorem functional_remainder
    (μ : E →ₗ[K] K) (η : E) (Q : Module.End K E)
    (hμη : μ η = 1) (hμQ : ∀ f, μ (Q f) = μ f) (f : E) :
    μ ((Q - rankOne μ η) f) = 0 := by
  simp [hμQ, hμη]

/-- The remainder annihilates the distinguished eigenvector. -/
theorem remainder_eigenvector
    (μ : E →ₗ[K] K) (η : E) (Q : Module.End K E)
    (hμη : μ η = 1) (hQη : Q η = η) :
    (Q - rankOne μ η) η = 0 := by
  simp [hQη, hμη]

end LinearMaps

end SpectralAlgebra

end ConditionedStableLaws
