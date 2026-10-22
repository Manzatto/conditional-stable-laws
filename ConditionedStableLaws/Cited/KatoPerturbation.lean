import ConditionedStableLaws.PerturbationStability

/-!
# Stability of an isolated simple eigenvalue under small perturbations
-/

namespace ConditionedStableLaws.Cited

/-- Stability of an isolated simple eigenvalue under small perturbations, from the local analytic
eigenpair and projection constructions. For `T₀` with the simple eigenvalue `1`, rank-one spectral
projection `Π₀ = ℓ(·) v` and the rest of the spectrum in a disc of radius `θ < 1`, there are `ε₀ >
0`, `K₀ ≥ 0`, `0 ≤ χ < 1` and `C' ≥ 0` such that every bounded `T` with `‖T - T₀‖ ≤ ε₀` has a real
eigenvalue `Λ` with spectral projection `Pr`, `T Pr = Pr T = Λ Pr`, `|Λ - 1| ≤ K₀ ‖T - T₀‖`, `‖Pr -
Π₀‖ ≤ K₀ ‖T - T₀‖`, `χ < Λ`, and `‖Tⁿ - Λⁿ Pr‖ ≤ C' χⁿ`; all constants depend only on `T₀`. (The
eigenvalue is real because it is simple and `T` is real; the projection and remainder bounds are
Lipschitz/uniform because the resolvent of `T` is uniformly bounded on circles separating `1` from
the rest of the spectrum.) -/
theorem kato_stability {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T₀ : E →L[ℝ] E) (v : E) (ℓ : E →L[ℝ] ℝ) (hℓv : ℓ v = 1)
    (hT₀P : T₀ * ℓ.smulRight v = ℓ.smulRight v) (hPT₀ : ℓ.smulRight v * T₀ = ℓ.smulRight v)
    {C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hgap : ∀ n : ℕ, 1 ≤ n → ‖T₀ ^ n - ℓ.smulRight v‖ ≤ C * θ ^ n) :
    ∃ ε₀ > 0, ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∃ χ : ℝ, 0 ≤ χ ∧ χ < 1 ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ T : E →L[ℝ] E, ‖T - T₀‖ ≤ ε₀ →
        ∃ (Λ : ℝ) (Pr : E →L[ℝ] E),
          T * Pr = Λ • Pr ∧ Pr * T = Λ • Pr ∧
          |Λ - 1| ≤ K₀ * ‖T - T₀‖ ∧ ‖Pr - ℓ.smulRight v‖ ≤ K₀ * ‖T - T₀‖ ∧ χ < Λ ∧
          ∀ n : ℕ, 1 ≤ n → ‖T ^ n - Λ ^ n • Pr‖ ≤ C' * χ ^ n :=
  OperatorPerturbation.stability_of_rank_one_gap T₀ v ℓ hℓv hT₀P hPT₀ hθ0 hθ hgap

end ConditionedStableLaws.Cited
