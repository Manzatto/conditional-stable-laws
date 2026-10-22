import ConditionedStableLaws.AnalyticSpectralProjection

/-!
# Stability of a normalized rank-one spectral gap

The analytic eigenpair and projection constructions give the real perturbation statement used in the
probabilistic arguments. The input is only a normalized rank-one decomposition and exponential decay
of the complementary powers.
-/

open Filter Metric
open scoped Topology
noncomputable section

namespace ConditionedStableLaws.OperatorPerturbation

set_option maxHeartbeats 4000000 in
/-- A real bounded operator with a normalized rank-one spectral gap has a
locally Lipschitz leading eigenvalue and projection, together with a uniform
geometric bound for the complementary powers. -/
theorem stability_of_rank_one_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T₀ : E →L[ℝ] E) (v : E) (ℓ : E →L[ℝ] ℝ) (hℓv : ℓ v = 1)
    (hT₀P : T₀ * ℓ.smulRight v = ℓ.smulRight v)
    (hPT₀ : ℓ.smulRight v * T₀ = ℓ.smulRight v)
    {C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hgap : ∀ n : ℕ, 1 ≤ n → ‖T₀ ^ n - ℓ.smulRight v‖ ≤ C * θ ^ n) :
    ∃ ε₀ > 0, ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∃ χ : ℝ, 0 ≤ χ ∧ χ < 1 ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ T : E →L[ℝ] E, ‖T - T₀‖ ≤ ε₀ →
        ∃ (Λ : ℝ) (Pr : E →L[ℝ] E),
          T * Pr = Λ • Pr ∧ Pr * T = Λ • Pr ∧
          |Λ - 1| ≤ K₀ * ‖T - T₀‖ ∧ ‖Pr - ℓ.smulRight v‖ ≤ K₀ * ‖T - T₀‖ ∧ χ < Λ ∧
          ∀ n : ℕ, 1 ≤ n → ‖T ^ n - Λ ^ n • Pr‖ ≤ C' * χ ^ n := by
  let P : E →L[ℝ] E := ℓ.smulRight v
  let R : E →L[ℝ] E := T₀ - P
  have hPP : P * P = P := by
    ext w
    simp [P, hℓv]
  have hTP : T₀ * P = P := by simpa [P] using hT₀P
  have hPT : P * T₀ = P := by simpa [P] using hPT₀
  have hμR : ∀ w, ℓ (R w) = 0 := by
    intro w
    have h := congrArg (fun A : E →L[ℝ] E => ℓ (A w)) hPT
    have hmean : ℓ (T₀ w) = ℓ w := by simpa [P, hℓv] using h
    simp [R, P, hmean, hℓv]
  have hRv : R v = 0 := by
    have h := congrArg (fun A : E →L[ℝ] E => A v) hTP
    have hfix : T₀ v = v := by simpa [P, hℓv] using h
    simp [R, P, hfix, hℓv]
  have hRpow : ∀ n : ℕ, 1 ≤ n → ‖R ^ n‖ ≤ C * θ ^ n := by
    intro n hn
    have hpow := SpectralAlgebra.operator_pow_eq_projection_add T₀ P hPP hPT hTP n hn
    have heq : T₀ ^ n - P = R ^ n := by rw [hpow]; simp [R]
    rw [← heq]
    simpa [P] using hgap n hn
  have hs : Summable (fun n : ℕ => R ^ n) := summable_powers R hθ0 hθ hRpow
  obtain ⟨q, hq, hq1, D, hD, hrem⟩ :=
    remainderBranch_uniform_geometric_bound_of_positive_powers R ℓ v hs hℓv hθ0 hθ hRpow
  obtain ⟨Keig, hKeig⟩ :=
    (analyticAt_eigenvalueBranch R ℓ v hs).differentiableAt.hasFDerivAt.isBigO_sub.bound
  obtain ⟨KP, hKP⟩ :=
    (analyticAt_projectionBranch R ℓ v hs hℓv).differentiableAt.hasFDerivAt.isBigO_sub.bound
  let K₀ := max 0 (max Keig KP)
  have hK₀ : 0 ≤ K₀ := le_max_left _ _
  have heiglip : ∀ᶠ Δ : E →L[ℝ] E in 𝓝 0,
      |eigenvalueBranch R ℓ v hs Δ - 1| ≤ K₀ * ‖Δ‖ := by
    filter_upwards [hKeig] with Δ hΔ
    have hΔ' : ‖eigenvalueBranch R ℓ v hs Δ - 1‖ ≤ Keig * ‖Δ‖ := by
      simpa only [eigenvalueBranch_zero, sub_zero] using hΔ
    rw [← Real.norm_eq_abs]
    exact hΔ'.trans (mul_le_mul_of_nonneg_right
      ((le_max_left Keig KP).trans (le_max_right 0 (max Keig KP))) (norm_nonneg _))
  have hPlip : ∀ᶠ Δ : E →L[ℝ] E in 𝓝 0,
      ‖projectionBranch R ℓ v hs Δ - P‖ ≤ K₀ * ‖Δ‖ := by
    filter_upwards [hKP] with Δ hΔ
    have hΔ' : ‖projectionBranch R ℓ v hs Δ - P‖ ≤ KP * ‖Δ‖ := by
      change ‖projectionBranch R ℓ v hs Δ - projection ℓ v‖ ≤ KP * ‖Δ‖
      simpa only [projectionBranch_zero R ℓ v hs hℓv, sub_zero] using hΔ
    exact hΔ'.trans (mul_le_mul_of_nonneg_right
      ((le_max_right Keig KP).trans (le_max_right 0 (max Keig KP))) (norm_nonneg _))
  have heigq : ∀ᶠ Δ : E →L[ℝ] E in 𝓝 0, q < eigenvalueBranch R ℓ v hs Δ := by
    have ht := (analyticAt_eigenvalueBranch R ℓ v hs).continuousAt
    change Tendsto _ (𝓝 0) (𝓝 (eigenvalueBranch R ℓ v hs 0)) at ht
    rw [eigenvalueBranch_zero] at ht
    exact ht.eventually (lt_mem_nhds hq1)
  have hall : ∀ᶠ Δ : E →L[ℝ] E in 𝓝 0,
      (projectionBranch R ℓ v hs Δ * projectionBranch R ℓ v hs Δ =
          projectionBranch R ℓ v hs Δ ∧
        projectionBranch R ℓ v hs Δ * (P + R + Δ) =
          eigenvalueBranch R ℓ v hs Δ • projectionBranch R ℓ v hs Δ ∧
        (P + R + Δ) * projectionBranch R ℓ v hs Δ =
          eigenvalueBranch R ℓ v hs Δ • projectionBranch R ℓ v hs Δ) ∧
      (∀ n : ℕ, 1 ≤ n → (P + R + Δ) ^ n =
        eigenvalueBranch R ℓ v hs Δ ^ n • projectionBranch R ℓ v hs Δ +
          remainderBranch R ℓ v hs Δ ^ n) ∧
      (∀ n : ℕ, ‖remainderBranch R ℓ v hs Δ ^ n‖ ≤ D * q ^ n) ∧
      |eigenvalueBranch R ℓ v hs Δ - 1| ≤ K₀ * ‖Δ‖ ∧
      ‖projectionBranch R ℓ v hs Δ - P‖ ≤ K₀ * ‖Δ‖ ∧
      q < eigenvalueBranch R ℓ v hs Δ := by
    filter_upwards [projectionBranch_eventually R ℓ v hs hℓv hμR hRv,
      spectral_power_decomposition_eventually R ℓ v hs hℓv hμR hRv,
      hrem, heiglip, hPlip, heigq] with Δ hproj hpow hremΔ heigΔ hPΔ hqΔ
    exact ⟨hproj, hpow, hremΔ, heigΔ, hPΔ, hqΔ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ε / 2, by positivity, K₀, hK₀, q, hq.le, hq1, D, hD, ?_⟩
  intro T hT
  let Δ : E →L[ℝ] E := T - T₀
  have hΔε : ‖Δ‖ < ε := by
    dsimp [Δ]
    linarith
  have hΔ := hball (by simpa only [dist_zero_right] using hΔε)
  let Λ : ℝ := eigenvalueBranch R ℓ v hs Δ
  let Pr : E →L[ℝ] E := projectionBranch R ℓ v hs Δ
  have hbase : P + R + Δ = T := by
    dsimp [R, Δ]
    abel
  refine ⟨Λ, Pr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Λ, Pr, hbase] using hΔ.1.2.2
  · simpa [Λ, Pr, hbase] using hΔ.1.2.1
  · simpa [Λ, Δ] using hΔ.2.2.2.1
  · simpa [Pr, P, Δ] using hΔ.2.2.2.2.1
  · simpa [Λ] using hΔ.2.2.2.2.2
  · intro n hn
    have heq : T ^ n - Λ ^ n • Pr = remainderBranch R ℓ v hs Δ ^ n := by
      rw [← hbase, hΔ.2.1 n hn]
      simp [Λ, Pr]
    rw [heq]
    exact hΔ.2.2.1 n

end ConditionedStableLaws.OperatorPerturbation
