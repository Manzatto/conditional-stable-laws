import ConditionedStableLaws.AnalyticEigenpair
import ConditionedStableLaws.PowerStability
import ConditionedStableLaws.SpectralAlgebra

/-!
# Analytic rank-one projections from left and right eigenvectors

The dual construction supplies a left eigenvector. Nonzero pairing identifies the two eigenvalues
and normalizes the projection.
-/

open Filter Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace ConditionedStableLaws.OperatorPerturbation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Transposition as a bounded linear map on operator spaces. -/
def transpose : (E →L[𝕜] E) →L[𝕜] ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜)) :=
  (ContinuousLinearMap.compL 𝕜 E E 𝕜).flip

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem transpose_apply (T : E →L[𝕜] E) (φ : E →L[𝕜] 𝕜) (v : E) :
    transpose T φ v = φ (T v) := rfl

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem transpose_one : transpose (1 : E →L[𝕜] E) = 1 := by ext; rfl

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem transpose_pow (T : E →L[𝕜] E) (n : ℕ) : transpose (T ^ n) = (transpose T) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, transpose_one]
  | succ n ih =>
    rw [pow_succ', pow_succ, ← ih]
    ext φ v
    rfl

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- Convergent powers remain convergent after transposition. -/
theorem summable_transpose_powers (R : E →L[𝕜] E) (hs : Summable (fun n : ℕ => R ^ n)) :
    Summable (fun n : ℕ => (transpose R) ^ n) := by
  simpa only [transpose_pow] using transpose.summable hs

/-- Evaluation at the fixed eigenvector is the left functional for the dual problem. -/
def evaluation (η : E) : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.apply 𝕜 𝕜 η

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem evaluation_apply (η : E) (φ : E →L[𝕜] 𝕜) : evaluation η φ = φ η := rfl

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem transpose_projection (μ : E →L[𝕜] 𝕜) (η : E) :
    transpose (projection μ η) = projection (evaluation η) μ := by
  ext φ v
  simp [smul_eq_mul, mul_comm]

variable [CompleteSpace E]

/-- The unnormalized analytic left eigenvector constructed in the continuous dual. -/
def leftBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (Δ : E →L[𝕜] E) : E →L[𝕜] 𝕜 :=
  eigenvectorBranch (transpose R) (evaluation η) μ (summable_transpose_powers R hs) (transpose Δ)

def leftEigenvalue (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (Δ : E →L[𝕜] E) : 𝕜 :=
  eigenvalueBranch (transpose R) (evaluation η) μ (summable_transpose_powers R hs) (transpose Δ)

omit [CharZero 𝕜] in
omit [CompleteSpace E] in
@[simp] theorem leftBranch_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : leftBranch R μ η hs 0 = μ := by simp only [leftBranch, map_zero, eigenvectorBranch_zero]

omit [CharZero 𝕜] in
omit [CompleteSpace E] in
@[simp] theorem leftEigenvalue_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : leftEigenvalue R μ η hs 0 = 1 := by simp only [leftEigenvalue, map_zero, eigenvalueBranch_zero]

omit [CharZero 𝕜] in
omit [CompleteSpace E] in
theorem analyticAt_leftBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : AnalyticAt 𝕜 (leftBranch R μ η hs) 0 := by
  have ht : AnalyticAt 𝕜 (fun Δ : E →L[𝕜] E => transpose Δ) 0 :=
    ContinuousLinearMap.analyticAt (𝕜 := 𝕜) (E := E →L[𝕜] E)
      (F := (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜)) transpose 0
  exact (analyticAt_eigenvectorBranch (transpose R) (evaluation η) μ
    (summable_transpose_powers R hs)).comp_of_eq ht (map_zero transpose)

omit [CharZero 𝕜] in
omit [CompleteSpace E] in
theorem analyticAt_leftEigenvalue (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : AnalyticAt 𝕜 (leftEigenvalue R μ η hs) 0 := by
  have ht : AnalyticAt 𝕜 (fun Δ : E →L[𝕜] E => transpose Δ) 0 :=
    ContinuousLinearMap.analyticAt (𝕜 := 𝕜) (E := E →L[𝕜] E)
      (F := (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜)) transpose 0
  exact (analyticAt_eigenvalueBranch (transpose R) (evaluation η) μ
    (summable_transpose_powers R hs)).comp_of_eq ht (map_zero transpose)

omit [CompleteSpace E] in
/-- The left eigen-equation holds on a neighborhood. -/
theorem leftBranch_eventually (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1)
    (hμR : ∀ v, μ (R v) = 0) (hRη : R η = 0) :
    ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E), ∀ v : E,
      leftBranch R μ η hs Δ ((projection μ η + R + Δ) v) =
        leftEigenvalue R μ η hs Δ * leftBranch R μ η hs Δ v := by
  have hdual := eigenpairBranch_eventually (transpose R) (evaluation η) μ
    (summable_transpose_powers R hs) hμη
    (fun φ => by simp [hRη]) (by ext v; exact hμR v)
  have ht : Tendsto transpose (𝓝 (0 : E →L[𝕜] E)) (𝓝 0) := by
    simpa using transpose.continuous.tendsto (0 : E →L[𝕜] E)
  filter_upwards [ht.eventually hdual] with Δ hΔ v
  have h := congrArg (fun φ : E →L[𝕜] 𝕜 => φ v) hΔ.2
  change (projection (evaluation η) μ + transpose R + transpose Δ)
    (leftBranch R μ η hs Δ) v = _ at h
  rw [← transpose_projection, ← map_add, ← map_add] at h
  exact h

/-- The pairing of the two eigenvector branches. -/
def pairing (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (Δ : E →L[𝕜] E) : 𝕜 :=
  leftBranch R μ η hs Δ (eigenvectorBranch R μ η hs Δ)

omit [CharZero 𝕜] in
@[simp] theorem pairing_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : pairing R μ η hs 0 = μ η := by simp [pairing]

omit [CharZero 𝕜] in
theorem analyticAt_pairing (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : AnalyticAt 𝕜 (pairing R μ η hs) 0 :=
  analyticAt_clm_apply (analyticAt_leftBranch R μ η hs) (analyticAt_eigenvectorBranch R μ η hs)

theorem pairing_eventually_ne_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1) :
    ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E), pairing R μ η hs Δ ≠ 0 := by
  have ht := (analyticAt_pairing R μ η hs).continuousAt
  change Tendsto _ _ (𝓝 (pairing R μ η hs 0)) at ht
  rw [pairing_zero, hμη] at ht
  exact ht.eventually (eventually_ne_nhds one_ne_zero)

/-- Nonzero pairing proves that the independently constructed eigenvalues coincide. -/
theorem leftEigenvalue_eq_eventually (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1)
    (hμR : ∀ v, μ (R v) = 0) (hRη : R η = 0) :
    ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E), leftEigenvalue R μ η hs Δ = eigenvalueBranch R μ η hs Δ := by
  filter_upwards [leftBranch_eventually R μ η hs hμη hμR hRη,
    eigenpairBranch_eventually R μ η hs hμη hμR hRη,
    pairing_eventually_ne_zero R μ η hs hμη] with Δ hl hr hp
  have h := hl (eigenvectorBranch R μ η hs Δ)
  rw [hr.2, map_smul, smul_eq_mul] at h
  exact (mul_right_cancel₀ hp h).symm

/-- The left eigenfunctional normalized against the constructed right eigenvector. -/
def normalizedLeftBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (Δ : E →L[𝕜] E) : E →L[𝕜] 𝕜 :=
  (pairing R μ η hs Δ)⁻¹ • leftBranch R μ η hs Δ

/-- The rank-one projection near the fixed simple eigenvalue. -/
def projectionBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (Δ : E →L[𝕜] E) : E →L[𝕜] E :=
  projection (normalizedLeftBranch R μ η hs Δ) (eigenvectorBranch R μ η hs Δ)

/-- The complementary operator; no power bound is part of this definition. -/
def remainderBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (Δ : E →L[𝕜] E) : E →L[𝕜] E :=
  projection μ η + R + Δ - eigenvalueBranch R μ η hs Δ • projectionBranch R μ η hs Δ

omit [CharZero 𝕜] in
@[simp] theorem normalizedLeftBranch_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1) : normalizedLeftBranch R μ η hs 0 = μ := by
  simp [normalizedLeftBranch, hμη]

omit [CharZero 𝕜] in
@[simp] theorem projectionBranch_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1) : projectionBranch R μ η hs 0 = projection μ η := by
  simp [projectionBranch, hμη]

omit [CharZero 𝕜] in
@[simp] theorem remainderBranch_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1) : remainderBranch R μ η hs 0 = R := by
  simp [remainderBranch, hμη, add_sub_cancel_left]

theorem analyticAt_normalizedLeftBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1) :
    AnalyticAt 𝕜 (normalizedLeftBranch R μ η hs) 0 :=
  ((analyticAt_pairing R μ η hs).inv (by simp [hμη])).smul (analyticAt_leftBranch R μ η hs)

theorem analyticAt_projectionBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1) :
    AnalyticAt 𝕜 (projectionBranch R μ η hs) 0 := by
  have ha := (ContinuousLinearMap.smulRightL 𝕜 E E).analyticAt_bilinear
    (normalizedLeftBranch R μ η hs 0, eigenvectorBranch R μ η hs 0)
  exact ha.comp (f := fun Δ => (normalizedLeftBranch R μ η hs Δ, eigenvectorBranch R μ η hs Δ))
    ((analyticAt_normalizedLeftBranch R μ η hs hμη).prod (analyticAt_eigenvectorBranch R μ η hs))

theorem analyticAt_remainderBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1) :
    AnalyticAt 𝕜 (remainderBranch R μ η hs) 0 :=
  (analyticAt_const.add analyticAt_id).sub ((analyticAt_eigenvalueBranch R μ η hs).smul
    (analyticAt_projectionBranch R μ η hs hμη))

/-- The constructed complementary operators converge in operator norm to R. -/
theorem remainderBranch_tendsto (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1) :
    Tendsto (remainderBranch R μ η hs) (𝓝 0) (𝓝 R) := by
  have h := (analyticAt_remainderBranch R μ η hs hμη).continuousAt
  change Tendsto _ _ (𝓝 (remainderBranch R μ η hs 0)) at h
  simpa only [remainderBranch_zero R μ η hs hμη] using h

/-- Idempotence and both spectral commutation identities hold for the
constructed projection throughout a neighborhood of the original operator. -/
theorem projectionBranch_eventually (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1)
    (hμR : ∀ v, μ (R v) = 0) (hRη : R η = 0) :
    ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E),
      projectionBranch R μ η hs Δ * projectionBranch R μ η hs Δ = projectionBranch R μ η hs Δ ∧
      projectionBranch R μ η hs Δ * (projection μ η + R + Δ) =
        eigenvalueBranch R μ η hs Δ • projectionBranch R μ η hs Δ ∧
      (projection μ η + R + Δ) * projectionBranch R μ η hs Δ =
        eigenvalueBranch R μ η hs Δ • projectionBranch R μ η hs Δ := by
  filter_upwards [pairing_eventually_ne_zero R μ η hs hμη,
    leftBranch_eventually R μ η hs hμη hμR hRη,
    leftEigenvalue_eq_eventually R μ η hs hμη hμR hRη,
    eigenpairBranch_eventually R μ η hs hμη hμR hRη] with Δ hp hl he hr
  have hn : normalizedLeftBranch R μ η hs Δ (eigenvectorBranch R μ η hs Δ) = 1 := by
    change (pairing R μ η hs Δ)⁻¹ * pairing R μ η hs Δ = 1
    exact inv_mul_cancel₀ hp
  have hleft (v : E) : normalizedLeftBranch R μ η hs Δ ((projection μ η + R + Δ) v) =
      eigenvalueBranch R μ η hs Δ * normalizedLeftBranch R μ η hs Δ v := by
    change (pairing R μ η hs Δ)⁻¹ * leftBranch R μ η hs Δ ((projection μ η + R + Δ) v) = _
    rw [hl, he]
    change _ = eigenvalueBranch R μ η hs Δ * ((pairing R μ η hs Δ)⁻¹ * leftBranch R μ η hs Δ v)
    ring
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [mul_apply_eq_comp, projectionBranch, projection_apply, map_smul, hn, one_smul]
  · ext v
    simp only [mul_apply_eq_comp, projectionBranch, projection_apply, hleft, smul_apply, mul_smul]
  · ext v
    simp only [mul_apply_eq_comp, projectionBranch, projection_apply, map_smul, hr.2, smul_apply]
    exact smul_comm _ _ _

/-- The complementary operator annihilates the constructed projection on both sides. -/
theorem remainderBranch_annihilation (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1)
    (hμR : ∀ v, μ (R v) = 0) (hRη : R η = 0) :
    ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E),
      projectionBranch R μ η hs Δ * remainderBranch R μ η hs Δ = 0 ∧
      remainderBranch R μ η hs Δ * projectionBranch R μ η hs Δ = 0 := by
  filter_upwards [projectionBranch_eventually R μ η hs hμη hμR hRη] with Δ hΔ
  constructor
  · rw [remainderBranch, mul_sub, mul_smul_comm, hΔ.1, hΔ.2.1, sub_self]
  · rw [remainderBranch, sub_mul, smul_mul_assoc, hΔ.1, hΔ.2.2, sub_self]


omit [CompleteSpace 𝕜] [CharZero 𝕜] [CompleteSpace E] in
/-- Positive powers of a weighted projection plus an annihilating remainder. -/
theorem weighted_projection_add_remainder_pow (P R : E →L[𝕜] E) (z : 𝕜)
    (hP : P * P = P) (hPR : P * R = 0) (hRP : R * P = 0) (n : ℕ) :
    (z • P + R) ^ (n + 1) = z ^ (n + 1) • P + R ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc,
      mul_smul_comm, hP, smul_smul, smul_mul_assoc, hPR, smul_zero,
      mul_smul_comm, SpectralAlgebra.positive_power_mul_eq_zero R P hRP n,
      smul_zero, add_zero, zero_add, ← pow_succ, ← pow_succ]

/-- The exact positive-power spectral decomposition for the constructed branches. -/
theorem spectral_power_decomposition_eventually (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1)
    (hμR : ∀ v, μ (R v) = 0) (hRη : R η = 0) :
    ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E), ∀ n : ℕ, 1 ≤ n →
      (projection μ η + R + Δ) ^ n =
        eigenvalueBranch R μ η hs Δ ^ n • projectionBranch R μ η hs Δ +
          remainderBranch R μ η hs Δ ^ n := by
  filter_upwards [projectionBranch_eventually R μ η hs hμη hμR hRη,
    remainderBranch_annihilation R μ η hs hμη hμR hRη] with Δ hP hR n hn
  have he : projection μ η + R + Δ = eigenvalueBranch R μ η hs Δ • projectionBranch R μ η hs Δ +
      remainderBranch R μ η hs Δ := by unfold remainderBranch; abel
  rw [he]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact weighted_projection_add_remainder_pow _ _ _ hP.1 hR.1 hR.2 k

/-- A single rate below one and a single constant bound all powers of every
nearby complementary operator. This bound is derived from continuity and a
finite contracting block of the original remainder. -/
theorem remainderBranch_uniform_geometric_bound (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hpow : ∀ n : ℕ, ‖R ^ n‖ ≤ C * r ^ n) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E), ∀ n : ℕ,
        ‖remainderBranch R μ η hs Δ ^ n‖ ≤ D * q ^ n := by
  have hη : η ≠ 0 := by intro he; simp [he] at hμη
  let : Nontrivial E := ⟨⟨η, 0, hη⟩⟩
  obtain ⟨q, hq, hq1, D, hD, he⟩ :=
    PowerStability.eventually_geometric_bound R hC hr hr1 hpow
  exact ⟨q, hq, hq1, D, hD, (remainderBranch_tendsto R μ η hs hμη).eventually he⟩

/-- The construction also accepts a bound for positive powers only. -/
theorem remainderBranch_uniform_geometric_bound_of_positive_powers
    (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1)
    {C r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hpow : ∀ n : ℕ, 1 ≤ n → ‖R ^ n‖ ≤ C * r ^ n) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E), ∀ n : ℕ,
        ‖remainderBranch R μ η hs Δ ^ n‖ ≤ D * q ^ n := by
  apply remainderBranch_uniform_geometric_bound R μ η hs hμη
    (C := max 1 C) (le_trans zero_le_one (le_max_left _ _)) hr hr1
  intro n
  cases n with
  | zero =>
      simp only [pow_zero, mul_one]
      exact (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)).trans (le_max_left 1 C)
  | succ n =>
      exact (hpow (n + 1) (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hr _))

end ConditionedStableLaws.OperatorPerturbation
