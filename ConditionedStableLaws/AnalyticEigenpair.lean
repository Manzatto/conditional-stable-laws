import ConditionedStableLaws.OperatorPerturbation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Analytic eigenpairs near a normalized rank-one eigenvalue

The scalar Schur equation is solved by the analytic inverse-function theorem. The only spectral
input is summability of powers of the complementary operator.
-/

open Filter Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace ConditionedStableLaws.OperatorPerturbation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
theorem analyticAt_clm_apply
    {U E F : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {c : U → E →L[𝕜] F} {v : U → E} {x : U}
    (hc : AnalyticAt 𝕜 c x) (hv : AnalyticAt 𝕜 v x) :
    AnalyticAt 𝕜 (fun y => c y (v y)) x :=
by
  have hb : AnalyticAt 𝕜 (fun p : (E →L[𝕜] F) × E => p.1 p.2) (c x, v x) :=
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).analyticAt_bilinear (c x, v x)
  exact hb.comp (f := fun y => (c y, v y)) (hc.prod hv)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem correction_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E) (z : 𝕜) :
    correction R μ η z 0 = 0 := by simp [correction]

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
@[simp] theorem scalarEquation_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E) (z : 𝕜) :
    scalarEquation R μ η z 0 = z - 1 := by simp [scalarEquation]

variable [CompleteSpace E]

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
theorem analyticAt_correction (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) :
    AnalyticAt 𝕜 (fun p : 𝕜 × (E →L[𝕜] E) => correction R μ η p.1 p.2) (1, 0) := by
  apply analyticAt_clm_apply (analyticAt_resolvent R μ η hs)
  exact ((complement μ η).analyticAt _).comp
    (((ContinuousLinearMap.apply 𝕜 E η).analyticAt _).comp analyticAt_snd)

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
theorem analyticAt_scalarEquation (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) :
    AnalyticAt 𝕜 (fun p : 𝕜 × (E →L[𝕜] E) => scalarEquation R μ η p.1 p.2) (1, 0) := by
  exact (analyticAt_fst.sub analyticAt_const).sub ((μ.analyticAt _).comp
    (analyticAt_clm_apply analyticAt_snd (analyticAt_const.add (analyticAt_correction R μ η hs))))

/-- The augmented scalar equation preserves the perturbation parameter. -/
def schurMap (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (p : 𝕜 × (E →L[𝕜] E)) : 𝕜 × (E →L[𝕜] E) :=
  (scalarEquation R μ η p.1 p.2, p.2)

omit [CompleteSpace 𝕜] [CharZero 𝕜] [CompleteSpace E] in
@[simp] theorem schurMap_base (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E) :
    schurMap R μ η (1, 0) = (0, 0) := by simp [schurMap]

/-- Explicit invertible derivative of the augmented equation. -/
def schurDerivative (μ : E →L[𝕜] 𝕜) (η : E) :
    (𝕜 × (E →L[𝕜] E)) ≃L[𝕜] (𝕜 × (E →L[𝕜] E)) where
  toFun p := (p.1 - μ (p.2 η), p.2)
  invFun p := (p.1 + μ (p.2 η), p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp [add_apply]; ring
  map_smul' c p := by simp [smul_apply]; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [CompleteSpace 𝕜] [CharZero 𝕜] [CompleteSpace E] in
@[simp] theorem schurDerivative_apply (μ : E →L[𝕜] 𝕜) (η : E) (p : 𝕜 × (E →L[𝕜] E)) :
    schurDerivative μ η p = (p.1 - μ (p.2 η), p.2) := rfl

omit [CompleteSpace 𝕜] [CharZero 𝕜] [CompleteSpace E] in
@[simp] theorem schurDerivative_symm_apply (μ : E →L[𝕜] 𝕜) (η : E) (p : 𝕜 × (E →L[𝕜] E)) :
    (schurDerivative μ η).symm p = (p.1 + μ (p.2 η), p.2) := rfl

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
theorem analyticAt_schurMap (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : AnalyticAt 𝕜 (schurMap R μ η) (1, 0) :=
  (analyticAt_scalarEquation R μ η hs).prod analyticAt_snd

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- The strict derivative is the explicit triangular linear equivalence. -/
theorem hasStrictFDerivAt_schurMap (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) :
    HasStrictFDerivAt (schurMap R μ η) (schurDerivative μ η).toContinuousLinearMap (1, 0) := by
  have hf := (ContinuousLinearMap.fst 𝕜 𝕜 (E →L[𝕜] E)).hasStrictFDerivAt (x := (1, 0))
  have hg := (ContinuousLinearMap.snd 𝕜 𝕜 (E →L[𝕜] E)).hasStrictFDerivAt (x := (1, 0))
  have hh := (analyticAt_correction R μ η hs).hasStrictFDerivAt
  have hm := hg.clm_apply ((hasStrictFDerivAt_const η ((1 : 𝕜), (0 : E →L[𝕜] E))).add hh)
  have hμ := (μ.hasStrictFDerivAt).comp (1, (0 : E →L[𝕜] E)) hm
  have ht := ((hf.sub_const 1).sub hμ).prodMk hg
  convert! ht using 1
  ext p <;> simp

omit [CompleteSpace 𝕜] [CharZero 𝕜] in
/-- Analytic inverse-function theorem for the Banach-space local inverse. -/
theorem analyticAt_localInverse_of_equiv
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : U → V} {a : U} {L : U ≃L[𝕜] V}
    (ha : AnalyticAt 𝕜 f a) (hd : HasStrictFDerivAt f L.toContinuousLinearMap a) :
    AnalyticAt 𝕜 (hd.localInverse f L a) (f a) := by
  obtain ⟨p, hp⟩ := ha
  let H := hd.toOpenPartialHomeomorph f
  have he : p 1 = (continuousMultilinearCurryFin1 𝕜 U V).symm L.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 𝕜 U V).injective
    simp only [LinearIsometryEquiv.apply_symm_apply]
    exact hp.hasFDerivAt.unique hd.hasFDerivAt
  exact (H.hasFPowerSeriesAt_symm hd.mem_toOpenPartialHomeomorph_source hp he).analyticAt

/-- The local inverse of the augmented equation. -/
def schurInverse (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) :
    (𝕜 × (E →L[𝕜] E)) → 𝕜 × (E →L[𝕜] E) :=
  (hasStrictFDerivAt_schurMap R μ η hs).localInverse (schurMap R μ η) (schurDerivative μ η) (1, 0)

omit [CharZero 𝕜] in
@[simp] theorem schurInverse_base (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : schurInverse R μ η hs (0, 0) = (1, 0) := by
  rw [← schurMap_base R μ η]
  exact (hasStrictFDerivAt_schurMap R μ η hs).localInverse_apply_image

omit [CharZero 𝕜] in
theorem analyticAt_schurInverse (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : AnalyticAt 𝕜 (schurInverse R μ η hs) (0, 0) := by
  have h := analyticAt_localInverse_of_equiv (analyticAt_schurMap R μ η hs)
    (hasStrictFDerivAt_schurMap R μ η hs)
  simpa only [schurMap_base, schurInverse] using h

/-- The eigenvalue branch is constructed by solving the scalar equation. -/
def eigenvalueBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (Δ : E →L[𝕜] E) : 𝕜 :=
  (schurInverse R μ η hs (0, Δ)).1

/-- The normalized eigenvector branch reconstructed from the resolvent. -/
def eigenvectorBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (Δ : E →L[𝕜] E) : E :=
  η + correction R μ η (eigenvalueBranch R μ η hs Δ) Δ

omit [CharZero 𝕜] in
@[simp] theorem eigenvalueBranch_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : eigenvalueBranch R μ η hs 0 = 1 := by
  simp [eigenvalueBranch]

omit [CharZero 𝕜] in
@[simp] theorem eigenvectorBranch_zero (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : eigenvectorBranch R μ η hs 0 = η := by
  simp [eigenvectorBranch]

omit [CharZero 𝕜] in
theorem analyticAt_eigenvalueBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : AnalyticAt 𝕜 (eigenvalueBranch R μ η hs) 0 := by
  exact analyticAt_fst.comp ((analyticAt_schurInverse R μ η hs).comp
    (analyticAt_const.prod analyticAt_id))

omit [CharZero 𝕜] in
theorem analyticAt_eigenvectorBranch (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) : AnalyticAt 𝕜 (eigenvectorBranch R μ η hs) 0 := by
  apply analyticAt_const.add
  exact (analyticAt_correction R μ η hs).comp_of_eq
    ((analyticAt_eigenvalueBranch R μ η hs).prod analyticAt_id) (by simp)

omit [CharZero 𝕜] in
/-- The constructed scalar branch solves the scalar equation near zero. -/
theorem eigenvalueBranch_equation (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) :
    ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E), scalarEquation R μ η (eigenvalueBranch R μ η hs Δ) Δ = 0 := by
  have ht := (hasStrictFDerivAt_schurMap R μ η hs).eventually_right_inverse
  rw [schurMap_base] at ht
  have hc : Tendsto (fun Δ : E →L[𝕜] E => ((0 : 𝕜), Δ)) (𝓝 0) (𝓝 (0, 0)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  filter_upwards [hc.eventually ht] with Δ hΔ
  have h₁ := congrArg Prod.fst hΔ
  have h₂ := congrArg Prod.snd hΔ
  change (schurInverse R μ η hs (0, Δ)).2 = Δ at h₂
  change scalarEquation R μ η (schurInverse R μ η hs (0, Δ)).1
    (schurInverse R μ η hs (0, Δ)).2 = 0 at h₁
  rw [h₂] at h₁
  exact h₁

/-- Local analytic eigenpair existence, obtained from the inverse theorem. -/
theorem eigenpairBranch_eventually (R : E →L[𝕜] E) (μ : E →L[𝕜] 𝕜) (η : E)
    (hs : Summable (fun n : ℕ => R ^ n)) (hμη : μ η = 1)
    (hμR : ∀ v, μ (R v) = 0) (hRη : R η = 0) :
    ∀ᶠ Δ in 𝓝 (0 : E →L[𝕜] E),
      μ (eigenvectorBranch R μ η hs Δ) = 1 ∧
        (projection μ η + R + Δ) (eigenvectorBranch R μ η hs Δ) =
          eigenvalueBranch R μ η hs Δ • eigenvectorBranch R μ η hs Δ := by
  have hc : Tendsto (eigenvalueBranch R μ η hs) (𝓝 0) (𝓝 1) := by
    have ht := (analyticAt_eigenvalueBranch R μ η hs).continuousAt
    change Tendsto _ (𝓝 0) (𝓝 (eigenvalueBranch R μ η hs 0)) at ht
    simpa only [eigenvalueBranch_zero] using ht
  have hpair := hc.prodMk_nhds (tendsto_id : Tendsto (id : (E →L[𝕜] E) → _) (𝓝 0) (𝓝 0))
  filter_upwards [hc.eventually (eventually_ne_nhds (one_ne_zero : (1 : 𝕜) ≠ 0)),
    hpair.eventually (eventually_isUnit_denominator R μ η hs), eigenvalueBranch_equation R μ η hs]
    with Δ hne hu he
  exact eigenvector_of_scalarEquation R μ η hμη hμR hRη _ hne Δ hu he

end ConditionedStableLaws.OperatorPerturbation
