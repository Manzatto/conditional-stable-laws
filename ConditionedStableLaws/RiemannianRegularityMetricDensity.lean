import ConditionedStableLaws.RiemannianRegularityLocalVolume
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The Riemannian coordinate density

In tangent coordinates the metric matrix is the Gram matrix of the coordinate tangent vectors. Its
square-root determinant is continuous on the chart target and strictly positive at the centre.
-/

open Module Bundle Set MeasureTheory MeasureTheory.Measure Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

namespace ConditionedStableLaws

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsManifold 𝓘(ℝ, E) 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Riemannian metric tensor in tangent-normalized coordinates, written
in an arbitrary basis of the tangent model space. -/
def tangentMetricMatrix (x : M) (b : Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x))
    (z : TangentSpace 𝓘(ℝ, E) x) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (fun i =>
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ
      ((tangentChart (E := E) x).symm z) (tangentCoordinateEquiv (E := E) x (b i)))

omit [IsRiemannianManifold 𝓘(ℝ, E) M] [Fintype ι] [DecidableEq ι] in
/-- Coordinate tangent vectors vary continuously as sections of the tangent
bundle, even though the norm on each tangent fibre is different. -/
theorem continuousOn_tangentMetricMatrix (x : M)
    (b : Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) :
    ContinuousOn (tangentMetricMatrix x b) (tangentChart (E := E) x).target := by
  let T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  let A := tangentCoordinateEquiv (E := E) x
  let e := tangentChart (E := E) x
  have hsec (v : E) : ContinuousOn (fun y : M =>
      TotalSpace.mk' E y (T.symmL ℝ y v)) T.baseSet := by
    have h := T.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (show MapsTo (fun y : M => (y, v)) T.baseSet (T.baseSet ×ˢ univ) from
        fun _ hy => ⟨hy, mem_univ _⟩)
    apply h.congr
    intro y hy
    simp only [Function.comp_apply, Trivialization.symmL_apply T hy, id_eq]
  have hmatrix : ContinuousOn
      (fun y : M => Matrix.gram ℝ (fun i => T.symmL ℝ y (A (b i)))) T.baseSet := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (hsec (A (b i))).inner_bundle (hsec (A (b j)))
  apply hmatrix.comp e.symm.continuousOn
  intro z hz
  simpa only [T, TangentBundle.trivializationAt_baseSet,
    e, tangentChart, OpenPartialHomeomorph.transHomeomorph_source] using e.map_target hz

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] [Fintype ι] [DecidableEq ι] in
/-- At the centre, the constructed coordinate tangent vectors are exactly the original basis
vectors. -/
theorem tangentMetricMatrix_self (x : M)
    (b : Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) :
    tangentMetricMatrix x b (tangentChart (E := E) x x) = Matrix.gram ℝ b := by
  have hx := mem_tangentChart_source (E := E) x
  let G (y : M) : Matrix ι ι ℝ := Matrix.gram ℝ (fun i =>
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ y
      (tangentCoordinateEquiv (E := E) x (b i)))
  change G ((tangentChart (E := E) x).symm ((tangentChart (E := E) x) x)) = _
  rw [(tangentChart (E := E) x).left_inv hx]
  dsimp only [G]
  congr 1
  funext i
  have heq : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ x =
      (tangentCoordinateEquiv (E := E) x).symm.toContinuousLinearMap :=
    (Trivialization.symm_continuousLinearEquivAt_eq' _ _).symm
  rw [heq]
  exact (tangentCoordinateEquiv (E := E) x).symm_apply_apply (b i)

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
/-- Positive definiteness of the Riemannian coordinate tensor at its centre
implies positivity of its determinant. -/
theorem tangentMetricMatrix_det_pos (x : M)
    (b : Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) :
    0 < Matrix.det (tangentMetricMatrix x b (tangentChart (E := E) x x)) := by
  rw [tangentMetricMatrix_self]
  exact (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos

/-- The square-root determinant of the Riemannian metric tensor. -/
def tangentVolumeDensity (x : M) (b : Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x))
    (z : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  Real.sqrt (Matrix.det (tangentMetricMatrix x b z))

omit [IsRiemannianManifold 𝓘(ℝ, E) M] in
theorem continuousOn_tangentVolumeDensity (x : M)
    (b : Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) :
    ContinuousOn (tangentVolumeDensity x b) (tangentChart (E := E) x).target := by
  exact Real.continuous_sqrt.comp_continuousOn
    (continuous_id.matrix_det.comp_continuousOn (continuousOn_tangentMetricMatrix x b))

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
theorem tangentVolumeDensity_pos (x : M)
    (b : Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) :
    0 < tangentVolumeDensity x b (tangentChart (E := E) x x) :=
  Real.sqrt_pos.mpr (tangentMetricMatrix_det_pos x b)

end ConditionedStableLaws
