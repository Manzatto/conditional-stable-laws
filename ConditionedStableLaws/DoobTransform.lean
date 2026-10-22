import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# The Doob transform from explicit spectral data

The construction starts with a measurable, finite, nonnegative right eigenfunction and a positive
finite eigenvalue. The resulting kernel and its iterates are given by kernel composition.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ConditionedStableLaws

namespace DoobTransform

noncomputable section

variable {M : Type*} [MeasurableSpace M]

/-- Spectral input on a space where the eigenfunction is strictly positive.
The zero set is removed by a subtype construction below. -/
structure PositiveEigenData (K : Kernel M M) where
  rate : ℝ≥0∞
  rate_ne_zero : rate ≠ 0
  rate_ne_top : rate ≠ ∞
  weight : M → ℝ≥0∞
  measurable_weight : Measurable weight
  weight_ne_zero : ∀ x, weight x ≠ 0
  weight_ne_top : ∀ x, weight x ≠ ∞
  right_eigen : ∀ x, ∫⁻ y, weight y ∂K x = rate * weight x

namespace PositiveEigenData

variable {K : Kernel M M} [IsSFiniteKernel K] (d : PositiveEigenData K)

/-- The factor `η(y)/(λ η(x))`, with all inverses finite on this state space. -/
def density (x y : M) : ℝ≥0∞ := d.rate⁻¹ * (d.weight x)⁻¹ * d.weight y

omit [IsSFiniteKernel K] in
theorem measurable_density : Measurable (Function.uncurry d.density) := by
  exact ((measurable_const.mul (d.measurable_weight.comp measurable_fst).inv).mul
    (d.measurable_weight.comp measurable_snd))

/-- Doob transition kernel, obtained by weighting the killed kernel. -/
def kernel : Kernel M M := K.withDensity d.density

theorem kernel_apply (x : M) (A : Set M) :
    d.kernel x A = d.rate⁻¹ * (d.weight x)⁻¹ * ∫⁻ y in A, d.weight y ∂K x := by
  rw [kernel, Kernel.withDensity_apply' _ d.measurable_density]
  exact lintegral_const_mul _ d.measurable_weight

/-- The right eigenfunction relation normalizes the transformed kernel. -/
instance isMarkovKernel : IsMarkovKernel d.kernel := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [d.kernel_apply x univ, Measure.restrict_univ, d.right_eigen x]
  calc
    d.rate⁻¹ * (d.weight x)⁻¹ * (d.rate * d.weight x) =
        (d.rate⁻¹ * d.rate) * ((d.weight x)⁻¹ * d.weight x) := by ac_rfl
    _ = 1 := by rw [ENNReal.inv_mul_cancel d.rate_ne_zero d.rate_ne_top,
      ENNReal.inv_mul_cancel (d.weight_ne_zero x) (d.weight_ne_top x), one_mul]

/-- Integration against one transformed step is conjugation by the positive
eigenfunction. -/
theorem lintegral_kernel (x : M) (g : M → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂d.kernel x) =
      d.rate⁻¹ * (d.weight x)⁻¹ * ∫⁻ y, d.weight y * g y ∂K x := by
  rw [kernel, Kernel.lintegral_withDensity _ d.measurable_density x hg]
  calc
    _ = ∫⁻ y, (d.rate⁻¹ * (d.weight x)⁻¹) * (d.weight y * g y) ∂K x := by
      apply lintegral_congr
      intro y
      simp only [density, mul_assoc]
    _ = _ := lintegral_const_mul _ (d.measurable_weight.mul hg)

/-- The n-step Doob formula for all nonnegative measurable test functions. The powers are
compositions of the respective kernels. -/
theorem lintegral_kernel_pow (n : ℕ) (x : M) (g : M → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂(d.kernel ^ n) x) =
      (d.rate⁻¹) ^ n * (d.weight x)⁻¹ *
        ∫⁻ y, d.weight y * g y ∂(K ^ n) x := by
  induction n generalizing x with
  | zero =>
      simp only [pow_zero]
      simp only [show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply]
      change (∫⁻ y, g y ∂Measure.dirac x) =
        1 * (d.weight x)⁻¹ * ∫⁻ y, d.weight y * g y ∂Measure.dirac x
      have hzero : (∫⁻ y, d.weight y * g y ∂Measure.dirac x) = d.weight x * g x :=
        lintegral_dirac' x (d.measurable_weight.mul hg)
      rw [lintegral_dirac' x hg, hzero, one_mul,
        ENNReal.inv_mul_cancel_left (d.weight_ne_zero x) (d.weight_ne_top x)]
  | succ n ih =>
      have hI : Measurable (fun y => ∫⁻ z, d.weight z * g z ∂(K ^ n) y) :=
        (Measure.measurable_lintegral (d.measurable_weight.mul hg)).comp (K ^ n).measurable
      have hJ : Measurable (fun y => ∫⁻ z, g z ∂(d.kernel ^ n) y) :=
        (Measure.measurable_lintegral hg).comp (d.kernel ^ n).measurable
      have hcomp : (∫⁻ y, d.weight y * g y ∂(K ^ (n + 1)) x) =
          ∫⁻ y, ∫⁻ z, d.weight z * g z ∂(K ^ n) y ∂K x := by
        rw [pow_succ]
        exact Measure.lintegral_bind (K ^ n).aemeasurable
          (d.measurable_weight.mul hg).aemeasurable
      calc
        (∫⁻ y, g y ∂(d.kernel ^ (n + 1)) x) =
            ∫⁻ y, ∫⁻ z, g z ∂(d.kernel ^ n) y ∂d.kernel x := by
          rw [pow_succ]
          exact Measure.lintegral_bind (d.kernel ^ n).aemeasurable hg.aemeasurable
        _ = d.rate⁻¹ * (d.weight x)⁻¹ *
            ∫⁻ y, d.weight y * (∫⁻ z, g z ∂(d.kernel ^ n) y) ∂K x :=
          d.lintegral_kernel x _ hJ
        _ = d.rate⁻¹ * (d.weight x)⁻¹ *
            ((d.rate⁻¹) ^ n * ∫⁻ y, ∫⁻ z, d.weight z * g z ∂(K ^ n) y ∂K x) := by
          congr 1
          calc
            _ = ∫⁻ y, (d.rate⁻¹) ^ n *
                (∫⁻ z, d.weight z * g z ∂(K ^ n) y) ∂K x := by
              apply lintegral_congr
              intro y
              rw [ih y]
              calc
                _ = (d.rate⁻¹) ^ n * (d.weight y * (d.weight y)⁻¹) *
                    (∫⁻ z, d.weight z * g z ∂(K ^ n) y) := by ac_rfl
                _ = _ := by rw [ENNReal.mul_inv_cancel (d.weight_ne_zero y)
                  (d.weight_ne_top y), mul_one]
            _ = _ := lintegral_const_mul _ hI
        _ = (d.rate⁻¹) ^ (n + 1) * (d.weight x)⁻¹ *
            ∫⁻ y, d.weight y * g y ∂(K ^ (n + 1)) x := by
          rw [hcomp, pow_succ]
          ac_rfl

/-- The n-step transition formula on measurable sets. -/
theorem kernel_pow_apply (n : ℕ) (x : M) (A : Set M) (hA : MeasurableSet A) :
    (d.kernel ^ n) x A =
      (d.rate⁻¹) ^ n * (d.weight x)⁻¹ * ∫⁻ y in A, d.weight y ∂(K ^ n) x := by
  have h := d.lintegral_kernel_pow n x (A.indicator (fun _ => 1))
    (measurable_const.indicator hA)
  have heq : (fun y => d.weight y * A.indicator (fun _ => 1) y) = A.indicator d.weight := by
    funext y
    by_cases hy : y ∈ A <;> simp [hy]
  simpa only [heq, lintegral_indicator hA, lintegral_const, one_mul,
    Measure.restrict_apply_univ] using h

/-- A left eigenmeasure becomes invariant after weighting by the right
eigenfunction. Invariance is derived from the eigenmeasure equation. -/
theorem invariant_withDensity (μ : Measure M)
    (hleft : K ∘ₘ μ = d.rate • μ) :
    d.kernel ∘ₘ μ.withDensity d.weight = μ.withDensity d.weight := by
  ext A hA
  have hI : Measurable (fun x => ∫⁻ y in A, d.weight y ∂K x) := by
    simp only [← lintegral_indicator hA]
    exact (Measure.measurable_lintegral (d.measurable_weight.indicator hA)).comp K.measurable
  have hcomp : (∫⁻ x, ∫⁻ y in A, d.weight y ∂K x ∂μ) =
      d.rate * ∫⁻ y in A, d.weight y ∂μ := by
    rw [← lintegral_indicator hA]
    simp only [← lintegral_indicator hA]
    rw [← Measure.lintegral_bind K.aemeasurable
      (d.measurable_weight.indicator hA).aemeasurable]
    change (∫⁻ y, A.indicator d.weight y ∂(K ∘ₘ μ)) = _
    rw [hleft, lintegral_smul_measure, smul_eq_mul]
  rw [Measure.bind_apply hA d.kernel.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul μ d.measurable_weight (d.kernel.measurable_coe hA),
    withDensity_apply _ hA]
  calc
    _ = ∫⁻ x, d.rate⁻¹ * (∫⁻ y in A, d.weight y ∂K x) ∂μ := by
      apply lintegral_congr
      intro x
      simp only [Pi.mul_apply, d.kernel_apply]
      calc
        _ = d.rate⁻¹ * (d.weight x * (d.weight x)⁻¹) *
            (∫⁻ y in A, d.weight y ∂K x) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel (d.weight_ne_zero x)
          (d.weight_ne_top x), mul_one]
    _ = d.rate⁻¹ * (d.rate * ∫⁻ y in A, d.weight y ∂μ) := by
      rw [lintegral_const_mul _ hI, hcomp]
    _ = _ := ENNReal.inv_mul_cancel_left d.rate_ne_zero d.rate_ne_top

omit [IsSFiniteKernel K] in
/-- The normalization `μ(η)=1` makes the invariant weighted measure a probability measure. -/
theorem isProbabilityMeasure_withDensity (μ : Measure M)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) : IsProbabilityMeasure (μ.withDensity d.weight) := by
  constructor
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hnorm

end PositiveEigenData

/-- Spectral data before removing the zero set of the eigenfunction. -/
structure EigenData (K : Kernel M M) where
  rate : ℝ≥0∞
  rate_ne_zero : rate ≠ 0
  rate_ne_top : rate ≠ ∞
  weight : M → ℝ≥0∞
  measurable_weight : Measurable weight
  weight_ne_top : ∀ x, weight x ≠ ∞
  right_eigen : ∀ x, ∫⁻ y, weight y ∂K x = rate * weight x

namespace EigenData

variable {K : Kernel M M} (d : EigenData K)

/-- The positive-eigenfunction region, equal to `{x | 0 < η x}`. -/
def liveSet : Set M := {x | d.weight x ≠ 0}

theorem liveSet_eq_positive : d.liveSet = {x | 0 < d.weight x} := by
  ext x
  exact pos_iff_ne_zero.symm

/-- The state space of the Doob-transformed chain. -/
abbrev State := {x : M // x ∈ d.liveSet}

theorem measurableSet_liveSet : MeasurableSet d.liveSet :=
  (d.measurable_weight (measurableSet_singleton 0)).compl

theorem live_embedding : MeasurableEmbedding (Subtype.val : d.State → M) :=
  MeasurableEmbedding.subtype_coe d.measurableSet_liveSet

/-- Original transitions restricted in source and target to the positive
region. The restriction can still lose mass. -/
def liveKernel : Kernel d.State d.State :=
  (K.comap Subtype.val measurable_subtype_coe).comapRight d.live_embedding

instance liveKernel_isSFinite [IsSFiniteKernel K] : IsSFiniteKernel d.liveKernel := by
  unfold liveKernel
  infer_instance

theorem liveKernel_apply (x : d.State) (A : Set d.State) (hA : MeasurableSet A) :
    d.liveKernel x A = K x.val (Subtype.val '' A) := by
  rw [liveKernel, Kernel.comapRight_apply' _ _ _ hA]
  rfl

/-- The eigenfunction vanishes identically outside the live region, and its
eigenrelation forces all transitions from there to have zero live-state mass. -/
theorem no_return_from_zero {x : M} (hx : x ∉ d.liveSet) : K x d.liveSet = 0 := by
  have hzero : d.weight x = 0 := not_not.mp hx
  have hint : ∫⁻ y, d.weight y ∂K x = 0 := by rw [d.right_eigen x, hzero, mul_zero]
  have hae := (lintegral_eq_zero_iff d.measurable_weight).1 hint
  exact ae_iff.mp hae

/-- The right eigenfunction equation remains valid after restriction to its
positive region. -/
theorem right_eigen_live (x : d.State) :
    (∫⁻ y : d.State, d.weight y.val ∂d.liveKernel x) = d.rate * d.weight x.val := by
  change (∫⁻ y : d.State, d.weight y.val ∂(K x.val).comap Subtype.val) = _
  rw [lintegral_subtype_comap d.measurableSet_liveSet]
  rw [setLIntegral_eq_of_support_subset (show Function.support d.weight ⊆ d.liveSet from
    fun _ h => h)]
  exact d.right_eigen x.val

/-- Restricting to the live region commutes with the transition of any initial measure. -/
theorem live_comap_comp (μ : Measure M) :
    (K ∘ₘ μ).comap (Subtype.val : d.State → M) =
      d.liveKernel ∘ₘ μ.comap (Subtype.val : d.State → M) := by
  ext A hA
  have himage : MeasurableSet ((Subtype.val : d.State → M) '' A) :=
    d.live_embedding.measurableSet_image' hA
  rw [d.live_embedding.comap_apply, Measure.bind_apply himage K.aemeasurable,
    Measure.bind_apply hA d.liveKernel.aemeasurable]
  simp_rw [d.liveKernel_apply _ A hA]
  rw [lintegral_subtype_comap d.measurableSet_liveSet
    (fun x : M => K x (Subtype.val '' A))]
  symm
  apply setLIntegral_eq_of_support_subset
  intro x hx
  by_contra hnot
  exact hx (measure_mono_null (Subtype.coe_image_subset d.liveSet A)
    (d.no_return_from_zero hnot))

/-- Powers of the restricted kernel are the restrictions of the original
powers; excursions to the zero set cannot contribute to a return. -/
theorem liveKernel_pow (n : ℕ) (x : d.State) :
    (d.liveKernel ^ n) x = ((K ^ n) x.val).comap (Subtype.val : d.State → M) := by
  induction n with
  | zero =>
      simp only [pow_zero, show (1 : Kernel d.State d.State) = Kernel.id from rfl,
        show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply]
      rw [← Measure.map_dirac' measurable_subtype_coe]
      exact (d.live_embedding.comap_map _).symm
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change d.liveKernel ∘ₘ ((d.liveKernel ^ n) x) =
        (K ∘ₘ ((K ^ n) x.val)).comap Subtype.val
      rw [ih, d.live_comap_comp]

/-- The positive-eigenfunction data are derived on the live subtype. -/
def positiveData : PositiveEigenData d.liveKernel where
  rate := d.rate
  rate_ne_zero := d.rate_ne_zero
  rate_ne_top := d.rate_ne_top
  weight x := d.weight x.val
  measurable_weight := d.measurable_weight.comp measurable_subtype_coe
  weight_ne_zero x := x.property
  weight_ne_top x := d.weight_ne_top x.val
  right_eigen := d.right_eigen_live

variable [IsSFiniteKernel K]

/-- The Doob kernel on `{η>0}`. -/
def kernel : Kernel d.State d.State := d.positiveData.kernel

instance isMarkovKernel : IsMarkovKernel d.kernel :=
  d.positiveData.isMarkovKernel

/-- The full n-step formula with the original killed-kernel powers. -/
theorem kernel_pow_apply (n : ℕ) (x : d.State) (A : Set d.State)
    (hA : MeasurableSet A) :
    (d.kernel ^ n) x A = (d.rate⁻¹) ^ n * (d.weight x.val)⁻¹ *
      ∫⁻ y in (Subtype.val '' A), d.weight y ∂(K ^ n) x.val := by
  change (d.positiveData.kernel ^ n) x A = _
  rw [d.positiveData.kernel_pow_apply n x A hA]
  change (d.rate⁻¹) ^ n * (d.weight x.val)⁻¹ *
      (∫⁻ y in A, d.weight y.val ∂(d.liveKernel ^ n) x) = _
  rw [d.liveKernel_pow n x,
    setLIntegral_subtype d.measurableSet_liveSet A d.weight]

/-- In particular the one-step formula is `Q(x,dy)=η(y)/(λ η(x)) K(x,dy)`
on the positive region. -/
theorem kernel_apply (x : d.State) (A : Set d.State) (hA : MeasurableSet A) :
    d.kernel x A = d.rate⁻¹ * (d.weight x.val)⁻¹ *
      ∫⁻ y in (Subtype.val '' A), d.weight y ∂K x.val := by
  simpa using d.kernel_pow_apply 1 x A hA

omit [IsSFiniteKernel K] in
/-- Restricting the weighted measure to the positive region commutes with
weighting the restricted reference measure. -/
theorem weightedMeasure_comap (μ : Measure M) :
    (μ.withDensity d.weight).comap (Subtype.val : d.State → M) =
      (μ.comap (Subtype.val : d.State → M)).withDensity (fun x => d.weight x.val) := by
  ext A hA
  rw [d.live_embedding.comap_apply,
    withDensity_apply _ (d.live_embedding.measurableSet_image' hA), withDensity_apply _ hA]
  exact (setLIntegral_subtype d.measurableSet_liveSet A d.weight).symm

/-- A left eigenmeasure of the original killed kernel yields the invariant measure `η μ`, restricted
to the live-state space. -/
theorem invariant_weightedMeasure (μ : Measure M)
    (hleft : K ∘ₘ μ = d.rate • μ) :
    d.kernel ∘ₘ (μ.withDensity d.weight).comap (Subtype.val : d.State → M) =
      (μ.withDensity d.weight).comap (Subtype.val : d.State → M) := by
  rw [d.weightedMeasure_comap]
  apply d.positiveData.invariant_withDensity
  rw [← d.live_comap_comp, hleft, Measure.comap_smul]
  rfl

omit [IsSFiniteKernel K] in
/-- The invariant measure on the live subtype is a probability measure under the normalization
`μ(η)=1`, even if the eigenfunction vanishes elsewhere. -/
theorem isProbabilityMeasure_weightedMeasure (μ : Measure M)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    IsProbabilityMeasure ((μ.withDensity d.weight).comap (Subtype.val : d.State → M)) := by
  rw [d.weightedMeasure_comap]
  apply d.positiveData.isProbabilityMeasure_withDensity
  change (∫⁻ x : d.State, d.weight x.val ∂μ.comap Subtype.val) = 1
  rw [lintegral_subtype_comap d.measurableSet_liveSet,
    setLIntegral_eq_of_support_subset (show Function.support d.weight ⊆ d.liveSet from
      fun _ h => h)]
  exact hnorm

end EigenData

end

end DoobTransform

end ConditionedStableLaws
