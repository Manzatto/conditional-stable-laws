import ConditionedStableLaws.ClusterMixing
import ConditionedStableLaws.SpectralSurvival

/-!
# Stationary Doob cluster laws

The initial law is the weighted measure `η μ` on the live subtype. Trajectory laws are constructed
by Ionescu--Tulcea. The identities below connect their multitime observations to the original
killed-kernel words.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

namespace ConditionedStableLaws.StationaryClusters
open QProcessLimit PathMixing
variable {M : Type*} [MeasurableSpace M]

/-- The trajectory kernel with a specified starting state. -/
def trajectoryKernel (K : Kernel M M) [IsMarkovKernel K] : Kernel M (ℕ → M) :=
  (Kernel.traj (historyKernel K) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => M)).symm
    (MeasurableEquiv.piUnique _).symm.measurable

/-- The trajectory law with an arbitrary initial distribution. -/
def initialPathMeasure (K : Kernel M M) [IsMarkovKernel K] (ν : Measure M) :
    Measure (ℕ → M) := Kernel.trajMeasure ν (historyKernel K)

theorem initialPathMeasure_eq_comp (K : Kernel M M) [IsMarkovKernel K] (ν : Measure M) :
    initialPathMeasure K ν = trajectoryKernel K ∘ₘ ν := by
  unfold initialPathMeasure Kernel.trajMeasure
  rw [kernel_comp_map_measure _ _ _ (MeasurableEquiv.piUnique _).symm.measurable]
  rfl

theorem trajectoryKernel_apply (K : Kernel M M) [IsMarkovKernel K] (x : M) :
    trajectoryKernel K x = QProcessLimit.pathMeasure K x := by
  change trajectoryKernel K x = initialPathMeasure K (Measure.dirac x)
  rw [initialPathMeasure_eq_comp]
  exact (Measure.dirac_bind (trajectoryKernel K).measurable x).symm

/-- Arbitrary-initial-law Markov product identity. -/
theorem lintegral_initial_pathProduct (K : Kernel M M) [IsMarkovKernel K] (ν : Measure M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2) :
    (∫⁻ ω, pathProduct w ω ∂initialPathMeasure K ν) =
      ∫⁻ x, PathMixing.kernelWord K w (fun _ => 1) x ∂ν := by
  rw [initialPathMeasure_eq_comp,
    Measure.lintegral_bind (trajectoryKernel K).aemeasurable
      (measurable_pathProduct w hw).aemeasurable]
  apply lintegral_congr
  intro x
  rw [trajectoryKernel_apply]
  simpa only [mul_one] using lintegral_pathProduct K x w hw (fun _ => 1) measurable_const

end ConditionedStableLaws.StationaryClusters

namespace ConditionedStableLaws.DoobTransform.EigenData
open PathMixing
variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} [IsSFiniteKernel K]
  (d : DoobTransform.EigenData K)

omit [IsSFiniteKernel K] in
/-- The eigenrelation iterates through kernel powers. -/
theorem right_eigen_power (n : ℕ) (x : M) :
    (∫⁻ y, d.weight y ∂(K ^ n) x) = d.rate ^ n * d.weight x := by
  induction n generalizing x with
  | zero =>
      simp only [pow_zero, show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply,
        lintegral_dirac' _ d.measurable_weight, one_mul]
  | succ n ih =>
      rw [pow_succ]
      change (∫⁻ y, d.weight y ∂((K ^ n) ∘ₖ K) x) = _
      rw [Kernel.lintegral_comp _ _ _ d.measurable_weight]
      simp_rw [ih]
      rw [lintegral_const_mul _ d.measurable_weight, d.right_eigen, pow_succ]
      ac_rfl

omit [IsSFiniteKernel K] in
/-- If η vanishes initially, every nonnegative observation word ending in η
vanishes too. This proves the zero-region cancellation needed for mixtures. -/
theorem kernelWord_zero_of_weight_zero (w : List (ℕ × (M → ℝ≥0∞)))
    (x : M) (hx : d.weight x = 0) : PathMixing.kernelWord K w d.weight x = 0 := by
  induction w generalizing x with
  | nil => exact hx
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      have hzero : ∫⁻ y, d.weight y ∂(K ^ n) x = 0 := by
        rw [d.right_eigen_power, hx, mul_zero]
      have hae := (lintegral_eq_zero_iff d.measurable_weight).mp hzero
      change (∫⁻ y, f y * PathMixing.kernelWord K w d.weight y ∂(K ^ n) x) = 0
      calc
        _ = ∫⁻ _ : M, 0 ∂(K ^ n) x := by
          apply lintegral_congr_ae
          filter_upwards [hae] with y hy
          rw [ih y hy, mul_zero]
        _ = 0 := by simp

/-- The ambient n-step Doob formula, including removal of the zero region. -/
theorem lintegral_power_ambient (n : ℕ) (x : d.State) (g : M → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ y : d.State, g y.val ∂(d.kernel ^ n) x) =
      (d.rate⁻¹) ^ n * (d.weight x.val)⁻¹ *
        ∫⁻ y, d.weight y * g y ∂(K ^ n) x.val := by
  change (∫⁻ y : d.State, g y.val ∂(d.positiveData.kernel ^ n) x) = _
  rw [d.positiveData.lintegral_kernel_pow n x (fun y : d.State => g y.val) (hg.comp measurable_subtype_coe)]
  change (d.rate⁻¹) ^ n * (d.weight x.val)⁻¹ *
    (∫⁻ y : d.State, d.weight y.val * g y.val ∂(d.liveKernel ^ n) x) = _
  congr 1
  rw [d.liveKernel_pow,
    lintegral_subtype_comap d.measurableSet_liveSet (fun y => d.weight y * g y)]
  apply setLIntegral_eq_of_support_subset
  intro y hy
  exact fun hz => hy (by simp [hz])

/-- Pull an observation list back to the live subtype. -/
def liveObservations (w : List (ℕ × (M → ℝ≥0∞))) :
    List (ℕ × (d.State → ℝ≥0∞)) := w.map (fun p => (p.1, fun y => p.2 y.val))

omit [IsSFiniteKernel K] in
theorem measurable_liveObservations (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, Measurable p.2) :
    ∀ p ∈ d.liveObservations w, Measurable p.2 := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact (hw q hq).comp measurable_subtype_coe

/-- Exact Doob conjugacy for arbitrary finite observation blocks. -/
theorem kernelWord_doob (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, Measurable p.2) (x : d.State) :
    PathMixing.kernelWord d.kernel (d.liveObservations w) (fun _ => 1) x =
      (d.rate⁻¹) ^ totalTime w * (d.weight x.val)⁻¹ *
        PathMixing.kernelWord K w d.weight x.val := by
  induction w generalizing x with
  | nil =>
      change 1 = (d.rate⁻¹) ^ 0 * (d.weight x.val)⁻¹ * d.weight x.val
      rw [pow_zero, one_mul, ENNReal.inv_mul_cancel x.property (d.weight_ne_top _)]
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      have hf : Measurable f := hw (n, f) (by simp)
      have hwm : ∀ p ∈ w, Measurable p.2 := fun p hp => hw p (by simp [hp])
      let G : M → ℝ≥0∞ := fun y =>
        f y * ((d.rate⁻¹) ^ totalTime w * (d.weight y)⁻¹ *
          PathMixing.kernelWord K w d.weight y)
      have hG : Measurable G := hf.mul
        ((measurable_const.mul d.measurable_weight.inv).mul
          (measurable_kernelWord K w hwm d.weight d.measurable_weight))
      have hc (y : M) : d.weight y * ((d.weight y)⁻¹ *
          PathMixing.kernelWord K w d.weight y) = PathMixing.kernelWord K w d.weight y := by
        apply ENNReal.mul_inv_cancel_left'
        · exact d.kernelWord_zero_of_weight_zero w y
        · intro ht
          exact False.elim (d.weight_ne_top y ht)
      change (∫⁻ y, f y.val *
        PathMixing.kernelWord d.kernel (d.liveObservations w) (fun _ => 1) y
        ∂(d.kernel ^ n) x) = _
      calc
        _ = ∫⁻ y : d.State, G y.val ∂(d.kernel ^ n) x := by
          apply lintegral_congr
          intro y
          rw [ih hwm y]
        _ = (d.rate⁻¹) ^ n * (d.weight x.val)⁻¹ *
            ∫⁻ y, d.weight y * G y ∂(K ^ n) x.val := d.lintegral_power_ambient n x G hG
        _ = (d.rate⁻¹) ^ n * (d.weight x.val)⁻¹ *
            ((d.rate⁻¹) ^ totalTime w *
              ∫⁻ y, f y * PathMixing.kernelWord K w d.weight y ∂(K ^ n) x.val) := by
          congr 1
          calc
            _ = ∫⁻ y, (d.rate⁻¹) ^ totalTime w *
                (f y * PathMixing.kernelWord K w d.weight y) ∂(K ^ n) x.val := by
              apply lintegral_congr
              intro y
              dsimp [G]
              calc
                _ = (d.rate⁻¹) ^ totalTime w * (f y *
                    (d.weight y * ((d.weight y)⁻¹ * PathMixing.kernelWord K w d.weight y))) := by
                  ac_rfl
                _ = _ := by rw [hc]
            _ = _ := lintegral_const_mul _
              (hf.mul (measurable_kernelWord K w hwm d.weight d.measurable_weight))
        _ = _ := by
          simp only [totalTime, List.map_cons, List.sum_cons, pow_add, PathMixing.kernelWord]
          ac_rfl

/-- The stationary initial law, as a measure on the live subtype. -/
def weightedInitial (μ : Measure M) : Measure d.State :=
  (μ.withDensity d.weight).comap Subtype.val

/-- Its Ionescu–Tulcea trajectory law. Invariance follows from the left eigenmeasure relation. -/
def stationaryPathMeasure (μ : Measure M) : Measure (ℕ → d.State) :=
  StationaryClusters.initialPathMeasure d.kernel (d.weightedInitial μ)

/-- The cancellation against the initial law η μ gives the cluster probability as the original
normalized killed-kernel word integrated against μ. No positive lower bound on η is needed, and η
may vanish. -/
theorem lintegral_stationary_pathProduct (μ : Measure M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2) :
    (∫⁻ ω, pathProduct (d.liveObservations w) ω ∂d.stationaryPathMeasure μ) =
      (d.rate⁻¹) ^ totalTime w * ∫⁻ x, PathMixing.kernelWord K w d.weight x ∂μ := by
  rw [stationaryPathMeasure, StationaryClusters.lintegral_initial_pathProduct _ _ _
    (d.measurable_liveObservations w hw)]
  simp_rw [d.kernelWord_doob w hw]
  rw [weightedInitial, d.weightedMeasure_comap]
  have hF : Measurable (fun x : d.State => (d.rate⁻¹) ^ totalTime w *
      (d.weight x.val)⁻¹ * PathMixing.kernelWord K w d.weight x.val) :=
    (measurable_const.mul (d.measurable_weight.comp measurable_subtype_coe).inv).mul
      ((measurable_kernelWord K w hw d.weight d.measurable_weight).comp measurable_subtype_coe)
  have hweight : Measurable (fun x : d.State => d.weight x.val) :=
    d.measurable_weight.comp measurable_subtype_coe
  rw [lintegral_withDensity_eq_lintegral_mul _ hweight hF]
  have he : (fun x : d.State => d.weight x.val *
      ((d.rate⁻¹) ^ totalTime w * (d.weight x.val)⁻¹ *
        PathMixing.kernelWord K w d.weight x.val)) =
      (fun x : d.State => (d.rate⁻¹) ^ totalTime w *
        PathMixing.kernelWord K w d.weight x.val) := by
    funext x
    calc
      _ = (d.rate⁻¹) ^ totalTime w * ((d.weight x.val * (d.weight x.val)⁻¹) *
          PathMixing.kernelWord K w d.weight x.val) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel x.property (d.weight_ne_top _), one_mul]
  change (∫⁻ x : d.State, d.weight x.val * _ ∂μ.comap Subtype.val) = _
  have hi : Measurable (fun x : d.State => PathMixing.kernelWord K w d.weight x.val) :=
    (measurable_kernelWord K w hw d.weight d.measurable_weight).comp measurable_subtype_coe
  rw [he, lintegral_const_mul _ hi,
    lintegral_subtype_comap d.measurableSet_liveSet (PathMixing.kernelWord K w d.weight)]
  congr 1
  apply setLIntegral_eq_of_support_subset
  intro x hx
  exact fun hz => hx (d.kernelWord_zero_of_weight_zero w x hz)

end ConditionedStableLaws.DoobTransform.EigenData

namespace ConditionedStableLaws.StationaryClusters
open PathMixing StandingHypothesis
variable {M : Type*} [MeasurableSpace M]

theorem kernelWord_const_mul (K : Kernel M M) (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, Measurable p.2) (a : ℝ≥0∞) (g : M → ℝ≥0∞) (hg : Measurable g) (x : M) :
    PathMixing.kernelWord K w (fun y => a * g y) x = a * PathMixing.kernelWord K w g x := by
  induction w generalizing x with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      have hwm : ∀ p ∈ w, Measurable p.2 := fun p hp => hw p (by simp [hp])
      change (∫⁻ y, f y * PathMixing.kernelWord K w (fun z => a * g z) y ∂(K ^ n) x) = _
      simp_rw [ih hwm]
      calc
        _ = ∫⁻ y, a * (f y * PathMixing.kernelWord K w g y) ∂(K ^ n) x := by
          apply lintegral_congr
          intro y
          ac_rfl
        _ = _ := lintegral_const_mul _ ((hw (n, f) (by simp)).mul
          (measurable_kernelWord K w hwm g hg))

theorem realKernelWord_const_mul (K : KilledKernel M) (w : List (ℕ × (M → ℝ≥0∞)))
    (a : ℝ) (g : M → ℝ) (x : M) :
    realKernelWord K w (fun y => a * g y) x = a * realKernelWord K w g x := by
  induction w generalizing x with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      simp only [realKernelWord, ih]
      have he : (fun y => (f y).toReal * (a * realKernelWord K w g y)) =
          (fun y => a * ((f y).toReal * realKernelWord K w g y)) := by
        funext y
        ring
      rw [he, StandingHypothesis.kernelIterate_const_mul]

/-- Real conversion for any bounded nonnegative terminal function, rather than
only a terminal bounded by one. -/
theorem kernelWord_toReal_bounded (K : KilledKernel M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2)
    (hwb : ∀ p ∈ w, ∀ y, p.2 y ≤ 1)
    (g : M → ℝ≥0∞) (hg : Measurable g) (R : ℝ≥0∞)
    (hR0 : R ≠ 0) (hRt : R ≠ ∞) (hgb : ∀ y, g y ≤ R) (x : M) :
    (PathMixing.kernelWord K.kernel w g x).toReal =
      realKernelWord K w (fun y => (g y).toReal) x := by
  let g' : M → ℝ≥0∞ := fun y => R⁻¹ * g y
  have hg' : Measurable g' := measurable_const.mul hg
  have hgb' : ∀ y, g' y ≤ 1 := by
    intro y
    exact (mul_le_mul' (le_rfl : R⁻¹ ≤ R⁻¹) (hgb y)).trans_eq (ENNReal.inv_mul_cancel hR0 hRt)
  have he : g = fun y => R * g' y := by
    funext y
    exact (ENNReal.mul_inv_cancel_left hR0 hRt).symm
  conv_lhs => rw [he, kernelWord_const_mul K.kernel w hw R g' hg' x]
  rw [ENNReal.toReal_mul, PathMixing.kernelWord_toReal K w hw hwb g' hg' hgb']
  have hre : (fun y => (g y).toReal) = fun y => R.toReal * (g' y).toReal := by
    funext y
    rw [he, ENNReal.toReal_mul]
  rw [hre, realKernelWord_const_mul]

/-- Uniform finiteness of every such word, needed for the Bochner conversion. -/
theorem kernelWord_le_terminal_bound (K : KilledKernel M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2)
    (hwb : ∀ p ∈ w, ∀ y, p.2 y ≤ 1)
    (g : M → ℝ≥0∞) (hg : Measurable g) (R : ℝ≥0∞)
    (hR0 : R ≠ 0) (hRt : R ≠ ∞) (hgb : ∀ y, g y ≤ R) (x : M) :
    PathMixing.kernelWord K.kernel w g x ≤ R := by
  let g' : M → ℝ≥0∞ := fun y => R⁻¹ * g y
  have hg' : Measurable g' := measurable_const.mul hg
  have hgb' : ∀ y, g' y ≤ 1 := fun y =>
    (mul_le_mul' (le_rfl : R⁻¹ ≤ R⁻¹) (hgb y)).trans_eq (ENNReal.inv_mul_cancel hR0 hRt)
  have he : g = fun y => R * g' y := by
    funext y
    exact (ENNReal.mul_inv_cancel_left hR0 hRt).symm
  rw [he, kernelWord_const_mul K.kernel w hw R g' hg' x]
  simpa only [mul_one] using mul_le_mul' (le_rfl : R ≤ R)
    (PathMixing.kernelWord_le_one K w hwb g' hgb' x)

end ConditionedStableLaws.StationaryClusters

namespace ConditionedStableLaws.DoobTransform.EigenData
open PathMixing StationaryClusters StandingHypothesis
variable {M : Type*} [MeasurableSpace M] {K : KilledKernel M}
  (d : DoobTransform.EigenData K.kernel)

theorem weightedInitial_invariant (μ : Measure M)
    (hleft : K.kernel ∘ₘ μ = d.rate • μ) :
    d.kernel ∘ₘ d.weightedInitial μ = d.weightedInitial μ := d.invariant_weightedMeasure μ hleft

theorem stationaryPathMeasure_probability (μ : Measure M)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) : IsProbabilityMeasure (d.stationaryPathMeasure μ) := by
  have : IsProbabilityMeasure (d.weightedInitial μ) := d.isProbabilityMeasure_weightedMeasure μ hnorm
  unfold stationaryPathMeasure initialPathMeasure
  infer_instance

/-- Real-valued stationary cluster expectation, with boundedness used only
for the required ENNReal-to-Bochner conversions. -/
theorem integral_stationary_pathProduct (μ : Measure M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2)
    (hwb : ∀ p ∈ w, ∀ y, p.2 y ≤ 1) (R : ℝ≥0∞)
    (hR0 : R ≠ 0) (hRt : R ≠ ∞) (hweight : ∀ y, d.weight y ≤ R) :
    (∫ ω, (pathProduct (d.liveObservations w) ω).toReal ∂d.stationaryPathMeasure μ) =
      (d.rate.toReal⁻¹) ^ totalTime w *
        ∫ x, realKernelWord K w (fun y => (d.weight y).toReal) x ∂μ := by
  have hlive : ∀ p ∈ d.liveObservations w, ∀ y, p.2 y ≤ 1 := by
    intro p hp y
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact hwb q hq y.val
  rw [integral_toReal (measurable_pathProduct _
    (d.measurable_liveObservations w hw)).aemeasurable
    (Filter.Eventually.of_forall (fun ω => (pathProduct_le_one _ hlive ω).trans_lt ENNReal.one_lt_top)),
    d.lintegral_stationary_pathProduct μ w hw, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_inv]
  congr 1
  rw [← integral_toReal (measurable_kernelWord K.kernel w hw d.weight d.measurable_weight).aemeasurable
    (Filter.Eventually.of_forall (fun x =>
      (kernelWord_le_terminal_bound K w hw hwb d.weight d.measurable_weight R hR0 hRt hweight x).trans_lt
        (lt_top_iff_ne_top.mpr hRt)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    kernelWord_toReal_bounded K w hw hwb d.weight d.measurable_weight R hR0 hRt hweight x)

end ConditionedStableLaws.DoobTransform.EigenData

namespace ConditionedStableLaws.StandingHypothesis
open PathMixing StationaryClusters ConditionalMixing ClusterMixing
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- The eigenfunction is bounded everywhere, by smoothing its L∞ representative. No positive lower
bound on η is required. -/
theorem HypothesisH.weight_bounded (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (η : Lp ℝ ∞ ρ)
    (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal) :
    ∃ R : ℝ≥0∞, R ≠ 0 ∧ R ≠ ∞ ∧ ∀ y, d.weight y ≤ R := by
  let F := h.smoothedOperator (d.rate.toReal)⁻¹ η
  refine ⟨ENNReal.ofReal (‖F‖ + 1), ?_, ENNReal.ofReal_ne_top, ?_⟩
  · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · intro y
    rw [← ENNReal.ofReal_toReal (d.weight_ne_top y)]
    apply ENNReal.ofReal_le_ofReal
    rw [← h.smoothed_eigenvector d η hη y]
    exact (le_abs_self (F y)).trans
      ((BoundedContinuousFunction.norm_coe_le_norm F y).trans (by linarith))

/-- The original normalized operator word, evaluated by the eigenmeasure, is exactly the expectation
of the corresponding observations under the weighted Doob trajectory law. -/
theorem HypothesisH.stationary_product_eq_operatorWord (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (μ : Measure M) (hμρ : μ ≪ ρ)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (η : Lp ℝ ∞ ρ) (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfm : ∀ p ∈ w, Measurable (f p.2)) (hfb : ∀ p ∈ w, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2) :
    (∫ ω, (pathProduct (d.liveObservations (w.map (fun p => (p.1, f p.2)))) ω).toReal
      ∂d.stationaryPathMeasure μ) =
      mean (operatorWord (fun n => ((d.rate.toReal)⁻¹ • h.transitionOperator) ^ n)
        (multiplicationObservations ρ w) η) := by
  obtain ⟨R, hR0, hRt, hR⟩ := h.weight_bounded d η hη
  let v := w.map (fun p => (p.1, f p.2))
  have hvm : ∀ p ∈ v, Measurable p.2 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact hfm q hq
  have hvb : ∀ p ∈ v, ∀ y, p.2 y ≤ 1 := by
    intro p hp y
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact hfb q hq y
  rw [d.integral_stationary_pathProduct μ v hvm hvb R hR0 hRt hR, hmean]
  have he : realKernelWord K v (fun y => (d.weight y).toReal) =ᵐ[ρ]
      StandingHypothesis.kernelWord 1 K w η :=
    (h.realKernelWord_ae w f hrep _).trans (h.kernelWord_congr_ae 1 w hη.symm)
  rw [integral_congr_ae (hμρ.ae_eq he), ← integral_const_mul]
  apply integral_congr_ae
  apply hμρ.ae_eq
  refine Filter.EventuallyEq.trans ?_ (h.operatorWord_ae (d.rate.toReal)⁻¹ w η).symm
  apply Filter.Eventually.of_forall
  intro y
  rw [StandingHypothesis.kernelWord_normalization]
  have ht : totalTime v = (w.map Prod.fst).sum := by
    simp [v, totalTime, List.map_map, Function.comp_def]
  rw [ht]

/-- For a nonempty cluster the first observation is at time zero, so its operator word is the block
operator. -/
theorem HypothesisH.stationary_cluster_eq_block (h : HypothesisH ρ K)
    (d : DoobTransform.EigenData K.kernel) (μ : Measure M) (hμρ : μ ≪ ρ)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (η : Lp ℝ ∞ ρ) (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal)
    (b : Block (Lp ℝ ∞ ρ)) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfm : ∀ p ∈ (0, b.first) :: b.internal, Measurable (f p.2))
    (hfb : ∀ p ∈ (0, b.first) :: b.internal, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ (0, b.first) :: b.internal, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2) :
    (∫ ω, (pathProduct (d.liveObservations
        (((0, b.first) :: b.internal).map (fun p => (p.1, f p.2)))) ω).toReal
      ∂d.stationaryPathMeasure μ) =
      mean (blockOperator ((d.rate.toReal)⁻¹ • h.transitionOperator) (lpMultiplication ρ) b η) := by
  rw [h.stationary_product_eq_operatorWord d μ hμρ mean hmean η hη
    ((0, b.first) :: b.internal) f hfm hfb hrep]
  simp only [multiplicationObservations, List.map_cons, operatorWord, pow_zero,
    one_mul, blockOperator]

end ConditionedStableLaws.StandingHypothesis

namespace ConditionedStableLaws.StationaryClusters
open PathMixing ClusterMixing
variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} [IsSFiniteKernel K]

/-- The stationary Doob expectation of a cluster, based at its first observation time. For indicator
observations this is its joint probability. -/
def clusterExpectation (d : DoobTransform.EigenData K) (μ : Measure M)
    {A : Type*} (b : Block A) (f : A → M → ℝ≥0∞) : ℝ :=
  ∫ ω, (pathProduct (d.liveObservations
    (((0, b.first) :: b.internal).map (fun p => (p.1, f p.2)))) ω).toReal
      ∂d.stationaryPathMeasure μ

/-- A target-membership event at the consecutive-gap observation times. -/
def targetEvent : List (ℕ × Set M) → Set (ℕ → M)
  | [] => univ
  | (n, A) :: w => {ω | ω n ∈ A ∧ (fun k => ω (n + k)) ∈ targetEvent w}

omit [MeasurableSpace M] in
theorem pathProduct_target_indicators (w : List (ℕ × Set M)) (ω : ℕ → M) :
    pathProduct (indicatorObservations w) ω = (targetEvent w).indicator (fun _ => 1) ω := by
  induction w generalizing ω with
  | nil => simp [indicatorObservations, pathProduct, targetEvent]
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      change A.indicator (fun _ => 1) (ω n) *
        pathProduct (indicatorObservations w) (fun k => ω (n + k)) = _
      rw [ih]
      by_cases hA : ω n ∈ A <;> by_cases ht : (fun k => ω (n + k)) ∈ targetEvent w <;>
        simp [targetEvent, hA, ht]

theorem measurableSet_targetEvent (w : List (ℕ × Set M))
    (hw : ∀ p ∈ w, MeasurableSet p.2) : MeasurableSet (targetEvent w) := by
  have he : targetEvent w = pathProduct (indicatorObservations w) ⁻¹' {1} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, pathProduct_target_indicators]
    by_cases hω : ω ∈ targetEvent w <;> simp [hω]
  rw [he]
  exact (measurable_pathProduct _ (measurable_indicatorObservations w hw))
    (measurableSet_singleton 1)

/-- Indicator products equal the probabilities of the simultaneous membership events, for arbitrary
trajectory measures. -/
theorem integral_pathProduct_indicators (ν : Measure (ℕ → M))
    (w : List (ℕ × Set M)) (hw : ∀ p ∈ w, MeasurableSet p.2) :
    (∫ ω, (pathProduct (indicatorObservations w) ω).toReal ∂ν) = ν.real (targetEvent w) := by
  have hb : ∀ p ∈ indicatorObservations w, ∀ y, p.2 y ≤ 1 := by
    intro p hp y
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    by_cases hy : y ∈ q.2 <;> simp [hy]
  rw [integral_toReal (measurable_pathProduct _
    (measurable_indicatorObservations w hw)).aemeasurable
    (Filter.Eventually.of_forall (fun ω => (pathProduct_le_one _ hb ω).trans_lt ENNReal.one_lt_top))]
  simp_rw [pathProduct_target_indicators]
  rw [lintegral_indicator (measurableSet_targetEvent w hw)]
  simp [Measure.real]

end ConditionedStableLaws.StationaryClusters

namespace ConditionedStableLaws.CanonicalChain
open ClusterMixing ConditionalMixing StandingHypothesis PathMixing StationaryClusters
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  (C : CanonicalChain M) {ρ : Measure M}

local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

/-- Separated-cluster mixing with Doob-cluster leading terms. The stationary path law is initialized
by η μ on `{η>0}`; it is invariant and a probability measure by the left eigenmeasure relation and
the normalization. -/
theorem conditioned_cluster_mixing_stationary (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (μ : Measure M) (hμρ : μ ≪ ρ)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (η one : Lp ℝ ∞ ρ) (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal) (x : M)
    (hone : mean one = 1) (hone_rep : one =ᵐ[ρ] fun _ => (1 : ℝ))
    (ha : 0 < h.stepEvaluation (d.rate.toReal)⁻¹ x η)
    (w : List (ℕ × Block (Lp ℝ ∞ ρ))) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfm : ∀ p ∈ flatten w, Measurable (f p.2))
    (hfb : ∀ p ∈ flatten w, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ flatten w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2)
    (t m : ℕ) (U A θ : ℝ)
    (hU : 1 ≤ U) (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne mean η‖ ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖((d.rate.toReal)⁻¹ • h.transitionOperator) ^ n‖ ≤ U)
    (hgap : ∀ n, 1 ≤ n →
      ‖((d.rate.toReal)⁻¹ • h.transitionOperator) ^ n - rankOne mean η‖ ≤ A * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t)
    (hsmall : ‖h.stepEvaluation (d.rate.toReal)⁻¹ x‖ * A * θ ^ m * ‖one‖ ≤
      h.stepEvaluation (d.rate.toReal)⁻¹ x η / 2) :
    |(∫ ω, (pathProduct (liftObservations
        ((1, fun _ => 1) :: (flatten w).map (fun p => (p.1, f p.2)))) ω).toReal
      ∂C.conditionedMeasure x (((flatten w).map Prod.fst).sum + t + 1)) -
        (w.map fun p => clusterExpectation d μ p.2 f).prod| ≤
      (2 / h.stepEvaluation (d.rate.toReal)⁻¹ x η) *
        ‖h.stepEvaluation (d.rate.toReal)⁻¹ x‖ * A * ‖one‖ *
        ((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖mean‖ * ‖η‖) ^ w.length) *
        θ ^ m * observationNorms
          (blockObservations ((d.rate.toReal)⁻¹ • h.transitionOperator) (lpMultiplication ρ) w) := by
  have hc : (d.rate.toReal)⁻¹ ≠ 0 := inv_ne_zero
    (ENNReal.toReal_ne_zero.mpr ⟨d.rate_ne_zero, d.rate_ne_top⟩)
  have he : w.map (fun p => clusterExpectation d μ p.2 f) =
      w.map (fun p => mean (blockOperator ((d.rate.toReal)⁻¹ • h.transitionOperator)
        (lpMultiplication ρ) p.2 η)) := by
    apply List.map_congr_left
    intro p hp
    have hdata : ∀ q ∈ (0, p.2.first) :: p.2.internal,
        Measurable (f q.2) ∧ (∀ y, f q.2 y ≤ 1) ∧
        (fun y => (f q.2 y).toReal) =ᵐ[ρ] q.2 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · have hp' := mem_flatten_first w p hp
        exact ⟨hfm (p.1, p.2.first) hp', hfb (p.1, p.2.first) hp', hrep (p.1, p.2.first) hp'⟩
      · have hq' := mem_flatten_internal w p hp q hq
        exact ⟨hfm _ hq', hfb _ hq', hrep _ hq'⟩
    exact h.stationary_cluster_eq_block d μ hμρ mean hmean η hη p.2 f
      (fun q hq => (hdata q hq).1) (fun q hq => (hdata q hq).2.1)
      (fun q hq => (hdata q hq).2.2)
  rw [he]
  exact C.conditioned_cluster_mixing h (d.rate.toReal)⁻¹ hc mean η one x hone hone_rep ha
    w f hfm hfb hrep t m U A θ hU hA hθ0 hθ1 hP hQ hgap htimes ht hsmall

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.StationaryClusters
open PathMixing ClusterMixing
variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} [IsSFiniteKernel K]

/-- The cluster's simultaneous target-membership event for the Doob trajectory on `{η>0}`. -/
def clusterEvent (d : DoobTransform.EigenData K) (b : Block (Set M)) : Set (ℕ → d.State) :=
  targetEvent (((0, b.first) :: b.internal).map
    (fun p => (p.1, (Subtype.val : d.State → M) ⁻¹' p.2)))

/-- For targets, the coefficient in the mixing theorem is a probability of simultaneous membership.
-/
theorem clusterExpectation_indicators (d : DoobTransform.EigenData K) (μ : Measure M)
    (b : Block (Set M)) (hb : ∀ p ∈ (0, b.first) :: b.internal, MeasurableSet p.2) :
    clusterExpectation d μ b (fun A => A.indicator (fun _ => 1)) =
      (d.stationaryPathMeasure μ).real (clusterEvent d b) := by
  let v := ((0, b.first) :: b.internal).map
    (fun p => (p.1, (Subtype.val : d.State → M) ⁻¹' p.2))
  have hv : ∀ p ∈ v, MeasurableSet p.2 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (hb q hq).preimage measurable_subtype_coe
  have he : d.liveObservations
      (((0, b.first) :: b.internal).map (fun p => (p.1, p.2.indicator (fun _ => 1)))) =
      indicatorObservations v := by
    simp only [DoobTransform.EigenData.liveObservations, indicatorObservations, v,
      List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p _hp
    congr 1
  unfold clusterExpectation
  rw [he]
  exact integral_pathProduct_indicators (d.stationaryPathMeasure μ) v hv

end ConditionedStableLaws.StationaryClusters

namespace ConditionedStableLaws.StationaryClusters
open PathMixing ClusterMixing
variable {M : Type*} [MeasurableSpace M]

/-- Products of observations in `[0,1]` have expectations in `[0,1]`. -/
theorem integral_pathProduct_mem_Icc (ν : Measure (ℕ → M)) [IsProbabilityMeasure ν]
    (w : List (ℕ × (M → ℝ≥0∞))) (hb : ∀ p ∈ w, ∀ y, p.2 y ≤ 1) :
    (∫ ω, (pathProduct w ω).toReal ∂ν) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  · have hbound : ∀ᵐ ω ∂ν, ‖(pathProduct w ω).toReal‖ ≤ 1 := by
      apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (ENNReal.toReal_mono ENNReal.one_ne_top (pathProduct_le_one w hb ω)).trans_eq (by simp)
    have hn := norm_integral_le_of_norm_le_const hbound
    have hi : 0 ≤ ∫ ω, (pathProduct w ω).toReal ∂ν :=
      integral_nonneg (fun _ => ENNReal.toReal_nonneg)
    have hr : ν.real univ = 1 := by simp [Measure.real]
    simpa only [hr, mul_one, Real.norm_eq_abs, abs_of_nonneg hi] using hn

theorem clusterExpectation_mem_Icc {K : StandingHypothesis.KilledKernel M}
    (d : DoobTransform.EigenData K.kernel) (μ : Measure M)
    (hnorm : ∫⁻ y, d.weight y ∂μ = 1) {A : Type*} (b : Block A) (f : A → M → ℝ≥0∞)
    (hb : ∀ p ∈ (0, b.first) :: b.internal, ∀ y, f p.2 y ≤ 1) :
    clusterExpectation d μ b f ∈ Icc (0 : ℝ) 1 := by
  have := d.stationaryPathMeasure_probability μ hnorm
  apply integral_pathProduct_mem_Icc
  intro p hp y
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
  exact hb r hr y.val

/-- Finite products of probabilities remain probabilities. -/
theorem prod_mem_Icc (v : List ℝ) (hv : ∀ a ∈ v, a ∈ Icc (0 : ℝ) 1) :
    v.prod ∈ Icc (0 : ℝ) 1 := by
  induction v with
  | nil => simp
  | cons a v ih =>
      have ha := hv a (by simp)
      have ht := ih (fun b hb => hv b (by simp [hb]))
      constructor
      · exact mul_nonneg ha.1 ht.1
      · simpa only [List.prod_cons, mul_one] using
          mul_le_mul ha.2 ht.2 ht.1 zero_le_one

end ConditionedStableLaws.StationaryClusters

namespace ConditionedStableLaws.CanonicalChain
open ClusterMixing ConditionalMixing StandingHypothesis PathMixing StationaryClusters
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  (C : CanonicalChain M) {ρ : Measure M}
local instance : IsSFiniteKernel C.killedTransition :=
  inferInstanceAs (IsSFiniteKernel C.toKilledKernel.kernel)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- A crude probability bound covers the finite small-gap regime. -/
theorem conditioned_cluster_error_le_one (d : DoobTransform.EigenData C.killedTransition)
    (μ : Measure M) (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (x : M) (hx : x ∈ survivingSet C.killedTransition)
    (w : List (ℕ × Block (Lp ℝ ∞ ρ))) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfb : ∀ p ∈ flatten w, ∀ y, f p.2 y ≤ 1) (t : ℕ) :
    |(∫ ω, (pathProduct (liftObservations
        ((1, fun _ => 1) :: (flatten w).map (fun p => (p.1, f p.2)))) ω).toReal
      ∂C.conditionedMeasure x (((flatten w).map Prod.fst).sum + t + 1)) -
        (w.map fun p => clusterExpectation d μ p.2 f).prod| ≤ 1 := by
  have := C.conditionedMeasure_isProbability_of_surviving x hx
    (((flatten w).map Prod.fst).sum + t + 1)
  have hp := integral_pathProduct_mem_Icc
    (C.conditionedMeasure x (((flatten w).map Prod.fst).sum + t + 1))
    (liftObservations ((1, fun _ => 1) :: (flatten w).map (fun p => (p.1, f p.2))))
    (liftObservations_le_one _ (by
      intro p hp y
      rcases List.mem_cons.mp hp with rfl | hp
      · exact le_rfl
      · rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
        exact hfb q hq y))
  have hπ : (w.map fun p => clusterExpectation d μ p.2 f).prod ∈ Icc (0 : ℝ) 1 := by
    apply prod_mem_Icc
    intro a ha
    rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
    apply clusterExpectation_mem_Icc (K := C.toKilledKernel) d μ hnorm
    intro q hq y
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hfb (p.1, p.2.first) (mem_flatten_first w p hp) y
    · exact hfb q (mem_flatten_internal w p hp q hq) y
  apply abs_le.mpr
  constructor <;> linarith [hp.1, hp.2, hπ.1, hπ.2]

/-- Uniform separated-cluster estimate for every gap size. The large-gap case uses the spectral
expansion; the complementary case uses probability bounds. The constant is uniform in all targets
and all internal cluster gaps. -/
theorem conditioned_cluster_mixing_uniform (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (μ : Measure M) (hμρ : μ ≪ ρ)
    (hnorm : ∫⁻ y, d.weight y ∂μ = 1)
    (mean : Lp ℝ ∞ ρ →L[ℝ] ℝ) (hmean : ∀ v, mean v = ∫ y, v y ∂μ)
    (η one : Lp ℝ ∞ ρ) (hη : η =ᵐ[ρ] fun y => (d.weight y).toReal) (x : M)
    (hx : x ∈ survivingSet C.killedTransition)
    (hone : mean one = 1) (hone_rep : one =ᵐ[ρ] fun _ => (1 : ℝ))
    (ha : 0 < h.stepEvaluation (d.rate.toReal)⁻¹ x η)
    (w : List (ℕ × Block (Lp ℝ ∞ ρ))) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfm : ∀ p ∈ flatten w, Measurable (f p.2))
    (hfb : ∀ p ∈ flatten w, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ flatten w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2)
    (t m : ℕ) (U A θ : ℝ)
    (hU : 1 ≤ U) (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne mean η‖ ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖((d.rate.toReal)⁻¹ • h.transitionOperator) ^ n‖ ≤ U)
    (hgap : ∀ n, 1 ≤ n →
      ‖((d.rate.toReal)⁻¹ • h.transitionOperator) ^ n - rankOne mean η‖ ≤ A * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t) :
    |(∫ ω, (pathProduct (liftObservations
        ((1, fun _ => 1) :: (flatten w).map (fun p => (p.1, f p.2)))) ω).toReal
      ∂C.conditionedMeasure x (((flatten w).map Prod.fst).sum + t + 1)) -
        (w.map fun p => clusterExpectation d μ p.2 f).prod| ≤
      (2 / h.stepEvaluation (d.rate.toReal)⁻¹ x η) *
        ‖h.stepEvaluation (d.rate.toReal)⁻¹ x‖ * A * ‖one‖ *
        ((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖mean‖ * ‖η‖) ^ w.length) *
        θ ^ m * U ^ (w.map fun p => p.2.internal.length).sum := by
  let ev := h.stepEvaluation (d.rate.toReal)⁻¹ x
  have hU0 : 0 ≤ U := le_trans zero_le_one hU
  by_cases hsmall : ‖ev‖ * A * θ ^ m * ‖one‖ ≤ ev η / 2
  · have hb := C.conditioned_cluster_mixing_stationary h d μ hμρ mean hmean η one hη x
      hone hone_rep ha w f hfm hfb hrep t m U A θ
      hU hA hθ0 hθ1 hP hQ hgap htimes ht hsmall
    refine hb.trans ?_
    exact mul_le_mul_of_nonneg_left
      (blockNorms_le_of_representatives _ w f hfb hrep U hU hQ) (by positivity)
  · have hcrude := C.conditioned_cluster_error_le_one d μ hnorm x hx w f hfb t
    refine hcrude.trans ?_
    have hbase : 1 ≤ (2 / ev η) * (‖ev‖ * A * θ ^ m * ‖one‖) := by
      have hae : ev η ≠ 0 := ha.ne'
      have he : (2 / ev η) * (ev η / 2) = 1 := by field_simp [hae]
      rw [← he]
      exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hsmall)) (by positivity)
    have hH : 1 ≤ (w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖mean‖ * ‖η‖) ^ w.length := by
      have hpow : 1 ≤ U ^ (w.length + 1) := one_le_pow₀ hU
      have hlen : 1 ≤ (w.length + 1 : ℝ) := by linarith [Nat.cast_nonneg w.length (α := ℝ)]
      nlinarith [pow_nonneg (mul_nonneg (norm_nonneg mean) (norm_nonneg η)) w.length]
    have hJ : 1 ≤ U ^ (w.map fun p => p.2.internal.length).sum := one_le_pow₀ hU
    have hHJ : 1 ≤
        ((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖mean‖ * ‖η‖) ^ w.length) *
          U ^ (w.map fun p => p.2.internal.length).sum := by nlinarith
    calc
      1 ≤ ((2 / ev η) * (‖ev‖ * A * θ ^ m * ‖one‖)) *
          (((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖mean‖ * ‖η‖) ^ w.length) *
            U ^ (w.map fun p => p.2.internal.length).sum) := by nlinarith
      _ = _ := by dsimp [ev]; ring

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.StationaryClusters
open PathMixing
variable {M : Type*}

/-- The unit observation at the smoothing step contributes exactly one on a live trajectory, so the
shifted first gap can be restored to the original first observation time. -/
theorem pathProduct_remove_initial_smoothing (n : ℕ) (hn : 1 ≤ n)
    (f : M → ℝ≥0∞) (w : List (ℕ × (M → ℝ≥0∞))) (ω : ℕ → Option M)
    (hlive : ω 1 ≠ none) :
    pathProduct (liftObservations ((1, fun _ => 1) :: (n - 1, f) :: w)) ω =
      pathProduct (liftObservations ((n, f) :: w)) ω := by
  have htime : 1 + (n - 1) = n := by omega
  cases he : ω 1 with
  | none => exact False.elim (hlive he)
  | some y =>
      simp only [liftObservations, List.map_cons, pathProduct, he, liveExtension, one_mul,
        ← Nat.add_assoc, htime]

/-- The one-step shift only changes the geometric constant. -/
theorem geometric_shift (a θ : ℝ) (hθ : θ ≠ 0) (q : ℕ) (hq : 1 ≤ q) :
    a * θ ^ (q - 1) = (a / θ) * θ ^ q := by
  conv_rhs => rw [← Nat.sub_add_cancel hq, pow_add, pow_one]
  field_simp

end ConditionedStableLaws.StationaryClusters

namespace ConditionedStableLaws.CanonicalChain
open PathMixing StationaryClusters
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Exact removal of the initial smoothing convention under the survival-conditioned law. The
horizon equality includes the restored first gap. -/
theorem integral_remove_initial_smoothing (x : M) (n : ℕ) (hn : 1 ≤ n)
    (f : M → ℝ≥0∞) (w : List (ℕ × (M → ℝ≥0∞))) (t : ℕ) :
    (∫ ω, (pathProduct (liftObservations ((n, f) :: w)) ω).toReal
      ∂C.conditionedMeasure x (n + totalTime w + t)) =
      ∫ ω, (pathProduct (liftObservations ((1, fun _ => 1) :: (n - 1, f) :: w)) ω).toReal
        ∂C.conditionedMeasure x ((n - 1) + totalTime w + t + 1) := by
  have htime : (n - 1) + totalTime w + t + 1 = n + totalTime w + t := by omega
  rw [htime]
  apply integral_congr_ae
  filter_upwards [C.ae_survival_conditionedMeasure x (n + totalTime w + t)] with ω hω
  exact congrArg ENNReal.toReal
    (pathProduct_remove_initial_smoothing n hn f w ω (hω 1 (by omega))).symm

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.StationaryClusters
open ClusterMixing

/-- The quantitative constant can depend only on the total number of
observations, not on their partition into clusters. -/
theorem cluster_size_factor_le {A : Type*} (w : List (ℕ × Block A))
    (U V : ℝ) (hU : 1 ≤ U) (hV : 0 ≤ V) :
    (((w.length : ℝ) + 1) * U ^ (w.length + 1) + V ^ w.length) *
        U ^ (w.map fun p => p.2.internal.length).sum ≤
      ((((flatten w).length : ℝ) + 1) * U ^ ((flatten w).length + 1) +
        (max 1 V) ^ (flatten w).length) * U ^ (flatten w).length := by
  have hc : w.length ≤ (flatten w).length := by rw [length_flatten]; omega
  have hi : (w.map fun p => p.2.internal.length).sum ≤ (flatten w).length := by
    rw [length_flatten]; omega
  have hUp : U ^ (w.length + 1) ≤ U ^ ((flatten w).length + 1) :=
    pow_le_pow_right₀ hU (by omega)
  have hUi : U ^ (w.map fun p => p.2.internal.length).sum ≤ U ^ (flatten w).length :=
    pow_le_pow_right₀ hU hi
  have hVp : V ^ w.length ≤ (max 1 V) ^ (flatten w).length :=
    (pow_le_pow_left₀ hV (le_max_right 1 V) w.length).trans
      (pow_le_pow_right₀ (le_max_left 1 V) hc)
  have hcast : (w.length : ℝ) + 1 ≤ ((flatten w).length : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hc 1
  have hU0 : 0 ≤ U := le_trans zero_le_one hU
  exact mul_le_mul
    (add_le_add (mul_le_mul hcast hUp (pow_nonneg hU0 _) (by positivity)) hVp)
    hUi (pow_nonneg hU0 _) (by positivity)

end ConditionedStableLaws.StationaryClusters
