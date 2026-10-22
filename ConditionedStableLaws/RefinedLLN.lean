import ConditionedStableLaws.QProcessErgodic
import ConditionedStableLaws.Toeplitz
import ConditionedStableLaws.PathMixing
import ConditionedStableLaws.KernelLp
import ConditionedStableLaws.WeightedLp

/-!
# Refined conditional laws of large numbers

Trajectory and Doob-kernel integration lemmas.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.RefinedLLN

noncomputable section

open StandingHypothesis CanonicalChain

/-! ### Trajectory laws -/

section Trajectories

variable {X : Type*} [MeasurableSpace X] (K : Kernel X X) [IsMarkovKernel K]

/-- The time-zero marginal of the trajectory law started from `ν` is `ν`. -/
theorem trajMeasure_map_zero (ν : Measure X) [IsProbabilityMeasure ν] :
    (Kernel.trajMeasure (X := fun _ => X) ν (QProcessLimit.historyKernel K)).map (fun ω => ω 0) = ν := by
  let e : ((i : Finset.Iic 0) → X) → X := fun ω => ω ⟨0, by simp⟩
  have he : Measurable e := measurable_pi_apply _
  have hcoord : (fun ω : ℕ → X => ω 0) = e ∘ Preorder.frestrictLe 0 := rfl
  rw [hcoord, ← Measure.map_map he (Preorder.measurable_frestrictLe 0)]
  unfold Kernel.trajMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_map he (MeasurableEquiv.measurable _)]
  have hid : e ∘ (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X)).symm = id := by
    funext x
    rfl
  rw [hid, Measure.map_id]

/-- The path law started at `x` is the trajectory kernel evaluated at `x`. -/
theorem pathMeasure_eq_traj (x : X) :
    QProcessLimit.pathMeasure K x = Kernel.traj (QProcessLimit.historyKernel K) 0
      ((MeasurableEquiv.piUnique (fun _i : Finset.Iic 0 => X)).symm x) := by
  unfold QProcessLimit.pathMeasure Kernel.trajMeasure
  rw [Measure.map_dirac' (MeasurableEquiv.measurable _)]
  exact Measure.dirac_bind (Kernel.measurable _) _

/-- Disintegration: an almost sure property of the trajectory law started from
`ν` holds almost surely under the path law started at `ν`-almost every `x`. -/
theorem ae_pathMeasure_of_ae_trajMeasure (ν : Measure X) {P : (ℕ → X) → Prop}
    (h : ∀ᵐ ω ∂Kernel.trajMeasure (X := fun _ => X) ν (QProcessLimit.historyKernel K), P ω) :
    ∀ᵐ x ∂ν, ∀ᵐ ω ∂QProcessLimit.pathMeasure K x, P ω := by
  unfold Kernel.trajMeasure at h
  have h2 := Measure.ae_ae_of_ae_comp h
  have h3 := ae_of_ae_map (MeasurableEquiv.measurable _).aemeasurable h2
  filter_upwards [h3] with x hx
  rw [pathMeasure_eq_traj]
  exact hx

omit [MeasurableSpace X] in
theorem pathShift_iterate (i : ℕ) (ω : ℕ → X) (n : ℕ) :
    (Cited.pathShift^[i] ω) n = ω (n + i) := by
  induction i generalizing ω with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [Cited.pathShift]
      ring_nf

end Trajectories

/-! ### The quasi-ergodic law on `M \ Z` -/

section QuasiErgodic

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} (d : DoobTransform.EigenData K)
  (μ : Measure M)

/-- The quasi-ergodic law `ν = η μ` lives on `{η > 0}`. -/
theorem withDensity_ae_live : ∀ᵐ y ∂μ.withDensity d.weight, y ∈ d.liveSet := by
  rw [ae_iff]
  change μ.withDensity d.weight d.liveSetᶜ = 0
  rw [withDensity_apply _ d.measurableSet_liveSet.compl, lintegral_eq_zero_iff d.measurable_weight]
  filter_upwards [ae_restrict_mem d.measurableSet_liveSet.compl] with y hy
  exact not_not.1 hy

theorem map_comap_withDensity :
    ((μ.withDensity d.weight).comap (Subtype.val : d.State → M)).map Subtype.val =
      μ.withDensity d.weight := by
  rw [d.live_embedding.map_comap, Subtype.range_coe]
  exact Measure.restrict_eq_self_of_ae_mem (withDensity_ae_live d μ)

/-- `∫ f dν` computed on `M \ Z` or on `M`. -/
theorem integral_live (f : M → ℝ) :
    ∫ x : d.State, f x.val ∂(μ.withDensity d.weight).comap Subtype.val =
      ∫ y, f y ∂μ.withDensity d.weight := by
  rw [← d.live_embedding.integral_map, map_comap_withDensity]

theorem integrable_live {f : M → ℝ} (hf : Integrable f (μ.withDensity d.weight)) :
    Integrable (fun x : d.State => f x.val) ((μ.withDensity d.weight).comap Subtype.val) := by
  rw [← map_comap_withDensity d μ] at hf
  exact (d.live_embedding.integrable_map_iff).1 hf

end QuasiErgodic

/-! ### Step 2: convergence in probability for `h ∈ L¹(ν)` -/

section Step2

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem measurable_doobAverage {K : Kernel M M} (d : DoobTransform.EigenData K) {f : M → ℝ}
    (hf : Measurable f) (n : ℕ) : Measurable (Cited.doobAverage d f n) := by
  unfold Cited.doobAverage
  exact (Finset.measurable_sum _ fun i _ =>
    (hf.comp measurable_subtype_coe).comp (measurable_pi_apply i)).const_mul _


end Step2

/-! ### The Doob kernel against nonnegative functions -/

section DoobLIntegral

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} [IsSFiniteKernel K]
  (d : DoobTransform.EigenData K)

/-- `ℚⁱ(x, ·) = λ⁻ⁱ η(x)⁻¹ (η Kⁱ(x, ·))` on the live states. -/
theorem doob_kernel_pow_eq (i : ℕ) (x : d.State) :
    (d.kernel ^ i) x = ((d.rate⁻¹) ^ i * (d.weight x.val)⁻¹) •
      (((K ^ i) x.val).withDensity d.weight).comap (Subtype.val : d.State → M) := by
  ext A hA
  rw [d.kernel_pow_apply i x A hA, Measure.smul_apply, smul_eq_mul,
    d.live_embedding.comap_apply, withDensity_apply _ (d.live_embedding.measurableSet_image' hA)]

/-- Integration against the Doob kernel. -/
theorem lintegral_doob_pow (i : ℕ) (x : d.State) {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, F y.val ∂(d.kernel ^ i) x =
      (d.rate⁻¹) ^ i * (d.weight x.val)⁻¹ * ∫⁻ y, F y * d.weight y ∂(K ^ i) x.val := by
  rw [doob_kernel_pow_eq, lintegral_smul_measure, smul_eq_mul,
    lintegral_subtype_comap d.measurableSet_liveSet,
    setLIntegral_withDensity_eq_setLIntegral_mul _ d.measurable_weight hF d.measurableSet_liveSet,
    setLIntegral_eq_of_support_subset]
  · simp only [Pi.mul_apply, mul_comm]
  · intro y hy
    by_contra hyl
    exact hy (by simp [Pi.mul_apply, not_not.1 hyl])

end DoobLIntegral

/-!
### Geometric Cesàro averages
-/

theorem cesaro_term_div_tendsto_zero {r : ℕ → ℝ} {L : ℝ}
    (hL : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, r i) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => r n / (n + 1)) atTop (𝓝 0) := by
  set A := fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, r i
  have hsum (n : ℕ) : (n : ℝ) * A n = ∑ i ∈ Finset.range n, r i := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp only [A]
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul]
  have hid (n : ℕ) : r n / (n + 1) = A (n + 1) - (n / (n + 1 : ℝ)) * A n := by
    have h1 := hsum (n + 1)
    rw [Finset.sum_range_succ, ← hsum n] at h1
    push_cast at h1
    field_simp
    linarith
  have hfrac : Tendsto (fun n : ℕ => (n / (n + 1 : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
  have := ((hL.comp (tendsto_add_atTop_nat 1)).sub (hfrac.mul hL))
  simp only [one_mul, sub_self] at this
  exact this.congr (fun n => (hid n).symm)

/-- If the Cesàro averages of `r` converge, then `n⁻¹ ∑_{i<n} θ^{n-1-i} rᵢ → 0`
for `0 ≤ θ < 1` (Toeplitz's lemma). -/
theorem geometric_cesaro_tendsto_zero {r : ℕ → ℝ} {L θ : ℝ}
    (hL : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, r i) atTop (𝓝 L))
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, θ ^ (n - 1 - i) * r i)
      atTop (𝓝 0) := by
  let w : ℕ → ℕ → ℝ := fun n i => θ ^ (n - 1 - i) * ((i + 1 : ℝ) / n)
  have hw : ∀ n i, 0 ≤ w n i := fun n i =>
    mul_nonneg (pow_nonneg hθ0 _) (div_nonneg (by positivity) (Nat.cast_nonneg _))
  have hcol : ∀ i, Tendsto (fun n => w n i) atTop (𝓝 0) := by
    intro i
    have h1 : Tendsto (fun n : ℕ => ((i + 1 : ℝ) / n)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero (fun n => hw n i) (fun n => ?_) h1
    exact mul_le_of_le_one_left (div_nonneg (by positivity) (Nat.cast_nonneg _))
      (pow_le_one₀ hθ0 hθ1.le)
  have hrow : ∀ n, ∑ i ∈ Finset.range n, w n i ≤ (1 - θ)⁻¹ := by
    intro n
    calc ∑ i ∈ Finset.range n, w n i ≤ ∑ i ∈ Finset.range n, θ ^ (n - 1 - i) := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_of_le_one_right (pow_nonneg hθ0 _)
          have hin := Finset.mem_range.1 hi
          rw [div_le_one (by exact_mod_cast (show 0 < n by omega))]
          exact_mod_cast hin
      _ = ∑ j ∈ Finset.range n, θ ^ j := by
          rw [← Finset.sum_range_reflect]
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          have := Finset.mem_range.1 hj
          omega
      _ ≤ (1 - θ)⁻¹ := by
          rw [← tsum_geometric_of_lt_one hθ0 hθ1]
          exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hθ0 j)
            (summable_geometric_of_lt_one hθ0 hθ1)
  have hx := cesaro_term_div_tendsto_zero hL
  refine (toeplitz_tendsto_zero w (fun i => r i / (i + 1)) hw hcol hrow hx).congr fun n => ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [w]
  have hi : (i + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### The conditioned mean of a nonnegative Birkhoff average -/

section ConditionedMean

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

omit [MeasurableSpace M] in
theorem ofReal_zeroExtension (g : M → ℝ) (z : Option M) :
    ENNReal.ofReal (zeroExtension g z) =
      PathMixing.liveExtension (fun y => ENNReal.ofReal (g y)) z := by
  cases z <;> simp [zeroExtension, PathMixing.liveExtension]

/-- `E_x[h(Xᵢ) | τ > n] = Kⁿ(x,M)⁻¹ ∫ h(y) Kⁿ⁻ⁱ(y,M) Kⁱ(x,dy)` for `h ≥ 0`, `i ≤ n`. -/
theorem lintegral_conditioned_single (x : M) {i n : ℕ} (hin : i ≤ n) {G : M → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ ω, PathMixing.liveExtension G (ω i) ∂C.conditionedMeasure x n =
      ((C.killedTransition ^ n) x univ)⁻¹ *
        ∫⁻ y, G y * (C.killedTransition ^ (n - i)) y univ ∂(C.killedTransition ^ i) x := by
  have h := C.lintegral_conditioned_pathProduct x [(i, G)] (by simpa using hG) (n - i)
  simp only [PathMixing.totalTime, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Nat.add_sub_cancel' hin] at h
  have hl : (∫⁻ ω, PathMixing.liveExtension G (ω i) ∂C.conditionedMeasure x n) =
      ∫⁻ ω, PathMixing.pathProduct (PathMixing.liftObservations [(i, G)]) ω
        ∂C.conditionedMeasure x n := by
    apply lintegral_congr
    intro ω
    simp [PathMixing.pathProduct, PathMixing.liftObservations]
  rw [hl, h]
  rfl

/-- The conditioned mean of a nonnegative Birkhoff average, as a finite sum of killed-kernel
integrals. -/
theorem lintegral_conditioned_average (x : M) (n : ℕ) {g : M → ℝ} (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y) :
    ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ * pathBirkhoffSum g n ω) ∂C.conditionedMeasure x n =
      ENNReal.ofReal (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ((C.killedTransition ^ n) x univ)⁻¹ *
          ∫⁻ y, ENNReal.ofReal (g y) * (C.killedTransition ^ (n - i)) y univ
            ∂(C.killedTransition ^ i) x := by
  have hz (z : Option M) : 0 ≤ zeroExtension g z := by
    cases z <;> simp [zeroExtension, hg0]
  have hpt (ω : Path M) : ENNReal.ofReal ((n : ℝ)⁻¹ * pathBirkhoffSum g n ω) =
      ENNReal.ofReal (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        PathMixing.liveExtension (fun y => ENNReal.ofReal (g y)) (ω i) := by
    rw [ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg n)), pathBirkhoffSum, birkhoffSum,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hz _)]
    simp_rw [ofReal_zeroExtension]
  have hG : Measurable (fun y => ENNReal.ofReal (g y)) := hg.ennreal_ofReal
  have hmeas (i : ℕ) : Measurable (fun ω : Path M =>
      PathMixing.liveExtension (fun y => ENNReal.ofReal (g y)) (ω i)) :=
    (PathMixing.measurable_liveExtension hG).comp (measurable_pi_apply i)
  simp_rw [hpt]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hmeas i),
    MeasureTheory.lintegral_finsetSum _ (fun i _ => hmeas i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_conditioned_single C x (Finset.mem_range.1 hi).le hG

end ConditionedMean

/-! ### Step 3 helpers -/

section Step3Helpers

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} [IsFiniteKernel K] {μ : Measure M}
  {c : ℝ≥0∞}

omit [IsFiniteKernel K] in
/-- Iterating a left eigen-relation: `Kⁱ ∘ₘ μ = cⁱ μ`. -/
theorem kernel_pow_comp (hK : K ∘ₘ μ = c • μ) (i : ℕ) : (K ^ i) ∘ₘ μ = c ^ i • μ := by
  induction i with
  | zero =>
      simp only [pow_zero, one_smul]
      exact Measure.bind_dirac
  | succ i ih =>
      rw [Kernel.pow_add, pow_one, ← Measure.comp_assoc, hK, Measure.comp_smul, ih,
        smul_smul, pow_succ, mul_comm]

/-- If `∫ G dμ < ∞`, then `∫ G dKⁱ(y) < ∞` for all `i`, for `μ`-a.e. `y`. -/
theorem ae_lintegral_kernel_pow_ne_top (hK : K ∘ₘ μ = c • μ) (hc : c ≠ ∞) {G : M → ℝ≥0∞}
    (hG : Measurable G) (hfin : ∫⁻ y, G y ∂μ ≠ ∞) :
    ∀ᵐ y ∂μ, ∀ i : ℕ, ∫⁻ z, G z ∂(K ^ i) y ≠ ∞ := by
  rw [ae_all_iff]
  intro i
  have : IsFiniteKernel (K ^ i) := by
    induction i with
    | zero => change IsFiniteKernel (Kernel.id : Kernel M M); infer_instance
    | succ i ih => rw [pow_succ]; change IsFiniteKernel ((K ^ i) ∘ₖ K); infer_instance
  have hint := KernelLp.lintegral_lintegral_kernel (kernel_pow_comp hK i) hG
  have hlt : ∫⁻ y, ∫⁻ z, G z ∂(K ^ i) y ∂μ ≠ ∞ := by
    rw [hint]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hc) hfin
  filter_upwards [ae_lt_top (hG.lintegral_kernel) hlt] with y hy
  exact hy.ne

end Step3Helpers

section Live

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} (d : DoobTransform.EigenData K)
  (μ : Measure M)

/-- `μ`-almost sure properties hold for `ν`-almost every live state. -/
theorem ae_live_of_ae {P : M → Prop} (h : ∀ᵐ y ∂μ, P y) :
    ∀ᵐ x ∂(μ.withDensity d.weight).comap (Subtype.val : d.State → M), P x.val := by
  have h1 : ∀ᵐ y ∂μ.withDensity d.weight, P y := withDensity_absolutelyContinuous μ _ h
  rw [← map_comap_withDensity d μ] at h1
  exact ae_of_ae_map d.live_embedding.measurable.aemeasurable h1

end Live

/-! ### Step 3: the conditioned mean for `0 ≤ h ∈ L¹(μ)` -/

section Step3

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M} [IsSFiniteKernel K]
  (d : DoobTransform.EigenData K)

/-- Real form of the Doob identity: `η(x) ∫ F dQⁱ(x) = λ⁻ⁱ ∫ F η dKⁱ(x)` for
`F ≥ 0` with finite integral. -/
theorem doob_pow_integral (i : ℕ) (x : d.State) {F : M → ℝ} (hF : Measurable F)
    (hF0 : ∀ y, 0 ≤ F y)
    (_hfin : ∫⁻ y, ENNReal.ofReal (F y) * d.weight y ∂(K ^ i) x.val ≠ ∞) :
    (d.weight x.val).toReal * ∫ y, F y.val ∂(d.kernel ^ i) x =
      (d.rate.toReal)⁻¹ ^ i * ∫ y, F y * (d.weight y).toReal ∂(K ^ i) x.val := by
  have hw0 : d.weight x.val ≠ 0 := x.property
  have hwt : d.weight x.val ≠ ∞ := d.weight_ne_top _
  have hl := lintegral_doob_pow d i x hF.ennreal_ofReal
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => hF0 _)
      (hF.comp measurable_subtype_coe).aestronglyMeasurable, hl,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y => mul_nonneg (hF0 y) ENNReal.toReal_nonneg)
      (hF.mul d.measurable_weight.ennreal_toReal).aestronglyMeasurable]
  have heq : (∫⁻ y, ENNReal.ofReal (F y * (d.weight y).toReal) ∂(K ^ i) x.val) =
      ∫⁻ y, ENNReal.ofReal (F y) * d.weight y ∂(K ^ i) x.val := by
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (hF0 y), ENNReal.ofReal_toReal (d.weight_ne_top y)]
  rw [heq, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_inv, ← mul_assoc, ← mul_assoc, mul_comm (d.weight x.val).toReal,
    mul_assoc _ (d.weight x.val).toReal, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hw0, hwt⟩),
    mul_one]

end Step3

section Step3Chain

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

theorem integrable_of_lintegral_ne_top {μ : Measure M} {g : M → ℝ} (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y) (hfin : ∫⁻ y, ENNReal.ofReal (g y) ∂μ ≠ ∞) : Integrable g μ := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg0)]
  exact hfin.lt_top

/-- The conditioned mean of a nonnegative Birkhoff average as a real number. -/
theorem conditioned_average_eq_ofReal (x : M)
    (hx : x ∈ survivingSet C.killedTransition) (n : ℕ) {g : M → ℝ} (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y)
    (hfin : ∀ i, ∫⁻ y, ENNReal.ofReal (g y) ∂(C.killedTransition ^ i) x ≠ ∞) :
    ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ * pathBirkhoffSum g n ω) ∂C.conditionedMeasure x n =
      ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (((C.killedTransition ^ n) x).real univ)⁻¹ *
          ∫ y, g y * ((C.killedTransition ^ (n - i)) y).real univ
            ∂(C.killedTransition ^ i) x) := by
  have hpos : 0 < ((C.killedTransition ^ n) x).real univ := by
    have h1 := C.pathMeasure_survival_pos x hx n
    rw [C.pathMeasure_survival] at h1
    exact ENNReal.toReal_pos h1.ne'
      ((C.killedTransition_pow_mass_le_one x n).trans_lt ENNReal.one_lt_top).ne
  have hk (k : ℕ) (y : M) : ((C.killedTransition ^ k) y univ) ≠ ∞ :=
    ((C.killedTransition_pow_mass_le_one y k).trans_lt ENNReal.one_lt_top).ne
  have hint (i : ℕ) : Integrable (fun y => g y * ((C.killedTransition ^ (n - i)) y).real univ)
      ((C.killedTransition ^ i) x) := by
    refine (integrable_of_lintegral_ne_top hg hg0 (hfin i)).mul_bdd
      ((Kernel.measurable_coe _ MeasurableSet.univ).ennreal_toReal.aestronglyMeasurable)
      (c := 1) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact C.killedTransition_pow_mass_le_one y _)
  have hterm (i : ℕ) : 0 ≤ (((C.killedTransition ^ n) x).real univ)⁻¹ *
      ∫ y, g y * ((C.killedTransition ^ (n - i)) y).real univ ∂(C.killedTransition ^ i) x :=
    mul_nonneg (inv_nonneg.2 hpos.le)
      (integral_nonneg fun y => mul_nonneg (hg0 y) ENNReal.toReal_nonneg)
  rw [lintegral_conditioned_average C x n hg hg0,
    ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg n)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hpos.le), ENNReal.ofReal_inv_of_pos hpos,
    Measure.real, ENNReal.ofReal_toReal (hk n x),
    ofReal_integral_eq_lintegral_ofReal (hint i)
      (Eventually.of_forall fun y => mul_nonneg (hg0 y) ENNReal.toReal_nonneg)]
  congr 1
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (hg0 y), Measure.real, ENNReal.ofReal_toReal (hk _ y)]

end Step3Chain


end

end ConditionedStableLaws.RefinedLLN
