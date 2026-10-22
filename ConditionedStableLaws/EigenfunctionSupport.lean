import ConditionedStableLaws.DoobTransform
import ConditionedStableLaws.StandingHypothesis
import ConditionedStableLaws.QuasiErgodicSmallTargets

/-!
# Positivity of the eigenfunction on the nonescaping set

For a continuous nonzero nonnegative eigenfunction with positive eigenvalue, H2 forces its positive
set to be exactly the nonescaping set.
-/

open MeasureTheory ProbabilityTheory Set
open Filter
open scoped ENNReal Topology

namespace ConditionedStableLaws

namespace DoobTransform.EigenData

variable {M : Type*} [MeasurableSpace M] {K : Kernel M M}
  (d : DoobTransform.EigenData K)

/-- Iteration of the right eigenfunction equation through kernel powers. -/
theorem right_eigen_pow (n : ℕ) (x : M) :
    (∫⁻ y, d.weight y ∂(K ^ n) x) = d.rate ^ n * d.weight x := by
  induction n generalizing x with
  | zero => simp [show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply,
      lintegral_dirac' x d.measurable_weight]
  | succ n ih =>
      rw [pow_succ]
      change (∫⁻ y, d.weight y ∂((K ^ n) ∘ₖ K) x) = _
      rw [Kernel.lintegral_comp _ _ _ d.measurable_weight]
      simp_rw [ih]
      rw [lintegral_const_mul _ d.measurable_weight, d.right_eigen x, pow_succ]
      ac_rfl

/-- Every point of finite-time certain extinction has zero eigenfunction. -/
theorem weight_eq_zero_of_escaping {x : M}
    (hx : x ∈ StandingHypothesis.escapingSet K) : d.weight x = 0 := by
  obtain ⟨n, _hn, hmass⟩ := hx
  have hmeasure : (K ^ n) x = 0 := Measure.measure_univ_eq_zero.mp hmass
  have h := d.right_eigen_pow n x
  rw [hmeasure, lintegral_zero_measure] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero n d.rate_ne_zero)

/-- Positive eigenfunction points survive every finite horizon. -/
theorem liveSet_subset_survivingSet : d.liveSet ⊆ StandingHypothesis.survivingSet K := by
  intro x hx
  exact fun hesc => hx (d.weight_eq_zero_of_escaping hesc)

/-- The elementary lower bound behind the conditional denominator estimates. -/
theorem eigenfunction_le_survival_mass (B : ℝ≥0∞) (hB : ∀ y, d.weight y ≤ B)
    (n : ℕ) (x : M) : d.rate ^ n * d.weight x ≤ B * (K ^ n) x univ := by
  rw [← d.right_eigen_pow n x]
  calc
    ∫⁻ y, d.weight y ∂(K ^ n) x ≤ ∫⁻ _y, B ∂(K ^ n) x := lintegral_mono hB
    _ = _ := by simp

end DoobTransform.EigenData

/-- A measurable region that cannot be left in one step cannot be left in any finite number of
steps, for the composed kernel. -/
theorem kernel_pow_preserves_set
    {M : Type*} [MeasurableSpace M] (K : Kernel M M)
    (S : Set M) (hS : MeasurableSet S)
    (hclosed : ∀ x ∈ S, K x Sᶜ = 0) (n : ℕ) :
    ∀ x ∈ S, (K ^ n) x Sᶜ = 0 := by
  induction n with
  | zero =>
      intro x hx
      simp only [pow_zero, show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply]
      rw [Measure.dirac_apply' _ hS.compl]
      simp [hx]
  | succ n ih =>
      intro x hx
      rw [pow_succ]
      change ((K ^ n) ∘ₖ K) x Sᶜ = 0
      rw [Kernel.comp_apply' _ _ _ hS.compl]
      apply (lintegral_eq_zero_iff ((K ^ n).measurable_coe hS.compl)).mpr
      have hae : ∀ᵐ y ∂K x, y ∈ S := hclosed x hx
      filter_upwards [hae] with y hy
      exact ih y hy

namespace StandingHypothesis

variable {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {ρ : Measure M} {K : KilledKernel M}

/-- H2 propagates positivity from any nonzero point to every nonescaping point, for any continuous
eigenfunction with the explicit spectral data. -/
theorem HypothesisH.eigenfunction_liveSet_eq
    (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel)
    (hcont : Continuous d.weight) (hne : ∃ x, d.weight x ≠ 0) :
    d.liveSet = survivingSet K.kernel := by
  apply Subset.antisymm d.liveSet_subset_survivingSet
  intro x hx
  have hopen : IsOpen d.liveSet := by
    rw [d.liveSet_eq_positive]
    exact isOpen_lt continuous_const hcont
  have hrel : RelativelyOpen d.liveSet (survivingSet K.kernel) :=
    ⟨d.liveSet, hopen, (inter_eq_right.mpr d.liveSet_subset_survivingSet).symm⟩
  obtain ⟨n, _hn, hreach⟩ := h.irreducible x hx d.liveSet hrel hne
  have hint : 0 < ∫⁻ y, d.weight y ∂(K.kernel ^ n) x :=
    (lintegral_pos_iff_support d.measurable_weight).mpr hreach
  rw [d.right_eigen_pow] at hint
  change d.weight x ≠ 0
  intro hzero
  simp [hzero] at hint

/-- The eigenmeasure's support contains every nonescaping state. The proof
derives invariance of its closed support, then uses H2 and a positive-mass
eigenfunction point in that support. -/
theorem HypothesisH.survivingSet_subset_eigenmeasure_support
    (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel)
    (μ : Measure M) (hleft : K.kernel ∘ₘ μ = d.rate • μ)
    (hnorm : 0 < ∫⁻ x, d.weight x ∂μ) : survivingSet K.kernel ⊆ μ.support := by
  have hcont : ∀ A, MeasurableSet A → Continuous (fun x => (K.kernel x A).toReal) := by
    intro A hA
    simp_rw [h.kernel_real_eq_integral _ A hA]
    exact continuous_setIntegral_of_continuous_L1 h.continuous_density A
  have hclosed : ∀ x ∈ μ.support, K.kernel x μ.supportᶜ = 0 := by
    intro x hx
    exact kernel_null_on_support_of_eigenmeasure K.kernel μ hleft
      μ.isClosed_support.isOpen_compl.measurableSet
      (hcont _ μ.isClosed_support.isOpen_compl.measurableSet)
      μ.measure_compl_support hx
  have hμlive : 0 < μ d.liveSet :=
    (lintegral_pos_iff_support d.measurable_weight).mp hnorm
  obtain ⟨z, hzlive, hzsupp⟩ := μ.nonempty_inter_support_of_pos hμlive
  intro x hx
  by_contra hxsupp
  have hrel : RelativelyOpen (survivingSet K.kernel ∩ μ.supportᶜ)
      (survivingSet K.kernel) := ⟨μ.supportᶜ, μ.isClosed_support.isOpen_compl, rfl⟩
  obtain ⟨n, _hn, hreach⟩ := h.irreducible z (d.liveSet_subset_survivingSet hzlive)
    _ hrel ⟨x, hx, hxsupp⟩
  have hzero := kernel_pow_preserves_set K.kernel μ.support
    μ.isClosed_support.measurableSet hclosed n z hzsupp
  have hle := measure_mono (μ := (K.kernel ^ n) z)
    (inter_subset_right : survivingSet K.kernel ∩ μ.supportᶜ ⊆ μ.supportᶜ)
  rw [hzero] at hle
  exact (not_lt_of_ge hle) hreach

/-- The second small-target argument from normalized left/right eigen-data, including the
identification of the positive set and the support of the eigenmeasure. -/
theorem HypothesisH.uniform_small_targets_of_eigenData
    (h : HypothesisH ρ K) (d : DoobTransform.EigenData K.kernel)
    (hcont : Continuous d.weight) (μ : Measure M)
    (hleft : K.kernel ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1)
    (U : ℕ → Set M) (hUmeas : ∀ n, MeasurableSet (U n))
    (hUS : ∀ᶠ n in atTop, U n ⊆ survivingSet K.kernel)
    (hU : Tendsto (fun n => μ.withDensity d.weight (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x : M, (K.kernel x (U n)).toReal < ε := by
  have hnormpos : 0 < ∫⁻ x, d.weight x ∂μ := by rw [hnorm]; norm_num
  have hμlive : 0 < μ d.liveSet :=
    (lintegral_pos_iff_support d.measurable_weight).mp hnormpos
  obtain ⟨x, hx, _hxsupp⟩ := μ.nonempty_inter_support_of_pos hμlive
  have hlive := h.eigenfunction_liveSet_eq d hcont ⟨x, hx⟩
  have : IsProbabilityMeasure (μ.withDensity d.weight) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnorm]
  apply h.uniform_small_targets_weighted μ d.weight d.measurable_weight
    (fun x => ?_) (h.survivingSet_subset_eigenmeasure_support d μ hleft hnormpos)
    hleft d.right_eigen U hUmeas hUS hU
  exact Set.ext_iff.mp hlive x

end StandingHypothesis
end ConditionedStableLaws
