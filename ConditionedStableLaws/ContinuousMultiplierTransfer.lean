import ConditionedStableLaws.ContinuousMultiplierCentered
import ConditionedStableLaws.ContinuousMultiplierCompensation

/-! Transfer from centered cutoffs to full signed residual sums. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace ConditionedStableLaws.ContinuousMultiplier
noncomputable section
open CanonicalChain

section General
variable {M : Type*}

/-- A path contains an observation beyond the specified original-observable cutoff. -/
def largeEvent (f : M → ℝ) (B R : ℝ) (n : ℕ) : Set (Path M) :=
  {ω | ∃ j < n, R * B < zeroExtension f (ω j)}

theorem path_eq_cut_of_not_large {f r : M → ℝ} {B R : ℝ} {n : ℕ} {ω : Path M}
    (hω : ω ∉ largeEvent f B R n) :
    pathBirkhoffSum r n ω = pathBirkhoffSum (cut f r (R * B)) n ω := by
  unfold pathBirkhoffSum birkhoffSum
  apply Finset.sum_congr rfl
  intro j hj
  cases hstate : ω j with
  | none => simp [zeroExtension, hstate]
  | some x =>
    have hx : f x ≤ R * B := by
      by_contra hc
      apply hω
      exact ⟨j, Finset.mem_range.mp hj, by simpa [zeroExtension, hstate] using lt_of_not_ge hc⟩
    simp [zeroExtension, hstate, cut, hx]

variable [MeasurableSpace M]

/-- Centered cutoff approximation plus control of the rare maximum proves
negligibility of the full residual, under the changing conditioned laws. -/
theorem full_residual_negligible
    (P : ℕ → Measure (Path M)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : Measure M) {f r : M → ℝ} {B c : ℕ → ℝ}
    (hlarge : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 1 ≤ R ∧ ∀ᶠ n in atTop,
      (P n).real (largeEvent f (B n) R n) < δ)
    (hcut : ∀ R : ℝ, 1 ≤ R → ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (P n).real {ω | ε < |(B n)⁻¹ * pathBirkhoffSum
        (cut f r (R * B n)) n ω - n * (B n)⁻¹ * ∫ y, cut f r (R * B n) y ∂ν|})
      atTop (𝓝 0))
    (hcenter : ∀ R : ℝ, 1 ≤ R → Tendsto
      (fun n : ℕ => n * (B n)⁻¹ * (∫ y, cut f r (R * B n) y ∂ν) - (B n)⁻¹ * c n)
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (P n).real {ω | ε < |(B n)⁻¹ * (pathBirkhoffSum r n ω - c n)|})
      atTop (𝓝 0) := by
  intro ε hε
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨R, hR, hmax⟩ := hlarge (δ / 2) (half_pos hδ)
  have hsmall := (hcut R hR (ε / 2) (half_pos hε)).eventually_lt_const (half_pos hδ)
  have hcent := Metric.tendsto_nhds.mp (hcenter R hR) (ε / 2) (half_pos hε)
  filter_upwards [hmax, hsmall, hcent] with n hnmax hnsmall hncent
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hsub : {ω | ε < |(B n)⁻¹ * (pathBirkhoffSum r n ω - c n)|} ⊆
      largeEvent f (B n) R n ∪ {ω | ε / 2 < |(B n)⁻¹ * pathBirkhoffSum
        (cut f r (R * B n)) n ω - n * (B n)⁻¹ * ∫ y, cut f r (R * B n) y ∂ν|} := by
    intro ω hω
    by_cases hmaxω : ω ∈ largeEvent f (B n) R n
    · exact Or.inl hmaxω
    right
    have hid := path_eq_cut_of_not_large (r := r) hmaxω
    change ε / 2 < _
    by_contra hc
    have hle := le_of_not_gt hc
    have hsum := abs_add_le
      ((B n)⁻¹ * pathBirkhoffSum (cut f r (R * B n)) n ω -
        n * (B n)⁻¹ * ∫ y, cut f r (R * B n) y ∂ν)
      ((n : ℝ) * (B n)⁻¹ * (∫ y, cut f r (R * B n) y ∂ν) - (B n)⁻¹ * c n)
    simp only [Real.dist_eq, sub_zero] at hncent
    change ε < _ at hω
    rw [hid, mul_sub] at hω
    have heq : (B n)⁻¹ * pathBirkhoffSum (cut f r (R * B n)) n ω -
        n * (B n)⁻¹ * (∫ y, cut f r (R * B n) y ∂ν) +
        ((n : ℝ) * (B n)⁻¹ * (∫ y, cut f r (R * B n) y ∂ν) - (B n)⁻¹ * c n) =
        (B n)⁻¹ * pathBirkhoffSum (cut f r (R * B n)) n ω - (B n)⁻¹ * c n := by ring
    rw [heq] at hsum
    linarith
  calc
    _ ≤ (P n).real (largeEvent f (B n) R n ∪ {ω | ε / 2 < |(B n)⁻¹ * pathBirkhoffSum
        (cut f r (R * B n)) n ω - n * (B n)⁻¹ * ∫ y, cut f r (R * B n) y ∂ν|}) :=
      measureReal_mono hsub
    _ ≤ (P n).real (largeEvent f (B n) R n) +
      (P n).real {ω | ε / 2 < |(B n)⁻¹ * pathBirkhoffSum
        (cut f r (R * B n)) n ω - n * (B n)⁻¹ * ∫ y, cut f r (R * B n) y ∂ν|} :=
      measureReal_union_le _ _
    _ < δ := by linarith

end General
end
end ConditionedStableLaws.ContinuousMultiplier
