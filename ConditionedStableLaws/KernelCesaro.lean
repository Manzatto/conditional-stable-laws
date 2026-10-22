import ConditionedStableLaws.KernelMaximal
import ConditionedStableLaws.MaximalClosure
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Almost-everywhere Cesàro convergence through `L¹` approximations

For a nonnegative integrable observable, summably accurate approximations from below suffice. The
weak maximal inequality controls the remainder uniformly in the Cesàro horizon; Borel–Cantelli then
gives pointwise convergence.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.KernelCesaro

noncomputable section

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X} [IsMarkovKernel P]
  {ν : Measure X} [IsFiniteMeasure ν]

open KernelMaximal

theorem tendsto_ae_of_nonneg_approximation (hinv : P ∘ₘ ν = ν)
    {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    (v : ℕ → X → ℝ) (hv : ∀ j, Measurable (v j)) (hvi : ∀ j, Integrable (v j) ν)
    (hvle : ∀ j x, v j x ≤ g x)
    (b : ℕ → ℝ) (hb0 : ∀ j, 0 < b j) (hb : Tendsto b atTop (𝓝 0))
    (hbsum : (∑' j, ENNReal.ofReal (b j)) ≠ ∞)
    (herr : ∀ j, (∫ x, g x - v j x ∂ν) ≤ (b j) ^ 2)
    (hconv : ∀ j, ∀ᵐ x ∂ν,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * partialSum P (v j) n x) atTop
        (𝓝 (∫ y, v j y ∂ν))) :
    ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * partialSum P g n x) atTop
      (𝓝 (∫ y, g y ∂ν)) := by
  set r : ℕ → X → ℝ := fun j x => g x - v j x
  have hr (j : ℕ) : Integrable (r j) ν := hg.sub (hvi j)
  have hr0 (j : ℕ) (x : X) : 0 ≤ r j x := sub_nonneg.2 (hvle j x)
  have htail : Tendsto (fun j => ∫ x, r j x ∂ν) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg (hr0 j)) herr (by simpa using hb.pow 2)
  have hmean : Tendsto (fun j => ∫ x, v j x ∂ν) atTop (𝓝 (∫ x, g x ∂ν)) := by
    have hh := (tendsto_const_nhds (x := ∫ x, g x ∂ν)).sub htail
    simp only [sub_zero] at hh
    apply hh.congr
    intro j
    rw [show (∫ x, r j x ∂ν) = (∫ x, g x ∂ν) - ∫ x, v j x ∂ν from
      integral_sub hg (hvi j)]
    ring
  set F : ℕ → X → ℝ := fun n x => (n : ℝ)⁻¹ * partialSum P g n x
  set V : ℕ → ℕ → X → ℝ := fun j n x => (n : ℝ)⁻¹ * partialSum P (v j) n x
  have hmax (j : ℕ) : ν {x | ∃ n, b j < |F n x - V j n x|} ≤ ENNReal.ofReal (b j) := by
    have hsub : {x | ∃ n, b j < |F n x - V j n x|} ≤ᵐ[ν]
        {x | ∃ n : ℕ, (n : ℝ) * b j < partialSum P (r j) n x} := by
      filter_upwards [ae_all_iff.2 (partialSum_sub hinv hg (hvi j))] with x hx hmem
      obtain ⟨n, hn⟩ := hmem
      by_cases hn0 : n = 0
      · subst n
        simp only [F, V, Nat.cast_zero, inv_zero, zero_mul, sub_self, abs_zero] at hn
        exact False.elim ((not_lt_of_ge (hb0 j).le) hn)
      · have hnp : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
        change b j < |(n : ℝ)⁻¹ * partialSum P g n x -
          (n : ℝ)⁻¹ * partialSum P (v j) n x| at hn
        rw [← mul_sub, ← hx n, abs_mul, abs_of_nonneg (inv_nonneg.2 hnp.le),
          abs_of_nonneg (partialSum_nonneg (hr0 j) n x), inv_mul_eq_div,
          lt_div_iff₀ hnp] at hn
        exact ⟨n, by simpa only [mul_comm] using hn⟩
    have hbound := measure_maximal_partialSum hinv (hgm.sub (hv j)) (hr j) (hr0 j) (hb0 j)
    apply (measure_mono_ae hsub).trans (hbound.trans (ENNReal.ofReal_le_ofReal ?_))
    apply (div_le_iff₀ (hb0 j)).2
    simpa only [Pi.sub_apply, pow_two] using herr j
  apply MaximalClosure.tendsto_ae_of_maximal_approximation F V b
    (fun j => ∫ x, v j x ∂ν) (∫ x, g x ∂ν) hb hmean hconv
  exact ne_top_of_le_ne_top hbsum (ENNReal.tsum_le_tsum hmax)

/-- Convergence on bounded observables extends to every nonnegative `L¹` observable. -/
theorem tendsto_ae_nonneg (hinv : P ∘ₘ ν = ν)
    (hbounded : ∀ (v : X → ℝ), Measurable v →
      (∃ B : ℝ, ∀ x, |v x| ≤ B) → ∀ᵐ x ∂ν,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * partialSum P v n x) atTop (𝓝 (∫ y, v y ∂ν)))
    {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g ν) (hg0 : ∀ x, 0 ≤ g x) :
    ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * partialSum P g n x) atTop
      (𝓝 (∫ y, g y ∂ν)) := by
  set v : ℕ → X → ℝ := fun k x => min (g x) (k : ℝ)
  have hvm (k : ℕ) : Measurable (v k) := hgm.min measurable_const
  have hvi (k : ℕ) : Integrable (v k) ν := hg.inf (integrable_const (k : ℝ))
  have hvle (k : ℕ) (x : X) : v k x ≤ g x := min_le_left _ _
  have hv0 (k : ℕ) (x : X) : 0 ≤ v k x := le_min (hg0 x) (Nat.cast_nonneg k)
  have htail : Tendsto (fun k => ∫ x, g x - v k x ∂ν) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun k x => g x - v k x) (f := fun _ => (0 : ℝ)) g
      (fun k => (hgm.sub (hvm k)).aestronglyMeasurable) hg
      (fun k => ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (sub_nonneg.2 (hvle k x))]
        exact sub_le_self _ (hv0 k x))
      (ae_of_all _ fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈g x⌉₊] with k hk
        have hle : g x ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
        simp only [v, min_eq_left hle, sub_self])
    simpa only [integral_zero] using hd
  set b : ℕ → ℝ := fun j => (2 : ℝ)⁻¹ ^ j
  have hb0 (j : ℕ) : 0 < b j := pow_pos (by norm_num) _
  have hb : Tendsto b atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hchoose (j : ℕ) : ∃ k : ℕ, (∫ x, g x - v k x ∂ν) ≤ (b j) ^ 2 := by
    exact ((htail.eventually (ge_mem_nhds (sq_pos_of_pos (hb0 j)))).exists)
  choose k hk using hchoose
  have hbsum : (∑' j, ENNReal.ofReal (b j)) ≠ ∞ := by
    have heq (j : ℕ) : ENNReal.ofReal (b j) = (2⁻¹ : ℝ≥0∞) ^ j := by
      change ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j) = _
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2⁻¹),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [tsum_congr heq, ENNReal.tsum_geometric_two]
    norm_num
  apply tendsto_ae_of_nonneg_approximation hinv hgm hg (fun j => v (k j))
    (fun j => hvm (k j)) (fun j => hvi (k j)) (fun j => hvle (k j)) b hb0 hb hbsum hk
  intro j
  apply hbounded _ (hvm (k j))
  exact ⟨k j, fun x => by rw [abs_of_nonneg (hv0 (k j) x)]; exact min_le_right _ _⟩

/-- The same conclusion in the usual kernel-power notation. -/
theorem tendsto_ae_nonneg_kernel_sum (hinv : P ∘ₘ ν = ν)
    (hbounded : ∀ (v : X → ℝ), Measurable v →
      (∃ B : ℝ, ∀ x, |v x| ≤ B) → ∀ᵐ x ∂ν,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ y, v y ∂(P ^ i) x)
          atTop (𝓝 (∫ y, v y ∂ν)))
    {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g ν) (hg0 : ∀ x, 0 ≤ g x) :
    ∀ᵐ x ∂ν, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ y, g y ∂(P ^ i) x)
        atTop (𝓝 (∫ y, g y ∂ν)) := by
  have hrec : ∀ (v : X → ℝ), Measurable v → (∃ B : ℝ, ∀ x, |v x| ≤ B) →
      ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * partialSum P v n x)
        atTop (𝓝 (∫ y, v y ∂ν)) := by
    intro v hvm hvb
    obtain ⟨B, hB⟩ := hvb
    have hvi := Integrable.of_bound (μ := ν) hvm.aestronglyMeasurable B
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB x)
    filter_upwards [hbounded v hvm ⟨B, hB⟩, ae_all_iff.2 (partialSum_eq_sum hinv hvm hvi)]
      with x hx heq
    exact hx.congr (fun n => by rw [heq n])
  filter_upwards [tendsto_ae_nonneg hinv hrec hgm hg hg0,
    ae_all_iff.2 (partialSum_eq_sum hinv hgm hg)] with x hx heq
  exact hx.congr (fun n => by rw [heq n])

end

end ConditionedStableLaws.KernelCesaro
