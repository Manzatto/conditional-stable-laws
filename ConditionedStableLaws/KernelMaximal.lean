import ConditionedStableLaws.KernelLp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A maximal inequality for an invariant Markov kernel

The Hopf envelope is defined recursively by `H₀ = 0` and
`Hₙ₊₁ = max (f + P Hₙ) 0`. Positivity of `P` makes these envelopes
increasing almost everywhere. Integrating `Hₙ - P Hₙ` over its positive
set gives the finite maximal ergodic inequality without assuming ergodicity.
This is the positive-contraction version of the maximal argument needed
for the integrable-observable parts of the conditional LLN.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.KernelMaximal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X} [IsMarkovKernel P]
  {ν : Measure X} [IsFiniteMeasure ν]

def partialSum (P : Kernel X X) (f : X → ℝ) : ℕ → X → ℝ
  | 0 => 0
  | n + 1 => fun x => f x + KernelLp.kint P (partialSum P f n) x

def envelope (P : Kernel X X) (f : X → ℝ) : ℕ → X → ℝ
  | 0 => 0
  | n + 1 => fun x => max (f x + KernelLp.kint P (envelope P f n) x) 0

omit [IsMarkovKernel P] in
theorem measurable_partialSum {f : X → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (partialSum P f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hf.add (KernelLp.stronglyMeasurable_kint ih.stronglyMeasurable).measurable

omit [IsMarkovKernel P] in
theorem measurable_envelope {f : X → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (envelope P f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact (hf.add (KernelLp.stronglyMeasurable_kint ih.stronglyMeasurable).measurable).max
        measurable_const

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem integrable_kint (hinv : P ∘ₘ ν = ν) {f : X → ℝ} (hf : Integrable f ν) :
    Integrable (KernelLp.kint P f) ν := by
  have he : P ∘ₘ ν = (1 : ℝ≥0∞) • ν := by simpa using hinv
  have hm := KernelLp.memLp_one_kint he ENNReal.one_ne_top hf.toL1
  apply (memLp_one_iff_integrable.1 hm).congr
  exact KernelLp.kint_congr he hf.coeFn_toL1

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem integrable_partialSum (hinv : P ∘ₘ ν = ν) {f : X → ℝ}
    (hf : Integrable f ν) (n : ℕ) : Integrable (partialSum P f n) ν := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih => exact hf.add (integrable_kint hinv ih)

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem integrable_envelope (hinv : P ∘ₘ ν = ν) {f : X → ℝ}
    (hf : Integrable f ν) (n : ℕ) : Integrable (envelope P f n) ν := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih => exact (hf.add (integrable_kint hinv ih)).sup (integrable_zero _ _ _)

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem kint_mono (hinv : P ∘ₘ ν = ν) {f g : X → ℝ}
    (hf : Integrable f ν) (hg : Integrable g ν) (hfg : f ≤ᵐ[ν] g) :
    KernelLp.kint P f ≤ᵐ[ν] KernelLp.kint P g := by
  have he : P ∘ₘ ν = (1 : ℝ≥0∞) • ν := by simpa using hinv
  filter_upwards [Measure.ae_integrable_of_integrable_comp (hinv.symm ▸ hf),
    Measure.ae_integrable_of_integrable_comp (hinv.symm ▸ hg),
    KernelLp.ae_ae he hfg] with x hfx hgx hx
  exact integral_mono_ae hfx hgx hx

omit [IsMarkovKernel P] in
theorem envelope_nonneg (f : X → ℝ) (n : ℕ) (x : X) : 0 ≤ envelope P f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem envelope_mono_step (hinv : P ∘ₘ ν = ν) {f : X → ℝ}
    (hf : Integrable f ν) (n : ℕ) : envelope P f n ≤ᵐ[ν] envelope P f (n + 1) := by
  induction n with
  | zero => exact ae_of_all _ (envelope_nonneg f 1)
  | succ n ih =>
      filter_upwards [kint_mono hinv (integrable_envelope hinv hf n)
        (integrable_envelope hinv hf (n + 1)) ih] with x hx
      exact max_le_max (add_le_add_right hx _) le_rfl

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem partialSum_le_envelope (hinv : P ∘ₘ ν = ν) {f : X → ℝ}
    (hf : Integrable f ν) (n : ℕ) : partialSum P f n ≤ᵐ[ν] envelope P f n := by
  induction n with
  | zero => exact ae_of_all _ fun _ => le_rfl
  | succ n ih =>
      filter_upwards [kint_mono hinv (integrable_partialSum hinv hf n)
        (integrable_envelope hinv hf n) ih] with x hx
      exact (add_le_add_right hx _).trans (le_max_left _ _)

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
/-- The finite Hopf inequality, valid without an ergodicity assumption. -/
theorem integral_nonneg_on_envelope_pos (hinv : P ∘ₘ ν = ν) {f : X → ℝ}
    (hfm : Measurable f) (hf : Integrable f ν) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < envelope P f n x}, f x ∂ν := by
  cases n with
  | zero => simp [envelope]
  | succ n =>
      set H := envelope P f (n + 1)
      set E := {x | 0 < H x}
      have hE : MeasurableSet E := measurableSet_lt measurable_const (measurable_envelope hfm _)
      have hH : Integrable H ν := integrable_envelope hinv hf _
      have hPH : Integrable (KernelLp.kint P H) ν := integrable_kint hinv hH
      have hdiff : Integrable (fun x => H x - KernelLp.kint P H x) ν := hH.sub hPH
      have htotal : (∫ x, H x - KernelLp.kint P H x ∂ν) = 0 := by
        rw [integral_sub hH hPH, KernelLp.integral_kint
          (show P ∘ₘ ν = (1 : ℝ≥0∞) • ν by simpa using hinv) ENNReal.one_ne_top hH]
        simp
      have hcompl : (∫ x in Eᶜ, H x - KernelLp.kint P H x ∂ν) ≤ 0 := by
        apply integral_nonpos_of_ae
        filter_upwards [ae_restrict_mem hE.compl] with x hx
        have hz : H x = 0 := le_antisymm (not_lt.1 hx) (envelope_nonneg f _ x)
        rw [hz, zero_sub]
        exact neg_nonpos.2 (integral_nonneg fun y => envelope_nonneg f _ y)
      have hpos : 0 ≤ ∫ x in E, H x - KernelLp.kint P H x ∂ν := by
        have := integral_add_compl hE hdiff
        rw [htotal] at this
        linarith
      apply hpos.trans
      apply setIntegral_mono_on_ae hdiff.restrict hf.restrict hE
      filter_upwards [kint_mono hinv (integrable_envelope hinv hf n) hH
        (envelope_mono_step hinv hf n)] with x hx hxe
      have hrec : H x = f x + KernelLp.kint P (envelope P f n) x := by
        exact max_eq_left (le_of_lt ((lt_max_iff.1 hxe).resolve_right (lt_irrefl _)))
      rw [hrec]
      linarith

omit [IsMarkovKernel P] in
theorem measure_envelope_sub_const (hinv : P ∘ₘ ν = ν) {g : X → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν) (hg0 : ∀ x, 0 ≤ g x)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ν {x | 0 < envelope P (fun x => g x - ε) n x} ≤ ENNReal.ofReal ((∫ x, g x ∂ν) / ε) := by
  set E := {x | 0 < envelope P (fun x => g x - ε) n x}
  have hi := integral_nonneg_on_envelope_pos hinv (hgm.sub measurable_const)
    (hg.sub (integrable_const ε)) n
  change 0 ≤ ∫ x in E, g x - ε ∂ν at hi
  rw [integral_sub hg.restrict (integrable_const ε), integral_const, smul_eq_mul,
    measureReal_restrict_apply_univ] at hi
  have hle := setIntegral_le_integral (s := E) hg (ae_of_all _ hg0)
  have hb : ν.real E ≤ (∫ x, g x ∂ν) / ε := (le_div_iff₀ hε).2 (by nlinarith)
  rw [← ofReal_measureReal (μ := ν) (s := E)]
  exact ENNReal.ofReal_le_ofReal hb

omit [IsMarkovKernel P] in
theorem measure_exists_envelope_sub_const (hinv : P ∘ₘ ν = ν) {g : X → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν) (hg0 : ∀ x, 0 ≤ g x)
    {ε : ℝ} (hε : 0 < ε) :
    ν {x | ∃ n, 0 < envelope P (fun x => g x - ε) n x} ≤
      ENNReal.ofReal ((∫ x, g x ∂ν) / ε) := by
  set f := fun x => g x - ε
  have hf : Integrable f ν := hg.sub (integrable_const ε)
  have hm : ∀ᵐ x ∂ν, Monotone (fun n => envelope P f n x) := by
    filter_upwards [ae_all_iff.2 (envelope_mono_step hinv hf)] with x hx
    exact monotone_nat_of_le_succ hx
  set G := {x | Monotone (fun n => envelope P f n x)}
  set E := fun n => {x | 0 < envelope P f n x}
  have hmono : Monotone (fun n => E n ∩ G) := by
    intro i j hij x hx
    exact ⟨lt_of_lt_of_le hx.1 (hx.2 hij), hx.2⟩
  have heq : {x | ∃ n, 0 < envelope P f n x} =ᵐ[ν] ⋃ n, E n ∩ G := by
    filter_upwards [hm] with x hx
    simp [E, G, hx]
  rw [measure_congr heq, hmono.measure_iUnion]
  exact iSup_le fun n => (measure_mono inter_subset_left).trans
    (measure_envelope_sub_const hinv hgm hg hg0 hε n)

omit [IsFiniteMeasure ν] in
theorem partialSum_sub_const (hinv : P ∘ₘ ν = ν) {g : X → ℝ}
    (hg : Integrable g ν) (ε : ℝ) (n : ℕ) :
    partialSum P (fun x => g x - ε) n =ᵐ[ν]
      fun x => partialSum P g n x - (n : ℝ) * ε := by
  induction n with
  | zero => exact ae_of_all _ fun _ => by simp [partialSum]
  | succ n ih =>
      have he : P ∘ₘ ν = (1 : ℝ≥0∞) • ν := by simpa using hinv
      filter_upwards [KernelLp.kint_congr he ih,
        Measure.ae_integrable_of_integrable_comp
          (hinv.symm ▸ integrable_partialSum hinv hg n)] with x hx hix
      simp only [partialSum, Nat.cast_add, Nat.cast_one]
      rw [hx]
      change g x - ε + (∫ y, partialSum P g n y - (n : ℝ) * ε ∂P x) = _
      rw [integral_sub hix (integrable_const _), integral_const]
      simp only [probReal_univ, one_smul]
      change g x - ε + (KernelLp.kint P (partialSum P g n) x - _) = _
      ring

/-- Weak `(1,1)` maximal inequality for nonnegative integrable observables.
The partial sums are recursive versions of `∑ i < n, Pⁱ g`. -/
theorem measure_maximal_partialSum (hinv : P ∘ₘ ν = ν) {g : X → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν) (hg0 : ∀ x, 0 ≤ g x)
    {ε : ℝ} (hε : 0 < ε) :
    ν {x | ∃ n : ℕ, (n : ℝ) * ε < partialSum P g n x} ≤
      ENNReal.ofReal ((∫ x, g x ∂ν) / ε) := by
  have hf : Integrable (fun x => g x - ε) ν := hg.sub (integrable_const ε)
  apply le_trans (measure_mono_ae (t := {x | ∃ n, 0 < envelope P (fun x => g x - ε) n x}) ?_)
    (measure_exists_envelope_sub_const hinv hgm hg hg0 hε)
  filter_upwards [ae_all_iff.2 (partialSum_sub_const hinv hg ε),
    ae_all_iff.2 (partialSum_le_envelope hinv hf)] with x hx hle hxmem
  obtain ⟨n, hn⟩ := hxmem
  exact ⟨n, lt_of_lt_of_le (by rw [hx n]; linarith) (hle n)⟩

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem invariant_pow (hinv : P ∘ₘ ν = ν) (n : ℕ) : (P ^ n) ∘ₘ ν = ν := by
  induction n with
  | zero => exact Measure.bind_dirac
  | succ n ih => rw [Kernel.pow_add, pow_one, ← Measure.comp_assoc, hinv, ih]

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem partialSum_eq_sum (hinv : P ∘ₘ ν = ν) {g : X → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν) (n : ℕ) :
    partialSum P g n =ᵐ[ν] fun x => ∑ i ∈ Finset.range n, ∫ y, g y ∂(P ^ i) x := by
  induction n with
  | zero => exact ae_of_all _ fun _ => by simp [partialSum]
  | succ n ih =>
      have he : P ∘ₘ ν = (1 : ℝ≥0∞) • ν := by simpa using hinv
      have hinner (i : ℕ) : Integrable (KernelLp.kint (P ^ i) g) ν :=
        integrable_kint (invariant_pow hinv i) hg
      have hEach := ae_all_iff.2 fun i =>
        Measure.ae_integrable_of_integrable_comp (hinv.symm ▸ hinner i)
      have hPow := ae_all_iff.2 fun i =>
        Measure.ae_integrable_of_integrable_comp ((invariant_pow hinv (i + 1)).symm ▸ hg)
      filter_upwards [KernelLp.kint_congr he ih, hEach, hPow] with x hx hix hpx
      simp only [partialSum]
      rw [hx]
      change g x + (∫ y, ∑ i ∈ Finset.range n, KernelLp.kint (P ^ i) g y ∂P x) = _
      rw [integral_finsetSum _ (fun i _ => hix i), Finset.sum_range_succ']
      have hzero : (∫ y, g y ∂(P ^ 0) x) = g x := by
        change (∫ y, g y ∂Kernel.id x) = g x
        rw [Kernel.id_apply, integral_dirac' _ _ hgm.stronglyMeasurable]
      rw [hzero, add_comm (∑ _ ∈ _, _)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hp := hpx i
      rw [Kernel.pow_add, pow_one] at hp ⊢
      exact (Kernel.integral_comp hp).symm

/-- The maximal bound in terms of the powers of the Markov kernel. -/
theorem measure_maximal_kernel_sum (hinv : P ∘ₘ ν = ν) {g : X → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν) (hg0 : ∀ x, 0 ≤ g x)
    {ε : ℝ} (hε : 0 < ε) :
    ν {x | ∃ n : ℕ, (n : ℝ) * ε < ∑ i ∈ Finset.range n, ∫ y, g y ∂(P ^ i) x} ≤
      ENNReal.ofReal ((∫ x, g x ∂ν) / ε) := by
  apply le_trans (measure_mono_ae (t := {x | ∃ n : ℕ, (n : ℝ) * ε < partialSum P g n x}) ?_)
    (measure_maximal_partialSum hinv hgm hg hg0 hε)
  filter_upwards [ae_all_iff.2 (partialSum_eq_sum hinv hgm hg)] with x hx hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n, by rw [hx n]; exact hn⟩

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem partialSum_nonneg {g : X → ℝ} (hg : ∀ x, 0 ≤ g x) (n : ℕ) (x : X) :
    0 ≤ partialSum P g n x := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (hg x) (integral_nonneg ih)

omit [IsMarkovKernel P] [IsFiniteMeasure ν] in
theorem partialSum_sub (hinv : P ∘ₘ ν = ν) {f g : X → ℝ}
    (hf : Integrable f ν) (hg : Integrable g ν) (n : ℕ) :
    partialSum P (fun x => f x - g x) n =ᵐ[ν]
      fun x => partialSum P f n x - partialSum P g n x := by
  induction n with
  | zero => exact ae_of_all _ fun _ => by simp [partialSum]
  | succ n ih =>
      have he : P ∘ₘ ν = (1 : ℝ≥0∞) • ν := by simpa using hinv
      filter_upwards [KernelLp.kint_congr he ih,
        Measure.ae_integrable_of_integrable_comp
          (hinv.symm ▸ integrable_partialSum hinv hf n),
        Measure.ae_integrable_of_integrable_comp
          (hinv.symm ▸ integrable_partialSum hinv hg n)] with x hx hfx hgx
      simp only [partialSum]
      rw [hx]
      change f x - g x + (∫ y, partialSum P f n y - partialSum P g n y ∂P x) = _
      rw [integral_sub hfx hgx]
      change f x - g x + (KernelLp.kint P (partialSum P f n) x -
        KernelLp.kint P (partialSum P g n) x) = _
      ring

end

end ConditionedStableLaws.KernelMaximal
