import ConditionedStableLaws.MarkovPairs
import ConditionedStableLaws.PathSurvival

/-!
# A Feynman–Kac formula for Markov trajectories

For a Markov kernel `K`, bounded measurable functions `φ₀, …, φₙ₋₁` and `h` (real or complex
valued),

`E_x[φ₀(X₀) ⋯ φₙ₋₁(Xₙ₋₁) h(Xₙ)] = (φ₀ K φ₁ K ⋯ φₙ₋₁ K h)(x)`.

For the canonical absorbing chain, with observables extended by zero at the cemetery, this becomes a
formula for `E_x[φ₀(X₀) ⋯ φₙ₋₁(Xₙ₋₁) ; τ > n]` in terms of the killed kernel. It covers products of
finitely many observations and the twisted operators of the spectral method.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace ConditionedStableLaws.FeynmanKac

noncomputable section

open QProcessLimit

variable {𝕜 : Type*} [RCLike 𝕜]

section Markov

variable {X : Type*} [MeasurableSpace X] (K : Kernel X X) [IsMarkovKernel K]

/-- The operator word `φ₀ K φ₁ K ⋯ φₙ₋₁ K h`, built from the right. -/
def word (φ : ℕ → X → 𝕜) : ℕ → (X → 𝕜) → X → 𝕜
  | 0, h => h
  | n + 1, h => word φ n (fun y => φ n y * ∫ z, h z ∂K y)

/-- Extending a finite history to a path (beyond its horizon by its last state). -/
def extendHistory (n : ℕ) (h : History X n) : ℕ → X :=
  fun i => if hi : i ≤ n then h ⟨i, Finset.mem_Iic.2 hi⟩ else last n h

theorem measurable_extendHistory (n : ℕ) : Measurable (extendHistory (X := X) n) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ≤ n
  · simp only [extendHistory, hi, dite_true]
    exact measurable_pi_apply _
  · simp only [extendHistory, hi, dite_false]
    exact measurable_pi_apply _

omit [MeasurableSpace X] in
theorem extendHistory_restrict (n : ℕ) (ω : ℕ → X) {i : ℕ} (hi : i ≤ n) :
    extendHistory n (Preorder.frestrictLe n ω) i = ω i := by
  simp [extendHistory, hi, Preorder.frestrictLe]

theorem integral_bdd_le {h : X → 𝕜} {B : ℝ} (hB : ∀ y, ‖h y‖ ≤ B) (y : X) :
    ‖∫ z, h z ∂K y‖ ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := K y) (Eventually.of_forall hB)
  simpa using this

/-- **Feynman–Kac formula** for bounded measurable observables. -/
theorem integral_prod_eq_word (φ : ℕ → X → 𝕜) (hφ : ∀ i, Measurable (φ i)) {A : ℝ}
    (hA : ∀ i y, ‖φ i y‖ ≤ A) (n : ℕ) :
    ∀ (h : X → 𝕜), Measurable h → ∀ B : ℝ, (∀ y, ‖h y‖ ≤ B) → ∀ x : X,
      ∫ ω, (∏ i ∈ Finset.range n, φ i (ω i)) * h (ω n) ∂pathMeasure K x = word K φ n h x := by
  induction n with
  | zero =>
      intro h hh B hB x
      simp only [Finset.range_zero, Finset.prod_empty, one_mul, word]
      rw [← integral_map (measurable_pi_apply 0).aemeasurable hh.aestronglyMeasurable,
        MarkovPairs.map_single K x 0]
      change ∫ y, h y ∂(Kernel.id x) = h x
      rw [Kernel.id_apply, integral_dirac' _ _ hh.stronglyMeasurable]
  | succ n ih =>
      intro h hh B hB x
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
      have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 x)
      have hKh : Measurable (fun y => ∫ z, h z ∂K y) :=
        (hh.stronglyMeasurable.integral_kernel (κ := K)).measurable
      set Φ : History X n → 𝕜 := fun hist =>
        ∏ i ∈ Finset.range (n + 1), φ i (extendHistory n hist i)
      have hΦm : Measurable Φ := Finset.measurable_prod _ fun i _ =>
        (hφ i).comp ((measurable_pi_apply i).comp (measurable_extendHistory n))
      have hΦb (hist : History X n) : ‖Φ hist‖ ≤ A ^ (n + 1) := by
        simp only [Φ]
        rw [norm_prod]
        calc ∏ i ∈ Finset.range (n + 1), ‖φ i (extendHistory n hist i)‖
            ≤ ∏ _i ∈ Finset.range (n + 1), A :=
              Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hA i _)
          _ = A ^ (n + 1) := by rw [Finset.prod_const, Finset.card_range]
      set G : History X n × X → 𝕜 := fun p => Φ p.1 * h p.2
      have hGm : Measurable G := (hΦm.comp measurable_fst).mul (hh.comp measurable_snd)
      have hpair : Measurable (fun ω : ℕ → X => (Preorder.frestrictLe n ω, ω (n + 1))) :=
        (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
      have hG_eq (ω : ℕ → X) : (∏ i ∈ Finset.range (n + 1), φ i (ω i)) * h (ω (n + 1)) =
          G (Preorder.frestrictLe n ω, ω (n + 1)) := by
        simp only [G, Φ]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [extendHistory_restrict n ω (by have := Finset.mem_range.1 hi; omega)]
      have hGi : Integrable G (historyLaw K x n ⊗ₘ historyKernel K n) := by
        refine Integrable.of_bound hGm.aestronglyMeasurable (A ^ (n + 1) * B)
          (Eventually.of_forall fun p => ?_)
        simp only [G, norm_mul]
        exact mul_le_mul (hΦb _) (hB _) (norm_nonneg _) (pow_nonneg hA0 _)
      have hlaw : historyLaw K x n ⊗ₘ historyKernel K n =
          (pathMeasure K x).map (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) :=
        Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      -- Integrate out the last step.
      have hstep : ∫ ω, (∏ i ∈ Finset.range (n + 1), φ i (ω i)) * h (ω (n + 1)) ∂pathMeasure K x =
          ∫ hist, Φ hist * ∫ y, h y ∂K (last n hist) ∂historyLaw K x n := by
        simp_rw [hG_eq]
        rw [← integral_map hpair.aemeasurable (hlaw ▸ hGm.aestronglyMeasurable), ← hlaw,
          Measure.integral_compProd hGi]
        apply integral_congr_ae
        refine Eventually.of_forall fun hist => ?_
        show ∫ y, Φ hist * h y ∂(K (last n hist)) = Φ hist * ∫ y, h y ∂K (last n hist)
        exact integral_const_mul _ _
      -- Back to the path, with one fewer observation.
      have hback : ∫ hist, Φ hist * ∫ y, h y ∂K (last n hist) ∂historyLaw K x n =
          ∫ ω, (∏ i ∈ Finset.range n, φ i (ω i)) * (φ n (ω n) * ∫ y, h y ∂K (ω n))
            ∂pathMeasure K x := by
        unfold historyLaw
        rw [integral_map (Preorder.measurable_frestrictLe n).aemeasurable
          ((hΦm.mul (hKh.comp (measurable_pi_apply _))).aestronglyMeasurable)]
        apply integral_congr_ae
        refine Eventually.of_forall fun ω => ?_
        simp only [Φ, Finset.prod_range_succ]
        rw [Finset.prod_congr rfl (fun i hi => by
          rw [extendHistory_restrict n ω (by have := Finset.mem_range.1 hi; omega)]),
          extendHistory_restrict n ω le_rfl]
        simp only [last, Preorder.frestrictLe, Finset.restrict]
        ring
      rw [hstep, hback]
      exact ih (fun y => φ n y * ∫ z, h z ∂K y) ((hφ n).mul hKh) (A * B)
        (fun y => by
          rw [norm_mul]
          exact mul_le_mul (hA n y) (integral_bdd_le K hB y) (norm_nonneg _) hA0) x

end Markov

section Canonical

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Extension by zero at the cemetery. -/
def ext (f : M → 𝕜) : Option M → 𝕜
  | none => 0
  | some y => f y

omit [MeasurableSpace M] in
@[simp] theorem ext_none (f : M → 𝕜) : ext f none = 0 := rfl
omit [MeasurableSpace M] in
@[simp] theorem ext_some (f : M → 𝕜) (y : M) : ext f (some y) = f y := rfl

theorem measurable_ext {f : M → 𝕜} (hf : Measurable f) : Measurable (ext f) := by
  intro A hA
  change MeasurableSet (Option.some ⁻¹' (ext f ⁻¹' A))
  exact hf hA

omit [MeasurableSpace M] in
theorem norm_ext_le {f : M → 𝕜} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, ‖f y‖ ≤ B) (z : Option M) :
    ‖ext f z‖ ≤ B := by
  cases z with
  | none => simpa using hB0
  | some y => exact hB y

/-- The killed-kernel operator word `φ₀ K φ₁ K ⋯ φₙ₋₁ K h`. -/
def killedWord (φ : ℕ → M → 𝕜) : ℕ → (M → 𝕜) → M → 𝕜
  | 0, h => h
  | n + 1, h => killedWord φ n (fun y => φ n y * ∫ z, h z ∂C.killedTransition y)

theorem integral_ext_transition (h : M → 𝕜) (y : M) :
    ∫ z, ext h z ∂C.transition (some y) = ∫ z, h z ∂C.killedTransition y := by
  have hK : C.killedTransition y = (C.transition (some y)).comap Option.some := by
    ext A hA
    rw [C.killedTransition_apply y A hA, measurableEmbedding_some_state.comap_apply]
  rw [hK, ← show ∫ z, ext h z ∂((C.transition (some y)).comap Option.some).map Option.some =
      ∫ z, h z ∂(C.transition (some y)).comap Option.some from
    measurableEmbedding_some_state.integral_map _, measurableEmbedding_some_state.map_comap]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  cases z with
  | none => rfl
  | some w => exact absurd ⟨w, rfl⟩ hz

theorem word_ext (φ : ℕ → M → 𝕜) (n : ℕ) :
    ∀ h : M → 𝕜, word C.transition (fun i => ext (φ i)) n (ext h) = ext (killedWord C φ n h) := by
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      have hfun : (fun z => ext (φ n) z * ∫ w, ext h w ∂C.transition z) =
          ext (fun y => φ n y * ∫ z, h z ∂C.killedTransition y) := by
        funext z
        cases z with
        | none => simp
        | some y => simp only [ext_some, integral_ext_transition]
      change word C.transition (fun i => ext (φ i)) n
        (fun z => ext (φ n) z * ∫ w, ext h w ∂C.transition z) = _
      rw [hfun, ih]
      rfl

/-- **Feynman–Kac formula for the killed chain.** -/
theorem integral_prod_eq_killedWord (φ : ℕ → M → 𝕜) (hφ : ∀ i, Measurable (φ i)) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ i y, ‖φ i y‖ ≤ A) (n : ℕ) {h : M → 𝕜} (hh : Measurable h) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ y, ‖h y‖ ≤ B) (x : M) :
    ∫ ω, (∏ i ∈ Finset.range n, ext (φ i) (ω i)) * ext h (ω n) ∂C.pathMeasure x =
      killedWord C φ n h x := by
  have := integral_prod_eq_word C.transition (fun i => ext (φ i)) (fun i => measurable_ext (hφ i))
    (fun i z => norm_ext_le hA0 (hA i) z) n (ext h) (measurable_ext hh) B (norm_ext_le hB0 hB)
    (some x)
  rw [word_ext] at this
  exact this

/-- The survival-weighted expectation `E_x[φ₀(X₀) ⋯ φₙ₋₁(Xₙ₋₁) ; τ > n]`. -/
theorem integral_prod_survival (φ : ℕ → M → 𝕜) (hφ : ∀ i, Measurable (φ i)) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ i y, ‖φ i y‖ ≤ A) (n : ℕ) (x : M) :
    ∫ ω, (CanonicalChain.survival n).indicator
        (fun ω => ∏ i ∈ Finset.range n, ext (φ i) (ω i)) ω ∂C.pathMeasure x =
      killedWord C φ n (fun _ => 1) x := by
  rw [← integral_prod_eq_killedWord C φ hφ hA0 hA n measurable_const zero_le_one
    (fun _ => by simp) x]
  apply integral_congr_ae
  filter_upwards [C.ae_mem_survival_iff x n] with ω hω
  by_cases hs : ω ∈ CanonicalChain.survival n
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hω.1 hs)
    rw [Set.indicator_of_mem hs, hy, ext_some, mul_one]
  · have hn : ω n = none := by
      by_contra h'
      exact hs (hω.2 h')
    rw [Set.indicator_of_notMem hs, hn, ext_none, mul_zero]

end Canonical

end

end ConditionedStableLaws.FeynmanKac
