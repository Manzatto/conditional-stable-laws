import ConditionedStableLaws.QProcessLimit
import ConditionedStableLaws.KernelMixing

/-!
# Multitime observations under the conditioned trajectory law

The Markov product identity below is derived from the constructed trajectory law, through its
finite-history Markov property. Observations are nonnegative; in particular measurable-set
indicators are covered without integrability assumptions. The killed-kernel formula includes the
remaining survival gap.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section
namespace ConditionedStableLaws.PathMixing

variable {M : Type*} [MeasurableSpace M]
open QProcessLimit

/-- Gaps are measured from the preceding observation, starting at time zero. -/
def totalTime (w : List (ℕ × (M → ℝ≥0∞))) : ℕ := (w.map Prod.fst).sum

def pathProduct : List (ℕ × (M → ℝ≥0∞)) → (ℕ → M) → ℝ≥0∞
  | [], _ => 1
  | (n, f) :: w, ω => f (ω n) * pathProduct w (fun k => ω (n + k))

def historyProduct : (w : List (ℕ × (M → ℝ≥0∞))) →
    History M (totalTime w) → ℝ≥0∞
  | [], _ => 1
  | (n, f) :: w, h =>
      f (h ⟨n, Finset.mem_Iic.mpr (Nat.le_add_right n (totalTime w))⟩) *
      historyProduct w (fun i => h ⟨n + i.val,
        Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp i.property) n)⟩)

theorem measurable_historyProduct (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, Measurable p.2) : Measurable (historyProduct w) := by
  induction w with
  | nil => exact measurable_const
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      change Measurable (fun h : History M (n + totalTime w) =>
        f (h ⟨n, Finset.mem_Iic.mpr (Nat.le_add_right n (totalTime w))⟩) *
          historyProduct w (fun i => h ⟨n + i.val,
            Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp i.property) n)⟩))
      exact ((hw (n, f) (by simp)).comp (measurable_pi_apply _)).mul
        ((ih (fun p hp => hw p (by simp [hp]))).comp
          (Measurable.of_eval (fun _ => measurable_pi_apply _)))

omit [MeasurableSpace M] in
@[simp] theorem historyProduct_restrict (w : List (ℕ × (M → ℝ≥0∞)))
    (ω : ℕ → M) :
    historyProduct w (Preorder.frestrictLe (totalTime w) ω) = pathProduct w ω := by
  induction w generalizing ω with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      change f (ω n) * historyProduct w
        (Preorder.frestrictLe (totalTime w) (fun k => ω (n + k))) = _
      rw [ih]
      rfl

omit [MeasurableSpace M] in
@[simp] theorem totalTime_append (w v : List (ℕ × (M → ℝ≥0∞))) :
    totalTime (w ++ v) = totalTime w + totalTime v := by
  simp [totalTime]

omit [MeasurableSpace M] in
theorem pathProduct_append_singleton (w : List (ℕ × (M → ℝ≥0∞)))
    (n : ℕ) (f : M → ℝ≥0∞) (ω : ℕ → M) :
    pathProduct (w ++ [(n, f)]) ω = pathProduct w ω * f (ω (totalTime w + n)) := by
  induction w generalizing ω with
  | nil => simp [pathProduct, totalTime]
  | cons p w ih =>
      rcases p with ⟨k, g⟩
      simp [pathProduct, ih, totalTime, Nat.add_assoc, mul_assoc]

/-- Nested integrals against powers of the transition kernel. -/
def kernelWord (K : Kernel M M) :
    List (ℕ × (M → ℝ≥0∞)) → (M → ℝ≥0∞) → M → ℝ≥0∞
  | [], g => g
  | (n, f) :: w, g => fun x => ∫⁻ y, f y * kernelWord K w g y ∂(K ^ n) x

theorem measurable_kernelWord (K : Kernel M M) (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, Measurable p.2) (g : M → ℝ≥0∞) (hg : Measurable g) :
    Measurable (kernelWord K w g) := by
  induction w with
  | nil => exact hg
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      exact (Measure.measurable_lintegral ((hw (n, f) (by simp)).mul
        (ih (fun p hp => hw p (by simp [hp]))))).comp (K ^ n).measurable

theorem kernelWord_append_singleton (K : Kernel M M)
    (w : List (ℕ × (M → ℝ≥0∞))) (n : ℕ) (f g : M → ℝ≥0∞) :
    kernelWord K (w ++ [(n, f)]) g =
      kernelWord K w (fun x => ∫⁻ y, f y * g y ∂(K ^ n) x) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨k, h⟩
      simp only [List.cons_append, kernelWord, ih]

/-- The multitime Markov product formula for the trajectory law. -/
theorem lintegral_pathProduct (K : Kernel M M) [IsMarkovKernel K] (x : M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2)
    (g : M → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, pathProduct w ω * g (ω (totalTime w)) ∂QProcessLimit.pathMeasure K x) =
      kernelWord K w g x := by
  induction w using List.reverseRecOn generalizing g with
  | nil =>
      have hm := lintegral_map (hg.comp (measurable_pi_apply
        (⟨0, by simp⟩ : Finset.Iic 0))) (Preorder.measurable_frestrictLe 0)
        (μ := QProcessLimit.pathMeasure K x)
      change (∫⁻ h, g (last 0 h) ∂historyLaw K x 0) = _ at hm
      rw [historyLaw_zero] at hm
      have hl : Measurable (fun h : History M 0 => g (last 0 h)) :=
        hg.comp (measurable_pi_apply _)
      rw [lintegral_dirac' _ hl] at hm
      simpa [pathProduct, totalTime, kernelWord, last] using hm.symm
  | append_singleton w p ih =>
      rcases p with ⟨n, f⟩
      have hw' : ∀ p ∈ w, Measurable p.2 := fun p hp => hw p (by simp [hp])
      have hf : Measurable f := hw (n, f) (by simp)
      let G : M → ℝ≥0∞ := fun y => ∫⁻ z, f z * g z ∂(K ^ n) y
      have hG : Measurable G := (Measure.measurable_lintegral (hf.mul hg)).comp
        (K ^ n).measurable
      calc
        _ = ∫⁻ ω, historyProduct w (Preorder.frestrictLe (totalTime w) ω) *
            (f (ω (totalTime w + n)) * g (ω (totalTime w + n)))
              ∂QProcessLimit.pathMeasure K x := by
          apply lintegral_congr
          intro ω
          simp only [historyProduct_restrict, pathProduct_append_singleton, totalTime_append]
          simp [totalTime, mul_assoc]
        _ = ∫⁻ h, historyProduct w h * G (last (totalTime w) h)
              ∂historyLaw K x (totalTime w) :=
          lintegral_history_future K x (totalTime w) n (historyProduct w)
            (measurable_historyProduct w hw') (fun y => f y * g y) (hf.mul hg)
        _ = ∫⁻ ω, pathProduct w ω * G (ω (totalTime w))
              ∂QProcessLimit.pathMeasure K x := by
          have hJ : Measurable (fun h : History M (totalTime w) =>
              historyProduct w h * G (last (totalTime w) h)) :=
            (measurable_historyProduct w hw').mul (hG.comp (measurable_pi_apply _))
          rw [historyLaw, lintegral_map hJ (Preorder.measurable_frestrictLe _)]
          apply lintegral_congr
          intro ω
          change historyProduct w (Preorder.frestrictLe (totalTime w) ω) *
            G (ω (totalTime w)) = _
          rw [historyProduct_restrict]
        _ = kernelWord K w G x := ih hw' G hG
        _ = _ := by rw [kernelWord_append_singleton]

/-- Zero extension of a nonnegative observable to the cemetery state. -/
def liveExtension (f : M → ℝ≥0∞) : Option M → ℝ≥0∞
  | none => 0
  | some x => f x

theorem measurable_liveExtension {f : M → ℝ≥0∞} (hf : Measurable f) :
    Measurable (liveExtension f) := by
  intro A hA
  change MeasurableSet (Option.some ⁻¹' (liveExtension f ⁻¹' A))
  exact hf hA

def liftObservations (w : List (ℕ × (M → ℝ≥0∞))) :
    List (ℕ × (Option M → ℝ≥0∞)) :=
  w.map (fun p => (p.1, liveExtension p.2))

omit [MeasurableSpace M] in
@[simp] theorem totalTime_liftObservations (w : List (ℕ × (M → ℝ≥0∞))) :
    totalTime (liftObservations w) = totalTime w := by
  simp [totalTime, liftObservations, List.map_map, Function.comp_def]

theorem measurable_liftObservations (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, Measurable p.2) :
    ∀ p ∈ liftObservations w, Measurable p.2 := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact measurable_liveExtension (hw q hq)

/-- Removing the cemetery from every nested integral gives the killed kernel word. -/
theorem kernelWord_liveExtension (C : CanonicalChain M)
    (w : List (ℕ × (M → ℝ≥0∞))) (g : M → ℝ≥0∞) (x : M) :
    kernelWord C.transition (liftObservations w) (liveExtension g) (some x) =
      kernelWord C.killedTransition w g x := by
  induction w generalizing x with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      change (∫⁻ y, liveExtension f y *
        kernelWord C.transition (liftObservations w) (liveExtension g) y
        ∂(C.transition ^ n) (some x)) = _
      rw [lintegral_eq_live_comap _ _ (by simp [liveExtension]),
        C.transition_pow_live_comap]
      apply lintegral_congr
      intro y
      simp only [liveExtension, ih]

end ConditionedStableLaws.PathMixing

namespace ConditionedStableLaws.CanonicalChain
open QProcessLimit PathMixing
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Conditional expectation of any nonnegative finite-history functional, with its exact
remaining-survival weight. -/
theorem lintegral_conditioned_history (x : M) (n t : ℕ)
    (F : History (Option M) n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (Preorder.frestrictLe n ω) ∂C.conditionedMeasure x (n + t)) =
      ((C.killedTransition ^ (n + t)) x univ)⁻¹ *
        ∫⁻ h, F h * C.remainingSurvival t (last n h)
          ∂(C.pathMeasure x).map (Preorder.frestrictLe n) := by
  let g := ({none} : Set (Option M))ᶜ.indicator (fun _ => (1 : ℝ≥0∞))
  have hg : Measurable g := measurable_const.indicator measurableSet_cemetery.compl
  have hm := QProcessLimit.lintegral_history_future C.transition (some x) n t F hF g hg
  have hright (z : Option M) : (∫⁻ y, g y ∂(C.transition ^ t) z) =
      C.remainingSurvival t z := by
    simp only [g, lintegral_indicator measurableSet_cemetery.compl, lintegral_const,
      one_mul, Measure.restrict_apply_univ, remainingSurvival]
  simp_rw [hright] at hm
  unfold conditionedMeasure ProbabilityTheory.cond
  rw [lintegral_smul_measure, ← lintegral_indicator (measurableSet_survival (n + t)),
    C.pathMeasure_survival]
  congr 1
  calc
    _ = ∫⁻ ω, F (Preorder.frestrictLe n ω) * g (ω (n + t)) ∂C.pathMeasure x := by
      apply lintegral_congr_ae
      filter_upwards [C.ae_mem_survival_iff x (n + t)] with ω hω
      by_cases hs : ω ∈ survival (n + t) <;> simp [g, hs, ← hω]
    _ = _ := hm

/-- The multitime conditional correlation is exactly a nested killed-kernel
integral, divided by survival probability. All nonnegative measurable
observations are allowed, including bounded observables and indicators.
The final gap `t` is the time from the last observation to conditioning. -/
theorem lintegral_conditioned_pathProduct (x : M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2) (t : ℕ) :
    (∫⁻ ω, pathProduct (liftObservations w) ω
      ∂C.conditionedMeasure x (totalTime w + t)) =
      ((C.killedTransition ^ (totalTime w + t)) x univ)⁻¹ *
        PathMixing.kernelWord C.killedTransition w
          (fun y => (C.killedTransition ^ t) y univ) x := by
  let v := liftObservations w
  have hv : ∀ p ∈ v, Measurable p.2 := measurable_liftObservations w hw
  have he : totalTime v = totalTime w := totalTime_liftObservations w
  have hh := C.lintegral_conditioned_history x (totalTime v) t
    (historyProduct v) (measurable_historyProduct v hv)
  simp only [historyProduct_restrict, he] at hh
  rw [hh]
  congr 1
  have hsurv : C.remainingSurvival t =
      liveExtension (fun y => (C.killedTransition ^ t) y univ) := by
    funext y
    cases y with
    | none => exact C.remainingSurvival_none t
    | some y => exact C.remainingSurvival_some t y
  calc
    _ = ∫⁻ ω, pathProduct v ω * C.remainingSurvival t (ω (totalTime v))
        ∂C.pathMeasure x := by
      have hJ : Measurable (fun h : History (Option M) (totalTime v) =>
          historyProduct v h * C.remainingSurvival t (last (totalTime v) h)) :=
        (measurable_historyProduct v hv).mul
          ((C.measurable_remainingSurvival t).comp (measurable_pi_apply _))
      rw [lintegral_map hJ (Preorder.measurable_frestrictLe _)]
      apply lintegral_congr
      intro ω
      change historyProduct v (Preorder.frestrictLe (totalTime v) ω) *
        C.remainingSurvival t (ω (totalTime v)) = _
      rw [historyProduct_restrict]
    _ = PathMixing.kernelWord C.transition v (C.remainingSurvival t) (some x) :=
      lintegral_pathProduct C.transition (some x) v hv
        (C.remainingSurvival t) (C.measurable_remainingSurvival t)
    _ = _ := by rw [hsurv]; exact kernelWord_liveExtension C w _ x

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.PathMixing
open StandingHypothesis
variable {M : Type*} [MeasurableSpace M]

/-- Sub-Markov kernels remain sub-Markov under every kernel power. -/
theorem killed_power_mass_le_one (K : KilledKernel M) (n : ℕ) (x : M) :
    (K.kernel ^ n) x univ ≤ 1 := by
  induction n generalizing x with
  | zero => simp [show (1 : Kernel M M) = Kernel.id from rfl]
  | succ n ih =>
      rw [pow_succ]
      change ((K.kernel ^ n) ∘ₖ K.kernel) x univ ≤ 1
      rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
      calc
        _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂K.kernel x := lintegral_mono (fun y => ih y)
        _ = K.kernel x univ := by simp
        _ ≤ 1 := K.mass_le_one x

theorem kernelWord_le_one (K : KilledKernel M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, ∀ y, p.2 y ≤ 1)
    (g : M → ℝ≥0∞) (hg : ∀ y, g y ≤ 1) (x : M) : kernelWord K.kernel w g x ≤ 1 := by
  induction w generalizing x with
  | nil => exact hg x
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      calc
        _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(K.kernel ^ n) x := by
          apply lintegral_mono
          intro y
          simpa only [one_mul] using mul_le_mul' (hw (n, f) (by simp) y)
            (ih (fun p hp => hw p (by simp [hp])) y)
        _ = (K.kernel ^ n) x univ := by simp
        _ ≤ 1 := killed_power_mass_le_one K n x

/-- Real conversion is justified by sub-Markov boundedness at every nested integral. -/
theorem lintegral_power_toReal (K : KilledKernel M) (n : ℕ)
    (f : M → ℝ≥0∞) (hf : Measurable f) (hfb : ∀ y, f y ≤ 1) (x : M) :
    (∫⁻ y, f y ∂(K.kernel ^ n) x).toReal =
      kernelIterate 1 K n (fun y => (f y).toReal) x := by
  induction n generalizing x with
  | zero =>
      change (∫⁻ y, f y ∂Measure.dirac x).toReal = (f x).toReal
      rw [lintegral_dirac' _ hf]
  | succ n ih =>
      rw [pow_succ]
      change (∫⁻ y, f y ∂((K.kernel ^ n) ∘ₖ K.kernel) x).toReal = _
      rw [Kernel.lintegral_comp _ _ _ hf]
      have hm : Measurable (fun y => ∫⁻ z, f z ∂(K.kernel ^ n) y) :=
        (Measure.measurable_lintegral hf).comp (K.kernel ^ n).measurable
      have hb (y : M) : (∫⁻ z, f z ∂(K.kernel ^ n) y) ≤ 1 := by
        calc
          _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(K.kernel ^ n) y := lintegral_mono hfb
          _ = (K.kernel ^ n) y univ := by simp
          _ ≤ 1 := killed_power_mass_le_one K n y
      rw [← integral_toReal hm.aemeasurable
        (Filter.Eventually.of_forall (fun y => (hb y).trans_lt ENNReal.one_lt_top))]
      simp only [kernelIterate, one_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall ih

/-- A real nested word with the pointwise representatives of bounded nonnegative observations. -/
def realKernelWord (K : KilledKernel M) :
    List (ℕ × (M → ℝ≥0∞)) → (M → ℝ) → M → ℝ
  | [], g => g
  | (n, f) :: w, g => kernelIterate 1 K n
      (fun y => (f y).toReal * realKernelWord K w g y)

theorem kernelWord_toReal (K : KilledKernel M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2)
    (hwb : ∀ p ∈ w, ∀ y, p.2 y ≤ 1)
    (g : M → ℝ≥0∞) (hg : Measurable g) (hgb : ∀ y, g y ≤ 1) (x : M) :
    (kernelWord K.kernel w g x).toReal = realKernelWord K w (fun y => (g y).toReal) x := by
  induction w generalizing x with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      have hwm : ∀ p ∈ w, Measurable p.2 := fun p hp => hw p (by simp [hp])
      have hwb' : ∀ p ∈ w, ∀ y, p.2 y ≤ 1 := fun p hp => hwb p (by simp [hp])
      change (∫⁻ y, f y * kernelWord K.kernel w g y ∂(K.kernel ^ n) x).toReal = _
      have hm : Measurable (fun y => f y * kernelWord K.kernel w g y) :=
        (hw (n, f) (by simp)).mul (measurable_kernelWord K.kernel w hwm g hg)
      have hb : ∀ y, f y * kernelWord K.kernel w g y ≤ 1 := by
        intro y
        simpa only [one_mul] using
          mul_le_mul' (hwb (n, f) (by simp) y) (kernelWord_le_one K w hwb' g hgb y)
      rw [lintegral_power_toReal K n (fun y => f y * kernelWord K.kernel w g y) hm hb x]
      have he : (fun y => (f y * kernelWord K.kernel w g y).toReal) =
          (fun y => (f y).toReal * realKernelWord K w (fun z => (g z).toReal) y) := by
        funext y
        rw [ENNReal.toReal_mul, ih hwm hwb']
      rw [he]
      rfl

theorem measurable_pathProduct (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, Measurable p.2) : Measurable (pathProduct w) := by
  have hm : Measurable (fun ω : ℕ → M =>
      historyProduct w (Preorder.frestrictLe (totalTime w) ω)) :=
    (measurable_historyProduct w hw).comp
      (Preorder.measurable_frestrictLe (totalTime w))
  simpa only [Function.comp_def, historyProduct_restrict] using hm

omit [MeasurableSpace M] in
theorem pathProduct_le_one (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, ∀ y, p.2 y ≤ 1) (ω : ℕ → M) : pathProduct w ω ≤ 1 := by
  induction w generalizing ω with
  | nil => exact le_rfl
  | cons p w ih =>
      rcases p with ⟨n, f⟩
      simpa only [pathProduct, one_mul] using mul_le_mul' (hw (n, f) (by simp) (ω n))
        (ih (fun p hp => hw p (by simp [hp])) (fun k => ω (n + k)))

omit [MeasurableSpace M] in
theorem liftObservations_le_one (w : List (ℕ × (M → ℝ≥0∞)))
    (hw : ∀ p ∈ w, ∀ y, p.2 y ≤ 1) :
    ∀ p ∈ liftObservations w, ∀ y, p.2 y ≤ 1 := by
  intro p hp y
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  cases y with
  | none => exact bot_le
  | some y => exact hw q hq y

end ConditionedStableLaws.PathMixing

namespace ConditionedStableLaws.CanonicalChain
open PathMixing StandingHypothesis
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- The real expectation of a product of bounded nonnegative observations is
exactly the real nested integral ratio used by the spectral mixing estimate.
It also respects the zero-measure convention at a null survival event. -/
theorem integral_conditioned_pathProduct (x : M)
    (w : List (ℕ × (M → ℝ≥0∞))) (hw : ∀ p ∈ w, Measurable p.2)
    (hwb : ∀ p ∈ w, ∀ y, p.2 y ≤ 1) (t : ℕ) :
    (∫ ω, (pathProduct (liftObservations w) ω).toReal
      ∂C.conditionedMeasure x (totalTime w + t)) =
      realKernelWord C.toKilledKernel w
        (kernelIterate 1 C.toKilledKernel t (fun _ => 1)) x /
          ((C.killedTransition ^ (totalTime w + t)) x).real univ := by
  rw [integral_toReal (measurable_pathProduct _
    (measurable_liftObservations w hw)).aemeasurable
    (Filter.Eventually.of_forall (fun ω => (pathProduct_le_one _
      (liftObservations_le_one w hwb) ω).trans_lt ENNReal.one_lt_top)),
    C.lintegral_conditioned_pathProduct x w hw t, ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  have hm : Measurable (fun y => (C.killedTransition ^ t) y univ) :=
    (C.killedTransition ^ t).measurable_coe MeasurableSet.univ
  have hword := kernelWord_toReal C.toKilledKernel w hw hwb _ hm
    (fun y => C.killedTransition_pow_mass_le_one y t) x
  change (PathMixing.kernelWord C.killedTransition w _ x).toReal = _ at hword
  rw [hword]
  have ht : (fun y => ((C.killedTransition ^ t) y univ).toReal) =
      kernelIterate 1 C.toKilledKernel t (fun _ => 1) := by
    funext y
    exact (kernelIterate_one_eq_mass C.toKilledKernel t y).symm
  rw [ht]
  exact mul_comm _ _

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.StandingHypothesis
open PathMixing
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} {K : KilledKernel M}

/-- Passing to L∞ classes only uses almost-everywhere representative equalities.
In particular no point evaluation of an L∞ class enters the path formula. -/
theorem HypothesisH.realKernelWord_ae (h : HypothesisH ρ K)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hf : ∀ p ∈ w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2)
    (g : M → ℝ) :
    realKernelWord K (w.map (fun p => (p.1, f p.2))) g =ᵐ[ρ]
      StandingHypothesis.kernelWord 1 K w g := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      apply h.kernelIterate_congr_ae
      filter_upwards [hf (n, A) (by simp), ih (fun p hp => hf p (by simp [hp]))] with y hy hw
      rw [hy, hw]

/-- The extra initial transition makes the identification pointwise at every specified starting
state. -/
theorem HypothesisH.realKernelWord_first_step (h : HypothesisH ρ K)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hf : ∀ p ∈ w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2)
    (g : M → ℝ) (x : M) :
    kernelIterate 1 K 1 (realKernelWord K (w.map (fun p => (p.1, f p.2))) g) x =
      kernelIterate 1 K 1 (StandingHypothesis.kernelWord 1 K w g) x :=
  h.kernelIterate_succ_congr 1 0 (h.realKernelWord_ae w f hf g) x

end ConditionedStableLaws.StandingHypothesis

namespace ConditionedStableLaws.CanonicalChain
open PathMixing StandingHypothesis
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  (C : CanonicalChain M) {ρ : Measure M}

/-- Exact canonical-path version of the kernel mixing ratio. The leading `(1,1)` is the initial
smoothing step. Each observation has a measurable representative in `[0,1]`, which covers all
rare-event indicators; its L∞ class enters only through an AE equality. -/
theorem integral_conditioned_pathProduct_lp (h : HypothesisH ρ C.toKilledKernel)
    (x : M) (w : List (ℕ × Lp ℝ ∞ ρ)) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfm : ∀ p ∈ w, Measurable (f p.2))
    (hfb : ∀ p ∈ w, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2) (t : ℕ) :
    (∫ ω, (pathProduct (liftObservations
        ((1, fun _ => 1) :: w.map (fun p => (p.1, f p.2)))) ω).toReal
      ∂C.conditionedMeasure x ((w.map Prod.fst).sum + t + 1)) =
      kernelIterate 1 C.toKilledKernel 1
        (StandingHypothesis.kernelWord 1 C.toKilledKernel w
          (kernelIterate 1 C.toKilledKernel t (fun _ => 1))) x /
        ((C.killedTransition ^ ((w.map Prod.fst).sum + t + 1)) x).real univ := by
  let v : List (ℕ × (M → ℝ≥0∞)) :=
    (1, fun _ => 1) :: w.map (fun p => (p.1, f p.2))
  have hvm : ∀ p ∈ v, Measurable p.2 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact measurable_const
    · rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
      exact hfm q hq
  have hvb : ∀ p ∈ v, ∀ y, p.2 y ≤ 1 := by
    intro p hp y
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_rfl
    · rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
      exact hfb q hq y
  have htime : totalTime v + t = (w.map Prod.fst).sum + t + 1 := by
    simp [v, totalTime, List.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]
  have he := C.integral_conditioned_pathProduct x v hvm hvb t
  rw [htime] at he
  change _ = realKernelWord C.toKilledKernel v _ x / _ at he
  rw [he]
  congr 1
  change kernelIterate 1 C.toKilledKernel 1
      (fun y => (1 : ℝ≥0∞).toReal * realKernelWord C.toKilledKernel
        (w.map (fun p => (p.1, f p.2))) (kernelIterate 1 C.toKilledKernel t (fun _ => 1)) y) x = _
  simp only [ENNReal.toReal_one, one_mul]
  exact h.realKernelWord_first_step w f hrep _ x

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.CanonicalChain
open PathMixing StandingHypothesis ConditionalMixing
variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  (C : CanonicalChain M) {ρ : Measure M}

/-- The spectral word estimate for canonical-path products under the survival-conditioned law, given
the spectral decomposition and its rate. -/
theorem conditioned_path_mixing (h : HypothesisH ρ C.toKilledKernel)
    (c : ℝ) (hc : c ≠ 0) (μ : Lp ℝ ∞ ρ →L[ℝ] ℝ) (η one : Lp ℝ ∞ ρ) (x : M)
    (hone : μ one = 1) (hone_rep : one =ᵐ[ρ] fun _ => (1 : ℝ))
    (ha : 0 < h.stepEvaluation c x η)
    (w : List (ℕ × Lp ℝ ∞ ρ)) (f : Lp ℝ ∞ ρ → M → ℝ≥0∞)
    (hfm : ∀ p ∈ w, Measurable (f p.2))
    (hfb : ∀ p ∈ w, ∀ y, f p.2 y ≤ 1)
    (hrep : ∀ p ∈ w, (fun y => (f p.2 y).toReal) =ᵐ[ρ] p.2)
    (t m : ℕ) (U A θ : ℝ)
    (hU : 1 ≤ U) (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ‖rankOne μ η‖ ≤ U)
    (hQ : ∀ n, 1 ≤ n → ‖(c • h.transitionOperator) ^ n‖ ≤ U)
    (hgap : ∀ n, 1 ≤ n → ‖(c • h.transitionOperator) ^ n - rankOne μ η‖ ≤ A * θ ^ n)
    (htimes : ∀ p ∈ w, 1 ≤ p.1 ∧ m ≤ p.1) (ht : 1 ≤ t ∧ m ≤ t)
    (hsmall : ‖h.stepEvaluation c x‖ * A * θ ^ m * ‖one‖ ≤ h.stepEvaluation c x η / 2) :
    |(∫ ω, (pathProduct (liftObservations
        ((1, fun _ => 1) :: w.map (fun p => (p.1, f p.2)))) ω).toReal
      ∂C.conditionedMeasure x ((w.map Prod.fst).sum + t + 1)) -
        (w.map fun p => μ (lpMultiplication ρ p.2 η)).prod| ≤
      (2 / h.stepEvaluation c x η) * ‖h.stepEvaluation c x‖ * A * ‖one‖ *
        ((w.length + 1 : ℝ) * U ^ (w.length + 1) + (‖μ‖ * ‖η‖) ^ w.length) *
        θ ^ m * (w.map fun p => ‖p.2‖).prod := by
  rw [C.integral_conditioned_pathProduct_lp h x w f hfm hfb hrep t]
  exact h.kernel_mixing c hc μ η one x hone hone_rep ha w t m U A θ
    hU hA hθ0 hθ1 hP hQ hgap htimes ht hsmall

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.PathMixing
variable {M : Type*} [MeasurableSpace M]

/-- The event that the trajectory visits each target at the time specified by the consecutive gaps.
A cemetery state never belongs to a target. -/
def pathEvent : List (ℕ × Set M) → Set (ℕ → Option M)
  | [] => univ
  | (n, A) :: w => {ω | ω n ∈ Option.some '' A ∧ (fun k => ω (n + k)) ∈ pathEvent w}

def indicatorObservations (w : List (ℕ × Set M)) : List (ℕ × (M → ℝ≥0∞)) :=
  w.map (fun p => (p.1, p.2.indicator (fun _ => 1)))

theorem measurable_indicatorObservations (w : List (ℕ × Set M))
    (hw : ∀ p ∈ w, MeasurableSet p.2) :
    ∀ p ∈ indicatorObservations w, Measurable p.2 := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact measurable_const.indicator (hw q hq)

omit [MeasurableSpace M] in
theorem pathProduct_indicators (w : List (ℕ × Set M)) (ω : ℕ → Option M) :
    pathProduct (liftObservations (indicatorObservations w)) ω =
      (pathEvent w).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  induction w generalizing ω with
  | nil => simp [indicatorObservations, liftObservations, pathProduct, pathEvent]
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      change liveExtension (A.indicator (fun _ => 1)) (ω n) *
        pathProduct (liftObservations (indicatorObservations w)) (fun k => ω (n + k)) = _
      rw [ih]
      cases hy : ω n with
      | none => simp [liveExtension, pathEvent, hy]
      | some y =>
          by_cases hA : y ∈ A <;>
            by_cases ht : (fun k => ω (n + k)) ∈ pathEvent w <;>
            simp [liveExtension, pathEvent, hy, hA, ht]

theorem measurableSet_pathEvent (w : List (ℕ × Set M))
    (hw : ∀ p ∈ w, MeasurableSet p.2) : MeasurableSet (pathEvent w) := by
  have he : pathEvent w =
      pathProduct (liftObservations (indicatorObservations w)) ⁻¹' {1} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, pathProduct_indicators]
    by_cases hω : ω ∈ pathEvent w <;> simp [hω]
  rw [he]
  exact (measurable_pathProduct _ (measurable_liftObservations _
    (measurable_indicatorObservations w hw))) (measurableSet_singleton 1)

end ConditionedStableLaws.PathMixing

namespace ConditionedStableLaws.CanonicalChain
open PathMixing
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Exact multitime rare-event probabilities under survival conditioning, with target membership at
every observation time. -/
theorem conditioned_multitime_event (x : M) (w : List (ℕ × Set M))
    (hw : ∀ p ∈ w, MeasurableSet p.2) (t : ℕ) :
    C.conditionedMeasure x (totalTime (indicatorObservations w) + t) (pathEvent w) =
      ((C.killedTransition ^ (totalTime (indicatorObservations w) + t)) x univ)⁻¹ *
        PathMixing.kernelWord C.killedTransition (indicatorObservations w)
          (fun y => (C.killedTransition ^ t) y univ) x := by
  have he := C.lintegral_conditioned_pathProduct x (indicatorObservations w)
    (measurable_indicatorObservations w hw) t
  simp_rw [pathProduct_indicators] at he
  rw [lintegral_indicator (measurableSet_pathEvent w hw)] at he
  simpa using he

end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.CanonicalChain
open PathMixing StandingHypothesis
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- The same multitime event formula in real-valued probabilities, with real iterated integrals,
directly suitable for factorial-moment weights. -/
theorem conditioned_multitime_event_real (x : M) (w : List (ℕ × Set M))
    (hw : ∀ p ∈ w, MeasurableSet p.2) (t : ℕ) :
    (C.conditionedMeasure x (totalTime (indicatorObservations w) + t)).real (pathEvent w) =
      realKernelWord C.toKilledKernel (indicatorObservations w)
        (kernelIterate 1 C.toKilledKernel t (fun _ => 1)) x /
          ((C.killedTransition ^ (totalTime (indicatorObservations w) + t)) x).real univ := by
  have hb : ∀ p ∈ indicatorObservations w, ∀ y, p.2 y ≤ 1 := by
    intro p hp y
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    by_cases hy : y ∈ q.2 <;> simp [hy]
  have he := C.integral_conditioned_pathProduct x (indicatorObservations w)
    (measurable_indicatorObservations w hw) hb t
  have hm := integral_toReal
    ((measurable_pathProduct _ (measurable_liftObservations _
      (measurable_indicatorObservations w hw))).aemeasurable
      (μ := C.conditionedMeasure x (totalTime (indicatorObservations w) + t)))
    (Filter.Eventually.of_forall (fun ω => (pathProduct_le_one _
      (liftObservations_le_one _ hb) ω).trans_lt ENNReal.one_lt_top))
  rw [hm] at he
  simp_rw [pathProduct_indicators] at he
  rw [lintegral_indicator (measurableSet_pathEvent w hw)] at he
  simpa [Measure.real] using he

end ConditionedStableLaws.CanonicalChain
