import ConditionedStableLaws.DoobTransform
import ConditionedStableLaws.PathSurvival

/-!
# Finite-horizon laws of the Doob process

Identities for the Ionescu–Tulcea trajectory laws of the Doob process.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ConditionedStableLaws.QProcessLimit
noncomputable section

variable {M : Type*} [MeasurableSpace M]

abbrev History (M : Type*) (n : ℕ) := (i : Finset.Iic n) → M

def last (n : ℕ) (h : History M n) : M := h ⟨n, by simp⟩

def append (n : ℕ) (p : History M n × M) : History M (n + 1) :=
  fun i => if hi : i.val ≤ n then p.1 ⟨i.val, Finset.mem_Iic.mpr hi⟩ else p.2

theorem measurable_append (n : ℕ) : Measurable (append (M := M) n) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.val ≤ n
  · simpa only [append, dite_eq_left hi, Function.comp_def] using (measurable_pi_apply
      (⟨i.val, Finset.mem_Iic.mpr hi⟩ : Finset.Iic n)).comp measurable_fst
  · simpa only [append, dite_eq_right hi] using (measurable_snd :
      Measurable (Prod.snd : History M n × M → M))

omit [MeasurableSpace M] in
@[simp] theorem last_append (n : ℕ) (p : History M n × M) :
    last (n + 1) (append n p) = p.2 := by simp [last, append]

omit [MeasurableSpace M] in
theorem append_restrict (n : ℕ) (ω : ℕ → M) :
    append n (Preorder.frestrictLe n ω, ω (n + 1)) = Preorder.frestrictLe (n + 1) ω := by
  funext i
  by_cases hi : i.val ≤ n
  · simp [append, hi, Preorder.frestrictLe]
  · have he : i.val = n + 1 := by have := Finset.mem_Iic.mp i.property; omega
    simp [append, Preorder.frestrictLe, he]

def historyKernel (K : Kernel M M) (n : ℕ) : Kernel (History M n) M :=
  K.comap (last n) (measurable_pi_apply _)

instance historyKernel_markov (K : Kernel M M) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (historyKernel K n) :=
  Kernel.IsMarkovKernel.comap K (measurable_pi_apply _)

def pathMeasure (K : Kernel M M) [IsMarkovKernel K] (x : M) : Measure (ℕ → M) :=
  Kernel.trajMeasure (Measure.dirac x) (historyKernel K)

instance pathMeasure_probability (K : Kernel M M) [IsMarkovKernel K] (x : M) :
    IsProbabilityMeasure (pathMeasure K x) := by unfold pathMeasure; infer_instance

def historyLaw (K : Kernel M M) [IsMarkovKernel K] (x : M) (n : ℕ) :
    Measure (History M n) := (pathMeasure K x).map (Preorder.frestrictLe n)

instance historyLaw_probability (K : Kernel M M) [IsMarkovKernel K] (x : M) (n : ℕ) :
    IsProbabilityMeasure (historyLaw K x n) :=
  by unfold historyLaw; infer_instance

variable (K : Kernel M M) [IsMarkovKernel K]

theorem historyLaw_zero (x : M) : historyLaw K x 0 = Measure.dirac (fun _ => x) := by
  unfold historyLaw pathMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_dirac' (MeasurableEquiv.piUnique _).symm.measurable]
  rfl

theorem historyLaw_succ (x : M) (n : ℕ) :
    historyLaw K x (n + 1) =
      ((historyLaw K x n) ⊗ₘ historyKernel K n).map (append n) := by
  have hj : historyLaw K x n ⊗ₘ historyKernel K n =
      (pathMeasure K x).map (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  rw [hj, Measure.map_map (measurable_append n)
    ((Preorder.measurable_frestrictLe n).prod (measurable_pi_apply (n + 1)))]
  unfold historyLaw
  congr 1
  funext ω
  exact (append_restrict n ω).symm

theorem lintegral_historyLaw_succ (x : M) (n : ℕ)
    (F : History M (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, F h ∂historyLaw K x (n + 1)) =
      ∫⁻ h, ∫⁻ y, F (append n (h, y)) ∂K (last n h) ∂historyLaw K x n := by
  rw [historyLaw_succ, lintegral_map hF (measurable_append n)]
  exact Measure.lintegral_compProd (hF.comp (measurable_append n))

variable {K}

/-- One transformed step, evaluated by functions on the original state space. -/
theorem lintegral_doob_ambient (d : DoobTransform.EigenData K) (x : d.State)
    (g : M → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y.val ∂d.kernel x) = d.rate⁻¹ * (d.weight x.val)⁻¹ *
      ∫⁻ y, d.weight y * g y ∂K x.val := by
  have hg' : Measurable (fun y : d.State => g y.val) := hg.comp measurable_subtype_coe
  change (∫⁻ y, g y.val ∂d.positiveData.kernel x) = _
  rw [d.positiveData.lintegral_kernel x _ hg']
  congr 1
  change (∫⁻ y : d.State, d.weight y.val * g y.val
    ∂(K x.val).comap Subtype.val) = _
  rw [lintegral_subtype_comap d.measurableSet_liveSet (fun y => d.weight y * g y)]
  apply setLIntegral_eq_of_support_subset
  intro y hy
  exact fun he => hy (by simp [he])


/-- Forget the proof that every state in the transformed history is live. -/
def coeHistory (d : DoobTransform.EigenData K) (n : ℕ)
    (h : History d.State n) : History M n := fun i => (h i).val

omit [IsMarkovKernel K] in
theorem measurable_coeHistory (d : DoobTransform.EigenData K) (n : ℕ) :
    Measurable (coeHistory d n) :=
  Measurable.of_eval (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))

omit [IsMarkovKernel K] in
theorem coeHistory_append (d : DoobTransform.EigenData K) (n : ℕ)
    (h : History d.State n) (y : d.State) :
    coeHistory d (n + 1) (append n (h, y)) = append n (coeHistory d n h, y.val) := by
  funext i
  by_cases hi : i.val ≤ n <;> simp [coeHistory, append, hi]

/-- Exact finite-history change of measure. On the zero set, the eigenrelation forces the weighted
next-step integral to vanish. -/
theorem lintegral_doob_history (d : DoobTransform.EigenData K) (x : d.State)
    (n : ℕ) (F : History M n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, F (coeHistory d n h) ∂historyLaw d.kernel x n) =
      (d.rate⁻¹)^n * (d.weight x.val)⁻¹ *
        ∫⁻ h, d.weight (last n h) * F h ∂historyLaw K x.val n := by
  induction n with
  | zero =>
      have hFc : Measurable (fun h => F (coeHistory d 0 h)) :=
        hF.comp (measurable_coeHistory d 0)
      have hFw : Measurable (fun h => d.weight (last 0 h) * F h) :=
        (d.measurable_weight.comp (measurable_pi_apply _)).mul hF
      rw [historyLaw_zero, historyLaw_zero,
        lintegral_dirac' _ hFc, lintegral_dirac' _ hFw, pow_zero]
      change F (fun _ => x.val) =
        1 * (d.weight x.val)⁻¹ * (d.weight x.val * F (fun _ => x.val))
      rw [one_mul, ENNReal.inv_mul_cancel_left x.property (d.weight_ne_top x.val)]
  | succ n ih =>
      let I : History M n → ℝ≥0∞ := fun h =>
        ∫⁻ y, d.weight y * F (append n (h, y)) ∂K (last n h)
      have hI : Measurable I :=
        ((d.measurable_weight.comp measurable_snd).mul
          (hF.comp (measurable_append n))).lintegral_kernel_prod_right'
          (κ := historyKernel K n)
      let G : History M n → ℝ≥0∞ := fun h =>
        d.rate⁻¹ * (d.weight (last n h))⁻¹ * I h
      have hG : Measurable G :=
        (measurable_const.mul (d.measurable_weight.comp (measurable_pi_apply _)).inv).mul hI
      have hcancel (h : History M n) :
          d.weight (last n h) * ((d.weight (last n h))⁻¹ * I h) = I h := by
        apply ENNReal.mul_inv_cancel_left'
        · intro hz
          have hzero : ∫⁻ y, d.weight y ∂K (last n h) = 0 := by
            rw [d.right_eigen, hz, mul_zero]
          have hae := (lintegral_eq_zero_iff d.measurable_weight).1 hzero
          change (∫⁻ y, d.weight y * F (append n (h, y)) ∂K (last n h)) = 0
          calc
            _ = ∫⁻ _ : M, 0 ∂K (last n h) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with y hy
              simp [hy]
            _ = 0 := by simp
        · intro ht
          exact False.elim (d.weight_ne_top _ ht)
      calc
        _ = ∫⁻ h, ∫⁻ y, F (append n (coeHistory d n h, y.val))
            ∂d.kernel (last n h) ∂historyLaw d.kernel x n := by
          have hFc : Measurable (fun h => F (coeHistory d (n + 1) h)) :=
            hF.comp (measurable_coeHistory d (n + 1))
          rw [lintegral_historyLaw_succ d.kernel x n _ hFc]
          simp_rw [coeHistory_append]
        _ = ∫⁻ h, G (coeHistory d n h) ∂historyLaw d.kernel x n := by
          apply lintegral_congr
          intro h
          exact lintegral_doob_ambient d (last n h) _
            (hF.comp ((measurable_append n).comp measurable_prodMk_left))
        _ = (d.rate⁻¹)^n * (d.weight x.val)⁻¹ *
            ∫⁻ h, d.weight (last n h) * G h ∂historyLaw K x.val n := ih G hG
        _ = (d.rate⁻¹)^n * (d.weight x.val)⁻¹ *
            (d.rate⁻¹ * ∫⁻ h, I h ∂historyLaw K x.val n) := by
          congr 1
          calc
            _ = ∫⁻ h, d.rate⁻¹ * I h ∂historyLaw K x.val n := by
              apply lintegral_congr
              intro h
              change d.weight (last n h) *
                (d.rate⁻¹ * (d.weight (last n h))⁻¹ * I h) = _
              calc
                _ = d.rate⁻¹ * (d.weight (last n h) *
                    ((d.weight (last n h))⁻¹ * I h)) := by ac_rfl
                _ = _ := by rw [hcancel]
            _ = _ := lintegral_const_mul _ hI
        _ = (d.rate⁻¹)^(n + 1) * (d.weight x.val)⁻¹ *
            ∫⁻ h, d.weight (last (n + 1) h) * F h ∂historyLaw K x.val (n + 1) := by
          have hFw : Measurable (fun h => d.weight (last (n + 1) h) * F h) :=
            (d.measurable_weight.comp (measurable_pi_apply _)).mul hF
          rw [lintegral_historyLaw_succ K x.val n _ hFw]
          simp only [last_append]
          rw [pow_succ]
          change _ = _ * _ * ∫⁻ h, I h ∂historyLaw K x.val n
          ac_rfl


/-- The finite-history law of the Doob process has the stated density with respect to the original
finite-history law. -/
theorem doob_historyLaw_eq_withDensity (d : DoobTransform.EigenData K)
    (x : d.State) (n : ℕ) :
    (historyLaw d.kernel x n).map (coeHistory d n) =
      (historyLaw K x.val n).withDensity
        (fun h => (d.rate⁻¹)^n * (d.weight x.val)⁻¹ * d.weight (last n h)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hw : Measurable (fun h : History M n =>
      (d.rate⁻¹)^n * (d.weight x.val)⁻¹ * d.weight (last n h)) :=
    measurable_const.mul (d.measurable_weight.comp (measurable_pi_apply _))
  rw [lintegral_map hF (measurable_coeHistory d n), lintegral_doob_history d x n F hF,
    lintegral_withDensity_eq_lintegral_mul _ hw hF]
  symm
  calc
    _ = ∫⁻ h, ((d.rate⁻¹)^n * (d.weight x.val)⁻¹) *
        (d.weight (last n h) * F h) ∂historyLaw K x.val n := by
      apply lintegral_congr
      intro h
      simp only [Pi.mul_apply, mul_assoc]
    _ = _ := lintegral_const_mul _
      ((d.measurable_weight.comp (measurable_pi_apply _)).mul hF)

/-- Every measurable finite-history cylinder satisfies the exact Doob formula. -/
theorem doob_cylinder (d : DoobTransform.EigenData K) (x : d.State)
    (n : ℕ) (A : Set (History M n)) (hA : MeasurableSet A) :
    pathMeasure d.kernel x
        {ω | coeHistory d n (Preorder.frestrictLe n ω) ∈ A} =
      (d.rate⁻¹)^n * (d.weight x.val)⁻¹ *
        ∫⁻ h in A, d.weight (last n h) ∂historyLaw K x.val n := by
  have hw : Measurable (fun h : History M n => d.weight (last n h)) :=
    d.measurable_weight.comp (measurable_pi_apply _)
  have h := congrArg (fun μ : Measure (History M n) => μ A)
    (doob_historyLaw_eq_withDensity d x n)
  rw [Measure.map_apply (measurable_coeHistory d n) hA,
    historyLaw, Measure.map_apply (Preorder.measurable_frestrictLe n)
      (hA.preimage (measurable_coeHistory d n)), withDensity_apply _ hA,
    lintegral_const_mul _ hw] at h
  exact h

end
end ConditionedStableLaws.QProcessLimit

namespace ConditionedStableLaws.CanonicalChain
noncomputable section
open QProcessLimit
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Extend a killed-kernel eigenfunction by zero at the absorbing cemetery. -/
def cemeteryWeight (d : DoobTransform.EigenData C.killedTransition) : Option M → ℝ≥0∞
  | none => 0
  | some x => d.weight x

theorem measurable_cemeteryWeight (d : DoobTransform.EigenData C.killedTransition) :
    Measurable (C.cemeteryWeight d) := by
  intro A hA
  change MeasurableSet (d.weight ⁻¹' A)
  exact d.measurable_weight hA

/-- Eigen-data for the absorbing transition, derived from the killed kernel. -/
def cemeteryEigenData (d : DoobTransform.EigenData C.killedTransition) :
    DoobTransform.EigenData C.transition where
  rate := d.rate
  rate_ne_zero := d.rate_ne_zero
  rate_ne_top := d.rate_ne_top
  weight := C.cemeteryWeight d
  measurable_weight := C.measurable_cemeteryWeight d
  weight_ne_top := by
    intro z
    cases z with
    | none => exact ENNReal.zero_ne_top
    | some x => exact d.weight_ne_top x
  right_eigen := by
    intro z
    cases z with
    | none =>
        rw [C.absorbing, lintegral_dirac' _ (C.measurable_cemeteryWeight d)]
        simp [cemeteryWeight]
    | some x =>
        rw [lintegral_eq_live_comap _ _ (show C.cemeteryWeight d none = 0 from rfl)]
        exact d.right_eigen x

/-- A live starting point regarded as a state of the transformed absorbing
kernel. -/
def doobStart (d : DoobTransform.EigenData C.killedTransition) (x : d.State) :
    (C.cemeteryEigenData d).State := ⟨some x.val, x.property⟩

/-- The Doob trajectory law, on the positive-eigenfunction subtype of the original absorbing state
space. -/
def doobPathMeasure (d : DoobTransform.EigenData C.killedTransition) (x : d.State) :
    Measure (ℕ → (C.cemeteryEigenData d).State) :=
  QProcessLimit.pathMeasure (C.cemeteryEigenData d).kernel (C.doobStart d x)

instance doobPathMeasure_probability (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) : IsProbabilityMeasure (C.doobPathMeasure d x) := by
  unfold doobPathMeasure
  infer_instance

/-- Canonical finite-horizon RN identity for the original absorbing chain.
The density is λ⁻ⁿ η(Xₙ)/η(x), and both path laws are constructed trajectories. -/
theorem doob_canonical_cylinder (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) (n : ℕ) (A : Set (QProcessLimit.History (Option M) n))
    (hA : MeasurableSet A) :
    C.doobPathMeasure d x
      {ω | QProcessLimit.coeHistory (C.cemeteryEigenData d) n
        (Preorder.frestrictLe n ω) ∈ A} =
      (d.rate⁻¹)^n * (d.weight x.val)⁻¹ *
        ∫⁻ h in A, C.cemeteryWeight d (QProcessLimit.last n h)
          ∂(C.pathMeasure x.val).map (Preorder.frestrictLe n) := by
  exact QProcessLimit.doob_cylinder (C.cemeteryEigenData d) (C.doobStart d x) n A hA

end
end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.QProcessLimit
noncomputable section
open Filter
variable {M : Type*} [MeasurableSpace M] (K : Kernel M M) [IsMarkovKernel K]

omit [MeasurableSpace M] [IsMarkovKernel K] in
theorem restrict_append {n m : ℕ} (hnm : n ≤ m) (h : History M m) (y : M) :
    Preorder.frestrictLe₂ (π := fun _ : ℕ => M) (hnm.trans (Nat.le_succ m)) (append m (h, y)) =
      Preorder.frestrictLe₂ (π := fun _ : ℕ => M) hnm h := by
  funext i
  have hi : i.val ≤ m := (Finset.mem_Iic.mp i.property).trans hnm
  simp [Preorder.frestrictLe₂, append, hi, Finset.restrict₂]

/-- The Markov property for a complete finite past and a later observation,
derived by iterating the joint past/next law of the constructed trajectory. -/
theorem lintegral_history_future (x : M) (n m : ℕ)
    (F : History M n → ℝ≥0∞) (hF : Measurable F)
    (g : M → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, F (Preorder.frestrictLe n ω) * g (ω (n + m)) ∂pathMeasure K x) =
      ∫⁻ h, F h * (∫⁻ y, g y ∂(K^m) (last n h)) ∂historyLaw K x n := by
  induction m generalizing g with
  | zero =>
      have hfg : Measurable (fun h : History M n => F h * g (last n h)) :=
        hF.mul (hg.comp (measurable_pi_apply _))
      have hm := lintegral_map hfg (Preorder.measurable_frestrictLe n)
        (μ := pathMeasure K x)
      simp only [pow_zero, show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply,
        lintegral_dirac' _ hg, Nat.add_zero]
      exact hm.symm
  | succ m ih =>
      let G : M → ℝ≥0∞ := fun y => ∫⁻ z, g z ∂K y
      have hG : Measurable G := (Measure.measurable_lintegral hg).comp K.measurable
      let J : History M (n + m + 1) → ℝ≥0∞ := fun h =>
        F (Preorder.frestrictLe₂ (π := fun _ : ℕ => M) (by omega : n ≤ n + m + 1) h) * g (last (n + m + 1) h)
      have hJ : Measurable J :=
        (hF.comp (Preorder.measurable_frestrictLe₂ (by omega))).mul
          (hg.comp (measurable_pi_apply _))
      let I : History M (n + m) → ℝ≥0∞ := fun h =>
        F (Preorder.frestrictLe₂ (π := fun _ : ℕ => M) (Nat.le_add_right n m) h) * G (last (n + m) h)
      have hI : Measurable I :=
        (hF.comp (Preorder.measurable_frestrictLe₂ (Nat.le_add_right n m))).mul
          (hG.comp (measurable_pi_apply _))
      calc
        _ = ∫⁻ h, J h ∂historyLaw K x (n + m + 1) :=
          (lintegral_map hJ (Preorder.measurable_frestrictLe (n + m + 1))).symm
        _ = ∫⁻ h, ∫⁻ y, J (append (n + m) (h, y))
            ∂K (last (n + m) h) ∂historyLaw K x (n + m) :=
          lintegral_historyLaw_succ K x (n + m) J hJ
        _ = ∫⁻ h, I h ∂historyLaw K x (n + m) := by
          apply lintegral_congr
          intro h
          change (∫⁻ y, F (Preorder.frestrictLe₂ (π := fun _ : ℕ => M) _ (append (n + m) (h, y))) *
            g (last (n + m + 1) (append (n + m) (h, y))) ∂K _) = _
          simp_rw [restrict_append (Nat.le_add_right n m), last_append]
          exact lintegral_const_mul _ hg
        _ = ∫⁻ ω, F (Preorder.frestrictLe n ω) * G (ω (n + m)) ∂pathMeasure K x :=
          lintegral_map hI (Preorder.measurable_frestrictLe (n + m))
        _ = ∫⁻ h, F h * (∫⁻ y, G y ∂(K^m) (last n h)) ∂historyLaw K x n := ih G hG
        _ = _ := by
          apply lintegral_congr
          intro h
          congr 1
          rw [pow_succ']
          exact (Measure.lintegral_bind K.aemeasurable hg.aemeasurable).symm

end
end ConditionedStableLaws.QProcessLimit

namespace ConditionedStableLaws.CanonicalChain
noncomputable section
open QProcessLimit Filter
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Remaining survival probability, including its value at the cemetery. -/
def remainingSurvival (m : ℕ) (z : Option M) : ℝ≥0∞ :=
  (C.transition^m) z ({none} : Set (Option M))ᶜ

theorem measurable_remainingSurvival (m : ℕ) : Measurable (C.remainingSurvival m) :=
  (C.transition^m).measurable_coe measurableSet_cemetery.compl

theorem transition_pow_live_comap (x : M) (m : ℕ) :
    ((C.transition^m) (some x)).comap Option.some = (C.killedTransition^m) x := by
  induction m with
  | zero =>
      simp only [pow_zero, show (1 : Kernel (Option M) (Option M)) = Kernel.id from rfl,
        show (1 : Kernel M M) = Kernel.id from rfl, Kernel.id_apply]
      rw [← Measure.map_dirac' measurable_some_state]
      exact measurableEmbedding_some_state.comap_map _
  | succ m ih =>
      rw [pow_succ', pow_succ']
      change (C.transition ∘ₘ (C.transition^m) (some x)).comap Option.some =
        C.killedTransition ∘ₘ (C.killedTransition^m) x
      rw [C.live_comap_transition_comp, ih]

theorem remainingSurvival_some (m : ℕ) (x : M) :
    C.remainingSurvival m (some x) = (C.killedTransition^m) x univ := by
  rw [← C.transition_pow_live_comap x m, measurableEmbedding_some_state.comap_apply,
    image_univ, live_states_eq_cemetery_compl]
  rfl

theorem transition_pow_none (m : ℕ) : (C.transition^m) none = Measure.dirac none := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ']
      change C.transition ∘ₘ (C.transition^m) none = _
      rw [ih]
      exact (Measure.dirac_bind C.transition.measurable none).trans C.absorbing

@[simp] theorem remainingSurvival_none (m : ℕ) : C.remainingSurvival m none = 0 := by
  rw [remainingSurvival, C.transition_pow_none, Measure.dirac_apply' _ measurableSet_cemetery.compl]
  simp

/-- The law of a finite history conditioned on a later survival event has
exact density given by the remaining survival probability. -/
theorem conditioned_cylinder (x : M) (n m : ℕ)
    (A : Set (History (Option M) n)) (hA : MeasurableSet A) :
    C.conditionedMeasure x (n + m) {ω | Preorder.frestrictLe n ω ∈ A} =
      (C.remainingSurvival (n + m) (some x))⁻¹ *
        ∫⁻ h in A, C.remainingSurvival m (last n h)
          ∂(C.pathMeasure x).map (Preorder.frestrictLe n) := by
  let F := A.indicator (fun _ => (1 : ℝ≥0∞))
  let g := ({none} : Set (Option M))ᶜ.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hA
  have hg : Measurable g := measurable_const.indicator measurableSet_cemetery.compl
  have hm := QProcessLimit.lintegral_history_future C.transition (some x) n m F hF g hg
  have hright (z : Option M) : (∫⁻ y, g y ∂(C.transition^m) z) =
      C.remainingSurvival m z := by
    simp only [g, lintegral_indicator measurableSet_cemetery.compl, lintegral_const,
      one_mul, Measure.restrict_apply_univ, remainingSurvival]
  simp_rw [hright] at hm
  have hprod : (∫⁻ ω, F (Preorder.frestrictLe n ω) * g (ω (n + m)) ∂C.pathMeasure x) =
      C.pathMeasure x (survival (n + m) ∩ {ω | Preorder.frestrictLe n ω ∈ A}) := by
    calc
      _ = ∫⁻ ω, (survival (n + m) ∩ {ω | Preorder.frestrictLe n ω ∈ A}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂C.pathMeasure x := by
        apply lintegral_congr_ae
        filter_upwards [C.ae_mem_survival_iff x (n + m)] with ω hω
        by_cases ha : Preorder.frestrictLe n ω ∈ A <;>
          by_cases hs : ω ∈ survival (n + m) <;>
          simp [F, g, ha, hs, ← hω]
      _ = _ := by
        have he : MeasurableSet (survival (n + m) ∩
            {ω : Path M | Preorder.frestrictLe n ω ∈ A}) :=
          (measurableSet_survival (n + m)).inter
            (hA.preimage (Preorder.measurable_frestrictLe n))
        rw [lintegral_indicator he]
        simp
  have hind : (fun h => F h * C.remainingSurvival m (last n h)) =
      A.indicator (fun h => C.remainingSurvival m (last n h)) := by
    funext h
    by_cases hh : h ∈ A <;> simp [F, hh]
  rw [hind, lintegral_indicator hA] at hm
  rw [C.conditionedMeasure_apply, C.pathMeasure_survival,
    ← C.remainingSurvival_some, ← hprod]
  exact congrArg (fun v => (C.remainingSurvival (n + m) (some x))⁻¹ * v) hm

end
end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.QProcessLimit

/-- Common finite nonzero factors cancel even when the unnormalized masses vanish, conditioning on a
null event giving zero. -/
theorem normalized_ratio (r s t : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ∞) :
    (r * s)⁻¹ * (r * t) = s⁻¹ * t := by
  rw [ENNReal.mul_inv (Or.inl hr0) (Or.inl hrt)]
  calc
    _ = (r⁻¹ * r) * (s⁻¹ * t) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hr0 hrt, one_mul]

end ConditionedStableLaws.QProcessLimit

namespace ConditionedStableLaws.CanonicalChain
noncomputable section
open QProcessLimit Filter
open scoped Topology
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Survival-conditioned finite-horizon cylinders converge to the Doob path law. The only asymptotic
input is normalized killed survival, together with a finite uniform bound. -/
theorem conditioned_cylinder_tendsto_doob
    (d : DoobTransform.EigenData C.killedTransition)
    (hlim : ∀ y : M, Tendsto
      (fun m : ℕ => (d.rate⁻¹)^m * (C.killedTransition^m) y univ)
      atTop (𝓝 (d.weight y)))
    (B : ℝ≥0∞) (hBt : B ≠ ∞)
    (hbound : ∀ (m : ℕ) (y : M),
      (d.rate⁻¹)^m * (C.killedTransition^m) y univ ≤ B)
    (x : d.State) (n : ℕ) (A : Set (History (Option M) n)) (hA : MeasurableSet A) :
    Tendsto (fun m : ℕ =>
      C.conditionedMeasure x.val (n + m) {ω | Preorder.frestrictLe n ω ∈ A}) atTop
      (𝓝 (C.doobPathMeasure d x {ω | coeHistory (C.cemeteryEigenData d) n
        (Preorder.frestrictLe n ω) ∈ A})) := by
  let μ := (C.pathMeasure x.val).map (Preorder.frestrictLe n)
  have hpoint (z : Option M) : Tendsto
      (fun m : ℕ => (d.rate⁻¹)^m * C.remainingSurvival m z)
      atTop (𝓝 (C.cemeteryWeight d z)) := by
    cases z with
    | none =>
        simp only [remainingSurvival_none, mul_zero, cemeteryWeight]
        exact tendsto_const_nhds
    | some y => simpa only [C.remainingSurvival_some, cemeteryWeight] using hlim y
  have hb (m : ℕ) (z : Option M) :
      (d.rate⁻¹)^m * C.remainingSurvival m z ≤ B := by
    cases z with
    | none => simp
    | some y => simpa only [C.remainingSurvival_some] using hbound m y
  have hnum : Tendsto
      (fun m : ℕ => ∫⁻ h in A, (d.rate⁻¹)^m * C.remainingSurvival m (last n h) ∂μ)
      atTop (𝓝 (∫⁻ h in A, C.cemeteryWeight d (last n h) ∂μ)) := by
    apply tendsto_lintegral_of_dominated_convergence (fun _ => B)
    · intro m
      exact measurable_const.mul ((C.measurable_remainingSurvival m).comp (measurable_pi_apply _))
    · intro m
      exact ae_of_all _ (fun h => hb m (last n h))
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top hBt (measure_ne_top _ _)
    · exact ae_of_all _ (fun h => hpoint (last n h))
  have hcancel : d.rate^n * (d.rate⁻¹)^n = 1 := by
    rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel
      (ENNReal.pow_ne_zero d.rate_ne_zero n) (ENNReal.pow_ne_top d.rate_ne_top)]
  have hden : Tendsto
      (fun m : ℕ => (d.rate⁻¹)^m * C.remainingSurvival (n + m) (some x.val))
      atTop (𝓝 (d.rate^n * d.weight x.val)) := by
    have ht := (hpoint (some x.val)).comp (tendsto_add_atTop_nat n)
    have ht' := ENNReal.Tendsto.const_mul ht (a := d.rate^n)
      (Or.inr (ENNReal.pow_ne_top d.rate_ne_top))
    change Tendsto _ _ (𝓝 (d.rate^n * d.weight x.val)) at ht'
    convert ht' using 1
    funext m
    simp only [Function.comp_apply]
    rw [Nat.add_comm m n, pow_add]
    change _ = d.rate^n * (((d.rate⁻¹)^n * (d.rate⁻¹)^m) * _)
    calc
      _ = (d.rate^n * (d.rate⁻¹)^n) *
          ((d.rate⁻¹)^m * C.remainingSurvival (n + m) (some x.val)) := by rw [hcancel, one_mul]
      _ = _ := by ac_rfl
  have hd0 : d.rate^n * d.weight x.val ≠ 0 :=
    mul_ne_zero (ENNReal.pow_ne_zero d.rate_ne_zero n) x.property
  have hdt : d.rate^n * d.weight x.val ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top d.rate_ne_top) (d.weight_ne_top x.val)
  have hquot := ENNReal.Tendsto.mul
    (tendsto_inv_iff.mpr hden)
    (Or.inl (ENNReal.inv_ne_zero.mpr hdt)) hnum
    (Or.inr (ENNReal.inv_ne_top.mpr hd0))
  have heq (m : ℕ) :
      ((d.rate⁻¹)^m * C.remainingSurvival (n + m) (some x.val))⁻¹ *
          (∫⁻ h in A, (d.rate⁻¹)^m * C.remainingSurvival m (last n h) ∂μ) =
        C.conditionedMeasure x.val (n + m) {ω | Preorder.frestrictLe n ω ∈ A} := by
    have hmeas : Measurable (fun h : History (Option M) n => C.remainingSurvival m (last n h)) :=
      (C.measurable_remainingSurvival m).comp (measurable_pi_apply _)
    rw [lintegral_const_mul _ hmeas, normalized_ratio]
    · exact (C.conditioned_cylinder x.val n m A hA).symm
    · exact ENNReal.pow_ne_zero (ENNReal.inv_ne_zero.mpr d.rate_ne_top) m
    · exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr d.rate_ne_zero)
  simp_rw [heq] at hquot
  rw [C.doob_canonical_cylinder d x n A hA]
  have hinv : (d.rate^n * d.weight x.val)⁻¹ = (d.rate⁻¹)^n * (d.weight x.val)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (ENNReal.pow_ne_zero d.rate_ne_zero n))
      (Or.inl (ENNReal.pow_ne_top d.rate_ne_top)), ENNReal.inv_pow]
  rwa [hinv] at hquot

end
end ConditionedStableLaws.CanonicalChain

namespace ConditionedStableLaws.CanonicalChain
noncomputable section
open QProcessLimit Filter
open scoped Topology
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- Uniform normalized survival asymptotics, as supplied by a spectral-gap estimate, identify every
fixed finite-horizon distribution of the Q-process. -/
theorem conditioned_cylinder_tendsto_doob_of_uniform
    (d : DoobTransform.EigenData C.killedTransition)
    (hlim : TendstoUniformly
      (fun (m : ℕ) (y : M) => ((d.rate⁻¹)^m * (C.killedTransition^m) y univ).toReal)
      (fun y => (d.weight y).toReal) atTop)
    (B : ℝ≥0∞) (hBt : B ≠ ∞)
    (hbound : ∀ (m : ℕ) (y : M),
      (d.rate⁻¹)^m * (C.killedTransition^m) y univ ≤ B)
    (x : d.State) (n : ℕ) (A : Set (History (Option M) n)) (hA : MeasurableSet A) :
    Tendsto (fun N : ℕ =>
      C.conditionedMeasure x.val N {ω | Preorder.frestrictLe n ω ∈ A}) atTop
      (𝓝 (C.doobPathMeasure d x {ω | coeHistory (C.cemeteryEigenData d) n
        (Preorder.frestrictLe n ω) ∈ A})) := by
  have hpoint (y : M) : Tendsto
      (fun m : ℕ => (d.rate⁻¹)^m * (C.killedTransition^m) y univ)
      atTop (𝓝 (d.weight y)) := by
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim.tendsto_at y)
    have heq : (fun m : ℕ => ENNReal.ofReal
        (((d.rate⁻¹)^m * (C.killedTransition^m) y univ).toReal)) =
        (fun m : ℕ => (d.rate⁻¹)^m * (C.killedTransition^m) y univ) := by
      funext m
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top hBt (hbound m y))
    simpa only [Function.comp_def, heq, ENNReal.ofReal_toReal (d.weight_ne_top y)] using ht
  apply (tendsto_add_atTop_iff_nat n).mp
  simpa only [Nat.add_comm] using
    C.conditioned_cylinder_tendsto_doob d hpoint B hBt hbound x n A hA

end
end ConditionedStableLaws.CanonicalChain
