import ConditionedStableLaws.QProcessReference
import ConditionedStableLaws.ConditionalTransferBasic

/-!
# Exact finite-history change of measure

A one-step density identity is iterated by the history-law recursion. The Doob specialization maps
live-subtype histories into the canonical chain histories, with the inverse-density formula used by
probability transfer.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.DoobHistoryChange
noncomputable section
open StandingHypothesis QProcessLimit CanonicalChain

def historyMap {X Y : Type*} (u : X → Y) (n : ℕ) (h : History X n) : History Y n :=
  fun i => u (h i)

theorem measurable_historyMap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {u : X → Y} (hu : Measurable u) (n : ℕ) : Measurable (historyMap u n) := by
  apply Measurable.of_eval
  intro i
  exact hu.comp (measurable_pi_apply i)

theorem historyMap_append {X Y : Type*} (u : X → Y) (n : ℕ) (h : History X n) (y : X) :
    historyMap u (n + 1) (append n (h, y)) = append n (historyMap u n h, u y) := by
  funext i
  by_cases hi : i.val ≤ n <;> simp [historyMap, append, hi]

theorem lintegral_history_change {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Kernel X X) [IsMarkovKernel P] (T : Kernel Y Y) [IsMarkovKernel T]
    (d : DoobTransform.EigenData T) (u : X → Y) (hu : Measurable u)
    (hu0 : ∀ x, d.weight (u x) ≠ 0)
    (hstep : ∀ (x : X) (F : Y → ℝ≥0∞), Measurable F →
      (∫⁻ y, F (u y) ∂P x) = d.rate⁻¹ * (d.weight (u x))⁻¹ *
        ∫⁻ y, d.weight y * F y ∂T (u x))
    (x : X) (n : ℕ) (F : History Y n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, F (historyMap u n h) ∂historyLaw P x n) =
      (d.rate⁻¹)^n * (d.weight (u x))⁻¹ *
        ∫⁻ h, d.weight (last n h) * F h ∂historyLaw T (u x) n := by
  induction n with
  | zero =>
      have hFc : Measurable (fun h => F (historyMap u 0 h)) :=
        hF.comp (measurable_historyMap hu 0)
      have hFw : Measurable (fun h => d.weight (last 0 h) * F h) :=
        (d.measurable_weight.comp (measurable_pi_apply _)).mul hF
      rw [historyLaw_zero, historyLaw_zero,
        lintegral_dirac' _ hFc, lintegral_dirac' _ hFw, pow_zero]
      change F (fun _ => (u x)) =
        1 * (d.weight (u x))⁻¹ * (d.weight (u x) * F (fun _ => (u x)))
      rw [one_mul, ENNReal.inv_mul_cancel_left (hu0 x) (d.weight_ne_top (u x))]
  | succ n ih =>
      let I : History Y n → ℝ≥0∞ := fun h =>
        ∫⁻ y, d.weight y * F (append n (h, y)) ∂T (last n h)
      have hI : Measurable I :=
        ((d.measurable_weight.comp measurable_snd).mul
          (hF.comp (measurable_append n))).lintegral_kernel_prod_right'
          (κ := historyKernel T n)
      let G : History Y n → ℝ≥0∞ := fun h =>
        d.rate⁻¹ * (d.weight (last n h))⁻¹ * I h
      have hG : Measurable G :=
        (measurable_const.mul (d.measurable_weight.comp (measurable_pi_apply _)).inv).mul hI
      have hcancel (h : History Y n) :
          d.weight (last n h) * ((d.weight (last n h))⁻¹ * I h) = I h := by
        apply ENNReal.mul_inv_cancel_left'
        · intro hz
          have hzero : ∫⁻ y, d.weight y ∂T (last n h) = 0 := by
            rw [d.right_eigen, hz, mul_zero]
          have hae := (lintegral_eq_zero_iff d.measurable_weight).1 hzero
          change (∫⁻ y, d.weight y * F (append n (h, y)) ∂T (last n h)) = 0
          calc
            _ = ∫⁻ _ : Y, 0 ∂T (last n h) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with y hy
              simp [hy]
            _ = 0 := by simp
        · intro ht
          exact False.elim (d.weight_ne_top _ ht)
      calc
        _ = ∫⁻ h, ∫⁻ y, F (append n (historyMap u n h, u y))
            ∂P (last n h) ∂historyLaw P x n := by
          have hFc : Measurable (fun h => F (historyMap u (n + 1) h)) :=
            hF.comp (measurable_historyMap hu (n + 1))
          rw [lintegral_historyLaw_succ P x n _ hFc]
          simp_rw [historyMap_append]
        _ = ∫⁻ h, G (historyMap u n h) ∂historyLaw P x n := by
          apply lintegral_congr
          intro h
          exact hstep (last n h) _
            (hF.comp ((measurable_append n).comp measurable_prodMk_left))
        _ = (d.rate⁻¹)^n * (d.weight (u x))⁻¹ *
            ∫⁻ h, d.weight (last n h) * G h ∂historyLaw T (u x) n := ih G hG
        _ = (d.rate⁻¹)^n * (d.weight (u x))⁻¹ *
            (d.rate⁻¹ * ∫⁻ h, I h ∂historyLaw T (u x) n) := by
          congr 1
          calc
            _ = ∫⁻ h, d.rate⁻¹ * I h ∂historyLaw T (u x) n := by
              apply lintegral_congr
              intro h
              change d.weight (last n h) *
                (d.rate⁻¹ * (d.weight (last n h))⁻¹ * I h) = _
              calc
                _ = d.rate⁻¹ * (d.weight (last n h) *
                    ((d.weight (last n h))⁻¹ * I h)) := by ac_rfl
                _ = _ := by rw [hcancel]
            _ = _ := lintegral_const_mul _ hI
        _ = (d.rate⁻¹)^(n + 1) * (d.weight (u x))⁻¹ *
            ∫⁻ h, d.weight (last (n + 1) h) * F h ∂historyLaw T (u x) (n + 1) := by
          have hFw : Measurable (fun h => d.weight (last (n + 1) h) * F h) :=
            (d.measurable_weight.comp (measurable_pi_apply _)).mul hF
          rw [lintegral_historyLaw_succ T (u x) n _ hFw]
          simp only [last_append]
          rw [pow_succ]
          change _ = _ * _ * ∫⁻ h, I h ∂historyLaw T (u x) n
          ac_rfl

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

theorem lintegral_doob_option (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) (F : Option M → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y, F (some y.val) ∂d.kernel x) =
      d.rate⁻¹ * (d.weight x.val)⁻¹ *
        ∫⁻ y, C.cemeteryWeight d y * F y ∂C.transition (some x.val) := by
  have hh := RefinedLLN.lintegral_doob_pow d 1 x (F := fun y => F (some y))
    (hF.comp measurable_some_state)
  simp only [pow_one] at hh
  rw [hh]
  congr 1
  rw [lintegral_eq_live_comap _ _ (show C.cemeteryWeight d none * F none = 0 by simp [cemeteryWeight])]
  apply lintegral_congr
  intro y
  simp only [cemeteryWeight, mul_comm]

theorem lintegral_doob_history_option (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) (n : ℕ) (F : History (Option M) n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, F (historyMap (fun y : d.State => some y.val) n h) ∂historyLaw d.kernel x n) =
      (d.rate⁻¹)^n * (d.weight x.val)⁻¹ *
        ∫⁻ h, C.cemeteryWeight d (last n h) * F h ∂historyLaw C.transition (some x.val) n := by
  exact lintegral_history_change d.kernel C.transition (C.cemeteryEigenData d)
    (fun y => some y.val) (measurable_some_state.comp measurable_subtype_coe)
    (fun y => y.property) (lintegral_doob_option C d) x n F hF

end
end ConditionedStableLaws.DoobHistoryChange
