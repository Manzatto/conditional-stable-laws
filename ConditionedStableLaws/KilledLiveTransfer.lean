import ConditionedStableLaws.QProcessEndpoint

/-! # Transfer to the chain conditioned to remain in the positive region -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.KilledLiveTransfer

noncomputable section
open StandingHypothesis QProcessLimit CanonicalChain DoobHistoryChange QProcessEndpoint

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

def qHistoryEvent (d : DoobTransform.EigenData C.killedTransition) (n : ℕ)
    (A : Set (History (Option M) n)) : Set (ℕ → d.State) :=
  {ω | historyMap (fun y : d.State => some y.val) n (Preorder.frestrictLe n ω) ∈ A}

theorem measurableSet_qHistoryEvent (d : DoobTransform.EigenData C.killedTransition)
    (n : ℕ) {A : Set (History (Option M) n)} (hA : MeasurableSet A) :
    MeasurableSet (qHistoryEvent C d n A) := hA.preimage
      ((measurable_historyMap (measurable_some_state.comp measurable_subtype_coe) n).comp
        (Preorder.measurable_frestrictLe n))

theorem ae_liveThrough_iff_endpoint (d : DoobTransform.EigenData C.killedTransition)
    (hlive : d.liveSet = survivingSet C.killedTransition) (x : M) (n : ℕ) :
    ∀ᵐ ω ∂C.pathMeasure x,
      (ω ∈ Cited.liveThrough C.killedTransition (n + 1) ↔ C.cemeteryWeight d (ω n) ≠ 0) := by
  have hno : ∀ z ∈ d.liveSetᶜ, C.killedTransition z d.liveSet = 0 := by
    intro z hz
    exact d.no_return_from_zero hz
  have hsteps := ae_all_iff.2 fun i => ConditionalTransfer.ae_no_entry_step C
    d.measurableSet_liveSet d.measurableSet_liveSet.compl hno x i
  have habs := ae_all_iff.2 fun i => C.ae_absorbing_step x i
  filter_upwards [hsteps, habs] with ω hω ha
  have hstep (i : ℕ) : ω i ∉ Option.some '' d.liveSet → ω (i+1) ∉ Option.some '' d.liveSet := by
    intro hi
    cases heq : ω i with
    | none =>
        rw [ha i heq]
        rintro ⟨z, _, hz⟩
        cases hz
    | some z =>
        have hz : z ∈ d.liveSetᶜ := by
          intro hz
          exact hi ⟨z, hz, heq.symm⟩
        exact hω i ⟨z, hz, heq.symm⟩
  have hend : (C.cemeteryWeight d (ω n) ≠ 0) ↔ ω n ∈ Option.some '' d.liveSet := by
    cases heq : ω n with
    | none => simp [cemeteryWeight]
    | some z => simp [cemeteryWeight, DoobTransform.EigenData.liveSet]
  rw [hend]
  constructor
  · intro hωn
    obtain ⟨z, hz, heq⟩ := hωn n (by omega)
    exact ⟨z, hlive.symm ▸ hz, heq.symm⟩
  · intro hn i hi
    have him : i ≤ n := by omega
    have hmem : ω i ∈ Option.some '' d.liveSet := by
      by_contra hnot
      have hprop : ∀ k, i ≤ k → ω k ∉ Option.some '' d.liveSet := by
        intro k hik
        induction k, hik using Nat.le_induction with
        | base => exact hnot
        | succ k _ ih => exact hstep k ih
      exact hprop n him hn
    obtain ⟨z, hz, heq⟩ := hmem
    exact ⟨z, hlive ▸ hz, heq.symm⟩

variable [MetricSpace M] [CompactSpace M] [BorelSpace M]

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
set_option backward.isDefEq.respectTransparency false in
theorem inverse_history_event (d : DoobTransform.EigenData C.killedTransition)
    (x : d.State) (n : ℕ) (A : Set (History (Option M) n)) (hA : MeasurableSet A) :
    (∫ ω in qHistoryEvent C d n A, inverseWeight d n ω ∂pathMeasure d.kernel x) =
      (d.rate.toReal)⁻¹ ^ n * ((d.weight x.val).toReal)⁻¹ *
        (C.pathMeasure x.val {ω : Path M | Preorder.frestrictLe n ω ∈ A ∧ C.cemeteryWeight d (ω n) ≠ 0}).toReal := by
  let F : History (Option M) n → ℝ≥0∞ :=
    A.indicator (fun h => (C.cemeteryWeight d (last n h))⁻¹)
  have hwm : Measurable (fun h : History (Option M) n => C.cemeteryWeight d (last n h)) :=
    (C.measurable_cemeteryWeight d).comp (measurable_pi_apply _)
  have hFm : Measurable F := hwm.inv.indicator hA
  have hRN := lintegral_doob_history_option C d x n F hFm
  have hQ : MeasurableSet (qHistoryEvent C d n A) := measurableSet_qHistoryEvent C d n hA
  have hi : Integrable ((qHistoryEvent C d n A).indicator (inverseWeight d n))
      (pathMeasure d.kernel x) :=
    (integrable_inverseWeight (K := C.toKilledKernel) d x n).indicator hQ
  have hpos : ∀ ω : ℕ → d.State, 0 ≤ (qHistoryEvent C d n A).indicator (inverseWeight d n) ω :=
    indicator_nonneg (fun _ _ => inv_nonneg.2 ENNReal.toReal_nonneg)
  have hOf := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hpos)
  rw [integral_indicator hQ] at hOf
  have hFin (ω : ℕ → d.State) : ENNReal.ofReal
      ((qHistoryEvent C d n A).indicator (inverseWeight d n) ω) =
      F (historyMap (fun y : d.State => some y.val) n (Preorder.frestrictLe n ω)) := by
    by_cases hmem : ω ∈ qHistoryEvent C d n A
    · rw [indicator_of_mem hmem]
      change ENNReal.ofReal (((d.weight (ω n).val).toReal)⁻¹) = _
      rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos (ω n).property (d.weight_ne_top _)),
        ENNReal.ofReal_toReal (d.weight_ne_top _)]
      change (d.weight (ω n).val)⁻¹ =
        A.indicator (fun h => (C.cemeteryWeight d (last n h))⁻¹)
          (historyMap (fun y : d.State => some y.val) n (Preorder.frestrictLe n ω))
      rw [indicator_of_mem (show historyMap (fun y : d.State => some y.val) n
        (Preorder.frestrictLe n ω) ∈ A from hmem)]
      rfl
    · rw [indicator_of_notMem hmem, ENNReal.ofReal_zero]
      change 0 = A.indicator (fun h => (C.cemeteryWeight d (last n h))⁻¹)
        (historyMap (fun y : d.State => some y.val) n (Preorder.frestrictLe n ω))
      exact (indicator_of_notMem (show historyMap (fun y : d.State => some y.val) n
        (Preorder.frestrictLe n ω) ∉ A from hmem) _).symm
  have hleft : (∫⁻ ω, ENNReal.ofReal ((qHistoryEvent C d n A).indicator (inverseWeight d n) ω)
      ∂pathMeasure d.kernel x) =
      ∫⁻ h, F (historyMap (fun y : d.State => some y.val) n h) ∂historyLaw d.kernel x n := by
    unfold historyLaw
    have hFc : Measurable (fun h : History d.State n =>
        F (historyMap (fun y : d.State => some y.val) n h)) :=
      hFm.comp (measurable_historyMap (u := fun y : d.State => some y.val)
        (measurable_some_state.comp measurable_subtype_coe) n)
    rw [lintegral_map hFc (Preorder.measurable_frestrictLe n)]
    exact lintegral_congr hFin
  rw [hleft, hRN] at hOf
  set E : Set (History (Option M) n) := {h | h ∈ A ∧ C.cemeteryWeight d (last n h) ≠ 0}
  have hE : MeasurableSet E := hA.inter (hwm (measurableSet_singleton 0)).compl
  have hwF (h : History (Option M) n) : C.cemeteryWeight d (last n h) * F h =
      E.indicator (fun _ => (1 : ℝ≥0∞)) h := by
    by_cases hmem : h ∈ A
    · by_cases hw : C.cemeteryWeight d (last n h) = 0
      · simp [F, E, hmem, hw]
      · simp only [F, indicator_of_mem hmem]
        rw [ENNReal.mul_inv_cancel hw ((C.cemeteryEigenData d).weight_ne_top _)]
        exact (indicator_of_mem (show h ∈ E from ⟨hmem, hw⟩)
          (fun _ => (1 : ℝ≥0∞))).symm
    · simp [F, E, hmem]
  simp_rw [hwF] at hOf
  simp only [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ, one_mul] at hOf
  rw [historyLaw, Measure.map_apply (Preorder.measurable_frestrictLe n) hE] at hOf
  have hh := congrArg ENNReal.toReal hOf
  have hIntPos : 0 ≤ ∫ ω in qHistoryEvent C d n A, inverseWeight d n ω ∂pathMeasure d.kernel x :=
    integral_nonneg (fun _ => inv_nonneg.2 ENNReal.toReal_nonneg)
  rw [ENNReal.toReal_ofReal hIntPos, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_inv] at hh
  exact hh

variable {ρ : Measure M}

set_option backward.isDefEq.respectTransparency false in
theorem transfer_history_events (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (x : d.State)
    (A : ∀ n : ℕ, Set (History (Option M) n)) (hA : ∀ n, MeasurableSet (A n))
    (hQ : Tendsto (fun n => pathMeasure d.kernel x (qHistoryEvent C d n (A n))) atTop (𝓝 0)) :
    Tendsto (fun n => C.pathMeasure x.val
      ({ω : Path M | Preorder.frestrictLe n ω ∈ A n} ∩ Cited.liveThrough C.killedTransition (n+1)) /
        C.pathMeasure x.val (Cited.liveThrough C.killedTransition (n+1))) atTop (𝓝 0) := by
  obtain ⟨μ, hleft, hnorm⟩ := QProcessReference.exists_probability_reference h d s ⟨x.val, x.property⟩
  have hm := inverseWeight_mass_tendsto h d s.continuous_weight (μ : Measure M) hleft hnorm x
  have hp : Tendsto (fun n => (pathMeasure d.kernel x).real (qHistoryEvent C d n (A n)))
      atTop (𝓝 0) := by
    have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hQ
    rw [ENNReal.toReal_zero] at hh
    convert hh using 1
    funext n
    rfl
  have ht := WeightedProbabilityTransfer.tendsto_normalized_weighted_event_mass
    (fun _ => pathMeasure d.kernel x) (inverseWeight d)
    (measurable_inverseWeight (K := C.toKilledKernel) d)
    (integrable_inverseWeight (K := C.toKilledKernel) d x)
    (fun _ _ => inv_nonneg.2 ENNReal.toReal_nonneg)
    (fun n => qHistoryEvent C d n (A n)) (fun n => measurableSet_qHistoryEvent C d n (hA n)) hp
    (inverseWeight_uniformly_integrable h d s.continuous_weight (μ : Measure M) hleft hnorm x)
    hm.1 hm.2
  have heq (n : ℕ) :
      ((∫ ω in qHistoryEvent C d n (A n), inverseWeight d n ω ∂pathMeasure d.kernel x) /
        (∫ ω, inverseWeight d n ω ∂pathMeasure d.kernel x)) =
      (C.pathMeasure x.val ({ω : Path M | Preorder.frestrictLe n ω ∈ A n} ∩
          Cited.liveThrough C.killedTransition (n+1)) /
        C.pathMeasure x.val (Cited.liveThrough C.killedTransition (n+1))).toReal := by
    have hnum := inverse_history_event C d x n (A n) (hA n)
    have hden := inverse_history_event C d x n univ MeasurableSet.univ
    have hall : qHistoryEvent C d n univ = univ := by ext ω; simp [qHistoryEvent]
    rw [hall, Measure.restrict_univ] at hden
    have hAE := ae_liveThrough_iff_endpoint C d hlive x.val n
    have hnumset : {ω : Path M | Preorder.frestrictLe n ω ∈ A n ∧ C.cemeteryWeight d (ω n) ≠ 0} =ᵐ[C.pathMeasure x.val]
        {ω : Path M | Preorder.frestrictLe n ω ∈ A n} ∩ Cited.liveThrough C.killedTransition (n+1) := by
      filter_upwards [hAE] with ω hω
      simp only [mem_ofPred_eq, mem_inter_iff, hω]
    have hdenset : {ω : Path M | Preorder.frestrictLe n ω ∈ (univ : Set (History (Option M) n)) ∧
        C.cemeteryWeight d (ω n) ≠ 0} =ᵐ[C.pathMeasure x.val]
        Cited.liveThrough C.killedTransition (n+1) := by
      filter_upwards [hAE] with ω hω
      simp only [mem_univ, true_and]
      exact propext hω.symm
    rw [measure_congr hnumset] at hnum
    rw [measure_congr hdenset] at hden
    rw [hnum, hden, ENNReal.toReal_div]
    have ha : (d.rate.toReal)⁻¹ ^ n * ((d.weight x.val).toReal)⁻¹ ≠ 0 := by
      apply mul_ne_zero
      · exact pow_ne_zero _ (inv_ne_zero (ENNReal.toReal_ne_zero.2 ⟨d.rate_ne_zero, d.rate_ne_top⟩))
      · exact inv_ne_zero (ENNReal.toReal_ne_zero.2 ⟨x.property, d.weight_ne_top _⟩)
    exact mul_div_mul_left _ _ ha
  have ht' := ht.congr heq
  apply (ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top).1 ht'
  exact (ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)
    |>.trans_lt ENNReal.one_lt_top).ne

def averageHistoryEvent (f : M → ℝ) (ε Γ : ℝ) (n : ℕ) : Set (History (Option M) n) :=
  (ConditionalTransfer.extend n) ⁻¹' ConditionalTransfer.avgSet f ε Γ (n+1) (n+1)

omit [MeasurableSpace M] in
omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem average_extend_eq (f : M → ℝ) (n : ℕ) (ω : Path M) :
    pathBirkhoffSum f (n+1) (ConditionalTransfer.extend n (Preorder.frestrictLe n ω)) =
      pathBirkhoffSum f (n+1) ω := by
  apply ConditionalTransfer.pathBirkhoffSum_congr
  intro i hi
  simp [ConditionalTransfer.extend, Preorder.frestrictLe, show i ≤ n by omega]

set_option backward.isDefEq.respectTransparency false in
theorem transfer_average (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (x : d.State)
    {f : M → ℝ} (hf : Measurable f) (Γ : ℝ)
    (hQ : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => pathMeasure d.kernel x
      {ω | ε < |Cited.doobAverage d f n ω - Γ|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      C.pathMeasure x.val ({ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - Γ|} ∩
        Cited.liveThrough C.killedTransition n) /
        C.pathMeasure x.val (Cited.liveThrough C.killedTransition n)) atTop (𝓝 0) := by
  intro ε hε
  let A := averageHistoryEvent (M := M) f ε Γ
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (ConditionalTransfer.measurableSet_avgSet hf _ _ _ _).preimage (ConditionalTransfer.measurable_extend n)
  have hqset (n : ℕ) : qHistoryEvent C d n (A n) =
      {ω | ε < |Cited.doobAverage d f (n+1) ω - Γ|} := by
    ext ω
    have hm : historyMap (fun y : d.State => some y.val) n (Preorder.frestrictLe n ω) =
        Preorder.frestrictLe n (fun i => some (ω i).val) := rfl
    simp only [qHistoryEvent, mem_ofPred_eq, A, averageHistoryEvent, mem_preimage, hm,
      ConditionalTransfer.avgSet, average_extend_eq]
    rfl
  have hcset (n : ℕ) : {ω : Path M | Preorder.frestrictLe n ω ∈ A n} =
      {ω | ε < |((n+1 : ℕ) : ℝ)⁻¹ * pathBirkhoffSum f (n+1) ω - Γ|} := by
    ext ω
    simp only [mem_ofPred_eq, A, averageHistoryEvent, mem_preimage,
      ConditionalTransfer.avgSet, average_extend_eq]
  have hp : Tendsto (fun n => pathMeasure d.kernel x (qHistoryEvent C d n (A n))) atTop (𝓝 0) := by
    apply ((hQ ε hε).comp (tendsto_add_atTop_nat 1)).congr
    intro n
    rw [hqset n]
    rfl
  have ht := transfer_history_events C h d s hlive x A hAm hp
  apply (tendsto_add_atTop_iff_nat 1).1
  apply ht.congr
  intro n
  rw [hcset n]

end
end ConditionedStableLaws.KilledLiveTransfer
