import ConditionedStableLaws.ConditionalTransferBasic
import ConditionedStableLaws.KilledLiveTransfer

/-!
# Probability and bounded-mean transfer under survival conditioning

The transfer for the chain killed on `Z` uses inverse endpoint weights. The entrance-time
decomposition and geometric estimates transfer it to the original survival condition.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.ConditionalTransfer

noncomputable section

open StandingHypothesis CanonicalChain QProcessLimit

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

section Main

variable [MetricSpace M] [CompactSpace M] [BorelSpace M] {ρ : Measure M}

omit [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem avgSet_subset {f : M → ℝ} {ε Γ : ℝ} {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hsmall : ((n : ℝ) - m) / n * |Γ| ≤ ε / 2) :
    avgSet f ε Γ n m ⊆ avgSet f (ε / 2) Γ m m := by
  intro ω hω
  simp only [avgSet, Set.mem_ofPred_eq] at hω ⊢
  set S := pathBirkhoffSum f m ω
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hid : (n : ℝ)⁻¹ * S - Γ = (m / n) * ((m : ℝ)⁻¹ * S - Γ) - ((n - m) / n) * Γ := by
    field_simp
    ring
  have hle : |(n : ℝ)⁻¹ * S - Γ| ≤ |(m : ℝ)⁻¹ * S - Γ| + ((n : ℝ) - m) / n * |Γ| := by
    rw [hid]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (div_nonneg hm'.le hn.le)]
      exact mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hn).2 hmn')
    · rw [abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.2 hmn') hn.le)]
  linarith

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem ratio_mono {f : M → ℝ} {ε ε' Γ : ℝ} (x : M) {n m n' m' : ℕ} (hm : m = m')
    (hsub : avgSet f ε Γ n m ⊆ avgSet f ε' Γ n' m') :
    ratio C f ε Γ x n m ≤ ratio C f ε' Γ x n' m' := by
  subst hm
  unfold ratio
  apply ENNReal.toReal_mono
  · exact (ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)
      |>.trans_lt ENNReal.one_lt_top).ne
  · exact ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ hsub)) _

/-- **Conditional transfer (i).** Convergence of the Birkhoff averages to `Γ` in `ℚₓ`-probability
implies convergence in `ℙₓ(· | τ > n)`-probability, for every measurable `h` vanishing on `Z` and
every `x ∈ M \ Z`. -/
theorem conditional_transfer (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (x : d.State)
    {f : M → ℝ} (hf : Measurable f) (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0)
    (Γ : ℝ)
    (hQ : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => QProcessLimit.pathMeasure d.kernel x
        {ω | ε < |Cited.doobAverage d f n ω - Γ|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => C.conditionedMeasure x.val n
        {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - Γ|}) atTop (𝓝 0) := by
  intro ε hε
  have htransfer := KilledLiveTransfer.transfer_average C h d s hlive x hf Γ hQ
  -- The τ̃-conditioned probabilities, in real form.
  have hq (ε' : ℝ) (hε' : 0 < ε') :
      Tendsto (fun m => ratio C f ε' Γ x.val m m) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (htransfer ε' hε')
    rw [ENNReal.toReal_zero] at this
    exact this
  obtain ⟨D, hD, hbound⟩ := transfer_estimate C h d s hlive x hf hZ ε Γ
  set θ := s.decay
  -- Each reflected term tends to zero.
  have hfixed (j : ℕ) :
      Tendsto (fun n => ratio C f ε Γ x.val n (n - 1 - j)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => ratio C f (ε / 2) Γ x.val (n - 1 - j) (n - 1 - j))
        atTop (𝓝 0) :=
      (hq (ε / 2) (half_pos hε)).comp
        ((tendsto_sub_atTop_nat 1).comp (tendsto_sub_atTop_nat j) |>.congr
          (fun n => by simp [Nat.sub_sub, add_comm]))
    have hsmall : ∀ᶠ n : ℕ in atTop, ((j + 1 : ℝ) / n) * |Γ| ≤ ε / 2 := by
      have : Tendsto (fun n : ℕ => ((j + 1 : ℝ) / n) * |Γ|) atTop (𝓝 0) := by
        simpa using (tendsto_const_div_atTop_nhds_zero_nat (j + 1 : ℝ)).mul_const |Γ|
      exact this.eventually (ge_mem_nhds (half_pos hε))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => ratio_nonneg C f ε Γ x.val n _) ?_
    filter_upwards [hsmall, eventually_ge_atTop (j + 2)] with n hn hn2
    apply ratio_mono C x.val rfl
    apply avgSet_subset (by omega) (by omega)
    have hcast : ((n : ℝ) - ((n - 1 - j : ℕ) : ℝ)) = j + 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcast]
    exact hn
  -- Dominated convergence for the geometric series.
  let F : ℕ → ℕ → ℝ := fun n j => if j < n then θ ^ j * ratio C f ε Γ x.val n (n - 1 - j) else 0
  have hF : Tendsto (fun n => ∑' j, F n j) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := F) (g := fun _ => (0 : ℝ))
      (bound := fun j => θ ^ j) (summable_geometric_of_lt_one s.decay_nonneg s.decay_lt_one)
      (fun j => by
        have : Tendsto (fun n => θ ^ j * ratio C f ε Γ x.val n (n - 1 - j)) atTop (𝓝 0) := by
          simpa using (hfixed j).const_mul (θ ^ j)
        apply this.congr'
        filter_upwards [eventually_gt_atTop j] with n hn
        simp [F, hn])
      (Eventually.of_forall fun n j => by
        simp only [F]
        split_ifs
        · rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg s.decay_nonneg _)
            (ratio_nonneg C f ε Γ x.val n _))]
          exact mul_le_of_le_one_right (pow_nonneg s.decay_nonneg _)
            (ratio_le_one C f ε Γ x.val n _)
        · simpa using pow_nonneg s.decay_nonneg j)
    simpa using this
  have hsum_eq (n : ℕ) : ∑ m ∈ Finset.range n, θ ^ (n - m - 1) * ratio C f ε Γ x.val n m =
      ∑' j, F n j := by
    rw [tsum_eq_sum (s := Finset.range n) (fun j hj => by
      simp [F, Finset.mem_range.not.1 hj])]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.1 hj
    simp only [F, hjn, ite_true]
    congr 2
    omega
  -- Squeeze in real numbers.
  have hreal : Tendsto (fun n => (C.conditionedMeasure x.val n
      (avgSet f ε Γ n n)).toReal) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => D * (ratio C f ε Γ x.val n n + ∑' j, F n j))
        atTop (𝓝 0) := by
      simpa using ((hq ε hε).add hF).const_mul D
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => ENNReal.toReal_nonneg) (fun n => ?_)
    rw [← hsum_eq]
    exact hbound n
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  have hfin (n : ℕ) : C.conditionedMeasure x.val n (avgSet f ε Γ n n) ≠ ∞ := by
    have := C.conditionedMeasure_isProbability_of_surviving x.val hx n
    exact measure_ne_top _ _
  rw [← ENNReal.toReal_zero] at hreal
  exact (ENNReal.tendsto_toReal_iff hfin ENNReal.zero_ne_top).1 hreal

/-- **Conditional transfer (ii).** For bounded `h`, the conditioned mean of `|Γₙ - Γ|` tends to
zero. -/
theorem conditional_transfer_mean (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (x : d.State)
    {f : M → ℝ} (hf : Measurable f) (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0)
    {H : ℝ} (hH : ∀ y, |f y| ≤ H) (Γ : ℝ)
    (hQ : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => QProcessLimit.pathMeasure d.kernel x
        {ω | ε < |Cited.doobAverage d f n ω - Γ|}) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ ω, |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - Γ|
      ∂C.conditionedMeasure x.val n) atTop (𝓝 0) := by
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  have := fun n => C.conditionedMeasure_isProbability_of_surviving x.val hx n
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH x.val)
  apply BoundedConvergence.tendsto_integral_abs_of_bounded_in_probability
    (fun n => C.conditionedMeasure x.val n)
    (fun n ω => (n : ℝ)⁻¹ * pathBirkhoffSum f n ω - Γ)
    (fun n => ((measurable_pathBirkhoffSum hf n).const_mul _).sub_const _) (H + |Γ|)
  · intro n
    refine Eventually.of_forall fun ω => ?_
    have hsum : |pathBirkhoffSum f n ω| ≤ n * H := by
      unfold pathBirkhoffSum birkhoffSum
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range n, |zeroExtension f (ω i)| ≤ ∑ _i ∈ Finset.range n, H := by
            apply Finset.sum_le_sum
            intro i _
            cases hω : ω i with
            | none => simp [zeroExtension_none, hH0]
            | some y => rw [zeroExtension_some]; exact hH y
        _ = n * H := by simp
    have havg : |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω| ≤ H := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hn, hH0]
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [abs_mul, abs_inv, Nat.abs_cast, inv_mul_le_iff₀ hn']
        exact hsum
    exact (abs_sub _ _).trans (add_le_add havg le_rfl)
  · intro ε hε
    have := conditional_transfer C h d s hlive x hf hZ Γ hQ ε hε
    have hfin (n : ℕ) : C.conditionedMeasure x.val n
        {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f n ω - Γ|} ≠ ∞ := measure_ne_top _ _
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
    rw [ENNReal.toReal_zero] at h'
    exact h'

end Main

end

end ConditionedStableLaws.ConditionalTransfer
