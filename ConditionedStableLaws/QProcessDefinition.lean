import ConditionedStableLaws.HypothesisQProcess

/-!
# The `Q`-process

A family `(ℚ_x)_{x ∈ M∖Z}` of probability measures on the canonical path space is a `Q`-process if
every finite-history event `A ∈ 𝓕ₙ` satisfies `ℚ_x(A) = lim_t ℙ_x(A | τ > t)`, and the coordinate
process is Markov under `ℚ_x` with transition probabilities `𝒬ᵐ(y, B) = ℚ_y[X_m ∈ B]`. The Markov
property is stated for a complete finite past: for nonnegative measurable `F` of `(X₀, …, Xₙ)` and
`g` of `X_{n+m}`, `𝔼_{ℚ_x}[F · g(X_{n+m})] = 𝔼_{ℚ_x}[F · 𝔼_{ℚ_{Xₙ}} g(X_m)]`. The state space `M ∖
Z` is the set `S` of nonescaping states, and the process is required to stay in it. A `Q`-process is
unique by definition. Under H the canonical Doob trajectory law is a `Q`-process.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.CanonicalChain

noncomputable section

open StandingHypothesis QProcessLimit

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- A family indexed by states, extended to the cemetery by the constant path. -/
def extendQ (Q : M → Measure (Path M)) : Option M → Measure (Path M)
  | some y => Q y
  | none => Measure.dirac fun _ => none

/-- **The `Q`-process**, on the state space `S = M ∖ Z`. -/
structure IsQProcess (S : Set M) (Q : M → Measure (Path M)) : Prop where
  isProbability : ∀ x ∈ S, IsProbabilityMeasure (Q x)
  limit : ∀ x ∈ S, ∀ (n : ℕ) (A : Set (History (Option M) n)), MeasurableSet A →
    Tendsto (fun t : ℕ => C.conditionedMeasure x t {ω | Preorder.frestrictLe n ω ∈ A}) atTop
      (𝓝 (Q x {ω | Preorder.frestrictLe n ω ∈ A}))
  stays : ∀ x ∈ S, ∀ n : ℕ, ∀ᵐ ω ∂Q x, ω n ∈ (Option.some : M → Option M) '' S
  markov : ∀ x ∈ S, ∀ (n m : ℕ) (F : History (Option M) n → ℝ≥0∞), Measurable F →
    ∀ g : Option M → ℝ≥0∞, Measurable g →
      ∫⁻ ω, F (Preorder.frestrictLe n ω) * g (ω (n + m)) ∂Q x =
        ∫⁻ ω, F (Preorder.frestrictLe n ω) * ∫⁻ ω', g (ω' m) ∂extendQ Q (ω n) ∂Q x

/-- A `Q`-process is unique: its finite-dimensional laws are the conditioned limits. -/
theorem IsQProcess.unique {S : Set M} {Q Q' : M → Measure (Path M)}
    (hQ : C.IsQProcess S Q) (hQ' : C.IsQProcess S Q') {x : M} (hx : x ∈ S) : Q x = Q' x := by
  have := hQ.isProbability x hx
  have := hQ'.isProbability x hx
  let P : (I : Finset ℕ) → Measure ((i : I) → (fun _ : ℕ => Option M) i) :=
    fun I => (Q x).map I.restrict
  have hP : IsProjectiveLimit (Q x) P := fun I => rfl
  have hPf : IsProjectiveMeasureFamily (α := fun _ : ℕ => Option M) P := by
    intro I J hJI
    simp only [P]
    rw [Measure.map_map (Finset.measurable_restrict₂ hJI) (Finset.measurable_restrict I)]
    rfl
  have : ∀ I, IsFiniteMeasure (P I) := fun I => by simp only [P]; infer_instance
  refine hP.unique ((MeasureTheory.isProjectiveLimit_nat_iff' hPf (Q' x) 0).2
    fun n _ => ?_)
  ext A hA
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) hA]
  simp only [P]
  rw [Measure.map_apply (Finset.measurable_restrict _) hA]
  exact tendsto_nhds_unique (hQ'.limit x hx n A hA) (hQ.limit x hx n A hA)

/-! ### The Doob trajectory law is a `Q`-process -/

theorem measurableSet_some_image' {A : Set M} (hA : MeasurableSet A) :
    MeasurableSet ((Option.some : M → Option M) '' A) :=
  measurableEmbedding_some_state.measurableSet_image' hA

/-- Forget that the coordinates of a Doob trajectory are live. -/
def coePath (d : DoobTransform.EigenData C.killedTransition) :
    (ℕ → (C.cemeteryEigenData d).State) → Path M := fun ω n => (ω n).val

theorem measurable_coePath (d : DoobTransform.EigenData C.killedTransition) :
    Measurable (C.coePath d) :=
  Measurable.of_eval fun n => measurable_subtype_coe.comp (measurable_pi_apply n)

open Classical in
/-- The Doob trajectory laws, viewed on the canonical path space. -/
def doobQ (d : DoobTransform.EigenData C.killedTransition) (x : M) : Measure (Path M) :=
  if hx : x ∈ d.liveSet then (C.doobPathMeasure d ⟨x, hx⟩).map (C.coePath d) else 0

theorem doobQ_of_mem (d : DoobTransform.EigenData C.killedTransition) {x : M}
    (hx : x ∈ d.liveSet) :
    C.doobQ d x = (C.doobPathMeasure d ⟨x, hx⟩).map (C.coePath d) := by
  simp [doobQ, hx]

theorem coeHistory_frestrictLe (d : DoobTransform.EigenData C.killedTransition) (n : ℕ)
    (ω : ℕ → (C.cemeteryEigenData d).State) :
    coeHistory (C.cemeteryEigenData d) n (Preorder.frestrictLe n ω) =
      Preorder.frestrictLe n (C.coePath d ω) := rfl

theorem doobQ_cylinder (d : DoobTransform.EigenData C.killedTransition) {x : M}
    (hx : x ∈ d.liveSet) (n : ℕ) (A : Set (History (Option M) n)) (hA : MeasurableSet A) :
    C.doobQ d x {ω | Preorder.frestrictLe n ω ∈ A} =
      C.doobPathMeasure d ⟨x, hx⟩
        {ω | coeHistory (C.cemeteryEigenData d) n (Preorder.frestrictLe n ω) ∈ A} := by
  rw [show {ω : Path M | Preorder.frestrictLe n ω ∈ A} = Preorder.frestrictLe n ⁻¹' A from rfl,
    C.doobQ_of_mem d hx, Measure.map_apply (C.measurable_coePath d)
    (hA.preimage (Preorder.measurable_frestrictLe n))]
  rfl

/-- The law of `X_m` under a Doob trajectory law. -/
theorem lintegral_coord_doob (d : DoobTransform.EigenData C.killedTransition)
    (z : (C.cemeteryEigenData d).State) (m : ℕ) (g : (C.cemeteryEigenData d).State → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ ω, g (ω m) ∂QProcessLimit.pathMeasure (C.cemeteryEigenData d).kernel z =
      ∫⁻ y, g y ∂((C.cemeteryEigenData d).kernel ^ m) z := by
  have h := lintegral_history_future (C.cemeteryEigenData d).kernel z 0 m (fun _ => 1)
    measurable_const g hg
  simp only [one_mul, zero_add] at h
  rw [h, historyLaw_zero, lintegral_dirac' _
    (show Measurable fun h : History (C.cemeteryEigenData d).State 0 =>
      ∫⁻ y, g y ∂((C.cemeteryEigenData d).kernel ^ m) (last 0 h) from
      hg.lintegral_kernel.comp (measurable_pi_apply _))]
  rfl

theorem lintegral_extendQ_doob (d : DoobTransform.EigenData C.killedTransition)
    (z : (C.cemeteryEigenData d).State) (m : ℕ) (g : Option M → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω', g (ω' m) ∂extendQ (C.doobQ d) z.val =
      ∫⁻ y, g y.val ∂((C.cemeteryEigenData d).kernel ^ m) z := by
  obtain ⟨z, hz⟩ := z
  cases z with
  | none => exact absurd rfl hz
  | some y =>
      have hy : y ∈ d.liveSet := hz
      have hstart : C.doobStart d ⟨y, hy⟩ = ⟨some y, hz⟩ := rfl
      simp only [extendQ]
      rw [C.doobQ_of_mem d hy, lintegral_map
        (show Measurable fun ω' : Path M => g (ω' m) from hg.comp (measurable_pi_apply m))
        (C.measurable_coePath d)]
      unfold doobPathMeasure
      rw [hstart]
      exact C.lintegral_coord_doob d _ m (fun y => g y.val) (hg.comp measurable_subtype_coe)

theorem doobQ_markov (d : DoobTransform.EigenData C.killedTransition) {x : M}
    (hx : x ∈ d.liveSet) (n m : ℕ) (F : History (Option M) n → ℝ≥0∞) (hF : Measurable F)
    (g : Option M → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, F (Preorder.frestrictLe n ω) * g (ω (n + m)) ∂C.doobQ d x =
      ∫⁻ ω, F (Preorder.frestrictLe n ω) * ∫⁻ ω', g (ω' m) ∂extendQ (C.doobQ d) (ω n)
        ∂C.doobQ d x := by
  set K' := (C.cemeteryEigenData d).kernel
  set F' : History (C.cemeteryEigenData d).State n → ℝ≥0∞ :=
    fun h => F (coeHistory (C.cemeteryEigenData d) n h)
  have hF' : Measurable F' := hF.comp (measurable_coeHistory _ n)
  set g' : (C.cemeteryEigenData d).State → ℝ≥0∞ := fun y => g y.val
  have hg' : Measurable g' := hg.comp measurable_subtype_coe
  set G : (C.cemeteryEigenData d).State → ℝ≥0∞ := fun z => ∫⁻ y, g' y ∂(K' ^ m) z
  have hG : Measurable G := hg'.lintegral_kernel
  have hL : Measurable fun ω : Path M => F (Preorder.frestrictLe n ω) * g (ω (n + m)) :=
    (hF.comp (Preorder.measurable_frestrictLe n)).mul (hg.comp (measurable_pi_apply _))
  have hemb : MeasurableEmbedding
      (Subtype.val : (C.cemeteryEigenData d).State → Option M) :=
    MeasurableEmbedding.subtype_coe (C.cemeteryEigenData d).measurableSet_liveSet
  set H : Option M → ℝ≥0∞ := Function.extend Subtype.val G 0 with hH_def
  have hH : Measurable H := hemb.measurable_extend hG measurable_const
  have hHG : ∀ z, H z.val = G z := fun z => hemb.injective.extend_apply _ _ z
  have hlive : ∀ᵐ ω ∂C.doobQ d x, ω n ∈ (C.cemeteryEigenData d).liveSet := by
    rw [C.doobQ_of_mem d hx, ae_map_iff (C.measurable_coePath d).aemeasurable
      ((C.cemeteryEigenData d).measurableSet_liveSet.preimage (measurable_pi_apply n))]
    exact Eventually.of_forall fun ω => (ω n).property
  have hRHS : ∫⁻ ω, F (Preorder.frestrictLe n ω) *
        ∫⁻ ω', g (ω' m) ∂extendQ (C.doobQ d) (ω n) ∂C.doobQ d x =
      ∫⁻ ω, F (Preorder.frestrictLe n ω) * H (ω n) ∂C.doobQ d x := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlive] with ω hω
    have := C.lintegral_extendQ_doob d ⟨ω n, hω⟩ m g hg
    rw [hHG ⟨ω n, hω⟩]
    exact congrArg _ this
  rw [hRHS, C.doobQ_of_mem d hx, lintegral_map hL (C.measurable_coePath d),
    lintegral_map (show Measurable fun ω : Path M => F (Preorder.frestrictLe n ω) * H (ω n) from
      (hF.comp (Preorder.measurable_frestrictLe n)).mul (hH.comp (measurable_pi_apply n)))
      (C.measurable_coePath d)]
  have e1 : ∫⁻ ω, F (Preorder.frestrictLe n (C.coePath d ω)) * g (C.coePath d ω (n + m))
        ∂C.doobPathMeasure d ⟨x, hx⟩ =
      ∫⁻ ω, F' (Preorder.frestrictLe n ω) * g' (ω (n + m))
        ∂QProcessLimit.pathMeasure K' (C.doobStart d ⟨x, hx⟩) := rfl
  have e2 : ∫⁻ ω, F (Preorder.frestrictLe n (C.coePath d ω)) * H (C.coePath d ω n)
        ∂C.doobPathMeasure d ⟨x, hx⟩ =
      ∫⁻ ω, F' (Preorder.frestrictLe n ω) * G (ω (n + 0))
        ∂QProcessLimit.pathMeasure K' (C.doobStart d ⟨x, hx⟩) :=
    lintegral_congr fun ω => congrArg _ (hHG (ω n))
  rw [e1, e2, lintegral_history_future K' _ n m F' hF' g' hg',
    lintegral_history_future K' _ n 0 F' hF' G hG]
  refine lintegral_congr fun h => ?_
  simp only [pow_zero, show (1 : Kernel _ _) = Kernel.id from rfl, Kernel.id_apply,
    lintegral_dirac' _ hG, G]

/-- **The Doob trajectory law is the `Q`-process**, on `S = M ∖ Z`, under H. -/
theorem _root_.ConditionedStableLaws.StandingHypothesis.HypothesisH.exists_isQProcess
    [MetricSpace M] [CompactSpace M] [BorelSpace M] {ρ : Measure M}
    (h : HypothesisH ρ C.toKilledKernel) :
    ∃ d : DoobTransform.EigenData C.killedTransition,
      d.liveSet = survivingSet C.killedTransition ∧
      C.IsQProcess (survivingSet C.killedTransition) (C.doobQ d) := by
  obtain ⟨d, _, _, hlive, hlim⟩ := C.exists_conditioned_cylinder_limit h
  refine ⟨d, hlive, ⟨fun x hx => ?_, fun x hx n A hA => ?_, fun x hx n => ?_,
    fun x hx n m F hF g hg => ?_⟩⟩
  all_goals rw [← hlive] at hx
  · rw [C.doobQ_of_mem d hx]
    exact (Measure.isProbabilityMeasure_map_iff (C.measurable_coePath d).aemeasurable).2
      inferInstance
  · rw [C.doobQ_cylinder d hx n A hA]
    exact hlim ⟨x, hx⟩ n A hA
  · rw [← hlive, C.doobQ_of_mem d hx, ae_map_iff (C.measurable_coePath d).aemeasurable
      ((measurableSet_some_image' d.measurableSet_liveSet).preimage (measurable_pi_apply n))]
    refine Eventually.of_forall fun ω => ?_
    change (ω n).val ∈ _
    generalize ω n = w
    obtain ⟨z, hz⟩ := w
    cases z with
    | none => exact absurd rfl hz
    | some y => exact ⟨y, hz, rfl⟩
  · exact C.doobQ_markov d hx n m F hF g hg

end

end ConditionedStableLaws.CanonicalChain
