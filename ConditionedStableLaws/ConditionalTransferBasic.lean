import ConditionedStableLaws.Cited.QProcess
import ConditionedStableLaws.BoundedConvergence
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Transfer from the Q-process to survival-conditioned laws

Let `x ∈ M \ Z` and let `h` be measurable with `h|_Z = 0`. If the Birkhoff averages `Γₙ` converge to
`Γ*` in `ℚₓ`-probability, then they converge to `Γ*` in `ℙₓ(· | τ > n)`-probability; if `h` is
bounded, also in conditional mean. The ingredients are: the decomposition of `{τ > n}` by the first
entrance time into `Z`, the absence of returns from `Z` to `M \ Z`, the geometric decay of survival
from `Z`, and dominated convergence of the resulting series.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ConditionedStableLaws.ConditionalTransfer

noncomputable section

open StandingHypothesis CanonicalChain QProcessLimit

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-! ### Path-space facts -/

/-- Live states in a measurable set `A`, as a measurable set of `Option M`. -/
theorem measurableSet_some_image {A : Set M} (hA : MeasurableSet A) :
    MeasurableSet ((Option.some : M → Option M) '' A) :=
  measurableEmbedding_some_state.measurableSet_image' hA

/-- At a fixed step, a path in a set with no transitions into `L` does not
move into `L`, almost surely. -/
theorem ae_no_entry_step {Zs L : Set M} (hL : MeasurableSet L) (hZs : MeasurableSet Zs)
    (hno : ∀ z ∈ Zs, C.killedTransition z L = 0) (x : M) (n : ℕ) :
    ∀ᵐ ω ∂C.pathMeasure x, ω n ∈ Option.some '' Zs → ω (n + 1) ∉ Option.some '' L := by
  let p : ((i : Finset.Iic n) → Option M) × Option M → Prop :=
    fun z => z.1 ⟨n, by simp⟩ ∈ Option.some '' Zs → z.2 ∉ Option.some '' L
  have hp : MeasurableSet {z | p z} := by
    apply MeasurableSet.imp
    · exact (measurableSet_some_image hZs).preimage ((measurable_pi_apply _).comp measurable_fst)
    · exact (measurableSet_some_image hL).compl.preimage measurable_snd
  have hprod : ∀ᵐ z ∂((C.pathMeasure x).map (Preorder.frestrictLe n) ⊗ₘ
      C.historyKernel n), p z := by
    apply Measure.ae_compProd_of_ae_ae hp
    apply Eventually.of_forall
    intro ω
    change ∀ᵐ y ∂C.historyKernel n ω, ω ⟨n, by simp⟩ ∈ Option.some '' Zs →
      y ∉ Option.some '' L
    by_cases hlast : ω ⟨n, by simp⟩ ∈ Option.some '' Zs
    · obtain ⟨z, hz, hzω⟩ := hlast
      have hnull : C.historyKernel n ω (Option.some '' L) = 0 := by
        rw [C.historyKernel_apply, ← hzω, ← C.killedTransition_apply z L hL]
        exact hno z hz
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall (fun _ h => False.elim (hlast h))
  rw [C.pathMeasure_past_next] at hprod
  exact ae_of_ae_map
    ((Preorder.measurable_frestrictLe n).prod (measurable_pi_apply (n + 1))).aemeasurable
    hprod

/-- Almost surely, once a surviving path lies in a set `Zs = Lᶜ` with no
transitions into `L`, it stays there while it survives. -/
theorem ae_stays {L : Set M} (hL : MeasurableSet L)
    (hno : ∀ z ∈ Lᶜ, C.killedTransition z L = 0) (x : M) :
    ∀ᵐ ω ∂C.pathMeasure x, ∀ m n : ℕ, m ≤ n → ω m ∈ Option.some '' Lᶜ →
      (∀ k ≤ n, ω k ≠ none) → ∀ k, m ≤ k → k ≤ n → ω k ∈ Option.some '' Lᶜ := by
  have hsteps := ae_all_iff.2 (fun n => ae_no_entry_step C hL hL.compl hno x n)
  filter_upwards [hsteps] with ω hω
  intro m n _ hm halive k hmk hkn
  induction k, hmk using Nat.le_induction with
  | base => exact hm
  | succ k hmk ih =>
      have hk := ih (by omega)
      have hnot := hω k hk
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (halive (k + 1) hkn)
      refine ⟨y, ?_, hy.symm⟩
      intro hyL
      exact hnot ⟨y, hyL, hy.symm⟩

/-- The survival-weighted law of a finite history: the unnormalized conditioned cylinder law. -/
theorem pathMeasure_survival_cylinder (x : M) (n m : ℕ)
    (A : Set (History (Option M) n)) (hA : MeasurableSet A) :
    C.pathMeasure x (survival (n + m) ∩ {ω | Preorder.frestrictLe n ω ∈ A}) =
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
  rw [← hprod]
  exact hm

/-- Extending a finite history by the cemetery. -/
def extend (n : ℕ) (h : History (Option M) n) : Path M :=
  fun i => if hi : i ≤ n then h ⟨i, Finset.mem_Iic.2 hi⟩ else none

theorem measurable_extend (n : ℕ) : Measurable (extend (M := M) n) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ≤ n
  · simp only [extend, hi, dite_true]
    exact measurable_pi_apply _
  · simp only [extend, hi, dite_false]
    exact measurable_const

/-- Markov bound at time `m`: for an event `S` determined by the history up to
time `m` and forcing `X_m ∈ Zs`, survival for another `k` steps costs at most
the largest `k`-step survival probability from `Zs`. -/
theorem pathMeasure_inter_survival_le (x : M) (m k : ℕ) (S : Set (Path M))
    (hS : MeasurableSet S)
    (hdep : ∀ ω ω' : Path M, (∀ i ≤ m, ω i = ω' i) → (ω ∈ S ↔ ω' ∈ S))
    {Zs : Set M} (hSZ : ∀ ω ∈ S, ω m ∈ Option.some '' Zs) {b : ℝ≥0∞}
    (hb : ∀ z ∈ Zs, (C.killedTransition ^ k) z univ ≤ b) :
    C.pathMeasure x (S ∩ survival (m + k)) ≤ C.pathMeasure x S * b := by
  set A : Set (History (Option M) m) := extend m ⁻¹' S
  have hA : MeasurableSet A := hS.preimage (measurable_extend m)
  have hext (ω : Path M) : extend m (Preorder.frestrictLe m ω) ∈ S ↔ ω ∈ S := by
    apply hdep
    intro i hi
    simp [extend, hi, Preorder.frestrictLe]
  have hSA : S = {ω : Path M | Preorder.frestrictLe m ω ∈ A} := by
    ext ω
    exact (hext ω).symm
  have hmap : (C.pathMeasure x).map (Preorder.frestrictLe m) A = C.pathMeasure x S := by
    rw [Measure.map_apply (Preorder.measurable_frestrictLe m) hA]
    exact congrArg _ hSA.symm
  rw [inter_comm, hSA, pathMeasure_survival_cylinder C x m k A hA, ← hSA, ← hmap, mul_comm,
    ← setLIntegral_const]
  apply setLIntegral_mono' hA
  intro hist hhist
  have hz := hSZ _ hhist
  obtain ⟨z, hzZ, hzeq⟩ := hz
  have hlast : last m hist = some z := by
    rw [hzeq]
    simp [extend, last]
  rw [hlast, C.remainingSurvival_some]
  exact hb z hzZ


/-! ### The first-entrance decomposition -/

/-- The event `{|n⁻¹ ∑_{i<m} h(Xᵢ) - Γ| > ε}`; for `m = n` it is `{|Γₙ - Γ| > ε}`,
and on `{τ̃ = m, τ > n}` it is `{|(m/n)Γₘ - Γ| > ε}`. -/
def avgSet (f : M → ℝ) (ε Γ : ℝ) (n m : ℕ) : Set (Path M) :=
  {ω | ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f m ω - Γ|}

theorem measurableSet_avgSet {f : M → ℝ} (hf : Measurable f) (ε Γ : ℝ) (n m : ℕ) :
    MeasurableSet (avgSet f ε Γ n m) :=
  measurableSet_lt measurable_const (continuous_abs.measurable.comp
    (((measurable_pathBirkhoffSum hf m).const_mul _).sub_const _))

omit [MeasurableSpace M] in
theorem pathBirkhoffSum_congr (f : M → ℝ) (m : ℕ) {ω ω' : Path M}
    (h : ∀ k < m, ω k = ω' k) : pathBirkhoffSum f m ω = pathBirkhoffSum f m ω' := by
  unfold pathBirkhoffSum birkhoffSum
  exact Finset.sum_congr rfl fun k hk => by dsimp only; rw [h k (Finset.mem_range.1 hk)]

omit [MeasurableSpace M] in
theorem pathBirkhoffSum_stop (f : M → ℝ) {m n : ℕ} (hmn : m ≤ n) (ω : Path M)
    (h : ∀ k, m ≤ k → k < n → zeroExtension f (ω k) = 0) :
    pathBirkhoffSum f n ω = pathBirkhoffSum f m ω := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [pathBirkhoffSum_succ, ih (fun k hk hkn => h k hk (by omega)), h n hmn (by omega),
        add_zero]

theorem measurableSet_liveThrough {K : Kernel M M} (m : ℕ) :
    MeasurableSet (Cited.liveThrough K m) := by
  have : Cited.liveThrough K m =
      ⋂ i ∈ Finset.range m, {ω : Path M | ω i ∈ Option.some '' survivingSet K} := by
    ext ω
    simp only [Cited.liveThrough, Set.mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_image]
    constructor
    · intro hω i hi
      obtain ⟨y, hy, he⟩ := hω i hi
      exact ⟨y, hy, he.symm⟩
    · intro hω i hi
      obtain ⟨y, hy, he⟩ := hω i hi
      exact ⟨y, hy, he.symm⟩
  rw [this]
  exact Finset.measurableSet_biInter _ fun i _ =>
    (measurableSet_some_image (measurableSet_survivingSet K)).preimage (measurable_pi_apply i)

/-- First entrance into `Z` at time `m`, after staying in `M \ Z` before. -/
def entrance (K : Kernel M M) (m : ℕ) : Set (Path M) :=
  Cited.liveThrough K m ∩ {ω | ω m ∈ Option.some '' (survivingSet K)ᶜ}

theorem measurableSet_entrance {K : Kernel M M} (m : ℕ) : MeasurableSet (entrance K m) :=
  (measurableSet_liveThrough m).inter
    ((measurableSet_some_image (measurableSet_survivingSet K).compl).preimage
      (measurable_pi_apply m))

/-- Almost surely, a path in `{|Γₙ - Γ| > ε}` surviving through time `n` either
stays in `M \ Z` before `n`, or first enters `Z` at some `m < n`, after which
`Γₙ = (m/n) Γₘ`. -/
theorem ae_decomposition {f : M → ℝ}
    (hno : ∀ z ∈ (survivingSet C.killedTransition)ᶜ,
      C.killedTransition z (survivingSet C.killedTransition) = 0)
    (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0) (ε Γ : ℝ) (x : M) (n : ℕ) :
    ∀ᵐ ω ∂C.pathMeasure x, ω ∈ avgSet f ε Γ n n ∩ survival n →
      ω ∈ avgSet f ε Γ n n ∩ Cited.liveThrough C.killedTransition n ∨
        ∃ m < n, ω ∈ avgSet f ε Γ n m ∩ entrance C.killedTransition m ∩ survival n := by
  set L := survivingSet C.killedTransition
  filter_upwards [ae_stays C (measurableSet_survivingSet _) hno x] with ω hstay
  rintro ⟨hA, hsurv⟩
  by_cases hlive : ω ∈ Cited.liveThrough C.killedTransition n
  · exact Or.inl ⟨hA, hlive⟩
  right
  have hex : ∃ i, i < n ∧ ω i ∉ Option.some '' L := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hlive
    intro i hi
    obtain ⟨y, hy, he⟩ := hcon i hi
    exact ⟨y, hy, he.symm⟩
  classical
  let m := Nat.find hex
  have hm : m < n ∧ ω m ∉ Option.some '' L := Nat.find_spec hex
  have hmin : ∀ i < m, ω i ∈ Option.some '' L := by
    intro i hi
    by_contra hcon
    exact Nat.find_min hex hi ⟨by omega, hcon⟩
  have halive : ∀ k ≤ n, ω k ≠ none := hsurv
  have hmZ : ω m ∈ Option.some '' Lᶜ := by
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (halive m hm.1.le)
    refine ⟨y, ?_, hy.symm⟩
    intro hyL
    exact hm.2 ⟨y, hyL, hy.symm⟩
  have hLT : ω ∈ Cited.liveThrough C.killedTransition m := by
    intro i hi
    obtain ⟨y, hy, he⟩ := hmin i hi
    exact ⟨y, hy, he.symm⟩
  refine ⟨m, hm.1, ⟨⟨?_, hLT, hmZ⟩, hsurv⟩⟩
  have hstop : pathBirkhoffSum f n ω = pathBirkhoffSum f m ω := by
    apply pathBirkhoffSum_stop f hm.1.le
    intro k hmk hkn
    obtain ⟨z, hz, hzk⟩ := hstay m n hm.1.le hmZ halive k hmk hkn.le
    rw [← hzk, zeroExtension_some]
    exact hZ z (by simpa [survivingSet] using hz)
  change ε < |(n : ℝ)⁻¹ * pathBirkhoffSum f m ω - Γ|
  rw [← hstop]
  exact hA

/-- The measure form of the decomposition, with the Markov bound applied to
each first-entrance term: `bound k` controls survival for `k` steps from `Z`. -/
theorem decomposition_le {f : M → ℝ} (hf : Measurable f)
    (hno : ∀ z ∈ (survivingSet C.killedTransition)ᶜ,
      C.killedTransition z (survivingSet C.killedTransition) = 0)
    (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0) (ε Γ : ℝ) (x : M) (n : ℕ)
    (bound : ℕ → ℝ≥0∞)
    (hbound : ∀ k, ∀ z ∈ (survivingSet C.killedTransition)ᶜ,
      (C.killedTransition ^ k) z univ ≤ bound k) :
    C.pathMeasure x (survival n ∩ avgSet f ε Γ n n) ≤
      C.pathMeasure x (avgSet f ε Γ n n ∩ Cited.liveThrough C.killedTransition n) +
        ∑ m ∈ Finset.range n,
          C.pathMeasure x (avgSet f ε Γ n m ∩ Cited.liveThrough C.killedTransition m) *
            bound (n - m) := by
  set K := C.killedTransition
  have hcover : survival n ∩ avgSet f ε Γ n n ≤ᵐ[C.pathMeasure x]
      (avgSet f ε Γ n n ∩ Cited.liveThrough K n ∪
        ⋃ m ∈ Finset.range n, avgSet f ε Γ n m ∩ entrance K m ∩ survival n : Set (Path M)) := by
    filter_upwards [ae_decomposition C hno hZ ε Γ x n] with ω hω hmem
    rcases hω ⟨hmem.2, hmem.1⟩ with h1 | ⟨m, hm, h2⟩
    · exact Or.inl h1
    · exact Or.inr (mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hm)) h2)
  refine (measure_mono_ae hcover).trans ((measure_union_le _ _).trans (add_le_add le_rfl ?_))
  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hmn : m < n := Finset.mem_range.1 hm
  have hsplit : n = m + (n - m) := by omega
  set S := avgSet f ε Γ n m ∩ entrance K m
  have hS : MeasurableSet S := (measurableSet_avgSet hf ε Γ n m).inter (measurableSet_entrance m)
  have hdep : ∀ ω ω' : Path M, (∀ i ≤ m, ω i = ω' i) → (ω ∈ S ↔ ω' ∈ S) := by
    intro ω ω' hωω'
    have hsum := pathBirkhoffSum_congr f m (fun k hk => hωω' k hk.le)
    simp only [S, avgSet, entrance, Cited.liveThrough, mem_inter_iff, Set.mem_ofPred_eq, hsum,
      hωω' m le_rfl]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i hi => by rw [← hωω' i hi.le]; exact h2 i hi, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i hi => by rw [hωω' i hi.le]; exact h2 i hi, h3⟩
  calc C.pathMeasure x (S ∩ survival n)
      = C.pathMeasure x (S ∩ survival (m + (n - m))) := by rw [← hsplit]
    _ ≤ C.pathMeasure x S * bound (n - m) :=
        pathMeasure_inter_survival_le C x m (n - m) S hS hdep (fun ω hω => hω.2.2)
          (fun z hz => hbound (n - m) z hz)
    _ ≤ C.pathMeasure x (avgSet f ε Γ n m ∩ Cited.liveThrough K m) * bound (n - m) := by
        gcongr
        exact inter_subset_inter_right _ inter_subset_left


/-! ### Numerical estimates -/

/-- A positive sequence converging to a positive limit is bounded below by a
positive constant. -/
theorem exists_pos_lower_bound {a : ℕ → ℝ} {l : ℝ} (ha : ∀ n, 0 < a n) (hl : 0 < l)
    (hlim : Tendsto a atTop (𝓝 l)) : ∃ c > 0, ∀ n, c ≤ a n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (eventually_ge_nhds (half_lt_self hl)))
  obtain ⟨c₀, hc₀, hc₀le⟩ : ∃ c₀ > 0, ∀ n < N, c₀ ≤ a n := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · exact ⟨1, one_pos, fun n hn => by omega⟩
    · obtain ⟨k, hk, hkmin⟩ := (Finset.range N).exists_min_image a
        ⟨0, Finset.mem_range.2 hNpos⟩
      exact ⟨a k, ha k, fun n hn => hkmin n (Finset.mem_range.2 hn)⟩
  refine ⟨min c₀ (l / 2), lt_min hc₀ (half_pos hl), fun n => ?_⟩
  by_cases hn : n < N
  · exact (min_le_left _ _).trans (hc₀le n hn)
  · exact (min_le_right _ _).trans (hN n (not_lt.1 hn))

/-- `a = (a/b) b` for finite masses `a ≤ b`, in real numbers. -/
theorem toReal_eq_ratio_mul {a b : ℝ≥0∞} (hab : a ≤ b) (hb : b ≠ ∞) :
    a.toReal = (a / b).toReal * b.toReal := by
  by_cases hb0 : b = 0
  · have : a = 0 := le_antisymm (hab.trans hb0.le) bot_le
    simp [this, hb0]
  · rw [ENNReal.toReal_div, div_mul_cancel₀]
    exact ENNReal.toReal_ne_zero.2 ⟨hb0, hb⟩

/-- The τ̃-conditioned probability `ℙₓ(|n⁻¹ ∑_{i<m} h(Xᵢ) - Γ| > ε | τ̃ > m - 1)`. -/
def ratio (f : M → ℝ) (ε Γ : ℝ) (x : M) (n m : ℕ) : ℝ :=
  (C.pathMeasure x (avgSet f ε Γ n m ∩ Cited.liveThrough C.killedTransition m) /
    C.pathMeasure x (Cited.liveThrough C.killedTransition m)).toReal

theorem ratio_nonneg (f : M → ℝ) (ε Γ : ℝ) (x : M) (n m : ℕ) :
    0 ≤ ratio C f ε Γ x n m := ENNReal.toReal_nonneg

theorem ratio_le_one (f : M → ℝ) (ε Γ : ℝ) (x : M) (n m : ℕ) :
    ratio C f ε Γ x n m ≤ 1 := by
  unfold ratio
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  rw [ENNReal.ofReal_one]
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)

theorem liveThrough_subset_survival {K : Kernel M M} (m : ℕ) :
    Cited.liveThrough K (m + 1) ⊆ survival (M := M) m := by
  intro ω hω k hk hnone
  obtain ⟨y, _, hy⟩ := hω k (by omega)
  rw [hy] at hnone
  cases hnone


section Estimate

variable [MetricSpace M] [CompactSpace M] [BorelSpace M] {ρ : Measure M}

/-- The deviation probability under `ℙₓ(· | τ > n)` is bounded by a geometric average of
τ̃-conditioned deviation probabilities. -/
theorem transfer_estimate (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (x : d.State)
    {f : M → ℝ} (hf : Measurable f) (hZ : ∀ z ∈ escapingSet C.killedTransition, f z = 0)
    (ε Γ : ℝ) :
    ∃ D ≥ 0, ∀ n : ℕ, (C.conditionedMeasure x.val n (avgSet f ε Γ n n)).toReal ≤
      D * (ratio C f ε Γ x.val n n +
        ∑ m ∈ Finset.range n, s.decay ^ (n - m - 1) * ratio C f ε Γ x.val n m) := by
  set L := survivingSet C.killedTransition
  set r := d.rate.toReal
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  have hrinv : (d.rate⁻¹).toReal = r⁻¹ := ENNReal.toReal_inv _
  have hx : x.val ∈ L := by rw [← hlive]; exact x.property
  have hw0 (z : M) (hz : z ∉ L) : d.weight z = 0 := by
    rw [← hlive] at hz
    exact not_not.1 hz
  have hno : ∀ z ∈ Lᶜ, C.killedTransition z L = 0 := by
    intro z hz
    have := d.no_return_from_zero (x := z) (by rw [hlive]; exact hz)
    rwa [hlive] at this
  set S := s.survivalConstant
  set θ := s.decay
  -- Survival from `Z` decays like `(λθ)ᵏ`.
  let bnd : ℕ → ℝ≥0∞ := fun k => if k = 0 then 1 else ENNReal.ofReal (r ^ k * (S * θ ^ (k - 1)))
  have hbound : ∀ k, ∀ z ∈ Lᶜ, (C.killedTransition ^ k) z univ ≤ bnd k := by
    intro k z hz
    rcases k with _ | j
    · simp [bnd, show (1 : Kernel M M) = Kernel.id from rfl]
    · simp only [bnd, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      have he := s.normalized_survival_error j z
      rw [hw0 z hz, ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at he
      have hfin : (C.killedTransition ^ (j + 1)) z univ ≠ ∞ :=
        ((C.killedTransition_pow_mass_le_one z (j + 1)).trans_lt ENNReal.one_lt_top).ne
      rw [ENNReal.le_ofReal_iff_toReal_le hfin
        (mul_nonneg (pow_nonneg hr.le _) (mul_nonneg s.survivalConstant_nonneg
          (pow_nonneg s.decay_nonneg _)))]
      have heq : ((d.rate⁻¹) ^ (j + 1) * (C.killedTransition ^ (j + 1)) z univ).toReal =
          r⁻¹ ^ (j + 1) * ((C.killedTransition ^ (j + 1)) z univ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, hrinv]
      change ((d.rate⁻¹) ^ (j + 1) * (C.killedTransition ^ (j + 1)) z univ).toReal ≤ S * θ ^ j at he
      rw [heq, inv_pow, inv_mul_le_iff₀ (pow_pos hr _)] at he
      exact he
  -- Masses of `{τ̃ > m - 1}` grow at most like `λᵐ`.
  set B := s.survivalBound
  set B' := 1 + B / r
  have hB' : 0 ≤ B' := by have := s.survivalBound_nonneg; positivity
  have hLT : ∀ m, (C.pathMeasure x.val (Cited.liveThrough C.killedTransition m)).toReal ≤ B' * r ^ m := by
    intro m
    rcases m with _ | j
    · have : (C.pathMeasure x.val (Cited.liveThrough C.killedTransition 0)).toReal ≤ 1 := by
        apply ENNReal.toReal_le_of_le_ofReal zero_le_one
        rw [ENNReal.ofReal_one]
        exact prob_le_one
      have h1 : (1 : ℝ) ≤ B' := by
        have := s.survivalBound_nonneg
        simp only [B']
        linarith [div_nonneg this hr.le]
      simpa using this.trans h1
    · have hmono : (C.pathMeasure x.val (Cited.liveThrough C.killedTransition (j + 1))).toReal ≤
          (C.pathMeasure x.val (survival j)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (liveThrough_subset_survival j))
      have hs := s.normalized_survival_real_le j x.val
      change ((d.rate⁻¹) ^ j * (C.killedTransition ^ j) x.val univ).toReal ≤ B at hs
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, hrinv, inv_pow,
        inv_mul_le_iff₀ (pow_pos hr _)] at hs
      rw [C.pathMeasure_survival] at hmono
      calc (C.pathMeasure x.val (Cited.liveThrough C.killedTransition (j + 1))).toReal
          ≤ r ^ j * B := hmono.trans hs
        _ = B / r * r ^ (j + 1) := by field_simp; ring
        _ ≤ B' * r ^ (j + 1) := by
            gcongr
            simp only [B']
            linarith
  -- `ℙₓ(τ > n) ≥ c λⁿ`.
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ n,
      c ≤ ((d.rate⁻¹) ^ n * (C.killedTransition ^ n) x.val univ).toReal := by
    apply exists_pos_lower_bound _ (ENNReal.toReal_pos x.property (d.weight_ne_top _))
      (s.normalized_survival_tendstoUniformly.tendsto_at x.val)
    intro n
    have hpos := C.pathMeasure_survival_pos x.val hx n
    rw [C.pathMeasure_survival] at hpos
    apply ENNReal.toReal_pos
    · exact mul_ne_zero (pow_ne_zero _ (ENNReal.inv_ne_zero.2 d.rate_ne_top)) hpos.ne'
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 d.rate_ne_zero))
        ((C.killedTransition_pow_mass_le_one x.val n).trans_lt ENNReal.one_lt_top).ne
  have hsurv : ∀ n, c * r ^ n ≤ (C.pathMeasure x.val (survival n)).toReal := by
    intro n
    have := hcle n
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, hrinv, inv_pow,
      le_inv_mul_iff₀ (pow_pos hr _)] at this
    rw [C.pathMeasure_survival]
    linarith [mul_comm c (r ^ n)]
  refine ⟨B' / c * max 1 S, by positivity, fun n => ?_⟩
  -- Assemble.
  set Ps := C.pathMeasure x.val (survival n)
  have hPs : 0 < Ps.toReal := (mul_pos hc (pow_pos hr n)).trans_le (hsurv n)
  have hcond : (C.conditionedMeasure x.val n (avgSet f ε Γ n n)).toReal =
      (C.pathMeasure x.val (survival n ∩ avgSet f ε Γ n n)).toReal / Ps.toReal := by
    rw [C.conditionedMeasure_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, inv_mul_eq_div]
  have hdec := decomposition_le C hf hno hZ ε Γ x.val n bnd hbound
  have hdec' : (C.pathMeasure x.val (survival n ∩ avgSet f ε Γ n n)).toReal ≤
      (C.pathMeasure x.val (avgSet f ε Γ n n ∩ Cited.liveThrough C.killedTransition n)).toReal +
        ∑ m ∈ Finset.range n,
          (C.pathMeasure x.val (avgSet f ε Γ n m ∩ Cited.liveThrough C.killedTransition m)).toReal *
            (bnd (n - m)).toReal := by
    have hfin : ∀ m ∈ Finset.range n,
        C.pathMeasure x.val (avgSet f ε Γ n m ∩ Cited.liveThrough C.killedTransition m) * bnd (n - m) ≠ ∞ := by
      intro m _
      refine ENNReal.mul_ne_top (measure_ne_top _ _) ?_
      simp only [bnd]
      split_ifs <;> simp
    refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      ENNReal.sum_ne_top.2 hfin⟩) hdec).trans_eq ?_
    rw [ENNReal.toReal_add (measure_ne_top _ _) (ENNReal.sum_ne_top.2 hfin),
      ENNReal.toReal_sum hfin]
    simp only [ENNReal.toReal_mul]
  -- Each term is a conditional probability times the mass of `{τ̃ > m - 1}`.
  have hterm0 : (C.pathMeasure x.val (avgSet f ε Γ n n ∩ Cited.liveThrough C.killedTransition n)).toReal ≤
      ratio C f ε Γ x.val n n * (B' * r ^ n) := by
    rw [toReal_eq_ratio_mul (measure_mono inter_subset_right) (measure_ne_top _ _)]
    exact mul_le_mul_of_nonneg_left (hLT n) (ratio_nonneg C f ε Γ x.val n n)
  have hterm : ∀ m ∈ Finset.range n,
      (C.pathMeasure x.val (avgSet f ε Γ n m ∩ Cited.liveThrough C.killedTransition m)).toReal *
        (bnd (n - m)).toReal ≤
      B' * S * r ^ n * (θ ^ (n - m - 1) * ratio C f ε Γ x.val n m) := by
    intro m hm
    have hmn : m < n := Finset.mem_range.1 hm
    have hb : (bnd (n - m)).toReal = r ^ (n - m) * (S * θ ^ (n - m - 1)) := by
      simp only [bnd, show n - m ≠ 0 by omega, ite_false]
      exact ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hr.le _)
        (mul_nonneg s.survivalConstant_nonneg (pow_nonneg s.decay_nonneg _)))
    rw [toReal_eq_ratio_mul (measure_mono inter_subset_right) (measure_ne_top _ _), hb]
    have hq := ratio_nonneg C f ε Γ x.val n m
    have hθ : 0 ≤ θ ^ (n - m - 1) := pow_nonneg s.decay_nonneg _
    calc ratio C f ε Γ x.val n m * (C.pathMeasure x.val (Cited.liveThrough C.killedTransition m)).toReal *
          (r ^ (n - m) * (S * θ ^ (n - m - 1)))
        ≤ ratio C f ε Γ x.val n m * (B' * r ^ m) * (r ^ (n - m) * (S * θ ^ (n - m - 1))) := by
          gcongr
          · exact mul_nonneg (pow_nonneg hr.le _)
              (mul_nonneg s.survivalConstant_nonneg hθ)
          · exact hLT m
      _ = B' * S * (r ^ m * r ^ (n - m)) * (θ ^ (n - m - 1) * ratio C f ε Γ x.val n m) := by
          ring
      _ = B' * S * r ^ n * (θ ^ (n - m - 1) * ratio C f ε Γ x.val n m) := by
          rw [← pow_add, Nat.add_sub_cancel' hmn.le]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  set sq := ∑ m ∈ Finset.range n, θ ^ (n - m - 1) * ratio C f ε Γ x.val n m
  have hsqnn : 0 ≤ sq := Finset.sum_nonneg fun m _ =>
    mul_nonneg (pow_nonneg s.decay_nonneg _) (ratio_nonneg C f ε Γ x.val n m)
  have hq0 := ratio_nonneg C f ε Γ x.val n n
  have hnum : (C.pathMeasure x.val (survival n ∩ avgSet f ε Γ n n)).toReal ≤
      B' * r ^ n * max 1 S * (ratio C f ε Γ x.val n n + sq) := by
    have h1 := hdec'.trans (add_le_add hterm0 hsum)
    have hS1 : S ≤ max 1 S := le_max_right _ _
    have h11 : (1 : ℝ) ≤ max 1 S := le_max_left _ _
    have hBr : 0 ≤ B' * r ^ n := mul_nonneg hB' (pow_nonneg hr.le _)
    nlinarith [mul_le_mul_of_nonneg_left hS1 (mul_nonneg hBr hsqnn),
      mul_le_mul_of_nonneg_left h11 (mul_nonneg hBr hq0)]
  rw [hcond, div_le_iff₀ hPs]
  calc (C.pathMeasure x.val (survival n ∩ avgSet f ε Γ n n)).toReal
      ≤ B' * r ^ n * max 1 S * (ratio C f ε Γ x.val n n + sq) := hnum
    _ = B' / c * max 1 S * (ratio C f ε Γ x.val n n + sq) * (c * r ^ n) := by
        field_simp
    _ ≤ B' / c * max 1 S * (ratio C f ε Γ x.val n n + sq) * Ps.toReal := by
        gcongr
        exact hsurv n

end Estimate

end

end ConditionedStableLaws.ConditionalTransfer
