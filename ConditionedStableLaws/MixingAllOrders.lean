import ConditionedStableLaws.SecondMoment

/-!
# Conditional mixing of all orders for signed observables

For bounded measurable `g₁, …, g_k` (of any sign), gaps `n₁, …, n_k ≥ m ≥ 1`, `s_j = n₁ + ⋯ + n_j`
and `x ∈ M \ Z`:

* `E_x[∏ g_j(X_{s_j}) | τ > s_k] = ∏_{j<k} ν(g_j) · μ(g_k) + O_{x,k}(ϑ^m ∏ ‖g_j‖∞)`;
* `E_x[∏ g_j(X_{s_j}) | τ > n] = ∏ ν(g_j) + O_{x,k}(ϑ^{m_n} ∏ ‖g_j‖∞)`, `n - s_k ≥ m_n`.

Observations are encoded as lists of (gap, observable, sup bound). The Feynman–Kac formula writes
the conditioned expectation as a nested word `P̂^{n₁}(g₁ P̂^{n₂}(g₂ ⋯))(x) / P̂ⁿ1(x)`, and each
`P̂^{n_j}` is replaced by its rank-one part `μ(·) η` with a pointwise exponential error (Hypothesis
H).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ConditionedStableLaws.MixingAllOrders

noncomputable section

open StandingHypothesis CanonicalChain FeynmanKac SecondMoment

/-- A list of observations: (gap, observable, sup bound). -/
abbrev Obs (M : Type*) := List (ℕ × (M → ℝ) × ℝ)

variable {M : Type*} [MeasurableSpace M]

/-- The total time `n₁ + ⋯ + n_k`. -/
def gapsum (w : Obs M) : ℕ := (w.map Prod.fst).sum

/-- Admissible observation lists: positive gaps, measurable bounded observables. -/
def Admissible (w : Obs M) : Prop :=
  ∀ p ∈ w, 1 ≤ p.1 ∧ Measurable p.2.1 ∧ 0 ≤ p.2.2 ∧ ∀ y, |p.2.1 y| ≤ p.2.2

/-- The time-indexed observables: `g_j` at time `s_j`, `1` elsewhere. -/
def obsφ : Obs M → ℕ → M → ℝ
  | [], _ => fun _ => 1
  | (n, g, _) :: w, i => if i < n then (fun _ => 1) else if i = n then g else obsφ w (i - n)

/-- The path observable `∏_j g_j(X_{t + s_j})` (zero at the cemetery). -/
def observe : Obs M → ℕ → CanonicalChain.Path M → ℝ
  | [], _, _ => 1
  | (n, g, _) :: w, t, ω => zeroExtension g (ω (t + n)) * observe w (t + n) ω

theorem admissible_cons {p : ℕ × (M → ℝ) × ℝ} {w : Obs M} (hw : Admissible (p :: w)) :
    Admissible w := fun q hq => hw q (List.mem_cons_of_mem _ hq)

theorem obsφ_zero {w : Obs M} (hw : Admissible w) : obsφ w 0 = fun _ => 1 := by
  cases w with
  | nil => rfl
  | cons p w =>
    obtain ⟨n, g, b⟩ := p
    have hn := (hw (n, g, b) List.mem_cons_self).1
    simp only [obsφ, ite_eq_left (show 0 < n by omega)]

omit [MeasurableSpace M] in
theorem obsφ_shift (n : ℕ) (g : M → ℝ) (b : ℝ) (w : Obs M) (i : ℕ) :
    obsφ ((n, g, b) :: w) (n + (1 + i)) = obsφ w (1 + i) := by
  simp only [obsφ, ite_eq_right (show ¬ n + (1 + i) < n by omega),
    ite_eq_right (show ¬ n + (1 + i) = n by omega), show n + (1 + i) - n = 1 + i by omega]

theorem measurable_obsφ {w : Obs M} (hw : Admissible w) (i : ℕ) : Measurable (obsφ w i) := by
  induction w generalizing i with
  | nil => exact measurable_const
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    simp only [obsφ]
    split_ifs
    · exact measurable_const
    · exact (hw (n, g, b) List.mem_cons_self).2.1
    · exact ih (admissible_cons hw) _

theorem abs_obsφ_le {w : Obs M} (hw : Admissible w) (i : ℕ) (y : M) :
    |obsφ w i y| ≤ 1 + (w.map fun p => p.2.2).sum := by
  induction w generalizing i with
  | nil => simp [obsφ]
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    have hb := hw (n, g, b) List.mem_cons_self
    have hsum : 0 ≤ (w.map fun p => p.2.2).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact (hw q (List.mem_cons_of_mem _ hq)).2.2.1
    simp only [obsφ, List.map_cons, List.sum_cons]
    split_ifs
    · simp; linarith [hb.2.2.1]
    · linarith [hb.2.2.2 y, hb.2.2.1]
    · linarith [ih (admissible_cons hw) (i - n), hb.2.2.1]

omit [MeasurableSpace M] in
theorem observe_shift (w : Obs M) : ∀ (t : ℕ) (ω : CanonicalChain.Path M),
    observe w t ω = observe w 0 (fun i => ω (t + i)) := by
  induction w with
  | nil => intro t ω; rfl
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    intro t ω
    simp only [observe, zero_add]
    rw [ih (t + n) ω, ih n (fun i => ω (t + i))]
    simp only [Nat.add_assoc]

omit [MeasurableSpace M] in
theorem observe_append (w v : Obs M) : ∀ (t : ℕ) (ω : CanonicalChain.Path M),
    observe (w ++ v) t ω = observe w t ω * observe v (t + gapsum w) ω := by
  induction w with
  | nil => intro t ω; simp [observe, gapsum]
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    intro t ω
    simp only [List.cons_append, observe, ih, gapsum, List.map_cons, List.sum_cons, mul_assoc]
    rw [Nat.add_assoc]

/-! ### Killed words of observation lists -/

section Words

variable (C : CanonicalChain M)

theorem killedWord_concat (φ : ℕ → M → ℝ) (a : ℕ) :
    ∀ b (h : M → ℝ), killedWord C φ (a + b) h =
      killedWord C φ a (killedWord C (fun i => φ (a + i)) b h) := by
  intro b
  induction b with
  | zero => intro h; rfl
  | succ b ih =>
    intro h
    show killedWord C φ (a + b) (fun y => φ (a + b) y * ∫ z, h z ∂C.killedTransition y) = _
    rw [ih]
    rfl

theorem killedWord_front (ψ : ℕ → M → ℝ) (b : ℕ) (h : M → ℝ) :
    killedWord C ψ (1 + b) h =
      fun x => ψ 0 x * ∫ z, killedWord C (fun i => ψ (1 + i)) b h z ∂C.killedTransition x := by
  rw [killedWord_concat]
  rfl

/-- The nested word `Tⁿ¹(g₁ Tⁿ²(g₂ ⋯ H))` of an observation list. -/
def nestK : Obs M → (M → ℝ) → M → ℝ
  | [], H => H
  | (n, g, _) :: w, H => kpow C n (fun y => g y * nestK w H y)

theorem measurable_nestK {w : Obs M} (hw : Admissible w) {H : M → ℝ} (hH : Measurable H) :
    Measurable (nestK C w H) := by
  induction w with
  | nil => exact hH
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    exact measurable_kpow C n ((hw (n, g, b) List.mem_cons_self).2.1.mul (ih (admissible_cons hw)))

theorem abs_nestK_le {w : Obs M} (hw : Admissible w) {H : M → ℝ} {BH : ℝ} (hBH0 : 0 ≤ BH)
    (hH : ∀ y, |H y| ≤ BH) (y : M) :
    |nestK C w H y| ≤ (w.map fun p => p.2.2).prod * BH := by
  induction w generalizing y with
  | nil => simpa [nestK] using hH y
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    have hb := hw (n, g, b) List.mem_cons_self
    have hprod : 0 ≤ (w.map fun p => p.2.2).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact (hw q (List.mem_cons_of_mem _ hq)).2.2.1
    simp only [nestK, List.map_cons, List.prod_cons]
    refine (abs_kpow_le C n (B := b * ((w.map fun p => p.2.2).prod * BH))
      (mul_nonneg hb.2.2.1 (mul_nonneg hprod hBH0)) (fun z => ?_) y).trans_eq (by ring)
    rw [abs_mul]
    exact mul_le_mul (hb.2.2.2 z) (ih (admissible_cons hw) z) (abs_nonneg _) hb.2.2.1

/-- The killed word of an observation list followed by `l ≥ 1` further steps. -/
theorem killedWord_obs {w : Obs M} (hw : Admissible w) {l : ℕ} (hl : 1 ≤ l) {h : M → ℝ}
    (hh : Measurable h) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, |h y| ≤ B) :
    killedWord C (obsφ w) (gapsum w + l) h = nestK C w (kpow C l h) := by
  induction w with
  | nil =>
    simp only [gapsum, List.map_nil, List.sum_nil, nestK]
    rw [killedWord_ones C (obsφ []) 0 l (fun k _ _ => rfl) h hh B hB0 hB]
    rfl
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    have hpb := hw (n, g, b) List.mem_cons_self
    have hw' := admissible_cons hw
    have hgs : gapsum ((n, g, b) :: w) + l = n + (gapsum w + l) := by
      simp only [gapsum, List.map_cons, List.sum_cons]; omega
    rw [hgs, killedWord_concat]
    -- The shifted word is `g` times the word of the tail.
    obtain ⟨R, hR⟩ : ∃ R, gapsum w + l = 1 + R := ⟨gapsum w + l - 1, by omega⟩
    have hshift : killedWord C (fun i => obsφ ((n, g, b) :: w) (n + i)) (gapsum w + l) h =
        fun y => g y * killedWord C (obsφ w) (gapsum w + l) h y := by
      rw [hR, killedWord_front, killedWord_front]
      funext y
      have h0 : obsφ ((n, g, b) :: w) (n + 0) = g := by simp [obsφ]
      have h1 : (fun i => obsφ ((n, g, b) :: w) (n + (1 + i))) = fun i => obsφ w (1 + i) :=
        funext fun i => obsφ_shift n g b w i
      simp only [h0, h1, obsφ_zero hw', one_mul]
    rw [hshift, ih hw']
    -- The first block consists of unit observations.
    have hones := killedWord_ones C (obsφ ((n, g, b) :: w)) 0 n
      (fun k _ hk => by simp only [obsφ, ite_eq_left (show k < n by omega)])
      (fun y => g y * nestK C w (kpow C l h) y)
      (hpb.2.1.mul (measurable_nestK C hw' (measurable_kpow C l hh)))
      (b * ((w.map fun p => p.2.2).prod * B))
      (mul_nonneg hpb.2.2.1 (mul_nonneg (List.prod_nonneg fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact (hw' q hq).2.2.1) hB0))
      (fun y => by
        rw [abs_mul]
        exact mul_le_mul (hpb.2.2.2 y) (abs_nestK_le C hw' hB0 (abs_kpow_le C l hB0 hB) y)
          (abs_nonneg _) hpb.2.2.1)
    simp only [Nat.zero_add] at hones
    rw [hones]
    rfl

/-- On the survival event, the product of the time-indexed observables is
the path observable. -/
theorem prod_obsφ_eq {w : Obs M} (hw : Admissible w) {l : ℕ} (hl : 1 ≤ l) :
    ∀ ω : CanonicalChain.Path M, ω ∈ survival (gapsum w + l) →
      ∏ i ∈ Finset.range (gapsum w + l), ext (obsφ w i) (ω i) = observe w 0 ω := by
  induction w with
  | nil =>
    intro ω hω
    simp only [gapsum, List.map_nil, List.sum_nil, zero_add, observe]
    refine Finset.prod_eq_one fun i hi => ?_
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hω i (by simp at hi; omega))
    rw [hy]; rfl
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    have hw' := admissible_cons hw
    intro ω hω
    have hgs : gapsum ((n, g, b) :: w) + l = n + (gapsum w + l) := by
      simp only [gapsum, List.map_cons, List.sum_cons]; omega
    rw [hgs] at hω ⊢
    rw [Finset.prod_range_add]
    have hfirst : ∏ i ∈ Finset.range n, ext (obsφ ((n, g, b) :: w) i) (ω i) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      have hin : i < n := Finset.mem_range.1 hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hω i (by omega))
      simp only [obsφ, ite_eq_left hin, hy, ext_some]
    rw [hfirst, one_mul]
    obtain ⟨R, hR⟩ : ∃ R, gapsum w + l = R + 1 := ⟨gapsum w + l - 1, by omega⟩
    set ω' : CanonicalChain.Path M := fun i => ω (n + i) with hω'
    have hω's : ω' ∈ survival (gapsum w + l) := fun i hi => hω (n + i) (by omega)
    have hih := ih hw' ω' hω's
    rw [hR, Finset.prod_range_succ'] at hih ⊢
    have hobs0 : ext (obsφ w 0) (ω' 0) = 1 := by
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hω's 0 (by omega))
      rw [obsφ_zero hw', hy]; rfl
    rw [hobs0, mul_one] at hih
    have hterms : ∏ i ∈ Finset.range R, ext (obsφ ((n, g, b) :: w) (n + (i + 1))) (ω (n + (i + 1)))
        = ∏ i ∈ Finset.range R, ext (obsφ w (i + 1)) (ω' (i + 1)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [show i + 1 = 1 + i by omega, obsφ_shift]
    have hn0 : obsφ ((n, g, b) :: w) (n + 0) = g := by simp [obsφ]
    rw [hterms, hih, hn0, ext_eq_zeroExtension, observe, zero_add, observe_shift w n ω, add_zero,
      mul_comm]

end Words

/-! ### The conditioned expectations as nested words -/

section Conditioned

variable (C : CanonicalChain M)

theorem sum_bounds_nonneg {w : Obs M} (hw : Admissible w) : 0 ≤ (w.map fun p => p.2.2).sum :=
  List.sum_nonneg fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact (hw q hq).2.2.1

theorem prod_bounds_nonneg {w : Obs M} (hw : Admissible w) : 0 ≤ (w.map fun p => p.2.2).prod :=
  List.prod_nonneg fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact (hw q hq).2.2.1

omit [MeasurableSpace M] in
theorem exists_none_of_not_survival {N : ℕ} {ω : CanonicalChain.Path M} (hω : ω ∉ survival N) :
    ∃ k, k ≤ N ∧ ω k = none := by
  by_contra hc
  push Not at hc
  exact hω fun k hk => hc k hk

/-- `E_x[∏ g_j(X_{s_j}) | τ > s_k + l] = ℙ_x(τ > s_k + l)⁻¹ Tⁿ¹(g₁ ⋯ Tˡ1)(x)` for `l ≥ 1`. -/
theorem integral_conditioned_observe {w : Obs M} (hw : Admissible w) {l : ℕ} (hl : 1 ≤ l)
    (x : M) :
    ∫ ω, observe w 0 ω ∂C.conditionedMeasure x (gapsum w + l) =
      (C.pathMeasure x (survival (gapsum w + l))).toReal⁻¹ *
        nestK C w (kpow C l (fun _ => 1)) x := by
  set N := gapsum w + l with hN_def
  rw [conditionedMeasure, ProbabilityTheory.cond, integral_smul_measure,
    ← integral_indicator (measurableSet_survival N), smul_eq_mul, ENNReal.toReal_inv]
  congr 1
  rw [← killedWord_obs C hw hl measurable_const zero_le_one (fun _ => by simp),
    ← integral_prod_eq_killedWord C (obsφ w) (measurable_obsφ hw)
      (A := 1 + (w.map fun p => p.2.2).sum) (by linarith [sum_bounds_nonneg hw])
      (fun i y => by rw [Real.norm_eq_abs]; exact abs_obsφ_le hw i y) N measurable_const
      zero_le_one (fun _ => by simp) x]
  congr 1
  funext ω
  by_cases hω : ω ∈ survival N
  · rw [indicator_of_mem hω, prod_obsφ_eq hw hl ω hω]
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hω N le_rfl)
    rw [hy, ext_some, mul_one]
  · rw [indicator_of_notMem hω]
    obtain ⟨k, hk, hkn⟩ := exists_none_of_not_survival hω
    rcases lt_or_eq_of_le hk with hlt | rfl
    · rw [Finset.prod_eq_zero (Finset.mem_range.2 hlt) (by rw [hkn]; rfl), zero_mul]
    · rw [hkn, ext_none, mul_zero]

/-- The version conditioned at the last observation time:
`E_x[∏_{j<k} g_j(X_{s_j}) g(X_{s_k}) | τ > s_k] = ℙ_x(τ > s_k)⁻¹ Tⁿ¹(g₁ ⋯ T^{n_k} g)(x)`. -/
theorem integral_conditioned_observe_last {w : Obs M} (hw : Admissible w) {n : ℕ} (hn : 1 ≤ n)
    {g : M → ℝ} (hg : Measurable g) {b : ℝ} (hb0 : 0 ≤ b) (hgb : ∀ y, |g y| ≤ b) (x : M) :
    ∫ ω, observe (w ++ [(n, g, b)]) 0 ω ∂C.conditionedMeasure x (gapsum w + n) =
      (C.pathMeasure x (survival (gapsum w + n))).toReal⁻¹ * nestK C w (kpow C n g) x := by
  set N := gapsum w + n with hN_def
  rw [conditionedMeasure, ProbabilityTheory.cond, integral_smul_measure,
    ← integral_indicator (measurableSet_survival N), smul_eq_mul, ENNReal.toReal_inv]
  congr 1
  rw [← killedWord_obs C hw hn hg hb0 hgb,
    ← integral_prod_eq_killedWord C (obsφ w) (measurable_obsφ hw)
      (A := 1 + (w.map fun p => p.2.2).sum) (by linarith [sum_bounds_nonneg hw])
      (fun i y => by rw [Real.norm_eq_abs]; exact abs_obsφ_le hw i y) N hg hb0
      (fun y => by rw [Real.norm_eq_abs]; exact hgb y) x]
  congr 1
  funext ω
  by_cases hω : ω ∈ survival N
  · rw [indicator_of_mem hω, prod_obsφ_eq hw hn ω hω, observe_append, zero_add]
    simp only [observe, mul_one]
    rw [ext_eq_zeroExtension]
  · rw [indicator_of_notMem hω]
    obtain ⟨k, hk, hkn⟩ := exists_none_of_not_survival hω
    rcases lt_or_eq_of_le hk with hlt | rfl
    · rw [Finset.prod_eq_zero (Finset.mem_range.2 hlt) (by rw [hkn]; rfl), zero_mul]
    · rw [hkn, ext_none, mul_zero]

end Conditioned

/-! ### Normalized nested words and the mixing estimate -/

section Estimate

variable {C : CanonicalChain M} {μ : Measure M}

/-- The normalized nested word `P̂ⁿ¹(g₁ P̂ⁿ²(g₂ ⋯ H))`. -/
def nestN (D : Data0 C μ) : Obs M → (M → ℝ) → M → ℝ
  | [], H => H
  | (n, g, _) :: w, H => nkp C D.r n (fun y => g y * nestN D w H y)

theorem nestN_eq (D : Data0 C μ) (w : Obs M) :
    ∀ (H : M → ℝ) (y : M), D.r⁻¹ ^ gapsum w * nestK C w H y = nestN D w H y := by
  induction w with
  | nil => intro H y; simp [nestK, nestN, gapsum]
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    intro H y
    have hgs : gapsum ((n, g, b) :: w) = n + gapsum w := by
      simp [gapsum]
    simp only [nestK, nestN, nkp, hgs]
    rw [pow_add, mul_assoc, ← kpow_mul_smul]
    congr 2
    funext z
    rw [ih]

theorem nestN_const_mul (D : Data0 C μ) (w : Obs M) (c : ℝ) :
    ∀ (H : M → ℝ) (y : M), nestN D w (fun z => c * H z) y = c * nestN D w H y := by
  induction w with
  | nil => intro H y; rfl
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    intro H y
    simp only [nestN, nkp]
    rw [show (fun z => g z * nestN D w (fun z => c * H z) z) = fun z => g z * (c * nestN D w H z)
      from funext fun z => by rw [ih], kpow_mul_smul]
    ring

theorem measurable_nestN (D : Data0 C μ) {w : Obs M} (hw : Admissible w) {H : M → ℝ}
    (hH : Measurable H) : Measurable (nestN D w H) := by
  induction w with
  | nil => exact hH
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    exact measurable_nkp C _ n ((hw (n, g, b) List.mem_cons_self).2.1.mul (ih (admissible_cons hw)))

theorem abs_nestN_le (D : Data0 C μ) {w : Obs M} (hw : Admissible w) {H : M → ℝ}
    (hH : Measurable H) {BH : ℝ} (hBH0 : 0 ≤ BH) (hHB : ∀ y, |H y| ≤ BH) (y : M) :
    |nestN D w H y| ≤ D.E ^ w.length * (w.map fun p => p.2.2).prod * BH := by
  induction w generalizing y with
  | nil => simpa [nestN] using hHB y
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    have hb := hw (n, g, b) List.mem_cons_self
    have hw' := admissible_cons hw
    have hP := prod_bounds_nonneg hw'
    have hE := D.E_nonneg
    simp only [nestN, List.map_cons, List.prod_cons, List.length_cons]
    refine (D.nkp_abs_le n (show Measurable fun z => g z * nestN D w H z from
        hb.2.1.mul (measurable_nestN D hw' hH))
      (B := b * (D.E ^ w.length * (w.map fun p => p.2.2).prod * BH))
      (mul_nonneg hb.2.2.1 (mul_nonneg (mul_nonneg (pow_nonneg hE _) hP) hBH0))
      (fun z => ?_) y).trans_eq (by ring)
    rw [abs_mul]
    exact mul_le_mul (hb.2.2.2 z) (ih hw' z) (abs_nonneg _) hb.2.2.1

/-- The constant `K_k` of the mixing estimate. -/
def Kfun (D : Data0 C μ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => D.A * D.Bη + D.E * Kfun D k

theorem Kfun_nonneg (D : Data0 C μ) [Nonempty M] (k : ℕ) : 0 ≤ Kfun D k := by
  induction k with
  | zero => simp [Kfun]
  | succ k ih =>
    simp only [Kfun]
    have := D.A_nonneg; have := D.Bη_nonneg; have := D.E_nonneg
    positivity

theorem abs_prod_nu_le [IsProbabilityMeasure μ] (D : Data0 C μ)
    (hη1 : ∫ y, D.η y ∂μ = 1) {w : Obs M} (hw : Admissible w) :
    |(w.map fun p => ∫ y, p.2.1 y * D.η y ∂μ).prod| ≤ (w.map fun p => p.2.2).prod := by
  induction w with
  | nil => simp
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    have hb := hw (n, g, b) List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, abs_mul]
    have hν : |∫ y, g y * D.η y ∂μ| ≤ b := by
      have hηi : Integrable D.η μ := SecondMoment.integrable_of_bdd D.measurable_η
        (B := D.Bη) (fun y => by rw [abs_of_nonneg (D.η_nonneg y)]; exact D.η_le y)
      calc |∫ y, g y * D.η y ∂μ| ≤ ∫ y, |g y * D.η y| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ y, b * D.η y ∂μ := integral_mono (SecondMoment.integrable_of_bdd
              (show Measurable fun y => g y * D.η y from hb.2.1.mul D.measurable_η)
              (B := b * D.Bη) (fun y => by
                rw [abs_mul, abs_of_nonneg (D.η_nonneg y)]
                exact mul_le_mul (hb.2.2.2 y) (D.η_le y) (D.η_nonneg y) hb.2.2.1)).abs
              (hηi.const_mul b) (fun y => by
                rw [abs_mul, abs_of_nonneg (D.η_nonneg y)]
                exact mul_le_mul_of_nonneg_right (hb.2.2.2 y) (D.η_nonneg y))
        _ = b := by rw [integral_const_mul, hη1, mul_one]
    exact mul_le_mul hν (ih (admissible_cons hw)) (abs_nonneg _) hb.2.2.1

/-- The inductive mixing estimate: if `H ≈ c_H η` within `e_H`, then
`P̂ⁿ¹(g₁ ⋯ H) ≈ ∏ ν(g_j) c_H η` within `K_k ∏ ‖g_j‖ (e_H + |c_H| θ^{m-1})`. -/
theorem nest_approx [IsProbabilityMeasure μ] [Nonempty M] (D : Data0 C μ)
    (hη1 : ∫ y, D.η y ∂μ = 1) {w : Obs M} (hw : Admissible w) {m : ℕ} (hm : 1 ≤ m)
    (hwm : ∀ p ∈ w, m ≤ p.1) {H : M → ℝ} (hH : Measurable H) {BH : ℝ} (hBH0 : 0 ≤ BH)
    (hHB : ∀ y, |H y| ≤ BH) {cH eH : ℝ} (happ : ∀ z, |H z - cH * D.η z| ≤ eH) (y : M) :
    |nestN D w H y - (w.map fun p => ∫ z, p.2.1 z * D.η z ∂μ).prod * cH * D.η y| ≤
      Kfun D w.length * (w.map fun p => p.2.2).prod * (eH + |cH| * D.θ ^ (m - 1)) := by
  induction w generalizing y with
  | nil =>
    simp only [nestN, List.map_nil, List.prod_nil, one_mul, List.length_nil, Kfun]
    have h1 := happ y
    have h2 : 0 ≤ |cH| * D.θ ^ (m - 1) := mul_nonneg (abs_nonneg _) (pow_nonneg D.θ_nonneg _)
    linarith
  | cons p w ih =>
    obtain ⟨n, g, b⟩ := p
    have hb := hw (n, g, b) List.mem_cons_self
    have hw' := admissible_cons hw
    have hb0' : 0 ≤ b := hb.2.2.1
    have hθ0 := D.θ_nonneg
    have hmn : m ≤ n := hwm (n, g, b) List.mem_cons_self
    have hwm' : ∀ p ∈ w, m ≤ p.1 := fun p hp => hwm p (List.mem_cons_of_mem _ hp)
    have hE := D.E_nonneg
    have hA := D.A_nonneg
    have hBη := D.Bη_nonneg
    have hP := prod_bounds_nonneg hw'
    set cw := (w.map fun p => ∫ z, p.2.1 z * D.η z ∂μ).prod with hcw_def
    set Pw := (w.map fun p => p.2.2).prod with hPw_def
    set q := nestN D w H with hq_def
    set ew := Kfun D w.length * Pw * (eH + |cH| * D.θ ^ (m - 1)) with hew_def
    have hew0 : 0 ≤ eH := (abs_nonneg _).trans (happ y)
    have hew : 0 ≤ ew := by
      have := Kfun_nonneg D w.length
      have : 0 ≤ |cH| * D.θ ^ (m - 1) := mul_nonneg (abs_nonneg _) (pow_nonneg D.θ_nonneg _)
      positivity
    have hR : ∀ z, |q z - cw * cH * D.η z| ≤ ew := fun z => ih hw' hwm' z
    have hqm : Measurable q := measurable_nestN D hw' hH
    have hqB : ∀ z, |q z| ≤ D.E ^ w.length * Pw * BH := abs_nestN_le D hw' hH hBH0 hHB
    -- Split `g q = c_w c_H (g η) + g (q - c_w c_H η)`.
    have hgη : Measurable fun z => g z * D.η z := hb.2.1.mul D.measurable_η
    have hgηb : ∀ z, |g z * D.η z| ≤ b * D.Bη := fun z => by
      rw [abs_mul, abs_of_nonneg (D.η_nonneg z)]
      exact mul_le_mul (hb.2.2.2 z) (D.η_le z) (D.η_nonneg z) hb.2.2.1
    have hRm : Measurable fun z => g z * (q z - cw * cH * D.η z) :=
      hb.2.1.mul (hqm.sub (measurable_const.mul D.measurable_η))
    have hRb : ∀ z, |g z * (q z - cw * cH * D.η z)| ≤ b * ew := fun z => by
      rw [abs_mul]; exact mul_le_mul (hb.2.2.2 z) (hR z) (abs_nonneg _) hb.2.2.1
    set Bc := |cw * cH| * (b * D.Bη) + b * ew with hBc_def
    have h1m : Measurable fun z => cw * cH * (g z * D.η z) := measurable_const.mul hgη
    have h1b : ∀ z, |cw * cH * (g z * D.η z)| ≤ Bc := fun z => by
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_left (hgηb z) (abs_nonneg (cw * cH))
      have : 0 ≤ b * ew := mul_nonneg hb.2.2.1 hew
      linarith
    have h2b : ∀ z, |g z * (q z - cw * cH * D.η z)| ≤ Bc := fun z => by
      have := hRb z
      have : 0 ≤ |cw * cH| * (b * D.Bη) := by positivity
      linarith
    have hsplit : nestN D ((n, g, b) :: w) H y =
        cw * cH * nkp C D.r n (fun z => g z * D.η z) y +
          nkp C D.r n (fun z => g z * (q z - cw * cH * D.η z)) y := by
      simp only [nestN]
      rw [← show nkp C D.r n (fun z => cw * cH * (g z * D.η z)) y =
          cw * cH * nkp C D.r n (fun z => g z * D.η z) y by
        simp only [nkp]; rw [kpow_const_mul]; ring]
      rw [← nkp_add C D.r n h1m hRm h1b h2b]
      congr 2
      funext z
      ring
    -- The rank-one part and the remainder.
    have hdec := D.decay (fun z => g z * D.η z) hgη (b * D.Bη) hgηb (n - 1) y
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hdec
    have hrem := D.nkp_abs_le n hRm (mul_nonneg hb.2.2.1 hew) hRb y
    have hθ : D.θ ^ (n - 1) ≤ D.θ ^ (m - 1) :=
      pow_le_pow_of_le_one D.θ_nonneg D.θ_lt_one.le (by omega)
    have hcwb : |cw| ≤ Pw := abs_prod_nu_le D hη1 hw'
    simp only [List.map_cons, List.prod_cons, List.length_cons, Kfun]
    rw [hsplit]
    have key : |cw * cH * nkp C D.r n (fun z => g z * D.η z) y -
        (∫ z, g z * D.η z ∂μ) * cw * cH * D.η y| ≤ Pw * |cH| * (D.A * D.θ ^ (m - 1) * (b * D.Bη)) := by
      rw [show cw * cH * nkp C D.r n (fun z => g z * D.η z) y -
          (∫ z, g z * D.η z ∂μ) * cw * cH * D.η y =
          (cw * cH) * (nkp C D.r n (fun z => g z * D.η z) y -
            (∫ z, g z * D.η z ∂μ) * D.η y) by ring, abs_mul, abs_mul]
      have h1 : D.A * D.θ ^ (n - 1) * (b * D.Bη) ≤ D.A * D.θ ^ (m - 1) * (b * D.Bη) := by
        have := mul_le_mul_of_nonneg_left hθ hA
        exact mul_le_mul_of_nonneg_right this (by positivity)
      calc |cw| * |cH| * |nkp C D.r n (fun z => g z * D.η z) y - (∫ z, g z * D.η z ∂μ) * D.η y|
          ≤ |cw| * |cH| * (D.A * D.θ ^ (m - 1) * (b * D.Bη)) :=
            mul_le_mul_of_nonneg_left (hdec.trans h1) (by positivity)
        _ ≤ Pw * |cH| * (D.A * D.θ ^ (m - 1) * (b * D.Bη)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcwb (abs_nonneg _))
              (by positivity)
    have hfin : |cw * cH * nkp C D.r n (fun z => g z * D.η z) y +
        nkp C D.r n (fun z => g z * (q z - cw * cH * D.η z)) y -
          (∫ z, g z * D.η z ∂μ) * cw * cH * D.η y| ≤
        Pw * |cH| * (D.A * D.θ ^ (m - 1) * (b * D.Bη)) + D.E * (b * ew) := by
      have := abs_add_le (cw * cH * nkp C D.r n (fun z => g z * D.η z) y -
        (∫ z, g z * D.η z ∂μ) * cw * cH * D.η y) (nkp C D.r n (fun z => g z * (q z - cw * cH * D.η z)) y)
      rw [show cw * cH * nkp C D.r n (fun z => g z * D.η z) y -
          (∫ z, g z * D.η z ∂μ) * cw * cH * D.η y +
          nkp C D.r n (fun z => g z * (q z - cw * cH * D.η z)) y =
          cw * cH * nkp C D.r n (fun z => g z * D.η z) y +
          nkp C D.r n (fun z => g z * (q z - cw * cH * D.η z)) y -
          (∫ z, g z * D.η z ∂μ) * cw * cH * D.η y by ring] at this
      linarith
    rw [show (∫ z, g z * D.η z ∂μ) * cw * cH * D.η y = (∫ z, g z * D.η z ∂μ) * cw * cH * D.η y
      from rfl]
    have hb0 := hb.2.2.1
    have hcθ : |cH| * D.θ ^ (m - 1) ≤ eH + |cH| * D.θ ^ (m - 1) := by linarith
    have hfirst : Pw * |cH| * (D.A * D.θ ^ (m - 1) * (b * D.Bη)) ≤
        D.A * D.Bη * (b * Pw) * (eH + |cH| * D.θ ^ (m - 1)) := by
      have := mul_le_mul_of_nonneg_left hcθ (by positivity : (0:ℝ) ≤ D.A * D.Bη * (b * Pw))
      nlinarith
    have hsecond : D.E * (b * ew) =
        D.E * Kfun D w.length * (b * Pw) * (eH + |cH| * D.θ ^ (m - 1)) := by
      rw [hew_def]; ring
    calc _ ≤ Pw * |cH| * (D.A * D.θ ^ (m - 1) * (b * D.Bη)) + D.E * (b * ew) := hfin
      _ ≤ D.A * D.Bη * (b * Pw) * (eH + |cH| * D.θ ^ (m - 1)) +
          D.E * Kfun D w.length * (b * Pw) * (eH + |cH| * D.θ ^ (m - 1)) := by
          rw [hsecond]; linarith
      _ = (D.A * D.Bη + D.E * Kfun D w.length) * (b * Pw) * (eH + |cH| * D.θ ^ (m - 1)) := by
          ring

end Estimate

/-!
### Mixing of all orders
-/

section Main

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

theorem ratio_bound {V P a η e₁ e₂ c : ℝ} (ha : c ≤ a) (hc : 0 < c)
    (h1 : |V - P * η| ≤ e₁) (h2 : |P| * |η - a| ≤ e₂) : |V / a - P| ≤ (e₁ + e₂) / c := by
  have ha0 : 0 < a := hc.trans_le ha
  rw [show V / a - P = (V - P * a) / a by field_simp, abs_div, abs_of_pos ha0]
  have he : 0 ≤ e₁ + e₂ := by linarith [abs_nonneg (V - P * η), mul_nonneg (abs_nonneg P) (abs_nonneg (η - a))]
  have hnum : |V - P * a| ≤ e₁ + e₂ := by
    have : V - P * a = (V - P * η) + P * (η - a) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]; linarith
  calc |V - P * a| / a ≤ (e₁ + e₂) / a := div_le_div_of_nonneg_right hnum ha0.le
    _ ≤ (e₁ + e₂) / c := div_le_div_of_nonneg_left he hc ha

set_option maxHeartbeats 2000000 in
/-- **Mixing of all orders** for bounded measurable observables of any sign. -/
theorem mixing_all_orders (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (x : d.State) :
    ∃ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 ∧ ∀ k : ℕ, ∃ Kk : ℝ, ∀ w : Obs M, w.length = k → Admissible w →
      ∀ m : ℕ, 1 ≤ m → (∀ p ∈ w, m ≤ p.1) →
        (∀ (n : ℕ) (g : M → ℝ) (b : ℝ), 1 ≤ n → m ≤ n → Measurable g → 0 ≤ b →
          (∀ y, |g y| ≤ b) →
          |∫ ω, observe (w ++ [(n, g, b)]) 0 ω ∂C.conditionedMeasure x.val (gapsum w + n) -
            (w.map fun p => ∫ y, p.2.1 y ∂μ.withDensity d.weight).prod * ∫ y, g y ∂μ| ≤
            Kk * ϑ ^ m * ((w.map fun p => p.2.2).prod * b)) ∧
        (∀ l : ℕ, 1 ≤ l → m ≤ l →
          |∫ ω, observe w 0 ω ∂C.conditionedMeasure x.val (gapsum w + l) -
            (w.map fun p => ∫ y, p.2.1 y ∂μ.withDensity d.weight).prod| ≤
            Kk * ϑ ^ m * (w.map fun p => p.2.2).prod) := by
  have : Nonempty M := ⟨x.val⟩
  obtain ⟨D, hDr, hDη, -⟩ := exists_data0 C h d s μ hleft hnorm 0 zero_lt_one
  have hη1 : ∫ y, D.η y ∂μ = 1 := by
    rw [hDη]; exact L2Compactness.integral_eta (K := C.toKilledKernel) d μ hnorm
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  set a : ℕ → ℝ := fun N => nkp C D.r N (fun _ => 1) x.val with ha_def
  have ha_eq : ∀ N, (C.pathMeasure x.val (survival N)).toReal = D.r ^ N * a N := by
    intro N
    have : IsFiniteKernel (C.killedTransition ^ N) := killedKernel_power_isFinite C.toKilledKernel N
    rw [C.pathMeasure_survival]
    simp only [ha_def, nkp, kpow, integral_const, smul_eq_mul, mul_one]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ D.r_pos.ne', one_pow, one_mul]
    rfl
  have ha_pos : ∀ N, 0 < a N := fun N => by
    have hp := C.pathMeasure_survival_pos x.val hx N
    have hpos : 0 < (C.pathMeasure x.val (survival N)).toReal :=
      ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
    rw [ha_eq] at hpos
    exact pos_of_mul_pos_right hpos (pow_pos D.r_pos N).le
  set ηx := (d.weight x.val).toReal with hηx_def
  have hηx : 0 < ηx := ENNReal.toReal_pos x.property (d.weight_ne_top _)
  have ha_lim : Tendsto a atTop (𝓝 ηx) := by
    have := s.normalized_survival_tendstoUniformly.tendsto_at x.val
    refine this.congr fun N => ?_
    rw [normalized_survival_toReal (K := C.toKilledKernel) d N x.val]
    have : IsFiniteKernel (C.killedTransition ^ N) := killedKernel_power_isFinite C.toKilledKernel N
    simp only [ha_def, nkp, kpow, integral_const, smul_eq_mul, mul_one, hDr]
    rfl
  obtain ⟨c, hc, hca⟩ := SecondMoment.exists_pos_lower ha_pos hηx ha_lim
  have hηDx : D.η x.val = ηx := by rw [hDη]
  set θ := D.θ with hθ_def
  have hθ0 : 0 ≤ θ := D.θ_nonneg
  set ϑ := max θ (1 / 2) with hϑ_def
  have hϑ0 : 0 < ϑ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hϑ1 : ϑ < 1 := max_lt D.θ_lt_one (by norm_num)
  have hθϑ : ∀ m : ℕ, 1 ≤ m → θ ^ (m - 1) ≤ 2 * ϑ ^ m := by
    intro m hm
    have h1 : θ ^ (m - 1) ≤ ϑ ^ (m - 1) := pow_le_pow_left₀ hθ0 (le_max_left _ _) _
    have h2 : ϑ ^ m = ϑ * ϑ ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm]
    have h3 : (1 / 2 : ℝ) ≤ ϑ := le_max_right _ _
    have h4 : 0 ≤ ϑ ^ (m - 1) := pow_nonneg hϑ0.le _
    nlinarith
  have hνeq : ∀ g : M → ℝ, ∫ y, g y ∂μ.withDensity d.weight = ∫ y, g y * D.η y ∂μ := by
    intro g
    rw [hDη, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
    congr 1; funext y; rw [smul_eq_mul, mul_comm]
  have hA := D.A_nonneg
  have hS := D.S_nonneg
  have hE := D.E_nonneg
  refine ⟨ϑ, hϑ0, hϑ1, fun k => ⟨2 * (Kfun D k * (D.A + D.S + 1) + D.S) / c,
    fun w hwk hw m hm hwm => ⟨fun n g b hn hmn hg hb0 hgb => ?_, fun l hl hml => ?_⟩⟩⟩
  all_goals
    have hprod : (w.map fun p => ∫ y, p.2.1 y ∂μ.withDensity d.weight).prod =
        (w.map fun p => ∫ z, p.2.1 z * D.η z ∂μ).prod := by
      congr 1; exact List.map_congr_left fun p _ => hνeq p.2.1
    have hK := Kfun_nonneg D k
    have hPw := prod_bounds_nonneg hw
    have hcw := abs_prod_nu_le D hη1 hw
    rw [hprod]
  · -- Conditioning at the last observation time.
    rw [integral_conditioned_observe_last C hw hn hg hb0 hgb, ha_eq]
    set N := gapsum w + n with hN_def
    have hscale : (D.r ^ N * a N)⁻¹ * nestK C w (kpow C n g) x.val =
        nestN D w (nkp C D.r n g) x.val / a N := by
      have e1 : nestN D w (nkp C D.r n g) x.val =
          D.r⁻¹ ^ n * (D.r⁻¹ ^ gapsum w * nestK C w (kpow C n g) x.val) := by
        rw [nestN_eq, ← nestN_const_mul]; rfl
      rw [e1, hN_def, pow_add, mul_inv, inv_pow, inv_pow]
      field_simp
    rw [hscale]
    have happ : ∀ z, |nkp C D.r n g z - (∫ y, g y ∂μ) * D.η z| ≤ D.A * θ ^ (n - 1) * b := by
      intro z
      have := D.decay g hg b hgb (n - 1) z
      rwa [Nat.sub_add_cancel hn] at this
    have hcH : |∫ y, g y ∂μ| ≤ b := SecondMoment.abs_integral_le_of_prob hgb
    have hnest := nest_approx D hη1 hw hm hwm (measurable_nkp C _ n hg) (mul_nonneg hE hb0)
      (D.nkp_abs_le n hg hb0 hgb) happ x.val
    rw [hwk] at hnest
    have hθn : θ ^ (n - 1) ≤ θ ^ (m - 1) := pow_le_pow_of_le_one hθ0 D.θ_lt_one.le (by omega)
    have hθN : θ ^ (N - 1) ≤ θ ^ (m - 1) := pow_le_pow_of_le_one hθ0 D.θ_lt_one.le (by omega)
    have hmass := D.mass_sub N x.val (by omega)
    have hηa : |D.η x.val - a N| ≤ D.S * θ ^ (m - 1) := by
      rw [abs_sub_comm]
      exact hmass.trans (mul_le_mul_of_nonneg_left hθN hS)
    set P := (w.map fun p => ∫ z, p.2.1 z * D.η z ∂μ).prod * ∫ y, g y ∂μ with hP_def
    have hPb : |P| ≤ (w.map fun p => p.2.2).prod * b := by
      rw [hP_def, abs_mul]; exact mul_le_mul hcw hcH (abs_nonneg _) hPw
    have he1 : Kfun D k * (w.map fun p => p.2.2).prod *
        (D.A * θ ^ (n - 1) * b + |∫ y, g y ∂μ| * θ ^ (m - 1)) ≤
        Kfun D k * (D.A + 1) * ((w.map fun p => p.2.2).prod * b) * θ ^ (m - 1) := by
      have h1 : D.A * θ ^ (n - 1) * b ≤ D.A * θ ^ (m - 1) * b :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθn hA) hb0
      have h2 : |∫ y, g y ∂μ| * θ ^ (m - 1) ≤ b * θ ^ (m - 1) :=
        mul_le_mul_of_nonneg_right hcH (pow_nonneg hθ0 _)
      have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
        (mul_nonneg hK hPw)
      calc _ ≤ Kfun D k * (w.map fun p => p.2.2).prod * (D.A * θ ^ (m - 1) * b +
            b * θ ^ (m - 1)) := h3
        _ = _ := by ring
    have hr := ratio_bound (hca N) hc (hnest.trans he1)
      (mul_le_mul hPb hηa (abs_nonneg _) (by positivity))
    have hfin := hθϑ m hm
    refine hr.trans ?_
    rw [div_le_iff₀ hc]
    have hX : 0 ≤ (w.map fun p => p.2.2).prod * b := by positivity
    have key : Kfun D k * (D.A + 1) * ((w.map fun p => p.2.2).prod * b) * θ ^ (m - 1) +
        (w.map fun p => p.2.2).prod * b * (D.S * θ ^ (m - 1)) ≤
        (Kfun D k * (D.A + D.S + 1) + D.S) * ((w.map fun p => p.2.2).prod * b) *
          (2 * ϑ ^ m) := by
      have hθm := pow_nonneg hθ0 (m - 1)
      have hsplit : Kfun D k * (D.A + 1) * ((w.map fun p => p.2.2).prod * b) * θ ^ (m - 1) +
          (w.map fun p => p.2.2).prod * b * (D.S * θ ^ (m - 1)) ≤
          (Kfun D k * (D.A + D.S + 1) + D.S) * ((w.map fun p => p.2.2).prod * b) *
            θ ^ (m - 1) := by
        have : 0 ≤ Kfun D k * D.S * ((w.map fun p => p.2.2).prod * b) * θ ^ (m - 1) := by
          positivity
        nlinarith
      refine hsplit.trans (mul_le_mul_of_nonneg_left hfin (by positivity))
    have : 2 * (Kfun D k * (D.A + D.S + 1) + D.S) / c * ϑ ^ m *
        ((w.map fun p => p.2.2).prod * b) * c =
        (Kfun D k * (D.A + D.S + 1) + D.S) * ((w.map fun p => p.2.2).prod * b) * (2 * ϑ ^ m) := by
      field_simp
    linarith
  · -- Conditioning beyond the last observation.
    rw [integral_conditioned_observe C hw hl, ha_eq]
    set N := gapsum w + l with hN_def
    have hscale : (D.r ^ N * a N)⁻¹ * nestK C w (kpow C l (fun _ => 1)) x.val =
        nestN D w (nkp C D.r l (fun _ => 1)) x.val / a N := by
      have e1 : nestN D w (nkp C D.r l (fun _ => 1)) x.val =
          D.r⁻¹ ^ l * (D.r⁻¹ ^ gapsum w * nestK C w (kpow C l (fun _ => 1)) x.val) := by
        rw [nestN_eq, ← nestN_const_mul]; rfl
      rw [e1, hN_def, pow_add, mul_inv, inv_pow, inv_pow]
      field_simp
    rw [hscale]
    have happ : ∀ z, |nkp C D.r l (fun _ => 1) z - 1 * D.η z| ≤ D.S * θ ^ (l - 1) := by
      intro z; rw [one_mul]; exact D.mass_sub l z hl
    have hnest := nest_approx D hη1 hw hm hwm (measurable_nkp C _ l measurable_const) hE
      (fun z => by rw [abs_of_nonneg (nkp_nonneg C D.r_pos.le l (fun _ => zero_le_one) z)]
                   exact D.mass_le l z) happ x.val
    rw [hwk, mul_one] at hnest
    have hθl : θ ^ (l - 1) ≤ θ ^ (m - 1) := pow_le_pow_of_le_one hθ0 D.θ_lt_one.le (by omega)
    have hθN : θ ^ (N - 1) ≤ θ ^ (m - 1) := pow_le_pow_of_le_one hθ0 D.θ_lt_one.le (by omega)
    have hmass := D.mass_sub N x.val (by omega)
    have hηa : |D.η x.val - a N| ≤ D.S * θ ^ (m - 1) := by
      rw [abs_sub_comm]
      exact hmass.trans (mul_le_mul_of_nonneg_left hθN hS)
    set P := (w.map fun p => ∫ z, p.2.1 z * D.η z ∂μ).prod with hP_def
    have he1 : Kfun D k * (w.map fun p => p.2.2).prod * (D.S * θ ^ (l - 1) + |1| * θ ^ (m - 1)) ≤
        Kfun D k * (D.S + 1) * (w.map fun p => p.2.2).prod * θ ^ (m - 1) := by
      rw [abs_one, one_mul]
      have h1 := mul_le_mul_of_nonneg_left hθl hS
      have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 (le_refl (θ ^ (m - 1))))
        (mul_nonneg hK hPw)
      calc _ ≤ Kfun D k * (w.map fun p => p.2.2).prod * (D.S * θ ^ (m - 1) + θ ^ (m - 1)) := h3
        _ = _ := by ring
    have hr := ratio_bound (P := P) (hca N) hc (by simpa only [mul_one] using hnest.trans he1)
      (mul_le_mul hcw hηa (abs_nonneg _) hPw)
    have hfin := hθϑ m hm
    refine hr.trans ?_
    rw [div_le_iff₀ hc]
    have key : Kfun D k * (D.S + 1) * (w.map fun p => p.2.2).prod * θ ^ (m - 1) +
        (w.map fun p => p.2.2).prod * (D.S * θ ^ (m - 1)) ≤
        (Kfun D k * (D.A + D.S + 1) + D.S) * (w.map fun p => p.2.2).prod * (2 * ϑ ^ m) := by
      have hθm := pow_nonneg hθ0 (m - 1)
      have hsplit : Kfun D k * (D.S + 1) * (w.map fun p => p.2.2).prod * θ ^ (m - 1) +
          (w.map fun p => p.2.2).prod * (D.S * θ ^ (m - 1)) ≤
          (Kfun D k * (D.A + D.S + 1) + D.S) * (w.map fun p => p.2.2).prod * θ ^ (m - 1) := by
        have : 0 ≤ Kfun D k * D.A * (w.map fun p => p.2.2).prod * θ ^ (m - 1) := by positivity
        nlinarith
      refine hsplit.trans (mul_le_mul_of_nonneg_left hfin (by positivity))
    have : 2 * (Kfun D k * (D.A + D.S + 1) + D.S) / c * ϑ ^ m *
        (w.map fun p => p.2.2).prod * c =
        (Kfun D k * (D.A + D.S + 1) + D.S) * (w.map fun p => p.2.2).prod * (2 * ϑ ^ m) := by
      field_simp
    linarith

end Main

end

end ConditionedStableLaws.MixingAllOrders
