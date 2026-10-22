import ConditionedStableLaws.FeynmanKac
import ConditionedStableLaws.QProcessVariance
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Conditional second moments of Birkhoff sums

For every `x ∈ M \ Z` there is `Cₓ` such that for every bounded measurable `g` with `ν(g) = 0` and
every `n ≥ 1`, `E_x[(∑_{i<n} g(Xᵢ))² | τ > n] ≤ Cₓ (n μ(g²) + ‖g‖∞²)`, which implies the bound `Cₓ n
(ν(g²) + μ(g²)) + Cₓ ‖g‖∞²`. The second moment is expanded with the Feynman–Kac formula into
operator words of the killed kernel, and estimated with the pointwise exponential decay of centred
kernel iterates, invariance of `μ`, a Cauchy–Schwarz inequality for kernels, and the `L²(μ)` decay
of `Rᵐ`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ConditionedStableLaws.SecondMoment

noncomputable section

open StandingHypothesis CanonicalChain FeynmanKac

/-! ### Operator words with blocks of ones -/

section Words

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- The `k`-step killed kernel integral `Tᵏ f (y) = ∫ f dKᵏ(y)`. -/
def kpow (k : ℕ) (f : M → ℝ) (y : M) : ℝ := ∫ z, f z ∂(C.killedTransition ^ k) y

theorem kpow_zero (f : M → ℝ) (hf : Measurable f) : kpow C 0 f = f := by
  funext y
  change ∫ z, f z ∂(Kernel.id y) = f y
  rw [Kernel.id_apply, integral_dirac' _ _ hf.stronglyMeasurable]

/-- `T (Tˡ h) = Tˡ⁺¹ h` for bounded measurable `h`. -/
theorem kpow_succ (l : ℕ) {h : M → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B)
    (y : M) : (∫ z, kpow C l h z ∂C.killedTransition y) = kpow C (l + 1) h y := by
  have : IsFiniteKernel (C.killedTransition ^ l) :=
    killedKernel_power_isFinite C.toKilledKernel l
  have : IsFiniteKernel (C.killedTransition ^ (l + 1)) :=
    killedKernel_power_isFinite C.toKilledKernel (l + 1)
  unfold kpow
  rw [pow_succ]
  refine (Kernel.integral_comp (η := C.killedTransition ^ l) (κ := C.killedTransition) (a := y)
    (f := h) ?_).symm
  refine Integrable.of_bound hh.aestronglyMeasurable B (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]; exact hB z

/-- `Tˡ (T h) = Tˡ⁺¹ h` for bounded measurable `h`. -/
theorem kpow_succ' (l : ℕ) {h : M → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B)
    (y : M) : kpow C l (fun z => ∫ w, h w ∂C.killedTransition z) y = kpow C (l + 1) h y := by
  have : IsFiniteKernel (C.killedTransition ^ l) :=
    killedKernel_power_isFinite C.toKilledKernel l
  have : IsFiniteKernel (C.killedTransition ^ (l + 1)) :=
    killedKernel_power_isFinite C.toKilledKernel (l + 1)
  unfold kpow
  rw [pow_succ']
  refine (Kernel.integral_comp (η := C.killedTransition) (κ := C.killedTransition ^ l) (a := y)
    (f := h) ?_).symm
  refine Integrable.of_bound hh.aestronglyMeasurable B (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]; exact hB z

theorem measurable_kpow (k : ℕ) {f : M → ℝ} (hf : Measurable f) : Measurable (kpow C k f) :=
  (hf.stronglyMeasurable.integral_kernel (κ := C.killedTransition ^ k)).measurable

theorem abs_kpow_le (k : ℕ) {f : M → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, |f y| ≤ B) (y : M) :
    |kpow C k f y| ≤ B := by
  have : IsFiniteKernel (C.killedTransition ^ k) := killedKernel_power_isFinite C.toKilledKernel k
  have := norm_integral_le_of_norm_le_const (μ := (C.killedTransition ^ k) y) (C := B)
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  have hm : ((C.killedTransition ^ k) y).real univ ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact C.killedTransition_pow_mass_le_one y k)
  nlinarith [measureReal_nonneg (μ := (C.killedTransition ^ k) y) (s := univ)]

/-- A block of `l` unit observations collapses to `Tˡ`. -/
theorem killedWord_ones (φ : ℕ → M → ℝ) (m : ℕ) :
    ∀ l : ℕ, (∀ k, m ≤ k → k < m + l → φ k = fun _ => 1) →
      ∀ (h : M → ℝ), Measurable h → ∀ B : ℝ, 0 ≤ B → (∀ y, |h y| ≤ B) →
        killedWord C φ (m + l) h = killedWord C φ m (kpow C l h) := by
  intro l
  induction l with
  | zero =>
      intro _ h hh B _ _
      simp only [Nat.add_zero]
      rw [kpow_zero C h hh]
  | succ l ih =>
      intro hφ h hh B hB0 hB
      rw [← Nat.add_assoc]
      change killedWord C φ (m + l) (fun y => φ (m + l) y * ∫ z, h z ∂C.killedTransition y) = _
      rw [hφ (m + l) (by omega) (by omega)]
      simp only [one_mul]
      have hKh : Measurable (fun y => ∫ z, h z ∂C.killedTransition y) :=
        (hh.stronglyMeasurable.integral_kernel (κ := C.killedTransition)).measurable
      rw [ih (fun k hk hk' => hφ k hk (by omega)) _ hKh B hB0
        (fun y => by simpa [kpow, pow_one] using abs_kpow_le C 1 hB0 hB y)]
      congr 1
      funext y
      exact kpow_succ' C l hh hB y

/-- Observations `g` at times `i` and `j`, and `1` elsewhere. -/
def pairObs (g : M → ℝ) (i j : ℕ) : ℕ → M → ℝ := fun k => if k = i ∨ k = j then g else fun _ => 1

/-- The observation `g²` at time `i`, and `1` elsewhere. -/
def diagObs (g : M → ℝ) (i : ℕ) : ℕ → M → ℝ := fun k => if k = i then fun y => g y * g y else fun _ => 1

theorem abs_mul_kpow_le {g f : M → ℝ} {G B : ℝ} (hG0 : 0 ≤ G) (hB0 : 0 ≤ B)
    (hg : ∀ y, |g y| ≤ G) (hf : ∀ y, |f y| ≤ B) (k : ℕ) (y : M) :
    |g y * kpow C k f y| ≤ G * B := by
  rw [abs_mul]; exact mul_le_mul (hg y) (abs_kpow_le C k hB0 hf y) (abs_nonneg _) hG0

/-- The pair word `Tⁱ(g Tʲ⁻ⁱ(g Tⁿ⁻ʲ 1))` for `i < j < n`. -/
theorem killedWord_pair {g : M → ℝ} (hg : Measurable g) {G : ℝ} (hG0 : 0 ≤ G)
    (hgG : ∀ y, |g y| ≤ G) {i j n : ℕ} (hij : i < j) (hjn : j < n) :
    killedWord C (pairObs g i j) n (fun _ => 1) =
      kpow C i (fun y => g y * kpow C (j - i) (fun z => g z * kpow C (n - j) (fun _ => 1) z) y) := by
  have h1 : ∀ y, |(fun _ : M => (1 : ℝ)) y| ≤ 1 := fun _ => by simp
  -- Times after `j`.
  obtain ⟨l, rfl⟩ : ∃ l, n = j + 1 + l := ⟨n - j - 1, by omega⟩
  rw [killedWord_ones C _ (j + 1) l (fun k hk hk' => by
      simp only [pairObs]; rw [ite_eq_right (by omega)]) _ measurable_const 1 zero_le_one h1]
  change killedWord C (pairObs g i j) j (fun y => pairObs g i j j y *
    ∫ z, kpow C l (fun _ => 1) z ∂C.killedTransition y) = _
  rw [show pairObs g i j j = g by simp [pairObs]]
  simp_rw [kpow_succ C l measurable_const h1]
  -- Times strictly between `i` and `j`.
  obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - i - 1, by omega⟩
  have hF : Measurable (fun y => g y * kpow C (i + 1 + m + 1 + l - (i + 1 + m)) (fun _ => 1) y) :=
    hg.mul (measurable_kpow C _ measurable_const)
  rw [killedWord_ones C _ (i + 1) m (fun k hk hk' => by
      simp only [pairObs]; rw [ite_eq_right (by omega)]) _ ?_ (G * 1) (by positivity) ?_]
  · change killedWord C (pairObs g i (i + 1 + m)) i (fun y => pairObs g i (i + 1 + m) i y *
      ∫ z, kpow C m (fun y => g y * kpow C (l + 1) (fun _ => 1) y) z ∂C.killedTransition y) = _
    rw [show pairObs g i (i + 1 + m) i = g by simp [pairObs]]
    simp_rw [kpow_succ C m (h := fun y => g y * kpow C (l + 1) (fun _ => 1) y)
      (hg.mul (measurable_kpow C _ measurable_const))
      (fun y => abs_mul_kpow_le C hG0 zero_le_one hgG h1 (l + 1) y)]
    -- Times before `i`.
    have := killedWord_ones C (pairObs g i (i + 1 + m)) 0 i (fun k hk hk' => by
      simp only [pairObs]; rw [ite_eq_right (by omega)])
      (fun y => g y * kpow C (m + 1) (fun y => g y * kpow C (l + 1) (fun _ => 1) y) y)
      (hg.mul (measurable_kpow C _ (hg.mul (measurable_kpow C _ measurable_const)))) (G * (G * 1))
      (by positivity) (fun y => abs_mul_kpow_le C hG0 (by positivity) hgG
        (fun z => abs_mul_kpow_le C hG0 zero_le_one hgG h1 _ z) _ y)
    simp only [Nat.zero_add] at this
    rw [this]
    have e1 : i + 1 + m - i = m + 1 := by omega
    have e2 : i + 1 + m + 1 + l - (i + 1 + m) = l + 1 := by omega
    rw [e1, e2]
    rfl
  · exact hg.mul (measurable_kpow C _ measurable_const)
  · exact fun y => abs_mul_kpow_le C hG0 zero_le_one hgG h1 _ y

/-- The diagonal word `Tⁱ(g² Tⁿ⁻ⁱ 1)` for `i < n`. -/
theorem killedWord_diag {g : M → ℝ} (hg : Measurable g) {G : ℝ} (hG0 : 0 ≤ G)
    (hgG : ∀ y, |g y| ≤ G) {i n : ℕ} (hin : i < n) :
    killedWord C (diagObs g i) n (fun _ => 1) =
      kpow C i (fun y => g y * g y * kpow C (n - i) (fun _ => 1) y) := by
  have h1 : ∀ y, |(fun _ : M => (1 : ℝ)) y| ≤ 1 := fun _ => by simp
  obtain ⟨l, rfl⟩ : ∃ l, n = i + 1 + l := ⟨n - i - 1, by omega⟩
  rw [killedWord_ones C _ (i + 1) l (fun k hk hk' => by
      simp only [diagObs]; rw [ite_eq_right (by omega)]) _ measurable_const 1 zero_le_one h1]
  change killedWord C (diagObs g i) i (fun y => diagObs g i i y *
    ∫ z, kpow C l (fun _ => 1) z ∂C.killedTransition y) = _
  rw [show diagObs g i i = fun y => g y * g y by simp [diagObs]]
  simp_rw [kpow_succ C l measurable_const h1]
  have hgg : ∀ y, |g y * g y| ≤ G * G := fun y => by
    rw [abs_mul]; exact mul_le_mul (hgG y) (hgG y) (abs_nonneg _) hG0
  have := killedWord_ones C (diagObs g i) 0 i (fun k hk hk' => by
      simp only [diagObs]; rw [ite_eq_right (by omega)])
    (fun y => g y * g y * kpow C (l + 1) (fun _ => 1) y)
    ((hg.mul hg).mul (measurable_kpow C _ measurable_const)) (G * G * 1) (by positivity)
    (fun y => abs_mul_kpow_le C (by positivity) zero_le_one hgg h1 _ y)
  simp only [Nat.zero_add] at this
  rw [this]
  have e : i + 1 + l - i = l + 1 := by omega
  rw [e]
  rfl

end Words

/-! ### The second-moment identity -/

section Identity

theorem sq_sum_eq (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, a i) ^ 2 =
      ∑ i ∈ Finset.range n, a i * a i + 2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, a i * a j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, add_sq, ih, Finset.sum_range_succ, Finset.sum_range_succ (fun j => _),
        mul_assoc 2, Finset.sum_mul]
      ring

theorem prod_ite_pair (a : ℕ → ℝ) {i j n : ℕ} (hij : i < j) (hjn : j < n) :
    ∏ k ∈ Finset.range n, (if k = i ∨ k = j then a k else 1) = a i * a j := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  have : (Finset.range n).filter (fun k => k = i ∨ k = j) = {i, j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro (rfl | rfl) <;> [exact ⟨by omega, Or.inl rfl⟩; exact ⟨hjn, Or.inr rfl⟩]
  rw [this, Finset.prod_pair (by omega)]

theorem prod_ite_single (a : ℕ → ℝ) {i n : ℕ} (hin : i < n) :
    ∏ k ∈ Finset.range n, (if k = i then a k else 1) = a i := by
  rw [Finset.prod_ite_eq' (Finset.range n) i a]
  simp [hin]

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

omit [MeasurableSpace M] in
theorem ext_eq_zeroExtension (g : M → ℝ) : ext g = zeroExtension g := by
  funext z; cases z <;> rfl

/-- `E_x[g(Xᵢ) g(Xⱼ) ; τ > n]` as a kernel word, `i < j < n`. -/
theorem integral_pair_survival {g : M → ℝ} (hg : Measurable g) {G : ℝ} (hG0 : 0 ≤ G)
    (hgG : ∀ y, |g y| ≤ G) {i j n : ℕ} (hij : i < j) (hjn : j < n) (x : M) :
    ∫ ω, (survival n).indicator (fun ω => zeroExtension g (ω i) * zeroExtension g (ω j)) ω
      ∂C.pathMeasure x =
      kpow C i (fun y => g y * kpow C (j - i) (fun z => g z * kpow C (n - j) (fun _ => 1) z) y) x := by
  have hφ : ∀ k, Measurable (pairObs g i j k) := fun k => by
    unfold pairObs; split_ifs; exacts [hg, measurable_const]
  have hA : ∀ k y, ‖pairObs g i j k y‖ ≤ max G 1 := fun k y => by
    unfold pairObs; split_ifs
    · rw [Real.norm_eq_abs]; exact (hgG y).trans (le_max_left _ _)
    · simp
  rw [← killedWord_pair C hg hG0 hgG hij hjn, ← integral_prod_survival C (pairObs g i j) hφ
    (le_max_of_le_right zero_le_one) hA n x]
  apply integral_congr_ae
  refine Eventually.of_forall fun ω => ?_
  by_cases hs : ω ∈ survival n
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    have : ∀ k ∈ Finset.range n, ext (pairObs g i j k) (ω k) =
        if k = i ∨ k = j then zeroExtension g (ω k) else 1 := by
      intro k hk
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hs k (Finset.mem_range.1 hk).le)
      unfold pairObs
      split_ifs
      · rw [ext_eq_zeroExtension]
      · rw [hy, ext_some]
    rw [Finset.prod_congr rfl this, prod_ite_pair (fun k => zeroExtension g (ω k)) hij hjn]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

/-- `E_x[g(Xᵢ)² ; τ > n]` as a kernel word, `i < n`. -/
theorem integral_diag_survival {g : M → ℝ} (hg : Measurable g) {G : ℝ} (hG0 : 0 ≤ G)
    (hgG : ∀ y, |g y| ≤ G) {i n : ℕ} (hin : i < n) (x : M) :
    ∫ ω, (survival n).indicator (fun ω => zeroExtension g (ω i) * zeroExtension g (ω i)) ω
      ∂C.pathMeasure x =
      kpow C i (fun y => g y * g y * kpow C (n - i) (fun _ => 1) y) x := by
  have hφ : ∀ k, Measurable (diagObs g i k) := fun k => by
    unfold diagObs; split_ifs; exacts [hg.mul hg, measurable_const]
  have hA : ∀ k y, ‖diagObs g i k y‖ ≤ max (G * G) 1 := fun k y => by
    unfold diagObs; split_ifs
    · rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hgG y) (hgG y) (abs_nonneg _) hG0).trans (le_max_left _ _)
    · simp
  rw [← killedWord_diag C hg hG0 hgG hin, ← integral_prod_survival C (diagObs g i) hφ
    (le_max_of_le_right zero_le_one) hA n x]
  apply integral_congr_ae
  refine Eventually.of_forall fun ω => ?_
  by_cases hs : ω ∈ survival n
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    have : ∀ k ∈ Finset.range n, ext (diagObs g i k) (ω k) =
        if k = i then zeroExtension g (ω k) * zeroExtension g (ω k) else 1 := by
      intro k hk
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hs k (Finset.mem_range.1 hk).le)
      unfold diagObs
      split_ifs
      · rw [hy, ext_some, zeroExtension_some]
      · rw [hy, ext_some]
    rw [Finset.prod_congr rfl this,
      prod_ite_single (fun k => zeroExtension g (ω k) * zeroExtension g (ω k)) hin]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

end Identity

/-! ### Geometric double sums -/

section Sums

variable {ϑ : ℝ} (h0 : 0 ≤ ϑ) (h1 : ϑ < 1)
include h0 h1

theorem geom_le (m : ℕ) : ∑ k ∈ Finset.range m, ϑ ^ k ≤ (1 - ϑ)⁻¹ := by
  rw [← tsum_geometric_of_lt_one h0 h1]
  exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg h0 j) (summable_geometric_of_lt_one h0 h1)

theorem geom_reflect_le (m : ℕ) : ∑ k ∈ Finset.range m, ϑ ^ (m - 1 - k) ≤ (1 - ϑ)⁻¹ := by
  rw [Finset.sum_range_reflect (fun k => ϑ ^ k) m]; exact geom_le h0 h1 m

theorem geom_pred_le (m : ℕ) : ∑ k ∈ Finset.range m, ϑ ^ (k - 1) ≤ 1 + (1 - ϑ)⁻¹ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp; have := inv_nonneg.2 (sub_pos.2 h1).le; linarith
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [Finset.sum_range_succ', zero_add]
  simp only [Nat.add_sub_cancel, Nat.zero_sub, pow_zero]
  linarith [geom_le h0 h1 m]

theorem dsum_gap_le (n : ℕ) :
    ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, ϑ ^ (j - i - 1) ≤ n * (1 - ϑ)⁻¹ := by
  calc ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, ϑ ^ (j - i - 1)
      ≤ ∑ _j ∈ Finset.range n, (1 - ϑ)⁻¹ := by
        apply Finset.sum_le_sum
        intro j _
        have : ∑ i ∈ Finset.range j, ϑ ^ (j - i - 1) = ∑ i ∈ Finset.range j, ϑ ^ (j - 1 - i) :=
          Finset.sum_congr rfl fun i hi => by congr 1; omega
        rw [this]; exact geom_reflect_le h0 h1 j
    _ = n * (1 - ϑ)⁻¹ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem dsum_end_le (n : ℕ) :
    ∑ j ∈ Finset.range n, ∑ _i ∈ Finset.range j, ϑ ^ (n - j - 1) ≤ n * (1 - ϑ)⁻¹ := by
  calc ∑ j ∈ Finset.range n, ∑ _i ∈ Finset.range j, ϑ ^ (n - j - 1)
      ≤ ∑ j ∈ Finset.range n, n * ϑ ^ (n - 1 - j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          show n - j - 1 = n - 1 - j by omega]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.1 hj).le)
          (pow_nonneg h0 _)
    _ = n * ∑ j ∈ Finset.range n, ϑ ^ (n - 1 - j) := by rw [Finset.mul_sum]
    _ ≤ n * (1 - ϑ)⁻¹ := mul_le_mul_of_nonneg_left (geom_reflect_le h0 h1 n) (Nat.cast_nonneg n)

theorem dsum_start_gap_le (n : ℕ) :
    ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, ϑ ^ (i - 1) * ϑ ^ (j - i - 1) ≤
      (1 + (1 - ϑ)⁻¹) * (1 - ϑ)⁻¹ := by
  rw [Finset.sum_comm' (t' := Finset.range n) (s' := fun i => Finset.Ioo i n)]
  · calc ∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ioo i n, ϑ ^ (i - 1) * ϑ ^ (j - i - 1)
        ≤ ∑ i ∈ Finset.range n, ϑ ^ (i - 1) * (1 - ϑ)⁻¹ := by
          apply Finset.sum_le_sum
          intro i _
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg h0 _)
          have : ∑ j ∈ Finset.Ioo i n, ϑ ^ (j - i - 1) = ∑ k ∈ Finset.range (n - i - 1), ϑ ^ k := by
            have hI : Finset.Ioo i n = Finset.Ico (i + 1) n := by
              ext k; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
            rw [hI, Finset.sum_Ico_eq_sum_range, show n - (i + 1) = n - i - 1 by omega]
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            omega
          rw [this]; exact geom_le h0 h1 _
      _ = (∑ i ∈ Finset.range n, ϑ ^ (i - 1)) * (1 - ϑ)⁻¹ := by rw [Finset.sum_mul]
      _ ≤ (1 + (1 - ϑ)⁻¹) * (1 - ϑ)⁻¹ :=
          mul_le_mul_of_nonneg_right (geom_pred_le h0 h1 n) (inv_nonneg.2 (sub_pos.2 h1).le)
  · intro j i
    simp only [Finset.mem_range, Finset.mem_Ioo]
    omega

theorem dsum_start_end_le (n : ℕ) :
    ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, ϑ ^ (i - 1) * ϑ ^ (n - j - 1) ≤
      (1 + (1 - ϑ)⁻¹) * (1 - ϑ)⁻¹ := by
  calc ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, ϑ ^ (i - 1) * ϑ ^ (n - j - 1)
      ≤ ∑ j ∈ Finset.range n, (1 + (1 - ϑ)⁻¹) * ϑ ^ (n - 1 - j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← Finset.sum_mul, show n - j - 1 = n - 1 - j by omega]
        exact mul_le_mul_of_nonneg_right (geom_pred_le h0 h1 j) (pow_nonneg h0 _)
    _ = (1 + (1 - ϑ)⁻¹) * ∑ j ∈ Finset.range n, ϑ ^ (n - 1 - j) := by rw [Finset.mul_sum]
    _ ≤ (1 + (1 - ϑ)⁻¹) * (1 - ϑ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left (geom_reflect_le h0 h1 n)
        have := inv_nonneg.2 (sub_pos.2 h1).le
        linarith

end Sums

/-! ### Cauchy–Schwarz for bounded functions -/

section CauchySchwarz

variable {X : Type*} [MeasurableSpace X]

theorem sq_integral_mul_le {ν : Measure X} [IsFiniteMeasure ν] {u v : X → ℝ}
    (hu : Measurable u) (hv : Measurable v) {U V : ℝ} (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    (∫ x, u x * v x ∂ν) ^ 2 ≤ (∫ x, u x ^ 2 ∂ν) * ∫ x, v x ^ 2 ∂ν := by
  have hb {f : X → ℝ} (hf : Measurable f) {F : ℝ} (hF : ∀ x, |f x| ≤ F) : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable F (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hF x)
  have hU0 : ∀ x, |u x ^ 2| ≤ U ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hU x) 2
  have hV0 : ∀ x, |v x ^ 2| ≤ V ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hV x) 2
  have hUV : ∀ x, |u x * v x| ≤ U * V := fun x => by
    rw [abs_mul]; exact mul_le_mul (hU x) (hV x) (abs_nonneg _) ((abs_nonneg _).trans (hU x))
  have hu2 := hb (hu.pow_const 2) hU0
  have hv2 := hb (hv.pow_const 2) hV0
  have huv := hb (hu.mul hv) hUV
  have hq : ∀ t : ℝ, 0 ≤ (∫ x, v x ^ 2 ∂ν) * (t * t) + (-2 * ∫ x, u x * v x ∂ν) * t +
      ∫ x, u x ^ 2 ∂ν := by
    intro t
    have h0 : 0 ≤ ∫ x, (u x - t * v x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have hexp : (fun x => (u x - t * v x) ^ 2) =
        fun x => u x ^ 2 + ((-2 * t) * (u x * v x) + (t * t) * v x ^ 2) := by
      funext x; ring
    have i1 : Integrable (fun x => (-2 * t) * (u x * v x)) ν := huv.const_mul _
    have i2 : Integrable (fun x => (t * t) * v x ^ 2) ν := hv2.const_mul _
    have i12 : Integrable (fun x => (-2 * t) * (u x * v x) + (t * t) * v x ^ 2) ν := i1.add i2
    rw [hexp, integral_add hu2 i12, integral_add i1 i2, integral_const_mul,
      integral_const_mul] at h0
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

end CauchySchwarz

/-! ### Kernel powers: constants, invariance, decay -/

section KernelFacts

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

theorem kpow_const_mul (k : ℕ) (c : ℝ) (f : M → ℝ) (y : M) :
    kpow C k (fun z => c * f z) y = c * kpow C k f y := integral_const_mul c _

theorem kpow_sub (k : ℕ) {f₁ f₂ : M → ℝ} (h₁ : Measurable f₁) (h₂ : Measurable f₂) {B : ℝ}
    (hb₁ : ∀ y, |f₁ y| ≤ B) (hb₂ : ∀ y, |f₂ y| ≤ B) (y : M) :
    kpow C k (fun z => f₁ z - f₂ z) y = kpow C k f₁ y - kpow C k f₂ y := by
  have : IsFiniteKernel (C.killedTransition ^ k) := killedKernel_power_isFinite C.toKilledKernel k
  unfold kpow
  exact integral_sub (Integrable.of_bound h₁.aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb₁ z))
    (Integrable.of_bound h₂.aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb₂ z))

theorem kpow_add (k : ℕ) {f₁ f₂ : M → ℝ} (h₁ : Measurable f₁) (h₂ : Measurable f₂) {B : ℝ}
    (hb₁ : ∀ y, |f₁ y| ≤ B) (hb₂ : ∀ y, |f₂ y| ≤ B) (y : M) :
    kpow C k (fun z => f₁ z + f₂ z) y = kpow C k f₁ y + kpow C k f₂ y := by
  have : IsFiniteKernel (C.killedTransition ^ k) := killedKernel_power_isFinite C.toKilledKernel k
  unfold kpow
  exact integral_add (Integrable.of_bound h₁.aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb₁ z))
    (Integrable.of_bound h₂.aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb₂ z))

theorem kpow_mono (k : ℕ) {f₁ f₂ : M → ℝ} (h₁ : Measurable f₁) (h₂ : Measurable f₂) {B : ℝ}
    (hb₁ : ∀ y, |f₁ y| ≤ B) (hb₂ : ∀ y, |f₂ y| ≤ B) (hle : ∀ y, f₁ y ≤ f₂ y) (y : M) :
    kpow C k f₁ y ≤ kpow C k f₂ y := by
  have : IsFiniteKernel (C.killedTransition ^ k) := killedKernel_power_isFinite C.toKilledKernel k
  unfold kpow
  exact integral_mono (Integrable.of_bound h₁.aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb₁ z))
    (Integrable.of_bound h₂.aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb₂ z)) hle

theorem kpow_nonneg (k : ℕ) {f : M → ℝ} (hf : ∀ y, 0 ≤ f y) (y : M) : 0 ≤ kpow C k f y :=
  integral_nonneg hf

/-- Kernel Cauchy–Schwarz: `(Tᵏ|F|)² ≤ Tᵏ1 · Tᵏ(F²)`. -/
theorem kpow_abs_sq_le (k : ℕ) {F : M → ℝ} (hF : Measurable F) {B : ℝ} (hB : ∀ y, |F y| ≤ B)
    (y : M) : kpow C k (fun z => |F z|) y ^ 2 ≤
      kpow C k (fun _ => 1) y * kpow C k (fun z => F z ^ 2) y := by
  have : IsFiniteKernel (C.killedTransition ^ k) := killedKernel_power_isFinite C.toKilledKernel k
  have := sq_integral_mul_le (ν := (C.killedTransition ^ k) y) (u := fun z => |F z|)
    (v := fun _ => 1) (continuous_abs.measurable.comp hF) measurable_const
    (U := B) (V := 1) (fun x => by simp only [abs_abs]; exact hB x) (fun _ => by simp)
  simp only [mul_one, one_pow, sq_abs] at this
  unfold kpow
  rw [mul_comm]
  exact this

end KernelFacts

/-! ### Normalized kernel powers and the analytic input -/

section Normalized

variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)

/-- The normalized iterate `P̂ᵏ F = r⁻ᵏ Tᵏ F`. -/
def nkp (r : ℝ) (k : ℕ) (F : M → ℝ) (y : M) : ℝ := r⁻¹ ^ k * kpow C k F y

theorem measurable_nkp (r : ℝ) (k : ℕ) {F : M → ℝ} (hF : Measurable F) :
    Measurable (nkp C r k F) :=
  measurable_const.mul (measurable_kpow C k hF)

theorem nkp_zero (r : ℝ) {F : M → ℝ} (hF : Measurable F) (y : M) : nkp C r 0 F y = F y := by
  simp [nkp, kpow_zero C F hF]

theorem nkp_nonneg {r : ℝ} (hr : 0 ≤ r) (k : ℕ) {F : M → ℝ} (hF : ∀ y, 0 ≤ F y) (y : M) :
    0 ≤ nkp C r k F y :=
  mul_nonneg (pow_nonneg (inv_nonneg.2 hr) _) (kpow_nonneg C k hF y)

theorem kpow_mul_smul (k : ℕ) (c : ℝ) (g f : M → ℝ) (y : M) :
    kpow C k (fun z => g z * (c * f z)) y = c * kpow C k (fun z => g z * f z) y := by
  unfold kpow
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

theorem nkp_pair (r : ℝ) (g : M → ℝ) {i j n : ℕ} (hij : i < j) (hjn : j < n) (x : M) :
    r⁻¹ ^ n * kpow C i (fun y => g y * kpow C (j - i)
        (fun z => g z * kpow C (n - j) (fun _ => 1) z) y) x =
      nkp C r i (fun y => g y * nkp C r (j - i)
        (fun z => g z * nkp C r (n - j) (fun _ => 1) z) y) x := by
  unfold nkp
  simp_rw [kpow_mul_smul]
  rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, show i + (j - i) + (n - j) = n by omega]

theorem nkp_diag (r : ℝ) (g : M → ℝ) {i n : ℕ} (hin : i < n) (x : M) :
    r⁻¹ ^ n * kpow C i (fun y => g y * g y * kpow C (n - i) (fun _ => 1) y) x =
      nkp C r i (fun y => g y * g y * nkp C r (n - i) (fun _ => 1) y) x := by
  unfold nkp
  rw [kpow_mul_smul C i _ (fun y => g y * g y), ← mul_assoc, ← pow_add,
    show i + (n - i) = n by omega]

theorem nkp_add (r : ℝ) (k : ℕ) {f₁ f₂ : M → ℝ} (h₁ : Measurable f₁) (h₂ : Measurable f₂)
    {B : ℝ} (hb₁ : ∀ y, |f₁ y| ≤ B) (hb₂ : ∀ y, |f₂ y| ≤ B) (y : M) :
    nkp C r k (fun z => f₁ z + f₂ z) y = nkp C r k f₁ y + nkp C r k f₂ y := by
  unfold nkp
  rw [kpow_add C k h₁ h₂ hb₁ hb₂, mul_add]

theorem abs_kpow_le_kpow_abs (k : ℕ) (F : M → ℝ) (y : M) :
    |kpow C k F y| ≤ kpow C k (fun z => |F z|) y :=
  abs_integral_le_integral_abs

theorem kpow_const (k : ℕ) (B : ℝ) (y : M) :
    kpow C k (fun _ => B) y = B * kpow C k (fun _ => 1) y := by
  simpa using kpow_const_mul C k B (fun _ => 1) y

/-- The `L^∞` analytic input: a normalizing rate, the eigenfunction, bounds for
normalized survival masses, pointwise decay of centred iterates and invariance
of `μ`. -/
structure Data0 (μ : Measure M) where
  r : ℝ
  r_pos : 0 < r
  η : M → ℝ
  measurable_η : Measurable η
  Bη : ℝ
  η_nonneg : ∀ y, 0 ≤ η y
  η_le : ∀ y, η y ≤ Bη
  E : ℝ
  one_le_E : 1 ≤ E
  mass_le : ∀ k y, nkp C r k (fun _ => 1) y ≤ E
  S : ℝ
  S_nonneg : 0 ≤ S
  θ : ℝ
  θ_nonneg : 0 ≤ θ
  θ_lt_one : θ < 1
  mass_sub : ∀ l y, 1 ≤ l → |nkp C r l (fun _ => 1) y - η y| ≤ S * θ ^ (l - 1)
  A : ℝ
  A_nonneg : 0 ≤ A
  decay : ∀ F : M → ℝ, Measurable F → ∀ B : ℝ, (∀ y, |F y| ≤ B) → ∀ (k : ℕ) (z : M),
    |nkp C r (k + 1) F z - (∫ y, F y ∂μ) * η z| ≤ A * θ ^ k * B
  invariant : ∀ (k : ℕ) (F : M → ℝ), Measurable F → ∀ B : ℝ, (∀ y, |F y| ≤ B) →
    ∫ y, nkp C r k F y ∂μ = ∫ y, F y ∂μ

/-- The analytic input for the second-moment estimate: `Data0` together with
the `L²(μ)` decay of centred iterates. -/
structure Data (μ : Measure M) extends Data0 C μ where
  L : ℝ
  L_nonneg : 0 ≤ L
  l2 : ∀ F : M → ℝ, Measurable F → ∀ B : ℝ, (∀ y, |F y| ≤ B) → ∫ y, F y ∂μ = 0 →
    ∀ m : ℕ, 1 ≤ m → ∫ y, nkp C r m F y ^ 2 ∂μ ≤ (L * θ ^ m) ^ 2 * ∫ y, F y ^ 2 ∂μ

theorem integrable_of_bdd {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

theorem abs_integral_le_of_prob {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {f : X → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂ν| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (C := B)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  simpa [Real.norm_eq_abs] using this

/-- Cauchy–Schwarz in the form used below: `μ(v²) ≤ c² μ(u²)` gives
`|μ(uv)| ≤ c μ(u²)`. -/
theorem abs_integral_mul_le {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {u v : X → ℝ} (hu : Measurable u) (hv : Measurable v) {U V : ℝ} (hU : ∀ x, |u x| ≤ U)
    (hV : ∀ x, |v x| ≤ V) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫ x, v x ^ 2 ∂ν ≤ c ^ 2 * ∫ x, u x ^ 2 ∂ν) :
    |∫ x, u x * v x ∂ν| ≤ c * ∫ x, u x ^ 2 ∂ν := by
  have hcs := sq_integral_mul_le (ν := ν) hu hv hU hV
  have hu0 : 0 ≤ ∫ x, u x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have : (∫ x, u x * v x ∂ν) ^ 2 ≤ (c * ∫ x, u x ^ 2 ∂ν) ^ 2 := by
    calc _ ≤ _ := hcs
      _ ≤ (∫ x, u x ^ 2 ∂ν) * (c ^ 2 * ∫ x, u x ^ 2 ∂ν) := mul_le_mul_of_nonneg_left h hu0
      _ = _ := by ring
  have := sq_le_sq.1 this
  rwa [abs_of_nonneg (mul_nonneg hc hu0)] at this

theorem four_le {a₁ a₂ a₃ a₄ X Y Z W : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃)
    (h₄ : 0 ≤ a₄) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hW : 0 ≤ W) :
    a₁ * X + a₂ * Y + a₃ * Z + a₄ * W ≤ (a₁ + a₂ + a₃ + a₄) * (X + Y + Z + W) := by
  nlinarith [mul_nonneg h₁ hY, mul_nonneg h₁ hZ, mul_nonneg h₁ hW, mul_nonneg h₂ hX,
    mul_nonneg h₂ hZ, mul_nonneg h₂ hW, mul_nonneg h₃ hX, mul_nonneg h₃ hY, mul_nonneg h₃ hW,
    mul_nonneg h₄ hX, mul_nonneg h₄ hY, mul_nonneg h₄ hZ]

theorem sq_bdd {X : Type*} {f : X → ℝ} {B : ℝ} (h : ∀ x, |f x| ≤ B) (x : X) :
    |f x ^ 2| ≤ B ^ 2 := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h x) 2

theorem sq_le_of_abs {X : Type*} {f : X → ℝ} {B : ℝ} (h : ∀ x, |f x| ≤ B) (x : X) :
    f x ^ 2 ≤ B ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h x) 2

namespace Data0

variable {C} {μ : Measure M} (D : Data0 C μ)

theorem E_nonneg : 0 ≤ D.E := zero_le_one.trans D.one_le_E

theorem Bη_nonneg [Nonempty M] : 0 ≤ D.Bη :=
  (D.η_nonneg (Classical.arbitrary M)).trans (D.η_le _)

theorem nkp_abs_le (k : ℕ) {F : M → ℝ} (hF : Measurable F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y, |F y| ≤ B) (y : M) : |nkp C D.r k F y| ≤ D.E * B := by
  have hr := (pow_pos (inv_pos.2 D.r_pos) k)
  unfold nkp
  rw [abs_mul, abs_of_pos hr]
  calc D.r⁻¹ ^ k * |kpow C k F y| ≤ D.r⁻¹ ^ k * kpow C k (fun _ => B) y := by
        refine mul_le_mul_of_nonneg_left ((abs_kpow_le_kpow_abs C k F y).trans ?_) hr.le
        exact kpow_mono C k (f₁ := fun z => |F z|) (continuous_abs.measurable.comp hF) measurable_const
          (fun z => by rw [abs_abs]; exact hB z) (fun _ => by rw [abs_of_nonneg hB0]) hB y
    _ = B * nkp C D.r k (fun _ => 1) y := by rw [kpow_const, nkp]; ring
    _ ≤ B * D.E := mul_le_mul_of_nonneg_left (D.mass_le k y) hB0
    _ = D.E * B := mul_comm _ _

theorem nkp_sq_le (k : ℕ) {F : M → ℝ} (hF : Measurable F) {B : ℝ} (hB : ∀ y, |F y| ≤ B)
    (y : M) : nkp C D.r k F y ^ 2 ≤ D.E * nkp C D.r k (fun z => F z ^ 2) y := by
  have hr := (pow_pos (inv_pos.2 D.r_pos) k)
  have h1 : kpow C k F y ^ 2 ≤ kpow C k (fun z => |F z|) y ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_kpow_le_kpow_abs C k F y) 2
  have h2 := kpow_abs_sq_le C k hF hB y
  have h3 : 0 ≤ nkp C D.r k (fun z => F z ^ 2) y :=
    nkp_nonneg C D.r_pos.le k (fun z => sq_nonneg _) y
  calc nkp C D.r k F y ^ 2 = (D.r⁻¹ ^ k) ^ 2 * kpow C k F y ^ 2 := by rw [nkp]; ring
    _ ≤ (D.r⁻¹ ^ k) ^ 2 * (kpow C k (fun _ => 1) y * kpow C k (fun z => F z ^ 2) y) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg _)
    _ = nkp C D.r k (fun _ => 1) y * nkp C D.r k (fun z => F z ^ 2) y := by
        simp only [nkp]; ring
    _ ≤ D.E * nkp C D.r k (fun z => F z ^ 2) y := mul_le_mul_of_nonneg_right (D.mass_le k y) h3

end Data0

namespace Data

variable {C} {μ : Measure M} (D : Data C μ)

section Bounds

variable [IsProbabilityMeasure μ]

/-- Constant in the pair estimate. -/
def pairConst : ℝ :=
  D.Bη * (D.L * D.Bη) + D.Bη * (D.E * D.S) + (D.A + 1) * (D.S * D.Bη) + (D.A + 1) * (D.A * D.E)

/-- Constant in the diagonal estimate. -/
def diagConst : ℝ := D.Bη * D.E + (D.A + 1) * D.E

omit [IsProbabilityMeasure μ] in
theorem pairConst_nonneg [Nonempty M] : 0 ≤ D.pairConst := by
  have := D.Bη_nonneg; have := D.E_nonneg; have := D.S_nonneg; have := D.A_nonneg
  have := D.L_nonneg
  unfold pairConst; positivity

omit [IsProbabilityMeasure μ] in
theorem diagConst_nonneg [Nonempty M] : 0 ≤ D.diagConst := by
  have := D.Bη_nonneg; have := D.E_nonneg; have := D.A_nonneg
  unfold diagConst; positivity

/-- The normalized pair word `P̂ⁱ(g P̂ᵐ(g P̂ˡ1))` for `m, l ≥ 1` and `ν(g) = 0`. -/
theorem pair_bound [Nonempty M] {g : M → ℝ} (hg : Measurable g) {G : ℝ} (hG0 : 0 ≤ G)
    (hgG : ∀ y, |g y| ≤ G) (hgη : ∫ y, g y * D.η y ∂μ = 0) (i : ℕ) {m l : ℕ} (hm : 1 ≤ m)
    (hl : 1 ≤ l) (x : M) :
    |nkp C D.r i (fun y => g y * nkp C D.r m (fun z => g z * nkp C D.r l (fun _ => 1) z) y) x| ≤
      D.pairConst * ((∫ y, g y ^ 2 ∂μ) * (D.θ ^ (m - 1) + D.θ ^ (l - 1)) +
        G ^ 2 * D.θ ^ (i - 1) * (D.θ ^ (m - 1) + D.θ ^ (l - 1))) := by
  have hBη := D.Bη_nonneg
  have hE := D.E_nonneg
  have hS := D.S_nonneg
  have hA := D.A_nonneg
  have hL := D.L_nonneg
  have hθ0 := D.θ_nonneg
  set e := nkp C D.r l (fun _ => 1) with he_def
  have he_meas : Measurable e := measurable_nkp C _ l measurable_const
  have he0 : ∀ y, 0 ≤ e y := fun y => nkp_nonneg C D.r_pos.le l (fun _ => zero_le_one) y
  have heE : ∀ y, |e y| ≤ D.E := fun y => by rw [abs_of_nonneg (he0 y)]; exact D.mass_le l y
  have heη : ∀ y, |e y - D.η y| ≤ D.S * D.θ ^ (l - 1) := fun y => D.mass_sub l y hl
  have hη : ∀ y, |D.η y| ≤ D.Bη := fun y => by
    rw [abs_of_nonneg (D.η_nonneg y)]; exact D.η_le y
  set μg := ∫ y, g y ^ 2 ∂μ with hμg_def
  have hμg : 0 ≤ μg := integral_nonneg fun y => sq_nonneg _
  set tl := D.θ ^ (l - 1) with htl_def
  set tm := D.θ ^ (m - 1) with htm_def
  set ti := D.θ ^ (i - 1) with hti_def
  have htl : 0 ≤ tl := pow_nonneg hθ0 _
  have htm : 0 ≤ tm := pow_nonneg hθ0 _
  have hti : 0 ≤ ti := pow_nonneg hθ0 _
  have htmm : D.θ ^ m ≤ tm := pow_le_pow_of_le_one hθ0 D.θ_lt_one.le (Nat.sub_le m 1)
  have hge : ∀ y, |g y * e y| ≤ G * D.E := fun y => by
    rw [abs_mul]; exact mul_le_mul (hgG y) (heE y) (abs_nonneg _) hG0
  have hgη' : ∀ y, |g y * D.η y| ≤ G * D.Bη := fun y => by
    rw [abs_mul]; exact mul_le_mul (hgG y) (hη y) (abs_nonneg _) hG0
  have hgeη : ∀ y, |g y * (e y - D.η y)| ≤ G * (D.S * tl) := fun y => by
    rw [abs_mul]; exact mul_le_mul (hgG y) (heη y) (abs_nonneg _) hG0
  have hηm : Measurable fun z => g z * D.η z := hg.mul D.measurable_η
  have heηm : Measurable fun z => g z * (e z - D.η z) := hg.mul (he_meas.sub D.measurable_η)
  -- The mean of `g e` is small since `ν(g) = μ(g η) = 0`.
  have hμw : |∫ y, g y * e y ∂μ| ≤ G * (D.S * tl) := by
    have : ∫ y, g y * e y ∂μ = ∫ y, g y * (e y - D.η y) ∂μ + ∫ y, g y * D.η y ∂μ := by
      rw [← integral_add (integrable_of_bdd heηm hgeη) (integrable_of_bdd hηm hgη')]
      congr 1; funext y; ring
    rw [this, hgη, add_zero]
    exact abs_integral_le_of_prob hgeη
  -- Sup bound for `H = P̂ᵐ(g e)`.
  set H := nkp C D.r m (fun z => g z * e z) with hH_def
  have hH_meas : Measurable H := measurable_nkp C _ m (hg.mul he_meas)
  set Hs := D.S * D.Bη * tl + D.A * D.E * tm with hHs_def
  have hHs : 0 ≤ Hs := by positivity
  have hH : ∀ z, |H z| ≤ G * Hs := by
    intro z
    have h1 := D.decay _ (hg.mul he_meas) _ hge (m - 1) z
    rw [Nat.sub_add_cancel hm] at h1
    have h2 : |(∫ y, g y * e y ∂μ) * D.η z| ≤ G * (D.S * tl) * D.Bη := by
      rw [abs_mul]; exact mul_le_mul hμw (hη z) (abs_nonneg _) (by positivity)
    have h3 := abs_add_le (H z - (∫ y, g y * e y ∂μ) * D.η z) ((∫ y, g y * e y ∂μ) * D.η z)
    rw [sub_add_cancel] at h3
    calc |H z| ≤ _ := h3
      _ ≤ D.A * tm * (G * D.E) + G * (D.S * tl) * D.Bη := add_le_add h1 h2
      _ = G * Hs := by rw [hHs_def]; ring
  -- Splitting `H` along `e = η + (e - η)`.
  have hB1 : ∀ y, |g y * D.η y| ≤ G * D.Bη + G * (D.S * tl) := fun y =>
    (hgη' y).trans (le_add_of_nonneg_right (by positivity))
  have hB2 : ∀ y, |g y * (e y - D.η y)| ≤ G * D.Bη + G * (D.S * tl) := fun y =>
    (hgeη y).trans (le_add_of_nonneg_left (by positivity))
  have hsplit : ∀ z, H z = nkp C D.r m (fun z => g z * D.η z) z +
      nkp C D.r m (fun z => g z * (e z - D.η z)) z := by
    intro z
    rw [← nkp_add C D.r m hηm heηm hB1 hB2, hH_def]
    congr 2; funext y; ring
  have hv1 : ∀ y, |nkp C D.r m (fun z => g z * D.η z) y| ≤ D.E * (G * D.Bη) :=
    D.nkp_abs_le m hηm (by positivity) hgη'
  have hv2 : ∀ y, |nkp C D.r m (fun z => g z * (e z - D.η z)) y| ≤ D.E * (G * (D.S * tl)) :=
    D.nkp_abs_le m heηm (by positivity) hgeη
  -- The centred part decays in `L²(μ)`.
  have ha : |∫ y, g y * nkp C D.r m (fun z => g z * D.η z) y ∂μ| ≤
      (D.L * D.θ ^ m * D.Bη) * μg := by
    refine abs_integral_mul_le hg (measurable_nkp C _ m hηm) hgG hv1 (by positivity) ?_
    have h1 := D.l2 _ hηm _ hgη' hgη m hm
    have h2 : ∫ y, (g y * D.η y) ^ 2 ∂μ ≤ D.Bη ^ 2 * μg := by
      rw [hμg_def, ← integral_const_mul]
      refine integral_mono (integrable_of_bdd (hηm.pow_const 2) (sq_bdd hgη'))
        (integrable_of_bdd ((hg.pow_const 2).const_mul _) (B := D.Bη ^ 2 * G ^ 2) ?_) (fun y => ?_)
      · intro y
        rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (sq_le_of_abs hgG y) (sq_nonneg _)
      · beta_reduce
        calc (g y * D.η y) ^ 2 = D.η y ^ 2 * g y ^ 2 := by ring
          _ ≤ D.Bη ^ 2 * g y ^ 2 := mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (D.η_nonneg y) (D.η_le y) 2) (sq_nonneg _)
    calc _ ≤ _ := h1
      _ ≤ (D.L * D.θ ^ m) ^ 2 * (D.Bη ^ 2 * μg) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  -- The remainder part is small by the survival estimate, Cauchy–Schwarz and invariance.
  have hb : |∫ y, g y * nkp C D.r m (fun z => g z * (e z - D.η z)) y ∂μ| ≤
      (D.E * (D.S * tl)) * μg := by
    refine abs_integral_mul_le hg (measurable_nkp C _ m heηm) hgG hv2 (by positivity) ?_
    have hsq : ∀ y, |(g y * (e y - D.η y)) ^ 2| ≤ (G * (D.S * tl)) ^ 2 := sq_bdd hgeη
    have h1 : ∫ y, nkp C D.r m (fun z => g z * (e z - D.η z)) y ^ 2 ∂μ ≤
        ∫ y, D.E * nkp C D.r m (fun z => (g z * (e z - D.η z)) ^ 2) y ∂μ :=
      integral_mono (integrable_of_bdd ((measurable_nkp C _ m heηm).pow_const 2) (sq_bdd hv2))
        (integrable_of_bdd ((measurable_nkp C _ m (heηm.pow_const 2)).const_mul _)
          (B := D.E * (D.E * (G * (D.S * tl)) ^ 2)) (fun y => by
            rw [abs_mul, abs_of_nonneg hE]
            exact mul_le_mul_of_nonneg_left
              (D.nkp_abs_le m (heηm.pow_const 2) (sq_nonneg _) hsq y) hE))
        (fun y => D.nkp_sq_le m heηm hgeη y)
    rw [integral_const_mul, D.invariant m _ (heηm.pow_const 2) _ hsq] at h1
    have h2 : ∫ y, (g y * (e y - D.η y)) ^ 2 ∂μ ≤ (D.S * tl) ^ 2 * μg := by
      rw [hμg_def, ← integral_const_mul]
      refine integral_mono (integrable_of_bdd (heηm.pow_const 2) hsq)
        (integrable_of_bdd ((hg.pow_const 2).const_mul _) (B := (D.S * tl) ^ 2 * G ^ 2)
          (fun y => by
            rw [abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (sq_le_of_abs hgG y) (sq_nonneg _))) (fun y => ?_)
      beta_reduce
      calc (g y * (e y - D.η y)) ^ 2 = (e y - D.η y) ^ 2 * g y ^ 2 := by ring
        _ ≤ (D.S * tl) ^ 2 * g y ^ 2 :=
            mul_le_mul_of_nonneg_right (sq_le_of_abs heη y) (sq_nonneg _)
    calc _ ≤ _ := h1
      _ ≤ D.E * ((D.S * tl) ^ 2 * μg) := mul_le_mul_of_nonneg_left h2 hE
      _ ≤ D.E ^ 2 * ((D.S * tl) ^ 2 * μg) :=
          mul_le_mul_of_nonneg_right (by nlinarith [D.one_le_E]) (by positivity)
      _ = _ := by ring
  -- The mean of `g H`.
  have hgH : |∫ y, g y * H y ∂μ| ≤ (D.L * D.θ ^ m * D.Bη + D.E * (D.S * tl)) * μg := by
    have : ∫ y, g y * H y ∂μ = ∫ y, g y * nkp C D.r m (fun z => g z * D.η z) y ∂μ +
        ∫ y, g y * nkp C D.r m (fun z => g z * (e z - D.η z)) y ∂μ := by
      have m1 : Measurable fun y => g y * nkp C D.r m (fun z => g z * D.η z) y :=
        hg.mul (measurable_nkp C _ m hηm)
      have m2 : Measurable fun y => g y * nkp C D.r m (fun z => g z * (e z - D.η z)) y :=
        hg.mul (measurable_nkp C _ m heηm)
      rw [← integral_add (integrable_of_bdd m1 (fun y => by
          rw [abs_mul]; exact mul_le_mul (hgG y) (hv1 y) (abs_nonneg _) hG0))
        (integrable_of_bdd m2 (fun y => by
          rw [abs_mul]; exact mul_le_mul (hgG y) (hv2 y) (abs_nonneg _) hG0))]
      congr 1; funext y; rw [hsplit y, mul_add]
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [add_mul]; exact add_le_add ha hb
  -- The outer iterate.
  have hgHm : Measurable fun y => g y * H y := hg.mul hH_meas
  have hgHb : ∀ y, |g y * H y| ≤ G * (G * Hs) := fun y => by
    rw [abs_mul]; exact mul_le_mul (hgG y) (hH y) (abs_nonneg _) hG0
  have hT : |nkp C D.r i (fun y => g y * H y) x| ≤
      D.Bη * |∫ y, g y * H y ∂μ| + (D.A + 1) * ti * (G ^ 2 * Hs) := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · rw [hi, nkp_zero C _ hgHm]
      have : ti = 1 := by rw [hti_def, hi]; simp
      rw [this]
      calc _ ≤ G * (G * Hs) := hgHb x
        _ ≤ _ := by
          nlinarith [mul_nonneg hBη (abs_nonneg (∫ y, g y * H y ∂μ)),
            mul_nonneg hA (mul_nonneg (sq_nonneg G) hHs)]
    · have h1 := D.decay _ hgHm _ hgHb (i - 1) x
      rw [Nat.sub_add_cancel hi] at h1
      have h2 : |(∫ y, g y * H y ∂μ) * D.η x| ≤ D.Bη * |∫ y, g y * H y ∂μ| := by
        rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hη x) (abs_nonneg _)
      have h3 := abs_add_le (nkp C D.r i (fun y => g y * H y) x -
        (∫ y, g y * H y ∂μ) * D.η x) ((∫ y, g y * H y ∂μ) * D.η x)
      rw [sub_add_cancel] at h3
      calc _ ≤ _ := h3
        _ ≤ D.A * ti * (G * (G * Hs)) + D.Bη * |∫ y, g y * H y ∂μ| := add_le_add h1 h2
        _ ≤ _ := by nlinarith [mul_nonneg hti (mul_nonneg (sq_nonneg G) hHs)]
  refine hT.trans ?_
  have hμgH := mul_le_mul_of_nonneg_left hgH hBη
  have hmm : D.Bη * (D.L * D.Bη) * (μg * D.θ ^ m) ≤ D.Bη * (D.L * D.Bη) * (μg * tm) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htmm hμg) (by positivity)
  calc D.Bη * |∫ y, g y * H y ∂μ| + (D.A + 1) * ti * (G ^ 2 * Hs)
      ≤ D.Bη * (D.L * D.Bη) * (μg * tm) + D.Bη * (D.E * D.S) * (μg * tl) +
          (D.A + 1) * (D.S * D.Bη) * (G ^ 2 * ti * tl) +
          (D.A + 1) * (D.A * D.E) * (G ^ 2 * ti * tm) := by
        rw [hHs_def]; nlinarith [hμgH, hmm]
    _ ≤ D.pairConst * (μg * tm + μg * tl + G ^ 2 * ti * tl + G ^ 2 * ti * tm) :=
        four_le (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
          (by positivity) (by positivity) (by positivity)
    _ = _ := by ring

/-- The normalized diagonal word `P̂ⁱ(g² P̂ˡ1)` for `l ≥ 1`. -/
theorem diag_bound [Nonempty M] {g : M → ℝ} (hg : Measurable g) {G : ℝ} (_hG0 : 0 ≤ G)
    (hgG : ∀ y, |g y| ≤ G) (i : ℕ) {l : ℕ} (x : M) :
    |nkp C D.r i (fun y => g y * g y * nkp C D.r l (fun _ => 1) y) x| ≤
      D.diagConst * ((∫ y, g y ^ 2 ∂μ) + G ^ 2 * D.θ ^ (i - 1)) := by
  have hBη := D.Bη_nonneg
  have hE := D.E_nonneg
  have hA := D.A_nonneg
  set e := nkp C D.r l (fun _ => 1) with he_def
  have he_meas : Measurable e := measurable_nkp C _ l measurable_const
  have he0 : ∀ y, 0 ≤ e y := fun y => nkp_nonneg C D.r_pos.le l (fun _ => zero_le_one) y
  have heE : ∀ y, e y ≤ D.E := D.mass_le l
  have hη : ∀ y, |D.η y| ≤ D.Bη := fun y => by
    rw [abs_of_nonneg (D.η_nonneg y)]; exact D.η_le y
  set μg := ∫ y, g y ^ 2 ∂μ with hμg_def
  have hμg : 0 ≤ μg := integral_nonneg fun y => sq_nonneg _
  set ti := D.θ ^ (i - 1) with hti_def
  have hti : 0 ≤ ti := pow_nonneg D.θ_nonneg _
  have hF : Measurable fun y => g y * g y * e y := (hg.mul hg).mul he_meas
  have hFb : ∀ y, |g y * g y * e y| ≤ G ^ 2 * D.E := fun y => by
    rw [abs_of_nonneg (mul_nonneg (mul_self_nonneg _) (he0 y))]
    exact mul_le_mul (by rw [← sq]; exact sq_le_of_abs hgG y) (heE y) (he0 y) (sq_nonneg _)
  have hmean : |∫ y, g y * g y * e y ∂μ| ≤ D.E * μg := by
    rw [abs_of_nonneg (integral_nonneg fun y => mul_nonneg (mul_self_nonneg _) (he0 y)),
      hμg_def, ← integral_const_mul]
    refine integral_mono (integrable_of_bdd hF hFb)
      (integrable_of_bdd ((hg.pow_const 2).const_mul _) (B := D.E * G ^ 2) ?_) (fun y => ?_)
    · intro y
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (sq_le_of_abs hgG y) hE
    · beta_reduce
      rw [← sq, mul_comm]
      exact mul_le_mul_of_nonneg_right (heE y) (sq_nonneg _)
  rcases Nat.eq_zero_or_pos i with hi | hi
  · rw [hi, nkp_zero C _ hF]
    have : ti = 1 := by rw [hti_def, hi]; simp
    rw [this]
    calc _ ≤ G ^ 2 * D.E := hFb x
      _ ≤ _ := by
        unfold diagConst
        nlinarith [mul_nonneg (mul_nonneg hBη hE) hμg, mul_nonneg (mul_nonneg hA hE) (sq_nonneg G),
          mul_nonneg (mul_nonneg hBη hE) (sq_nonneg G), mul_nonneg hE hμg,
          mul_nonneg (mul_nonneg hA hE) hμg]
  · have h1 := D.decay _ hF _ hFb (i - 1) x
    rw [Nat.sub_add_cancel hi] at h1
    have h2 : |(∫ y, g y * g y * e y ∂μ) * D.η x| ≤ D.Bη * (D.E * μg) := by
      rw [abs_mul, mul_comm]; exact mul_le_mul (hη x) hmean (abs_nonneg _) hBη
    have h3 := abs_add_le (nkp C D.r i (fun y => g y * g y * e y) x -
      (∫ y, g y * g y * e y ∂μ) * D.η x) ((∫ y, g y * g y * e y ∂μ) * D.η x)
    rw [sub_add_cancel] at h3
    calc _ ≤ _ := h3
      _ ≤ D.A * ti * (G ^ 2 * D.E) + D.Bη * (D.E * μg) := add_le_add h1 h2
      _ ≤ _ := by
        unfold diagConst
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hBη hE) (sq_nonneg G)) hti,
          mul_nonneg (mul_nonneg hA hE) hμg, mul_nonneg hE hμg,
          mul_nonneg (mul_nonneg hE (sq_nonneg G)) hti]

end Bounds

end Data

end Normalized

/-! ### The analytic input from hypothesis H -/

section FromH

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
theorem norm_sq_L2 {μ : Measure M} (u : Lp ℝ 2 μ) : ‖u‖ ^ 2 = ∫ y, u y ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  congr 1; funext y; simp [sq]

omit [BorelSpace M] in
/-- `Tᵏ η = λᵏ η`. -/
theorem kpow_eigen (d : DoobTransform.EigenData C.killedTransition) (hc : Continuous d.weight)
    (k : ℕ) (y : M) :
    kpow C k (fun z => (d.weight z).toReal) y = d.rate.toReal ^ k * (d.weight y).toReal := by
  obtain ⟨Bη, hBη⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d hc
  have hb : ∀ z, |(d.weight z).toReal| ≤ Bη := fun z => by
    have := hBη z; rw [Real.norm_eq_abs] at this; exact this
  have hm : Measurable fun z => (d.weight z).toReal := d.measurable_weight.ennreal_toReal
  induction k generalizing y with
  | zero => rw [kpow_zero C _ hm]; simp
  | succ k ih =>
    rw [← kpow_succ' C k hm hb]
    have : (fun z => ∫ w, (d.weight w).toReal ∂C.killedTransition z) =
        fun z => d.rate.toReal * (d.weight z).toReal := by
      funext z; exact L2Compactness.kint_eta (K := C.toKilledKernel) d z
    rw [this, kpow_const_mul, ih, pow_succ]; ring

/-- Hypothesis H supplies the `L^∞` analytic input, with `r = λ` and `η` the eigenfunction,
and with decay rate at least any prescribed `κ < 1`. -/
theorem exists_data0 (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (κ : ℝ) (hκ1 : κ < 1) :
    ∃ D : Data0 C μ, D.r = d.rate.toReal ∧ D.η = (fun y => (d.weight y).toReal) ∧ κ ≤ D.θ := by
  have hc := s.continuous_weight
  set r := d.rate.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  obtain ⟨Bη', hBη'⟩ := L2Compactness.exists_eta_bound (K := C.toKilledKernel) d hc
  set Bη := max Bη' 0 with hBη_def
  have hBη0 : 0 ≤ Bη := le_max_right _ _
  have hηb : ∀ y, |(d.weight y).toReal| ≤ Bη := fun y => by
    have := hBη' y; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hηm : Measurable fun y => (d.weight y).toReal := d.measurable_weight.ennreal_toReal
  obtain ⟨A, θ₁, hA, hθ₁0, hθ₁1, hdecay⟩ :=
    h.exists_pointwise_decay (K := C.toKilledKernel) d hc μ hleft hnorm
  set θ := max (max θ₁ s.decay) κ with hθ_def
  have hθ0 : 0 ≤ θ := le_max_of_le_left (le_max_of_le_left hθ₁0)
  have hθ1 : θ < 1 := max_lt (max_lt hθ₁1 s.decay_lt_one) hκ1
  have hθ₁θ : θ₁ ≤ θ := le_max_of_le_left (le_max_left _ _)
  have hdθ : s.decay ≤ θ := le_max_of_le_left (le_max_right _ _)
  have hκθ : κ ≤ θ := le_max_right _ _
  have hinv : ∀ (k : ℕ) (F : M → ℝ), Measurable F → ∀ B : ℝ, (∀ y, |F y| ≤ B) →
      ∫ y, nkp C r k F y ∂μ = ∫ y, F y ∂μ := by
    intro k F hF B hB
    have : IsFiniteKernel (C.killedTransition ^ k) :=
      killedKernel_power_isFinite C.toKilledKernel k
    have h1 := KernelLp.integral_kint (K := C.killedTransition ^ k)
      (RefinedLLN.kernel_pow_comp hleft k) (ENNReal.pow_ne_top d.rate_ne_top)
      (integrable_of_bdd hF hB)
    unfold nkp
    rw [integral_const_mul]
    change r⁻¹ ^ k * ∫ x, KernelLp.kint (C.killedTransition ^ k) F x ∂μ = _
    rw [h1, ENNReal.toReal_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
  refine ⟨
    { r := r
      r_pos := hr
      η := fun y => (d.weight y).toReal
      measurable_η := hηm
      Bη := Bη
      η_nonneg := fun y => ENNReal.toReal_nonneg
      η_le := fun y => (le_abs_self _).trans (hηb y)
      E := max s.survivalBound 1
      one_le_E := le_max_right _ _
      mass_le := ?_
      S := s.survivalConstant
      S_nonneg := s.survivalConstant_nonneg
      θ := θ
      θ_nonneg := hθ0
      θ_lt_one := hθ1
      mass_sub := ?_
      A := A * (1 + Bη)
      A_nonneg := mul_nonneg hA (by linarith)
      decay := ?_
      invariant := hinv }, rfl, rfl, hκθ⟩
  · intro k y
    have := s.normalized_survival_real_le k y
    rw [normalized_survival_toReal (K := C.toKilledKernel) d k y] at this
    simp only [nkp, kpow, integral_const, smul_eq_mul, mul_one]
    exact this.trans (le_max_left _ _)
  · intro l y hl
    have := s.normalized_survival_error (l - 1) y
    rw [Nat.sub_add_cancel hl, normalized_survival_toReal (K := C.toKilledKernel) d l y] at this
    simp only [nkp, kpow, integral_const, smul_eq_mul, mul_one]
    exact this.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ s.decay_nonneg hdθ _)
      s.survivalConstant_nonneg)
  · intro F hF B hB k z
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB z)
    set c := ∫ y, F y ∂μ with hc_def
    have hcB : |c| ≤ B := abs_integral_le_of_prob hB
    have hcm : Measurable fun y => c * (d.weight y).toReal := measurable_const.mul hηm
    have hF'm : Measurable fun y => F y - c * (d.weight y).toReal := hF.sub hcm
    have hcη : ∀ y, |c * (d.weight y).toReal| ≤ B * Bη := fun y => by
      rw [abs_mul]; exact mul_le_mul hcB (hηb y) (abs_nonneg _) hB0
    have hF'b : ∀ y, |F y - c * (d.weight y).toReal| ≤ B * (1 + Bη) := fun y =>
      (abs_sub _ _).trans (by have := hB y; have := hcη y; linarith)
    have hF'0 : ∫ y, (F y - c * (d.weight y).toReal) ∂μ = 0 := by
      rw [integral_sub (integrable_of_bdd hF hB) (integrable_of_bdd hcm hcη),
        integral_const_mul]
      have : ∫ y, (d.weight y).toReal ∂μ = 1 :=
        L2Compactness.integral_eta (K := C.toKilledKernel) d μ hnorm
      rw [this]; ring
    have h1 := hdecay _ hF'm _ hF'b hF'0 k z
    have hb1 : ∀ y, |F y| ≤ B + B * Bη := fun y => (hB y).trans (by nlinarith)
    have hb2 : ∀ y, |c * (d.weight y).toReal| ≤ B + B * Bη := fun y => (hcη y).trans (by linarith)
    have h2 : (d.rate.toReal)⁻¹ ^ (k + 1) * ∫ y, (F y - c * (d.weight y).toReal)
        ∂(C.toKilledKernel.kernel ^ (k + 1)) z = nkp C r (k + 1) F z - c * (d.weight z).toReal := by
      change r⁻¹ ^ (k + 1) * kpow C (k + 1) (fun y => F y - c * (d.weight y).toReal) z = _
      rw [kpow_sub C (k + 1) hF hcm hb1 hb2, kpow_const_mul, kpow_eigen C d hc, mul_sub, nkp]
      congr 1
      rw [inv_pow]
      field_simp
      rw [hr_def]; ring
    rw [h2] at h1
    calc _ ≤ A * θ₁ ^ k * (B * (1 + Bη)) := h1
      _ ≤ A * θ ^ k * (B * (1 + Bη)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ₁0 hθ₁θ k) hA) (by positivity)
      _ = A * (1 + Bη) * θ ^ k * B := by ring

/-- Hypothesis H supplies the analytic input, with `r = λ` and `η` the eigenfunction. -/
theorem exists_data (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) :
    ∃ D : Data C μ, D.r = d.rate.toReal ∧ D.η = fun y => (d.weight y).toReal := by
  have hc := s.continuous_weight
  set r := d.rate.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos d.rate_ne_zero d.rate_ne_top
  obtain ⟨-, -, P₂, R₂, -, hR₂, L, κ, hL, hκ0, hκ1, hdec⟩ :=
    h.l2_extension_decay (K := C.toKilledKernel) d hc μ hleft hnorm
  obtain ⟨D₀, hD₀r, hD₀η, hκθ⟩ := exists_data0 C h d s μ hleft hnorm κ hκ1
  set θ := D₀.θ with hθ_def
  have hinv := D₀.invariant
  rw [hD₀r] at hinv
  refine ⟨{ D₀ with
      L := L
      L_nonneg := hL.le
      l2 := ?_ }, hD₀r, hD₀η⟩
  show ∀ F : M → ℝ, Measurable F → ∀ B : ℝ, (∀ y, |F y| ≤ B) → ∫ y, F y ∂μ = 0 →
    ∀ m : ℕ, 1 ≤ m → ∫ y, nkp C D₀.r m F y ^ 2 ∂μ ≤ (L * θ ^ m) ^ 2 * ∫ y, F y ^ 2 ∂μ
  rw [hD₀r]
  intro F hF B hB hF0 m hm
  have hmem : MemLp F 2 μ := MemLp.of_bound hF.aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  set f := hmem.toLp F with hf_def
  have hae : ∀ k : ℕ, ((R₂ ^ k) f : M → ℝ) =ᵐ[μ] nkp C r k F := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, one_apply_eq_self]
      filter_upwards [hmem.coeFn_toLp] with y hy
      rw [hy, nkp_zero C r hF]
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      filter_upwards [hR₂ ((R₂ ^ k) f), KernelLp.kint_congr hleft ih] with y h1 h2
      rw [h1]
      have h3 : ∫ y, ((R₂ ^ k) f) y ∂μ = 0 := by
        rw [integral_congr_ae ih, hinv k F hF B hB, hF0]
      rw [h3, zero_mul, sub_zero]
      simp only [toKilledKernel_kernel]
      have h2' : ∫ z, ((R₂ ^ k) f) z ∂C.killedTransition y =
          ∫ z, nkp C r k F z ∂C.killedTransition y := h2
      rw [h2']
      change r⁻¹ * ∫ z, r⁻¹ ^ k * kpow C k F z ∂C.killedTransition y = nkp C r (k + 1) F y
      rw [integral_const_mul, kpow_succ C k hF hB, nkp, pow_succ]; ring
  have h1 := hdec m hm f
  have h2 : ‖(R₂ ^ m) f‖ ^ 2 ≤ (L * κ ^ m * ‖f‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e1 : ∫ y, ((R₂ ^ m) f) y ^ 2 ∂μ = ∫ y, nkp C r m F y ^ 2 ∂μ :=
    integral_congr_ae (by filter_upwards [hae m] with y hy; rw [hy])
  have e2 : ∫ y, f y ^ 2 ∂μ = ∫ y, F y ^ 2 ∂μ :=
    integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with y hy; rw [hy])
  rw [norm_sq_L2, mul_pow, norm_sq_L2, e1, e2] at h2
  calc _ ≤ _ := h2
    _ ≤ (L * θ ^ m) ^ 2 * ∫ y, F y ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ0.le hκθ m) hL.le) 2)
          (integral_nonneg fun y => sq_nonneg _)

end FromH

/-!
### The conditional second-moment bound
-/

section Main

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
  {ρ : Measure M} (C : CanonicalChain M)

theorem exists_pos_lower {a : ℕ → ℝ} {l : ℝ} (ha : ∀ n, 0 < a n) (hl : 0 < l)
    (hlim : Tendsto a atTop (𝓝 l)) : ∃ c > 0, ∀ n, c ≤ a n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (eventually_ge_nhds (half_lt_self hl)))
  obtain ⟨c₀, hc₀, hc₀le⟩ : ∃ c₀ > 0, ∀ n < N, c₀ ≤ a n := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · exact ⟨1, one_pos, fun n hn => by omega⟩
    · obtain ⟨k, -, hkmin⟩ := (Finset.range N).exists_min_image a ⟨0, Finset.mem_range.2 hNpos⟩
      exact ⟨a k, ha k, fun n hn => hkmin n (Finset.mem_range.2 hn)⟩
  refine ⟨min c₀ (l / 2), lt_min hc₀ (half_pos hl), fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact (min_le_left _ _).trans (hc₀le n hn)
  · exact (min_le_right _ _).trans (hN n hn)

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] [MeasurableSpace M] in
theorem abs_zeroExtension_le {g : M → ℝ} {G : ℝ} (hG0 : 0 ≤ G) (hgG : ∀ y, |g y| ≤ G)
    (z : Option M) : |zeroExtension g z| ≤ G := by
  cases z with
  | none => simpa using hG0
  | some y => simpa using hgG y

omit [MetricSpace M] [CompactSpace M] [BorelSpace M] in
/-- The squared Birkhoff sum on the survival event, expanded into killed-kernel words. -/
theorem integral_sq_survival {g : M → ℝ} (hg : Measurable g) {G : ℝ} (hG0 : 0 ≤ G)
    (hgG : ∀ y, |g y| ≤ G) (n : ℕ) (x : M) :
    ∫ ω, (survival n).indicator (fun ω => pathBirkhoffSum g n ω ^ 2) ω ∂C.pathMeasure x =
      ∑ i ∈ Finset.range n, kpow C i (fun y => g y * g y * kpow C (n - i) (fun _ => 1) y) x +
      2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, kpow C i (fun y => g y *
        kpow C (j - i) (fun z => g z * kpow C (n - j) (fun _ => 1) z) y) x := by
  set a : ℕ → Path M → ℝ := fun i ω => zeroExtension g (ω i) with ha_def
  have ham : ∀ i, Measurable (a i) := fun i =>
    (measurable_zeroExtension hg).comp (measurable_pi_apply i)
  have hab : ∀ i ω, |a i ω| ≤ G := fun i ω => abs_zeroExtension_le hG0 hgG _
  have hind : ∀ i j, Integrable (fun ω => (survival n).indicator (fun ω => a i ω * a j ω) ω)
      (C.pathMeasure x) := by
    intro i j
    refine integrable_of_bdd (((ham i).mul (ham j)).indicator (measurableSet_survival n))
      (B := G * G) (fun ω => ?_)
    by_cases hω : ω ∈ survival n
    · rw [Set.indicator_of_mem hω, abs_mul]
      exact mul_le_mul (hab i ω) (hab j ω) (abs_nonneg _) hG0
    · rw [Set.indicator_of_notMem hω, abs_zero]; positivity
  have hpt : (fun ω => (survival n).indicator (fun ω => pathBirkhoffSum g n ω ^ 2) ω) =
      fun ω => ∑ i ∈ Finset.range n, (survival n).indicator (fun ω => a i ω * a i ω) ω +
        2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j,
          (survival n).indicator (fun ω => a i ω * a j ω) ω := by
    funext ω
    by_cases hω : ω ∈ survival n
    · simp only [Set.indicator_of_mem hω, pathBirkhoffSum, birkhoffSum]
      exact sq_sum_eq (fun i => a i ω) n
    · simp only [Set.indicator_of_notMem hω, Finset.sum_const_zero, mul_zero, add_zero]
  have hI1 : Integrable (fun ω => ∑ i ∈ Finset.range n,
      (survival n).indicator (fun ω => a i ω * a i ω) ω) (C.pathMeasure x) :=
    MeasureTheory.integrable_finsetSum _ fun i _ => hind i i
  have hI2 : ∀ j, Integrable (fun ω => ∑ i ∈ Finset.range j,
      (survival n).indicator (fun ω => a i ω * a j ω) ω) (C.pathMeasure x) := fun j =>
    MeasureTheory.integrable_finsetSum _ fun i _ => hind i j
  have hI3 : Integrable (fun ω => ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j,
      (survival n).indicator (fun ω => a i ω * a j ω) ω) (C.pathMeasure x) :=
    MeasureTheory.integrable_finsetSum _ fun j _ => hI2 j
  rw [hpt, integral_add hI1 (hI3.const_mul 2), integral_const_mul,
    MeasureTheory.integral_finsetSum _ fun i _ => hind i i, MeasureTheory.integral_finsetSum _ fun j _ => hI2 j]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    exact integral_diag_survival C hg hG0 hgG (Finset.mem_range.1 hi) x
  · congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [MeasureTheory.integral_finsetSum _ fun i _ => hind i j]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact integral_pair_survival C hg hG0 hgG (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) x

/-- **Conditional second moment of Birkhoff sums.** For every `x ∈ M \ Z` there is `Cₓ` such that,
for every bounded measurable `g` with `ν(g) = 0` and every `n`, `E_x[(∑_{i<n} g(Xᵢ))² | τ > n] ≤ Cₓ
(n μ(g²) + ‖g‖∞²)`. -/
theorem conditional_sum_second_moment (h : HypothesisH ρ C.toKilledKernel)
    (d : DoobTransform.EigenData C.killedTransition) (s : SurvivalGapData h d)
    (hlive : d.liveSet = survivingSet C.killedTransition) (μ : Measure M)
    [IsProbabilityMeasure μ] (hleft : C.killedTransition ∘ₘ μ = d.rate • μ)
    (hnorm : ∫⁻ x, d.weight x ∂μ = 1) (x : d.State) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧ ∀ g : M → ℝ, Measurable g → ∀ G : ℝ, 0 ≤ G → (∀ y, |g y| ≤ G) →
      ∫ y, g y ∂μ.withDensity d.weight = 0 → ∀ n : ℕ,
        ∫ ω, pathBirkhoffSum g n ω ^ 2 ∂C.conditionedMeasure x.val n ≤
          Cx * (n * ∫ y, g y ^ 2 ∂μ + G ^ 2) := by
  have : Nonempty M := ⟨x.val⟩
  have hx : x.val ∈ survivingSet C.killedTransition := by rw [← hlive]; exact x.property
  obtain ⟨D, hDr, hDη⟩ := exists_data C h d s μ hleft hnorm
  set a : ℕ → ℝ := fun n => nkp C D.r n (fun _ => 1) x.val with ha_def
  have ha_eq : ∀ n, a n = D.r⁻¹ ^ n * ((C.killedTransition ^ n) x.val).real univ := fun n => by
    have : IsFiniteKernel (C.killedTransition ^ n) := killedKernel_power_isFinite C.toKilledKernel n
    simp only [ha_def, nkp, kpow, integral_const, smul_eq_mul, mul_one]
  have ha_pos : ∀ n, 0 < a n := fun n => by
    rw [ha_eq]
    refine mul_pos (pow_pos (inv_pos.2 D.r_pos) _) ?_
    have hp := C.pathMeasure_survival_pos x.val hx n
    rw [C.pathMeasure_survival] at hp
    have : IsFiniteKernel (C.killedTransition ^ n) := killedKernel_power_isFinite C.toKilledKernel n
    exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have ha_lim : Tendsto a atTop (𝓝 (d.weight x.val).toReal) := by
    have := s.normalized_survival_tendstoUniformly.tendsto_at x.val
    refine this.congr fun n => ?_
    rw [normalized_survival_toReal (K := C.toKilledKernel) d n x.val, ha_eq, hDr]; rfl
  obtain ⟨c, hc, hca⟩ :=
    exists_pos_lower ha_pos (ENNReal.toReal_pos x.property (d.weight_ne_top _)) ha_lim
  have hθ0 := D.θ_nonneg
  have hθ1 := D.θ_lt_one
  set K0 := (1 - D.θ)⁻¹ with hK0_def
  set K1 := 1 + K0 with hK1_def
  have hK0 : 0 ≤ K0 := inv_nonneg.2 (by linarith)
  have hK1 : 0 ≤ K1 := by positivity
  have hQ := D.pairConst_nonneg
  have hQd := D.diagConst_nonneg
  refine ⟨c⁻¹ * (D.diagConst + 4 * D.pairConst * K0 + D.diagConst * K1 +
    4 * D.pairConst * K1 * K0), by positivity, ?_⟩
  intro g hg G hG0 hgG hν n
  have hgη : ∫ y, g y * D.η y ∂μ = 0 := by
    rw [hDη, ← hν, integral_withDensity_eq_integral_toReal_smul d.measurable_weight
      (Eventually.of_forall fun y => lt_top_iff_ne_top.2 (d.weight_ne_top y))]
    congr 1; funext y; rw [smul_eq_mul, mul_comm]
  set μg := ∫ y, g y ^ 2 ∂μ with hμg_def
  have hμg : 0 ≤ μg := integral_nonneg fun y => sq_nonneg _
  -- The conditional expectation as a normalized integral.
  have hcond : ∫ ω, pathBirkhoffSum g n ω ^ 2 ∂C.conditionedMeasure x.val n =
      (D.r ^ n * a n)⁻¹ * ∫ ω, (survival n).indicator (fun ω => pathBirkhoffSum g n ω ^ 2) ω
        ∂C.pathMeasure x.val := by
    rw [conditionedMeasure, ProbabilityTheory.cond, integral_smul_measure,
      integral_indicator (measurableSet_survival n), C.pathMeasure_survival, ha_eq, ← mul_assoc,
      ← mul_pow, mul_inv_cancel₀ D.r_pos.ne', one_pow, one_mul, smul_eq_mul, ENNReal.toReal_inv]
    rfl
  rw [hcond, integral_sq_survival C hg hG0 hgG n x.val]
  -- Normalized words.
  set Pd : ℕ → ℝ := fun i =>
    nkp C D.r i (fun y => g y * g y * nkp C D.r (n - i) (fun _ => 1) y) x.val with hPd
  set Pp : ℕ → ℕ → ℝ := fun j i => nkp C D.r i (fun y => g y * nkp C D.r (j - i)
    (fun z => g z * nkp C D.r (n - j) (fun _ => 1) z) y) x.val with hPp
  have hnormed : (D.r ^ n * a n)⁻¹ *
      (∑ i ∈ Finset.range n, kpow C i (fun y => g y * g y * kpow C (n - i) (fun _ => 1) y) x.val +
      2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, kpow C i (fun y => g y *
        kpow C (j - i) (fun z => g z * kpow C (n - j) (fun _ => 1) z) y) x.val) =
      (a n)⁻¹ * (∑ i ∈ Finset.range n, Pd i + 2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j,
        Pp j i) := by
    rw [mul_inv, mul_comm (D.r ^ n)⁻¹, mul_assoc, ← inv_pow]
    congr 1
    rw [mul_add, Finset.mul_sum, mul_left_comm, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      exact nkp_diag C D.r g (Finset.mem_range.1 hi) x.val
    · congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      exact nkp_pair C D.r g (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) x.val
  rw [hnormed]
  -- Diagonal sum.
  have hdiag : |∑ i ∈ Finset.range n, Pd i| ≤ D.diagConst * (n * μg + G ^ 2 * K1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range n, |Pd i|
        ≤ ∑ i ∈ Finset.range n, D.diagConst * (μg + G ^ 2 * D.θ ^ (i - 1)) :=
          Finset.sum_le_sum fun i _ => D.diag_bound hg hG0 hgG i x.val
      _ = D.diagConst * (n * μg + G ^ 2 * ∑ i ∈ Finset.range n, D.θ ^ (i - 1)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, ← Finset.mul_sum]
      _ ≤ D.diagConst * (n * μg + G ^ 2 * K1) := by
          gcongr
          exact geom_pred_le hθ0 hθ1 n
  -- Pair sum.
  have hpair : |∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, Pp j i| ≤
      D.pairConst * (μg * (2 * (n * K0)) + G ^ 2 * (2 * (K1 * K0))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range n, |∑ i ∈ Finset.range j, Pp j i|
        ≤ ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, D.pairConst *
            (μg * (D.θ ^ (j - i - 1) + D.θ ^ (n - j - 1)) +
              G ^ 2 * D.θ ^ (i - 1) * (D.θ ^ (j - i - 1) + D.θ ^ (n - j - 1))) := by
          refine Finset.sum_le_sum fun j hj => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i hi => ?_)
          have hij := Finset.mem_range.1 hi
          have hjn := Finset.mem_range.1 hj
          exact D.pair_bound hg hG0 hgG hgη i (by omega) (by omega) x.val
      _ = D.pairConst * μg * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, D.θ ^ (j - i - 1) +
          D.pairConst * μg * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, D.θ ^ (n - j - 1) +
          D.pairConst * G ^ 2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j,
            D.θ ^ (i - 1) * D.θ ^ (j - i - 1) +
          D.pairConst * G ^ 2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j,
            D.θ ^ (i - 1) * D.θ ^ (n - j - 1) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ D.pairConst * μg * (n * K0) + D.pairConst * μg * (n * K0) +
          D.pairConst * G ^ 2 * (K1 * K0) + D.pairConst * G ^ 2 * (K1 * K0) := by
          have hQμ : 0 ≤ D.pairConst * μg := mul_nonneg hQ hμg
          have hQG : 0 ≤ D.pairConst * G ^ 2 := mul_nonneg hQ (sq_nonneg G)
          exact add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left (dsum_gap_le hθ0 hθ1 n) hQμ)
            (mul_le_mul_of_nonneg_left (dsum_end_le hθ0 hθ1 n) hQμ))
            (mul_le_mul_of_nonneg_left (dsum_start_gap_le hθ0 hθ1 n) hQG))
            (mul_le_mul_of_nonneg_left (dsum_start_end_le hθ0 hθ1 n) hQG)
      _ = _ := by ring
  have hX : |∑ i ∈ Finset.range n, Pd i + 2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, Pp j i|
      ≤ D.diagConst * (n * μg + G ^ 2 * K1) +
        2 * (D.pairConst * (μg * (2 * (n * K0)) + G ^ 2 * (2 * (K1 * K0)))) :=
    (abs_add_le _ _).trans (add_le_add hdiag (by
      rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left hpair zero_le_two))
  have han := ha_pos n
  calc (a n)⁻¹ * (∑ i ∈ Finset.range n, Pd i + 2 * ∑ j ∈ Finset.range n,
        ∑ i ∈ Finset.range j, Pp j i)
      ≤ (a n)⁻¹ * |∑ i ∈ Finset.range n, Pd i + 2 * ∑ j ∈ Finset.range n,
        ∑ i ∈ Finset.range j, Pp j i| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.2 han.le)
    _ ≤ c⁻¹ * (D.diagConst * (n * μg + G ^ 2 * K1) +
        2 * (D.pairConst * (μg * (2 * (n * K0)) + G ^ 2 * (2 * (K1 * K0))))) :=
        mul_le_mul (inv_anti₀ hc (hca n)) hX (abs_nonneg _) (inv_nonneg.2 hc.le)
    _ ≤ _ := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc.le)
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [mul_nonneg hQd (sq_nonneg G), mul_nonneg (mul_nonneg hQ hK0) (sq_nonneg G),
          mul_nonneg (mul_nonneg hQd hK1) (mul_nonneg hn0 hμg),
          mul_nonneg (mul_nonneg (mul_nonneg hQ hK1) hK0) (mul_nonneg hn0 hμg)]

end Main

end

end ConditionedStableLaws.SecondMoment
