import ConditionedStableLaws.PerturbationStability
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Exponentially twisted operators on `L∞`

Multiplication operators by bounded measurable functions on `L∞(ρ)`, the identity `exp(t M_h) =
M_{e^{th}}`, and, from the stability of an isolated simple eigenvalue, the bound `‖T(t)ᵏ‖ ≤ B e^{K k
t²}` for small `|t|` for the twisted family `T(t) = T₀ ∘ exp(t M_h)` when `ℓ(M_h v) = 0`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology Nat

namespace ConditionedStableLaws.TwistedOperators

noncomputable section

/-! ### Tails of the exponential series -/

theorem abs_exp_sub_partial_le {x a : ℝ} (hxa : |x| ≤ a) (N : ℕ) :
    |Real.exp x - ∑ n ∈ Finset.range N, x ^ n / (n ! : ℝ)| ≤
      Real.exp a - ∑ n ∈ Finset.range N, a ^ n / (n ! : ℝ) := by
  have hx : HasSum (fun n => x ^ n / (n ! : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have ha : HasSum (fun n => a ^ n / (n ! : ℝ)) (Real.exp a) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp a
  have hx' := (hasSum_nat_add_iff' N).2 hx
  have ha' := (hasSum_nat_add_iff' N).2 ha
  have hterm : ∀ m, |x ^ m / (m ! : ℝ)| ≤ a ^ m / (m ! : ℝ) := fun m => by
    rw [abs_div, abs_pow, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) hxa m) (Nat.cast_nonneg _)
  rw [abs_le]
  constructor
  · have := hasSum_le (fun m => neg_le_of_abs_le (hterm (m + N))) ha'.neg hx'
    linarith
  · exact hasSum_le (fun m => (le_abs_self _).trans (hterm (m + N))) hx' ha'

theorem tendsto_exp_partial (a : ℝ) :
    Tendsto (fun N => Real.exp a - ∑ n ∈ Finset.range N, a ^ n / (n ! : ℝ)) atTop (𝓝 0) := by
  have ha : HasSum (fun n => a ^ n / (n ! : ℝ)) (Real.exp a) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp a
  have := (tendsto_const_nhds (x := Real.exp a)).sub ha.tendsto_sum_nat
  rwa [sub_self] at this

/-! ### Multiplication operators -/

section Mul

variable {M : Type*} [MeasurableSpace M] {ρ : Measure M} [IsFiniteMeasure ρ]

omit [IsFiniteMeasure ρ] in
theorem ae_norm_le (f : Lp ℝ ∞ ρ) : ∀ᵐ x ∂ρ, ‖f x‖ ≤ ‖f‖ := by
  simpa only [Lp.norm_def, toReal_eLpNorm] using ae_le_lpNorm_exponent_top (Lp.memLp f)

/-- A bounded measurable multiplier. -/
structure Multiplier (M : Type*) [MeasurableSpace M] where
  toFun : M → ℝ
  measurable : Measurable toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  le_bound : ∀ y, |toFun y| ≤ bound

omit [IsFiniteMeasure ρ] in
theorem memLp_mul (q : Multiplier M) (f : Lp ℝ ∞ ρ) :
    MemLp (fun y => q.toFun y * f y) ∞ ρ :=
  memLp_top_of_bound (q.measurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (q.bound * ‖f‖) (by
      filter_upwards [ae_norm_le f] with y hy
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (q.le_bound y) hy (norm_nonneg _) q.bound_nonneg)

/-- Multiplication by a bounded measurable function on `L∞(ρ)`. -/
def mulL (q : Multiplier M) : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul q f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_mul q (f + g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_mul q f).toLp _) ((memLp_mul q g).toLp _),
          (memLp_mul q f).coeFn_toLp, (memLp_mul q g).coeFn_toLp, Lp.coeFn_add f g]
          with y h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]
      map_smul' := fun a f => by
        apply Lp.ext
        filter_upwards [(memLp_mul q (a • f)).coeFn_toLp,
          Lp.coeFn_smul a ((memLp_mul q f).toLp _), (memLp_mul q f).coeFn_toLp,
          Lp.coeFn_smul a f] with y h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul]
        ring }
    q.bound (fun f => by
      refine (Lp.norm_le_of_ae_bound (mul_nonneg q.bound_nonneg (norm_nonneg f)) ?_).trans_eq
        (by simp)
      filter_upwards [(memLp_mul q f).coeFn_toLp, ae_norm_le f] with y h1 h2
      change ‖((memLp_mul q f).toLp _ : M → ℝ) y‖ ≤ _
      rw [h1, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (q.le_bound y) h2 (norm_nonneg _) q.bound_nonneg)

theorem mulL_ae (q : Multiplier M) (f : Lp ℝ ∞ ρ) :
    (mulL q f : M → ℝ) =ᵐ[ρ] fun y => q.toFun y * f y :=
  (memLp_mul q f).coeFn_toLp

theorem norm_mulL_le (q : Multiplier M) : ‖(mulL q : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ)‖ ≤ q.bound :=
  LinearMap.mkContinuous_norm_le _ q.bound_nonneg _

/-- Operator-norm bound from an a.e. pointwise multiplier bound. -/
theorem opNorm_le_of_ae (A : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ) (ψ : M → ℝ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ y, |ψ y| ≤ c) (hA : ∀ f, (A f : M → ℝ) =ᵐ[ρ] fun y => ψ y * f y) : ‖A‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun f => ?_
  refine (Lp.norm_le_of_ae_bound (mul_nonneg hc0 (norm_nonneg f)) ?_).trans_eq (by simp)
  filter_upwards [hA f, ae_norm_le f] with y h1 h2
  rw [h1, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (hc y) h2 (norm_nonneg _) hc0

/-- The multiplier `e^{t h}`. -/
def expMultiplier (h : Multiplier M) (t : ℝ) : Multiplier M where
  toFun y := Real.exp (t * h.toFun y)
  measurable := (measurable_const.mul h.measurable).exp
  bound := Real.exp (|t| * h.bound)
  bound_nonneg := (Real.exp_pos _).le
  le_bound y := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    calc t * h.toFun y ≤ |t * h.toFun y| := le_abs_self _
      _ = |t| * |h.toFun y| := abs_mul _ _
      _ ≤ |t| * h.bound := mul_le_mul_of_nonneg_left (h.le_bound y) (abs_nonneg t)

theorem smul_pow_ae (h : Multiplier M) (t : ℝ) (n : ℕ) (f : Lp ℝ ∞ ρ) :
    (((t • (mulL h : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ)) ^ n) f : M → ℝ) =ᵐ[ρ]
      fun y => (t * h.toFun y) ^ n * f y := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [Lp.coeFn_smul t (mulL h (((t • mulL h) ^ n) f)),
      mulL_ae h (((t • mulL h) ^ n) f), ih f] with y h1 h2 h3
    rw [smul_apply, h1, Pi.smul_apply, h2, h3, smul_eq_mul]
    ring

/-- `exp(t M_h) = M_{e^{th}}`. -/
theorem exp_smul_mulL (h : Multiplier M) (t : ℝ) :
    NormedSpace.exp (t • (mulL h : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ)) = mulL (expMultiplier h t) := by
  set H : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := mulL h
  set S : ℕ → (Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ) := fun N =>
    ∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹) • (t • H) ^ n
  have hS : Tendsto S atTop (𝓝 (NormedSpace.exp (t • H))) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • H)).tendsto_sum_nat
  have hSae : ∀ N f, (S N f : M → ℝ) =ᵐ[ρ]
      fun y => (∑ n ∈ Finset.range N, (t * h.toFun y) ^ n / (n ! : ℝ)) * f y := by
    intro N f
    induction N with
    | zero =>
      simp only [S, Finset.range_zero, Finset.sum_empty, zero_apply,
        zero_mul]
      exact Lp.coeFn_zero _ _ _
    | succ N ih =>
      have e : S (N + 1) = S N + ((N ! : ℝ)⁻¹) • (t • H) ^ N := Finset.sum_range_succ _ _
      rw [e, add_apply, smul_apply]
      filter_upwards [Lp.coeFn_add (S N f) (((N ! : ℝ)⁻¹) • ((t • H) ^ N) f), ih,
        Lp.coeFn_smul ((N ! : ℝ)⁻¹) (((t • H) ^ N) f), smul_pow_ae h t N f] with y h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, h4, Finset.sum_range_succ, smul_eq_mul]
      ring
  have hlim : Tendsto S atTop (𝓝 (mulL (expMultiplier h t))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (tendsto_exp_partial (|t| * h.bound))
    refine opNorm_le_of_ae _ (fun y => (∑ n ∈ Finset.range N, (t * h.toFun y) ^ n / (n ! : ℝ)) -
      Real.exp (t * h.toFun y)) ?_ (fun y => ?_) (fun f => ?_)
    · exact (abs_nonneg _).trans (abs_exp_sub_partial_le (x := 0)
        (by rw [abs_zero]; exact mul_nonneg (abs_nonneg t) h.bound_nonneg) N)
    · rw [abs_sub_comm]
      have hy : |t * h.toFun y| ≤ |t| * h.bound := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.le_bound y) (abs_nonneg t)
      exact abs_exp_sub_partial_le hy N
    · filter_upwards [Lp.coeFn_sub (S N f) (mulL (expMultiplier h t) f), hSae N f,
        mulL_ae (expMultiplier h t) f] with y h1 h2 h3
      rw [sub_apply, h1, Pi.sub_apply, h2, h3]
      simp only [expMultiplier]
      ring
  exact tendsto_nhds_unique hS hlim

end Mul

/-! ### Consequences of rank-one perturbation stability -/

section Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem abs_le_of_mem_uIcc_zero {s t : ℝ} (hs : s ∈ uIcc 0 t) : |s| ≤ |t| := by
  rcases mem_uIcc.1 hs with h | h
  · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]; exact h.2
  · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]; linarith [h.1]

/-- `(AB)^{k+1} = A (BA)^k B`. -/
theorem mul_pow_succ_eq {R : Type*} [Monoid R] (A B : R) (k : ℕ) :
    (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]

theorem real_exp_tail_le {a : ℝ} (ha : 0 ≤ a) :
    Real.exp a - (1 + a + a ^ 2 / 2) ≤ a ^ 3 * Real.exp a := by
  have hx : HasSum (fun n => a ^ n / (n ! : ℝ)) (Real.exp a) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp a
  have h3 := (hasSum_nat_add_iff' 3).2 hx
  have hsum3 : ∑ i ∈ Finset.range 3, a ^ i / (i ! : ℝ) = 1 + a + a ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum3] at h3
  refine hasSum_le (fun n => ?_) h3 (hx.mul_left (a ^ 3))
  rw [pow_add, show a ^ n * a ^ 3 / ((n + 3)! : ℝ) = a ^ 3 * (a ^ n / ((n + 3)! : ℝ)) by ring]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (pow_nonneg ha n)
    (by exact_mod_cast Nat.factorial_pos n)
    (by exact_mod_cast Nat.factorial_le (Nat.le_add_right n 3))) (pow_nonneg ha 3)

theorem exp_taylor_two_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X : A) :
    ‖NormedSpace.exp X - (1 + X + (1 / 2 : ℝ) • X ^ 2)‖ ≤ ‖X‖ ^ 3 * Real.exp ‖X‖ := by
  have hX := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have h3 := (hasSum_nat_add_iff' 3).2 hX
  have hsum3 : ∑ i ∈ Finset.range 3, ((i ! : ℝ)⁻¹) • X ^ i = 1 + X + (1 / 2 : ℝ) • X ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum3] at h3
  have ha : HasSum (fun n => ‖X‖ ^ (n + 3) / ((n + 3) ! : ℝ))
      (Real.exp ‖X‖ - (1 + ‖X‖ + ‖X‖ ^ 2 / 2)) := by
    have hx : HasSum (fun n => ‖X‖ ^ n / (n ! : ℝ)) (Real.exp ‖X‖) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp ‖X‖
    have := (hasSum_nat_add_iff' 3).2 hx
    have hs : ∑ i ∈ Finset.range 3, ‖X‖ ^ i / (i ! : ℝ) = 1 + ‖X‖ + ‖X‖ ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rwa [hs] at this
  refine (h3.norm_le_of_bounded ha fun n => ?_).trans (real_exp_tail_le (norm_nonneg X))
  rw [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' X (by omega)) (by positivity)

/-- Second-order remainder of the exponential: `‖e^X - 1 - X‖ ≤ ‖X‖² (‖X‖e^{‖X‖} + 1/2)`. -/
theorem exp_sub_one_sub_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X : A) :
    ‖NormedSpace.exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * (‖X‖ * Real.exp ‖X‖ + 1 / 2) := by
  have e : NormedSpace.exp X - 1 - X =
      (NormedSpace.exp X - (1 + X + (1 / 2 : ℝ) • X ^ 2)) + (1 / 2 : ℝ) • X ^ 2 := by
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := exp_taylor_two_le X
  have h2 : ‖(1 / 2 : ℝ) • X ^ 2‖ ≤ 1 / 2 * ‖X‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le' X (by norm_num)) (by norm_num)
  nlinarith [h1, h2]

set_option maxHeartbeats 2000000 in
/-- The twisted family satisfies `‖T(t)ᵏ‖ ≤ B e^{K k t²}` for small `|t|`, provided the first-order
coefficient `ℓ(H v)` vanishes. The leading eigenvalue of `T(t)` is supplied by the local stability
of an isolated simple eigenvalue; its second-order behaviour `|Λ(t) - 1| = O(t²)` is derived from
the eigenrelation, `ℓ ∘ T₀ = ℓ`, `ℓ(Hv) = 0` and the Lipschitz dependence of the projection. -/
theorem twisted_power_bound (T₀ H : E →L[ℝ] E) (v : E) (ℓ : E →L[ℝ] ℝ) (hℓv : ℓ v = 1)
    (hℓT : ∀ w, ℓ (T₀ w) = ℓ w)
    (hT₀P : T₀ * ℓ.smulRight v = ℓ.smulRight v) (hPT₀ : ℓ.smulRight v * T₀ = ℓ.smulRight v)
    {C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hgap : ∀ n : ℕ, 1 ≤ n → ‖T₀ ^ n - ℓ.smulRight v‖ ≤ C * θ ^ n) (hHv : ℓ (H v) = 0) :
    ∃ t₀ > 0, ∃ K > 0, ∃ B > 0, ∀ t : ℝ, |t| ≤ t₀ → ∀ k : ℕ,
      ‖(T₀ * NormedSpace.exp (t • H)) ^ k‖ ≤ B * Real.exp (K * k * t ^ 2) := by
  obtain ⟨ε₀, hε₀, K₀, hK₀, χ, hχ0, hχ1, C', hC', hstab⟩ :=
    OperatorPerturbation.stability_of_rank_one_gap T₀ v ℓ hℓv hT₀P hPT₀ hθ0 hθ hgap
  set P := ℓ.smulRight v with hP_def
  set h := ‖H‖ with hh_def
  have hh0 : 0 ≤ h := norm_nonneg _
  set c₂ : ℝ := h * Real.exp h + 1 / 2 with hc₂_def
  have hc₂ : 0 ≤ c₂ := by positivity
  set L : ℝ := ‖T₀‖ * (1 + c₂ * h) * h with hL_def
  have hL : 0 ≤ L := by positivity
  set q : ℝ := ‖ℓ‖ * K₀ * L * ‖v‖ with hq_def
  have hq : 0 ≤ q := by positivity
  set t₀ : ℝ := min 1 (min (ε₀ / (L + 1)) (1 / (2 * (q + 1)))) with ht₀_def
  have ht₀ : 0 < t₀ := lt_min one_pos (lt_min (div_pos hε₀ (by linarith))
    (div_pos one_pos (by linarith)))
  have ht₀1 : t₀ ≤ 1 := min_le_left _ _
  have ht₀ε : L * t₀ ≤ ε₀ := by
    have h1 : t₀ ≤ ε₀ / (L + 1) := (min_le_right _ _).trans (min_le_left _ _)
    calc L * t₀ ≤ (L + 1) * t₀ := by nlinarith
      _ ≤ (L + 1) * (ε₀ / (L + 1)) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = ε₀ := by field_simp
  have ht₀q : q * t₀ ≤ 1 / 2 := by
    have h1 : t₀ ≤ 1 / (2 * (q + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    calc q * t₀ ≤ (q + 1) * t₀ := by nlinarith
      _ ≤ (q + 1) * (1 / (2 * (q + 1))) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 1 / 2 := by field_simp
  set K₂ : ℝ := ‖ℓ‖ * ‖v‖ * (h * K₀ * L + c₂ * h ^ 2 * (‖P‖ + K₀ * L)) with hK₂_def
  have hK₂ : 0 ≤ K₂ := by positivity
  refine ⟨t₀, ht₀, 2 * K₂ + 1, by positivity, ‖P‖ + K₀ * L + 1 + C', by positivity,
    fun t ht k => ?_⟩
  have ht1 : |t| ≤ 1 := ht.trans ht₀1
  set X : E →L[ℝ] E := t • H with hX_def
  set T : E →L[ℝ] E := T₀ * NormedSpace.exp X with hT_def
  set R : E →L[ℝ] E := NormedSpace.exp X - 1 - X with hR_def
  have hXn : ‖X‖ = |t| * h := by rw [hX_def, norm_smul, Real.norm_eq_abs]
  have hXh : ‖X‖ ≤ h := by rw [hXn]; nlinarith [abs_nonneg t]
  have hRn : ‖R‖ ≤ c₂ * (|t| * h) ^ 2 := by
    have h1 := exp_sub_one_sub_le X
    have h2 : ‖X‖ * Real.exp ‖X‖ + 1 / 2 ≤ c₂ := by
      have := mul_le_mul hXh (Real.exp_le_exp.2 hXh) (Real.exp_pos _).le hh0
      rw [hc₂_def]; linarith
    rw [← hXn]
    calc ‖R‖ ≤ ‖X‖ ^ 2 * (‖X‖ * Real.exp ‖X‖ + 1 / 2) := h1
      _ ≤ ‖X‖ ^ 2 * c₂ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = c₂ * ‖X‖ ^ 2 := mul_comm _ _
  have hE1 : ‖NormedSpace.exp X - 1‖ ≤ (1 + c₂ * h) * (|t| * h) := by
    have e : NormedSpace.exp X - 1 = X + R := by rw [hR_def]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [hXn]
    have hth : |t| * h ≤ h := by nlinarith [abs_nonneg t]
    have : c₂ * (|t| * h) ^ 2 ≤ c₂ * h * (|t| * h) := by
      rw [sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hth hc₂)
        (mul_nonneg (abs_nonneg t) hh0)
    nlinarith [hRn]
  have hD : ‖T - T₀‖ ≤ L * |t| := by
    have e : T - T₀ = T₀ * (NormedSpace.exp X - 1) := by rw [hT_def, mul_sub, mul_one]
    rw [e]
    refine (norm_mul_le _ _).trans ?_
    calc ‖T₀‖ * ‖NormedSpace.exp X - 1‖ ≤ ‖T₀‖ * ((1 + c₂ * h) * (|t| * h)) :=
          mul_le_mul_of_nonneg_left hE1 (norm_nonneg _)
      _ = L * |t| := by rw [hL_def]; ring
  have hDε : ‖T - T₀‖ ≤ ε₀ := hD.trans ((mul_le_mul_of_nonneg_left ht hL).trans ht₀ε)
  obtain ⟨Λ, Pr, hTPr, -, -, hPr, -, hpow⟩ := hstab T hDε
  have hPr' : ‖Pr - P‖ ≤ K₀ * L * |t| := by
    calc ‖Pr - P‖ ≤ K₀ * ‖T - T₀‖ := hPr
      _ ≤ K₀ * (L * |t|) := mul_le_mul_of_nonneg_left hD hK₀
      _ = K₀ * L * |t| := by ring
  have hPrn : ‖Pr‖ ≤ ‖P‖ + K₀ * L := by
    have h1 : ‖Pr‖ ≤ ‖P‖ + ‖Pr - P‖ := by
      have := norm_add_le P (Pr - P); rwa [add_sub_cancel] at this
    have h2 : K₀ * L * |t| ≤ K₀ * L := by nlinarith [mul_nonneg hK₀ hL]
    linarith
  have hPv : P v = v := by rw [hP_def, ContinuousLinearMap.smulRight_apply, hℓv, one_smul]
  set w := (Pr - P) v with hw_def
  have hwn : ‖w‖ ≤ K₀ * L * |t| * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hPr' (norm_nonneg _))
  have hPrv : Pr v = v + w := by
    rw [hw_def, sub_apply, hPv]; abel
  have hℓw : |ℓ w| ≤ q * |t| := by
    calc |ℓ w| ≤ ‖ℓ‖ * ‖w‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖ℓ‖ * (K₀ * L * |t| * ‖v‖) := mul_le_mul_of_nonneg_left hwn (norm_nonneg _)
      _ = q * |t| := by rw [hq_def]; ring
  have hℓPr : 1 / 2 ≤ ℓ (Pr v) := by
    rw [hPrv, map_add, hℓv]
    have : q * |t| ≤ 1 / 2 := (mul_le_mul_of_nonneg_left ht hq).trans ht₀q
    linarith [neg_abs_le (ℓ w)]
  -- The eigenrelation evaluated at `v` and paired with `ℓ`.
  have hkey : (Λ - 1) * ℓ (Pr v) = t * ℓ (H w) + ℓ (R (Pr v)) := by
    have h1 : ℓ (T (Pr v)) = Λ * ℓ (Pr v) := by
      have := congrArg (fun S : E →L[ℝ] E => ℓ (S v)) hTPr
      simpa [mul_apply_eq_comp, smul_apply] using this
    have hexp : NormedSpace.exp X = 1 + X + R := by rw [hR_def]; abel
    have h2 : ℓ (T (Pr v)) = ℓ (Pr v) + t * ℓ (H (Pr v)) + ℓ (R (Pr v)) := by
      rw [hT_def, mul_apply_eq_comp, hℓT, hexp, add_apply,
        add_apply, one_apply_eq_self, map_add, map_add, hX_def,
        smul_apply, map_smul, smul_eq_mul]
    have h3 : ℓ (H (Pr v)) = ℓ (H w) := by rw [hPrv, map_add, map_add, hHv, zero_add]
    rw [h3] at h2
    linarith
  have hbound : |Λ - 1| * (1 / 2) ≤ K₂ * t ^ 2 := by
    have hA : |t * ℓ (H w)| ≤ ‖ℓ‖ * ‖v‖ * (h * K₀ * L) * t ^ 2 := by
      rw [abs_mul, ← Real.norm_eq_abs (ℓ (H w))]
      have : ‖ℓ (H w)‖ ≤ ‖ℓ‖ * (h * (K₀ * L * |t| * ‖v‖)) :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hwn hh0))
          (norm_nonneg _))
      calc |t| * ‖ℓ (H w)‖ ≤ |t| * (‖ℓ‖ * (h * (K₀ * L * |t| * ‖v‖))) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg t)
        _ = ‖ℓ‖ * ‖v‖ * (h * K₀ * L) * |t| ^ 2 := by ring
        _ = _ := by rw [sq_abs]
    have hB : |ℓ (R (Pr v))| ≤ ‖ℓ‖ * ‖v‖ * (c₂ * h ^ 2 * (‖P‖ + K₀ * L)) * t ^ 2 := by
      rw [← Real.norm_eq_abs]
      calc ‖ℓ (R (Pr v))‖ ≤ ‖ℓ‖ * (‖R‖ * (‖Pr‖ * ‖v‖)) :=
            (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
              ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
                (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))) (norm_nonneg _))
        _ ≤ ‖ℓ‖ * ((c₂ * (|t| * h) ^ 2) * ((‖P‖ + K₀ * L) * ‖v‖)) := by
            gcongr
        _ = _ := by rw [mul_pow, sq_abs]; ring
    have hpos : 0 ≤ |Λ - 1| := abs_nonneg _
    calc |Λ - 1| * (1 / 2) ≤ |Λ - 1| * ℓ (Pr v) := mul_le_mul_of_nonneg_left hℓPr hpos
      _ = |(Λ - 1) * ℓ (Pr v)| := by
          rw [abs_mul, abs_of_pos (lt_of_lt_of_le (by norm_num) hℓPr)]
      _ = |t * ℓ (H w) + ℓ (R (Pr v))| := by rw [hkey]
      _ ≤ |t * ℓ (H w)| + |ℓ (R (Pr v))| := abs_add_le _ _
      _ ≤ _ := by rw [hK₂_def]; nlinarith [hA, hB]
  have hΛ : |Λ| ≤ Real.exp (2 * K₂ * t ^ 2) := by
    have h1 : |Λ| ≤ 1 + 2 * K₂ * t ^ 2 := by
      have := abs_sub_abs_le_abs_sub Λ 1
      rw [abs_one] at this
      linarith
    exact h1.trans (by linarith [Real.add_one_le_exp (2 * K₂ * t ^ 2)])
  have hexpk : Real.exp (2 * K₂ * t ^ 2) ^ k ≤ Real.exp ((2 * K₂ + 1) * k * t ^ 2) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    nlinarith [sq_nonneg t, Nat.cast_nonneg (α := ℝ) k]
  have hexp1 : 1 ≤ Real.exp ((2 * K₂ + 1) * k * t ^ 2) := Real.one_le_exp (by positivity)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [pow_zero]
    calc ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      _ ≤ (‖P‖ + K₀ * L + 1 + C') * 1 := by nlinarith [norm_nonneg P, mul_nonneg hK₀ hL]
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp1 (by positivity)
  · have h1 : ‖T ^ k‖ ≤ ‖T ^ k - Λ ^ k • Pr‖ + ‖Λ ^ k • Pr‖ := by
      have := norm_add_le (T ^ k - Λ ^ k • Pr) (Λ ^ k • Pr); rwa [sub_add_cancel] at this
    have h2 : ‖T ^ k - Λ ^ k • Pr‖ ≤ C' := (hpow k hk).trans
      (mul_le_of_le_one_right hC' (pow_le_one₀ hχ0 hχ1.le))
    have h3 : ‖Λ ^ k • Pr‖ ≤ Real.exp ((2 * K₂ + 1) * k * t ^ 2) * (‖P‖ + K₀ * L) := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      exact mul_le_mul ((pow_le_pow_left₀ (abs_nonneg _) hΛ k).trans hexpk) hPrn
        (norm_nonneg _) (Real.exp_pos _).le
    change ‖T ^ k‖ ≤ _
    nlinarith [norm_nonneg P, mul_nonneg hK₀ hL]

end Perturbation

end

end ConditionedStableLaws.TwistedOperators
