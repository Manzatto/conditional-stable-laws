import ConditionedStableLaws.L2Bridge
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The eigenvalue expansion for row-dependent twists

Let `T₀` be the normalized transition operator on `L∞(ρ)`, `J : L∞(ρ) → L²(μ)` the embedding, `g`
bounded measurable with `ν(g) = μ(g η) = 0`, and `(Λ, η')` an eigenpair of `T₀ ∘ e^{u g}` with
`μ(η') = 1` and `‖η'‖∞ ≤ C_sp`. Then, for `|u| ‖g‖∞ ≤ δ₀`, `|Λ - 1 - u²/2 (ν(g²) + 2 ∑_{m ≥ 1} μ(g
P̂ᵐ(η g)))| ≤ K |u|³ ‖g‖∞ (ν(g²) + μ(g²))`, with `δ₀, K` depending only on `T₀`, `C_sp` and the
`L²(μ)` constants. This is Step 2 (with `u = t/a_n`, for the real exponential twist); the
first-order eigenfunction correction `w = u ∑_{m ≥ 1} T₀ᵐ(g η)` is Step 1.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Nat

namespace ConditionedStableLaws.TriangularExpansion

noncomputable section

open TwistedOperators L2Bridge

/-! ### Real exponential estimates -/

theorem exp_tail_le {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    Real.exp a - ∑ k ∈ Finset.range N, a ^ k / (k ! : ℝ) ≤ a ^ N * Real.exp a := by
  have hx : HasSum (fun n => a ^ n / (n ! : ℝ)) (Real.exp a) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp a
  have hN := (hasSum_nat_add_iff' N).2 hx
  refine hasSum_le (fun n => ?_) hN (hx.mul_left (a ^ N))
  rw [pow_add, show a ^ n * a ^ N / ((n + N)! : ℝ) = a ^ N * (a ^ n / ((n + N)! : ℝ)) by ring]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (pow_nonneg ha n)
    (by exact_mod_cast Nat.factorial_pos n)
    (by exact_mod_cast Nat.factorial_le (Nat.le_add_right n N))) (pow_nonneg ha N)

theorem abs_exp_partial_le {x : ℝ} (hx : |x| ≤ 1) (N : ℕ) :
    |Real.exp x - ∑ k ∈ Finset.range N, x ^ k / (k ! : ℝ)| ≤ 3 * |x| ^ N := by
  refine (abs_exp_sub_partial_le (le_refl |x|) N).trans ((exp_tail_le (abs_nonneg x) N).trans ?_)
  have h1 : Real.exp |x| ≤ 3 :=
    (Real.exp_le_exp.2 hx).trans Real.exp_one_lt_three.le
  nlinarith [pow_nonneg (abs_nonneg x) N]

theorem abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1) : |Real.exp x - 1| ≤ 3 * |x| := by
  simpa using abs_exp_partial_le hx 1

theorem abs_exp_sub_one_sub_le {x : ℝ} (hx : |x| ≤ 1) : |Real.exp x - 1 - x| ≤ 3 * x ^ 2 := by
  have := abs_exp_partial_le hx 2
  simp [Finset.sum_range_succ] at this
  rwa [show Real.exp x - (1 + x) = Real.exp x - 1 - x by ring] at this

theorem abs_exp_sub_two_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2| ≤ 3 * |x| ^ 3 := by
  have := abs_exp_partial_le hx 3
  simp [Finset.sum_range_succ, Nat.factorial] at this
  rwa [show Real.exp x - (1 + x + x ^ 2 / 2) = Real.exp x - 1 - x - x ^ 2 / 2 by ring] at this

theorem le_of_sq_le_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc; push Not at hc; nlinarith

/-! ### Multipliers through the embedding -/

section Helpers

variable {M : Type*} [MeasurableSpace M]
  {ρ : Measure M} [IsFiniteMeasure ρ] {μ : Measure M}
  [IsProbabilityMeasure μ] (hμρ : μ ≪ ρ)

include hμρ

theorem embed_mulL_ae (q : Multiplier M) (f : Lp ℝ ∞ ρ) :
    (embed μ hμρ (mulL q f) : M → ℝ) =ᵐ[μ] fun y => q.toFun y * f y :=
  (embed_ae hμρ _).trans (hμρ.ae_le (mulL_ae q f))

theorem norm_embed_mulL_le (q : Multiplier M) (f : Lp ℝ ∞ ρ) :
    ‖embed μ hμρ (mulL q f)‖ ≤ q.bound * ‖embed μ hμρ f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [embed_mulL_ae hμρ q f, embed_ae hμρ f] with y h1 h2
  rw [h1, h2, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (q.le_bound y) (abs_nonneg _)

theorem norm_embed_mulL_sq (q : Multiplier M) (f : Lp ℝ ∞ ρ) :
    ‖embed μ hμρ (mulL q f)‖ ^ 2 = ∫ y, q.toFun y ^ 2 * f y ^ 2 ∂μ := by
  rw [SecondMoment.norm_sq_L2]
  exact integral_congr_ae (by
    filter_upwards [embed_mulL_ae hμρ q f] with y hy; rw [hy]; ring)

omit [IsProbabilityMeasure μ] in
theorem mean_mulL {ℓ : Lp ℝ ∞ ρ →L[ℝ] ℝ} (hmean : ∀ f, ℓ f = ∫ y, f y ∂μ) (q : Multiplier M)
    (f : Lp ℝ ∞ ρ) : ℓ (mulL q f) = ∫ y, q.toFun y * f y ∂μ := by
  rw [hmean]; exact integral_congr_ae (hμρ.ae_le (mulL_ae q f))

theorem abs_mean_mulL_le {ℓ : Lp ℝ ∞ ρ →L[ℝ] ℝ} (hmean : ∀ f, ℓ f = ∫ y, f y ∂μ)
    (q : Multiplier M) (f : Lp ℝ ∞ ρ) :
    |ℓ (mulL q f)| ≤ Real.sqrt (∫ y, q.toFun y ^ 2 ∂μ) * ‖embed μ hμρ f‖ := by
  rw [mean_mulL hμρ hmean]
  exact abs_integral_mul_le hμρ q.measurable q.le_bound f

end Helpers

/-! ### The expansion -/

variable {M : Type*} [MeasurableSpace M]
  {ρ : Measure M} [IsFiniteMeasure ρ] {μ : Measure M}
  [IsProbabilityMeasure μ] (hμρ : μ ≪ ρ)

set_option maxHeartbeats 4000000 in
/-- **Steps 1–2 of the triangular-array CLT: the eigenvalue expansion.** -/
theorem eigenvalue_expansion (T₀ : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ) (ℓ : Lp ℝ ∞ ρ →L[ℝ] ℝ)
    (v : Lp ℝ ∞ ρ) {η : M → ℝ} (hηm : Measurable η) {Bη : ℝ} (hBη0 : 0 ≤ Bη)
    (hη0 : ∀ y, 0 ≤ η y)
    (hηB : ∀ y, η y ≤ Bη) (hv : (v : M → ℝ) =ᵐ[ρ] η) (hmean : ∀ f, ℓ f = ∫ y, f y ∂μ)
    (hℓT : ∀ w, ℓ (T₀ w) = ℓ w) (hTv : T₀ v = v) (hℓv : ℓ v = 1)
    {Cop L κ : ℝ} (hCop0 : 0 ≤ Cop) (hL : 0 ≤ L) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hCop : ∀ f, ‖embed μ hμρ (T₀ f)‖ ≤ Cop * ‖embed μ hμρ f‖)
    (hdec : ∀ f, ℓ f = 0 → ∀ m : ℕ, 1 ≤ m →
      ‖embed μ hμρ ((T₀ ^ m) f)‖ ≤ L * κ ^ m * ‖embed μ hμρ f‖)
    {Cg θg : ℝ} (hθ0 : 0 ≤ θg) (hθ1 : θg < 1)
    (hgap : ∀ n : ℕ, 1 ≤ n → ‖T₀ ^ n - ℓ.smulRight v‖ ≤ Cg * θg ^ n)
    {Csp : ℝ} (hCsp0 : 0 ≤ Csp) :
    ∃ δ₀ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : Multiplier M), ∫ y, q.toFun y * η y ∂μ = 0 →
      ∀ u : ℝ, |u| * q.bound ≤ δ₀ → ∀ (Λ : ℝ) (η' : Lp ℝ ∞ ρ),
        T₀ (mulL (expMultiplier q u) η') = Λ • η' → ℓ η' = 1 → ‖η'‖ ≤ Csp →
        |Λ - 1 - u ^ 2 / 2 * (∫ y, q.toFun y ^ 2 * η y ∂μ +
            2 * ∑' m : ℕ, ℓ (mulL q ((T₀ ^ (m + 1)) (mulL q v))))| ≤
          K * |u| ^ 3 * q.bound *
            (∫ y, q.toFun y ^ 2 * η y ∂μ + ∫ y, q.toFun y ^ 2 ∂μ) := by
  set Ci := (1 + L) / (1 - κ) with hCi_def
  have h1κ : 0 < 1 - κ := by linarith
  have hCi0 : 0 ≤ Ci := by positivity
  set sB := Real.sqrt Bη with hsB_def
  have hsB0 : 0 ≤ sB := Real.sqrt_nonneg _
  have hsB2 : sB ^ 2 = Bη := Real.sq_sqrt hBη0
  set sB1 := Real.sqrt (Bη + 1) with hsB1_def
  have hsB10 : 0 ≤ sB1 := Real.sqrt_nonneg _
  have hsB12 : sB1 ^ 2 = Bη + 1 := Real.sq_sqrt (by linarith)
  set δ₀ := min (1 / 2) (1 / (2 * Ci * (3 * Cop + 3 * Csp) + 1)) with hδ₀_def
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (by positivity)
  set C1 := 2 * Ci * (3 * Cop + 2 * Csp) * sB with hC1_def
  have hC10 : 0 ≤ C1 := by positivity
  set C2 := 2 + 3 * C1 with hC2_def
  have hC20 : 0 ≤ C2 := by positivity
  set C0 := L * κ / (1 - κ) * sB with hC0_def
  have hC00 : 0 ≤ C0 := by positivity
  set C3 := Ci * (Cop * (3 * sB + 3 * C1) + C2 * Csp * sB1) with hC3_def
  have hC30 : 0 ≤ C3 := by positivity
  refine ⟨δ₀, hδ₀, 3 + 3 * C0 + 3 * C3, by positivity, fun q hqη u hu Λ η' heig hℓη' hη'b => ?_⟩
  set G := q.bound with hG_def
  have hG0 : 0 ≤ G := q.bound_nonneg
  set J := embed μ hμρ with hJ_def
  set Γ : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := mulL q with hΓ_def
  set Mu : Lp ℝ ∞ ρ →L[ℝ] Lp ℝ ∞ ρ := mulL (expMultiplier q u) with hMu_def
  set δ := |u| * G with hδ_def
  have hδ0 : 0 ≤ δ := by positivity
  have hδ12 : δ ≤ 1 / 2 := hu.trans (min_le_left _ _)
  have hδabs : Ci * (3 * Cop + 3 * Csp) * δ ≤ 1 / 2 := by
    have h1 : δ ≤ 1 / (2 * Ci * (3 * Cop + 3 * Csp) + 1) := hu.trans (min_le_right _ _)
    have hpos : 0 < 2 * Ci * (3 * Cop + 3 * Csp) + 1 := by positivity
    rw [le_div_iff₀ hpos] at h1
    nlinarith [mul_nonneg (mul_nonneg hCi0 (by positivity : 0 ≤ 3 * Cop + 3 * Csp)) hδ0]
  have hqu : ∀ y, |u * q.toFun y| ≤ δ := fun y => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (q.le_bound y) (abs_nonneg u)
  have hx : ∀ y, |u * q.toFun y| ≤ 1 := fun y => (hqu y).trans (by linarith)
  -- The multipliers `e^{uq} - 1` and `e^{uq} - 1 - uq`.
  set φm : Multiplier M :=
    { toFun := fun y => Real.exp (u * q.toFun y) - 1
      measurable := ((measurable_const.mul q.measurable).exp).sub measurable_const
      bound := 3 * δ
      bound_nonneg := by positivity
      le_bound := fun y => (abs_exp_sub_one_le (hx y)).trans
        (mul_le_mul_of_nonneg_left (hqu y) (by norm_num)) }
    with hφm_def
  set ψm : Multiplier M :=
    { toFun := fun y => Real.exp (u * q.toFun y) - 1 - u * q.toFun y
      measurable := (((measurable_const.mul q.measurable).exp).sub measurable_const).sub
        (measurable_const.mul q.measurable)
      bound := 3 * δ ^ 2
      bound_nonneg := by positivity
      le_bound := fun y => (abs_exp_sub_one_sub_le (hx y)).trans (by
        have := hqu y
        have h0 := abs_nonneg (u * q.toFun y)
        rw [← sq_abs]; nlinarith) }
    with hψm_def
  have hΦ : Mu - 1 = mulL φm := by
    ext1 f; apply Lp.ext
    filter_upwards [Lp.coeFn_sub (Mu f) f, mulL_ae (expMultiplier q u) f, mulL_ae φm f]
      with y h1 h2 h3
    rw [sub_apply, one_apply_eq_self, h1, Pi.sub_apply, h2, h3]
    simp only [expMultiplier, hφm_def]
    ring
  have hΨ : mulL φm - u • Γ = mulL ψm := by
    ext1 f; apply Lp.ext
    filter_upwards [Lp.coeFn_sub (mulL φm f) (u • Γ f), mulL_ae φm f,
      Lp.coeFn_smul u (Γ f), mulL_ae q f, mulL_ae ψm f] with y h1 h2 h3 h4 h5
    rw [sub_apply, smul_apply, h1, Pi.sub_apply, h2, h3,
      Pi.smul_apply, h4, h5]
    simp only [hφm_def, hψm_def, smul_eq_mul]
    ring
  -- Integrals of the squares.
  have hqm2 : Measurable fun y => q.toFun y ^ 2 := q.measurable.pow_const 2
  have hq2b : ∀ y, |q.toFun y ^ 2| ≤ G ^ 2 := SecondMoment.sq_bdd q.le_bound
  have hηb : ∀ y, |η y| ≤ Bη := fun y => by rw [abs_of_nonneg (hη0 y)]; exact hηB y
  set ν₂ := ∫ y, q.toFun y ^ 2 * η y ∂μ with hν₂_def
  set μ₂ := ∫ y, q.toFun y ^ 2 ∂μ with hμ₂_def
  set S := ν₂ + μ₂ with hS_def
  have hint_q2η : Integrable (fun y => q.toFun y ^ 2 * η y) μ :=
    SecondMoment.integrable_of_bdd (hqm2.mul hηm) (B := G ^ 2 * Bη) (fun y => by
      rw [abs_mul]; exact mul_le_mul (hq2b y) (hηb y) (abs_nonneg _) (sq_nonneg _))
  have hint_q2 : Integrable (fun y => q.toFun y ^ 2) μ := SecondMoment.integrable_of_bdd hqm2 hq2b
  have hν₂0 : 0 ≤ ν₂ := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hη0 y)
  have hμ₂0 : 0 ≤ μ₂ := integral_nonneg fun y => sq_nonneg _
  have hS0 : 0 ≤ S := by positivity
  have hμ₂G : μ₂ ≤ G ^ 2 := by
    have := SecondMoment.abs_integral_le_of_prob (ν := μ) hq2b
    exact (le_abs_self _).trans this
  have hν₂G : ν₂ ≤ Bη * G ^ 2 := by
    have := SecondMoment.abs_integral_le_of_prob (ν := μ) (f := fun y => q.toFun y ^ 2 * η y)
      (B := G ^ 2 * Bη) (fun y => by
        rw [abs_mul]; exact mul_le_mul (hq2b y) (hηb y) (abs_nonneg _) (sq_nonneg _))
    nlinarith [le_abs_self ν₂]
  set sν := Real.sqrt ν₂ with hsν_def
  set sμ := Real.sqrt μ₂ with hsμ_def
  set sS := Real.sqrt S with hsS_def
  have hsν0 : 0 ≤ sν := Real.sqrt_nonneg _
  have hsμ0 : 0 ≤ sμ := Real.sqrt_nonneg _
  have hsS0 : 0 ≤ sS := Real.sqrt_nonneg _
  have hsν2 : sν ^ 2 = ν₂ := Real.sq_sqrt hν₂0
  have hsμ2 : sμ ^ 2 = μ₂ := Real.sq_sqrt hμ₂0
  have hsS2 : sS ^ 2 = S := Real.sq_sqrt hS0
  have hsμG : sμ ≤ G := le_of_sq_le_sq' hG0 (by rw [hsμ2]; exact hμ₂G)
  have hsνG : sν ≤ sB * G := le_of_sq_le_sq' (by positivity) (by rw [hsν2, mul_pow, hsB2]; exact hν₂G)
  have hsνS : sν ≤ sS := le_of_sq_le_sq' hsS0 (by rw [hsν2, hsS2]; linarith)
  have hsμS : sμ ≤ sS := le_of_sq_le_sq' hsS0 (by rw [hsμ2, hsS2]; linarith)
  have hsμν : sμ * sν ≤ S := by nlinarith [sq_nonneg (sμ - sν)]
  have hsμsS : sμ * sS ≤ S := by nlinarith
  have hsSG : sS ≤ sB1 * G := le_of_sq_le_sq' (by positivity) (by
    rw [hsS2, mul_pow, hsB12]; nlinarith)
  have hSG : S ≤ sB1 * G * sS := by nlinarith
  -- Pointwise bounds through the embedding.
  have hvμ : (v : M → ℝ) =ᵐ[μ] η := hμρ.ae_le hv
  have hφ2 : ∀ y, (Real.exp (u * q.toFun y) - 1) ^ 2 ≤ 9 * u ^ 2 * q.toFun y ^ 2 := fun y => by
    have h1 := abs_exp_sub_one_le (hx y)
    have h2 := abs_nonneg (Real.exp (u * q.toFun y) - 1)
    rw [abs_mul] at h1
    rw [← sq_abs, show 9 * u ^ 2 * q.toFun y ^ 2 = (3 * (|u| * |q.toFun y|)) ^ 2 by
      rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring]
    exact pow_le_pow_left₀ h2 h1 2
  have hψ2 : ∀ y, (Real.exp (u * q.toFun y) - 1 - u * q.toFun y) ^ 2 ≤
      9 * u ^ 4 * G ^ 2 * q.toFun y ^ 2 := fun y => by
    have h1 := abs_exp_sub_one_sub_le (hx y)
    have h2 := abs_nonneg (Real.exp (u * q.toFun y) - 1 - u * q.toFun y)
    have h3 : 3 * (u * q.toFun y) ^ 2 ≤ 3 * u ^ 2 * G * |q.toFun y| := by
      rw [mul_pow, ← sq_abs (q.toFun y)]
      have h4 : |q.toFun y| ^ 2 ≤ G * |q.toFun y| := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (q.le_bound y) (abs_nonneg _)
      have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 3 * u ^ 2)
      linarith
    rw [← sq_abs, show 9 * u ^ 4 * G ^ 2 * q.toFun y ^ 2 = (3 * u ^ 2 * G * |q.toFun y|) ^ 2 by
      rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring]
    exact pow_le_pow_left₀ h2 (h1.trans h3) 2
  have hη2 : ∀ y, η y ^ 2 ≤ Bη * η y := fun y => by nlinarith [hη0 y, hηB y]
  have hJΦ : ∀ f, ‖J (mulL φm f)‖ ≤ 3 * δ * ‖J f‖ := fun f => norm_embed_mulL_le hμρ φm f
  have hJΦv : ‖J (mulL φm v)‖ ≤ 3 * |u| * sB * sν := by
    refine le_of_sq_le_sq' (by positivity) ?_
    rw [norm_embed_mulL_sq hμρ, integral_congr_ae (by
      filter_upwards [hvμ] with y hy; rw [hy])]
    calc ∫ y, φm.toFun y ^ 2 * η y ^ 2 ∂μ ≤ ∫ y, 9 * u ^ 2 * Bη * (q.toFun y ^ 2 * η y) ∂μ := by
          refine integral_mono (SecondMoment.integrable_of_bdd (φm.measurable.pow_const 2 |>.mul
            (hηm.pow_const 2)) (B := (3 * δ) ^ 2 * Bη ^ 2) (fun y => by
              rw [abs_mul]; exact mul_le_mul (SecondMoment.sq_bdd φm.le_bound y)
                (SecondMoment.sq_bdd hηb y) (abs_nonneg _) (sq_nonneg _)))
            (hint_q2η.const_mul _) (fun y => ?_)
          have h1 := hφ2 y
          have h2 := hη2 y
          simp only [hφm_def]
          have h3 : 0 ≤ 9 * u ^ 2 * q.toFun y ^ 2 := by positivity
          calc (Real.exp (u * q.toFun y) - 1) ^ 2 * η y ^ 2
              ≤ (9 * u ^ 2 * q.toFun y ^ 2) * (Bη * η y) := mul_le_mul h1 h2 (sq_nonneg _) h3
            _ = _ := by ring
      _ = (3 * |u| * sB * sν) ^ 2 := by
          rw [integral_const_mul, mul_pow, mul_pow, mul_pow, sq_abs, hsB2, hsν2]; ring
  have hsqrtφ : Real.sqrt (∫ y, φm.toFun y ^ 2 ∂μ) ≤ 3 * |u| * sμ := by
    rw [show 3 * |u| * sμ = Real.sqrt ((3 * |u|) ^ 2 * μ₂) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    rw [hμ₂_def, ← integral_const_mul]
    exact integral_mono (SecondMoment.integrable_of_bdd (φm.measurable.pow_const 2)
      (SecondMoment.sq_bdd φm.le_bound)) (hint_q2.const_mul _) (fun y => by
        have := hφ2 y; simp only [hφm_def]; rw [mul_pow, sq_abs]; linarith)
  have hℓΦ : ∀ f, |ℓ (mulL φm f)| ≤ 3 * |u| * sμ * ‖J f‖ := fun f =>
    (abs_mean_mulL_le hμρ hmean φm f).trans (mul_le_mul_of_nonneg_right hsqrtφ (norm_nonneg _))
  have hsqrtψ : Real.sqrt (∫ y, ψm.toFun y ^ 2 ∂μ) ≤ 3 * u ^ 2 * G * sμ := by
    rw [show 3 * u ^ 2 * G * sμ = Real.sqrt ((3 * u ^ 2 * G) ^ 2 * μ₂) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    rw [hμ₂_def, ← integral_const_mul]
    exact integral_mono (SecondMoment.integrable_of_bdd (ψm.measurable.pow_const 2)
      (SecondMoment.sq_bdd ψm.le_bound)) (hint_q2.const_mul _) (fun y => by
        have := hψ2 y; simp only [hψm_def]; nlinarith)
  have hℓΨ : ∀ f, |ℓ (mulL ψm f)| ≤ 3 * u ^ 2 * G * sμ * ‖J f‖ := fun f =>
    (abs_mean_mulL_le hμρ hmean ψm f).trans (mul_le_mul_of_nonneg_right hsqrtψ (norm_nonneg _))
  have hJΨv : ‖J (mulL ψm v)‖ ≤ 3 * u ^ 2 * G * sB * sν := by
    refine le_of_sq_le_sq' (by positivity) ?_
    rw [norm_embed_mulL_sq hμρ, integral_congr_ae (by
      filter_upwards [hvμ] with y hy; rw [hy])]
    calc ∫ y, ψm.toFun y ^ 2 * η y ^ 2 ∂μ ≤
          ∫ y, 9 * u ^ 4 * G ^ 2 * Bη * (q.toFun y ^ 2 * η y) ∂μ := by
          refine integral_mono (SecondMoment.integrable_of_bdd (ψm.measurable.pow_const 2 |>.mul
            (hηm.pow_const 2)) (B := (3 * δ ^ 2) ^ 2 * Bη ^ 2) (fun y => by
              rw [abs_mul]; exact mul_le_mul (SecondMoment.sq_bdd ψm.le_bound y)
                (SecondMoment.sq_bdd hηb y) (abs_nonneg _) (sq_nonneg _)))
            (hint_q2η.const_mul _) (fun y => ?_)
          have h1 := hψ2 y
          have h2 := hη2 y
          simp only [hψm_def]
          have h3 : 0 ≤ 9 * u ^ 4 * G ^ 2 * q.toFun y ^ 2 := by positivity
          calc (Real.exp (u * q.toFun y) - 1 - u * q.toFun y) ^ 2 * η y ^ 2
              ≤ (9 * u ^ 4 * G ^ 2 * q.toFun y ^ 2) * (Bη * η y) :=
                mul_le_mul h1 h2 (sq_nonneg _) h3
            _ = _ := by ring
      _ = (3 * u ^ 2 * G * sB * sν) ^ 2 := by
          rw [integral_const_mul, mul_pow, mul_pow, mul_pow, mul_pow, hsB2, hsν2]; ring
  have hJΓv : ‖J (Γ v)‖ ≤ sB * sν := by
    refine le_of_sq_le_sq' (by positivity) ?_
    rw [norm_embed_mulL_sq hμρ, integral_congr_ae (by
      filter_upwards [hvμ] with y hy; rw [hy])]
    calc ∫ y, q.toFun y ^ 2 * η y ^ 2 ∂μ ≤ ∫ y, Bη * (q.toFun y ^ 2 * η y) ∂μ := by
          refine integral_mono (SecondMoment.integrable_of_bdd (hqm2.mul (hηm.pow_const 2))
            (B := G ^ 2 * Bη ^ 2) (fun y => by
              rw [abs_mul]; exact mul_le_mul (hq2b y) (SecondMoment.sq_bdd hηb y) (abs_nonneg _)
                (sq_nonneg _))) (hint_q2η.const_mul _) (fun y => ?_)
          have := hη2 y
          calc q.toFun y ^ 2 * η y ^ 2 ≤ q.toFun y ^ 2 * (Bη * η y) :=
                mul_le_mul_of_nonneg_left this (sq_nonneg _)
            _ = _ := by ring
      _ = (sB * sν) ^ 2 := by rw [integral_const_mul, mul_pow, hsB2, hsν2]
  have hℓΓ0 : ℓ (Γ v) = 0 := by
    rw [mean_mulL hμρ hmean, integral_congr_ae (by
      filter_upwards [hvμ] with y hy; rw [hy])]
    exact hqη
  -- `ℓ(Φ v) = u² ν(q²)/2 + O(|u|³ G ν(q²))`.
  have hℓΦv : |ℓ (mulL φm v) - u ^ 2 / 2 * ν₂| ≤ 3 * |u| ^ 3 * G * ν₂ := by
    rw [mean_mulL hμρ hmean, integral_congr_ae (by
      filter_upwards [hvμ] with y hy; rw [hy])]
    have hiφ : Integrable (fun y => φm.toFun y * η y) μ :=
      SecondMoment.integrable_of_bdd (φm.measurable.mul hηm) (B := 3 * δ * Bη) (fun y => by
        rw [abs_mul]; exact mul_le_mul (φm.le_bound y) (hηb y) (abs_nonneg _) φm.bound_nonneg)
    have hiqη : Integrable (fun y => q.toFun y * η y) μ :=
      SecondMoment.integrable_of_bdd (q.measurable.mul hηm) (B := G * Bη) (fun y => by
        rw [abs_mul]; exact mul_le_mul (q.le_bound y) (hηb y) (abs_nonneg _) hG0)
    have hi1 : Integrable (fun y => u * (q.toFun y * η y)) μ := hiqη.const_mul u
    have hi2 : Integrable (fun y => u ^ 2 / 2 * (q.toFun y ^ 2 * η y)) μ := hint_q2η.const_mul _
    have hi12 : Integrable (fun y => φm.toFun y * η y - u * (q.toFun y * η y)) μ := hiφ.sub hi1
    have hsplit : ∫ y, φm.toFun y * η y ∂μ - u ^ 2 / 2 * ν₂ =
        ∫ y, (φm.toFun y * η y - u * (q.toFun y * η y) - u ^ 2 / 2 * (q.toFun y ^ 2 * η y)) ∂μ := by
      rw [integral_sub hi12 hi2, integral_sub hiφ hi1, integral_const_mul, integral_const_mul, hqη,
        mul_zero, sub_zero]
    rw [hsplit]
    have hpt : ∀ y, |φm.toFun y * η y - u * (q.toFun y * η y) - u ^ 2 / 2 * (q.toFun y ^ 2 * η y)|
        ≤ 3 * |u| ^ 3 * G * (q.toFun y ^ 2 * η y) := by
      intro y
      have h1 := abs_exp_sub_two_le (hx y)
      have heq : φm.toFun y * η y - u * (q.toFun y * η y) - u ^ 2 / 2 * (q.toFun y ^ 2 * η y) =
          (Real.exp (u * q.toFun y) - 1 - u * q.toFun y - (u * q.toFun y) ^ 2 / 2) * η y := by
        simp only [hφm_def]; ring
      rw [heq, abs_mul, abs_of_nonneg (hη0 y)]
      have h4 : |q.toFun y| ^ 3 ≤ G * q.toFun y ^ 2 := by
        rw [pow_succ, ← sq_abs (q.toFun y), mul_comm G]
        exact mul_le_mul_of_nonneg_left (q.le_bound y) (sq_nonneg _)
      have h3 : 3 * |u * q.toFun y| ^ 3 ≤ 3 * |u| ^ 3 * G * q.toFun y ^ 2 := by
        rw [abs_mul, mul_pow]
        have := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 3 * |u| ^ 3)
        linarith
      calc |Real.exp (u * q.toFun y) - 1 - u * q.toFun y - (u * q.toFun y) ^ 2 / 2| * η y
          ≤ 3 * |u * q.toFun y| ^ 3 * η y := mul_le_mul_of_nonneg_right h1 (hη0 y)
        _ ≤ 3 * |u| ^ 3 * G * q.toFun y ^ 2 * η y := mul_le_mul_of_nonneg_right h3 (hη0 y)
        _ = _ := by ring
    calc |∫ y, (φm.toFun y * η y - u * (q.toFun y * η y) - u ^ 2 / 2 * (q.toFun y ^ 2 * η y)) ∂μ|
        ≤ ∫ y, |φm.toFun y * η y - u * (q.toFun y * η y) - u ^ 2 / 2 * (q.toFun y ^ 2 * η y)| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, 3 * |u| ^ 3 * G * (q.toFun y ^ 2 * η y) ∂μ :=
          integral_mono (hi12.sub hi2).abs (hint_q2η.const_mul _) hpt
      _ = 3 * |u| ^ 3 * G * ν₂ := integral_const_mul _ _
  -- The eigen relation and the first-order bounds.
  set y := η' - v with hy_def
  have hℓy : ℓ y = 0 := by rw [hy_def, map_sub, hℓη', hℓv, sub_self]
  have hMu : Mu = 1 + mulL φm := by rw [← hΦ]; abel
  have h1 : T₀ η' + T₀ (mulL φm η') = Λ • η' := by
    rw [← map_add, ← heig, hMu, add_apply, one_apply_eq_self]
  have heq1 : y - T₀ y = T₀ (mulL φm η') - (Λ - 1) • η' := by
    rw [hy_def, map_sub, hTv, sub_smul, one_smul, ← h1]; abel
  have hΛ1 : Λ - 1 = ℓ (mulL φm η') := by
    have hT : T₀ (mulL φm η') = y - T₀ y + (Λ - 1) • η' := by rw [heq1]; abel
    calc Λ - 1 = ℓ (y - T₀ y + (Λ - 1) • η') := by
          rw [map_add, map_sub, hℓT, map_smul, hℓη', sub_self, zero_add, smul_eq_mul, mul_one]
      _ = ℓ (T₀ (mulL φm η')) := by rw [hT]
      _ = ℓ (mulL φm η') := hℓT _
  have hη'eq : η' = v + y := by rw [hy_def]; abel
  have hΦη' : mulL φm η' = mulL φm v + mulL φm y := by rw [hη'eq, map_add]
  have hΛsplit : Λ - 1 = ℓ (mulL φm v) + ℓ (mulL φm y) := by rw [hΛ1, hΦη', map_add]
  have hJη' : ‖J η'‖ ≤ Csp := (norm_embed_le hμρ η').trans hη'b
  set Ny := ‖J y‖ with hNy_def
  have hNy0 : 0 ≤ Ny := norm_nonneg _
  have hℓΦvabs : |ℓ (mulL φm v)| ≤ 2 * u ^ 2 * ν₂ := by
    have hc : 3 * |u| ^ 3 * G * ν₂ ≤ (3 / 2) * u ^ 2 * ν₂ := by
      have e : 3 * |u| ^ 3 * G * ν₂ = 3 * (u ^ 2 * ν₂) * δ := by rw [hδ_def, ← sq_abs u]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hδ12 (by positivity : (0:ℝ) ≤ 3 * (u ^ 2 * ν₂))
      linarith
    have := abs_sub_abs_le_abs_sub (ℓ (mulL φm v)) (u ^ 2 / 2 * ν₂)
    rw [abs_of_nonneg (by positivity : 0 ≤ u ^ 2 / 2 * ν₂)] at this
    linarith
  have hsμδ : 3 * |u| * sμ ≤ 3 * δ := by
    rw [hδ_def]
    have := mul_le_mul_of_nonneg_left hsμG (by positivity : (0:ℝ) ≤ 3 * |u|)
    linarith
  have hΛb00 : |Λ - 1| ≤ 2 * u ^ 2 * ν₂ + 3 * |u| * sμ * Ny := by
    rw [hΛsplit]
    exact (abs_add_le _ _).trans (add_le_add hℓΦvabs (hℓΦ y))
  have hΛb0 : |Λ - 1| ≤ 2 * u ^ 2 * ν₂ + 3 * δ * Ny :=
    hΛb00.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsμδ hNy0))
  have hinv := inverse_bound T₀ ℓ J hℓT hL hκ0 hκ1 hdec hℓy heq1
  have hRHS : ‖J (T₀ (mulL φm η') - (Λ - 1) • η')‖ ≤
      Cop * (3 * |u| * sB * sν + 3 * δ * Ny) + |Λ - 1| * Csp := by
    rw [map_sub, map_smul]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (hCop _).trans (mul_le_mul_of_nonneg_left ?_ hCop0)
      rw [hΦη', map_add]
      exact (norm_add_le _ _).trans (add_le_add hJΦv (hJΦ y))
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hJη' (abs_nonneg _)
  have hu2 : u ^ 2 * ν₂ ≤ |u| * sB * sν := by
    have e1 : u ^ 2 * ν₂ = (|u| * sν) * (|u| * sν) := by rw [← hsν2, ← sq_abs u]; ring
    have e2 : |u| * sν ≤ δ * sB := by
      rw [hδ_def]
      have := mul_le_mul_of_nonneg_left hsνG (abs_nonneg u)
      linarith
    have e3 := mul_le_mul_of_nonneg_left e2 (by positivity : (0:ℝ) ≤ |u| * sν)
    have e4 : δ * sB ≤ sB := by nlinarith
    have e5 := mul_le_mul_of_nonneg_left e4 (by positivity : (0:ℝ) ≤ |u| * sν)
    nlinarith
  have hNy : Ny ≤ C1 * |u| * sν := by
    have hL1 : |Λ - 1| * Csp ≤ (2 * u ^ 2 * ν₂ + 3 * δ * Ny) * Csp :=
      mul_le_mul_of_nonneg_right hΛb0 hCsp0
    have h2 : Ny ≤ Ci * (Cop * (3 * |u| * sB * sν + 3 * δ * Ny) +
        (2 * u ^ 2 * ν₂ + 3 * δ * Ny) * Csp) :=
      hinv.trans (mul_le_mul_of_nonneg_left (hRHS.trans (add_le_add le_rfl hL1)) hCi0)
    have habs := mul_le_mul_of_nonneg_right hδabs hNy0
    have hp := mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ 2 * Ci * Csp)
    rw [hC1_def]
    linear_combination 2 * h2 + 2 * habs + 2 * hp
  have hΛb : |Λ - 1| ≤ C2 * u ^ 2 * S := by
    have hp1 := mul_le_mul_of_nonneg_left hNy (by positivity : (0:ℝ) ≤ 3 * |u| * sμ)
    have hp2 : |u| * sμ * (|u| * sν) ≤ u ^ 2 * S := by
      have e : |u| * sμ * (|u| * sν) = u ^ 2 * (sμ * sν) := by rw [← sq_abs u]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hsμν (sq_nonneg u)
    have hν₂S : ν₂ ≤ S := by linarith
    have hp3 := mul_le_mul_of_nonneg_left hν₂S (by positivity : (0:ℝ) ≤ 2 * u ^ 2)
    have hp4 := mul_le_mul_of_nonneg_left hp2 (by positivity : (0:ℝ) ≤ 3 * C1)
    rw [hC2_def]
    linear_combination hΛb00 + hp1 + hp3 + hp4
  -- The first-order eigenfunction correction `w = u ∑_{m ≥ 1} T₀ᵐ(Γ v)` (Step 1).
  have hTk : ∀ k : ℕ, ℓ ((T₀ ^ k) (Γ v)) = 0 := by
    intro k
    induction k with
    | zero => simpa using hℓΓ0
    | succ k ih => rw [pow_succ', mul_apply_eq_comp, hℓT, ih]
  have hnormk : ∀ k : ℕ, 1 ≤ k → ‖(T₀ ^ k) (Γ v)‖ ≤ Cg * θg ^ k * ‖Γ v‖ := by
    intro k hk
    have : (T₀ ^ k - ℓ.smulRight v) (Γ v) = (T₀ ^ k) (Γ v) := by simp [hℓΓ0]
    rw [← this]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hgap k hk) (norm_nonneg _))
  have hsumm : Summable fun m : ℕ => (T₀ ^ (m + 1)) (Γ v) := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => |Cg| * ‖Γ v‖ * θg ^ (m + 1)) ?_ ?_
    · exact ((summable_geometric_of_lt_one hθ0 hθ1).mul_left (|Cg| * ‖Γ v‖ * θg)).congr
        fun m => by rw [pow_succ]; ring
    · intro m
      refine (hnormk (m + 1) (by omega)).trans ?_
      have : Cg * θg ^ (m + 1) * ‖Γ v‖ ≤ |Cg| * θg ^ (m + 1) * ‖Γ v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
          (pow_nonneg hθ0 _)) (norm_nonneg _)
      linarith
  set W := ∑' m : ℕ, (T₀ ^ (m + 1)) (Γ v) with hW_def
  have h1W : W = (T₀ ^ (0 + 1)) (Γ v) + ∑' m : ℕ, (T₀ ^ (m + 1 + 1)) (Γ v) :=
    hsumm.tsum_eq_zero_add
  have h2W : T₀ W = ∑' m : ℕ, (T₀ ^ (m + 1 + 1)) (Γ v) := by
    rw [hW_def, ContinuousLinearMap.map_tsum _ hsumm]
    congr 1; funext m; rw [pow_succ' T₀ (m + 1), mul_apply_eq_comp]
  have hWT : W - T₀ W = T₀ (Γ v) := by
    rw [h2W]; nth_rewrite 1 [h1W]; simp
  have hℓW : ℓ W = 0 := by
    rw [hW_def, ContinuousLinearMap.map_tsum _ hsumm]; simp only [hTk, tsum_zero]
  have hJW : ‖J W‖ ≤ L * κ / (1 - κ) * ‖J (Γ v)‖ := by
    have hJs : HasSum (fun m => J ((T₀ ^ (m + 1)) (Γ v))) (J W) := hsumm.hasSum.mapL J
    have hg : HasSum (fun m : ℕ => L * κ ^ (m + 1) * ‖J (Γ v)‖) (L * κ / (1 - κ) * ‖J (Γ v)‖) := by
      have := (hasSum_geometric_of_lt_one hκ0 hκ1).mul_left (L * κ * ‖J (Γ v)‖)
      convert this using 1
      · funext m; rw [pow_succ]; ring
      · field_simp
    exact hJs.norm_le_of_bounded hg fun m => hdec _ hℓΓ0 (m + 1) (by omega)
  have hJuW : ‖J (u • W)‖ ≤ |u| * C0 * sν := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, hC0_def]
    have := hJW.trans (mul_le_mul_of_nonneg_left hJΓv (by positivity))
    calc |u| * ‖J W‖ ≤ |u| * (L * κ / (1 - κ) * (sB * sν)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg u)
      _ = _ := by ring
  -- The second-order remainder `z = y - w`.
  set z := y - u • W with hz_def
  have hΨv : mulL ψm v = mulL φm v - u • Γ v := by
    rw [← hΨ]; rfl
  have heqz : z - T₀ z = T₀ (mulL ψm v) + T₀ (mulL φm y) - (Λ - 1) • η' := by
    have e1 : z - T₀ z = (y - T₀ y) - u • (W - T₀ W) := by
      rw [hz_def, map_sub, map_smul, smul_sub]; abel
    have e2 : T₀ (mulL ψm v) = T₀ (mulL φm v) - u • T₀ (Γ v) := by
      rw [hΨv, map_sub, map_smul]
    rw [e1, heq1, hWT, e2, hΦη', map_add]
    abel
  have hℓz : ℓ z = 0 := by rw [hz_def, map_sub, map_smul, hℓy, hℓW, smul_zero, sub_zero]
  have hinvz := inverse_bound T₀ ℓ J hℓT hL hκ0 hκ1 hdec hℓz heqz
  have hNz : ‖J z‖ ≤ C3 * u ^ 2 * G * sS := by
    have hR : ‖J (T₀ (mulL ψm v) + T₀ (mulL φm y) - (Λ - 1) • η')‖ ≤
        Cop * (3 * u ^ 2 * G * sB * sν + 3 * δ * Ny) + |Λ - 1| * Csp := by
      rw [map_sub, map_add, map_smul]
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
      · rw [mul_add]
        exact add_le_add ((hCop _).trans (mul_le_mul_of_nonneg_left hJΨv hCop0))
          ((hCop _).trans (mul_le_mul_of_nonneg_left (hJΦ y) hCop0))
      · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hJη' (abs_nonneg _)
    have hq1 : 3 * u ^ 2 * G * sB * sν ≤ 3 * sB * (u ^ 2 * G * sS) := by
      have := mul_le_mul_of_nonneg_left hsνS (by positivity : (0:ℝ) ≤ 3 * u ^ 2 * G * sB)
      linarith
    have hq2 : 3 * δ * Ny ≤ 3 * C1 * (u ^ 2 * G * sS) := by
      have h1 := mul_le_mul_of_nonneg_left hNy (by positivity : (0:ℝ) ≤ 3 * δ)
      have h2 := mul_le_mul_of_nonneg_left hsνS (by positivity : (0:ℝ) ≤ 3 * C1 * u ^ 2 * G)
      have e : 3 * δ * (C1 * |u| * sν) = 3 * C1 * u ^ 2 * G * sν := by
        rw [hδ_def, ← sq_abs u]; ring
      linarith
    have hq3 : |Λ - 1| * Csp ≤ C2 * Csp * sB1 * (u ^ 2 * G * sS) := by
      have h1 := mul_le_mul_of_nonneg_right hΛb hCsp0
      have h2 := mul_le_mul_of_nonneg_left hSG (by positivity : (0:ℝ) ≤ C2 * u ^ 2 * Csp)
      linarith
    have hR' := hR.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hq1 hq2) hCop0) hq3)
    have := hinvz.trans (mul_le_mul_of_nonneg_left hR' hCi0)
    rw [hC3_def]
    linarith
  -- The expansion.
  have hy_split : y = u • W + z := by rw [hz_def]; abel
  have hΦsplit : mulL φm = mulL ψm + u • Γ := by rw [← hΨ]; abel
  have hΓW : ℓ (Γ W) = ∑' m : ℕ, ℓ (mulL q ((T₀ ^ (m + 1)) (mulL q v))) := by
    have := (ℓ.comp Γ).map_tsum hsumm
    simpa [W] using this
  have hφW : ℓ (mulL φm (u • W)) = ℓ (mulL ψm (u • W)) + u * u * ℓ (Γ W) := by
    rw [hΦsplit]
    simp only [add_apply, smul_apply, map_smul, map_add,
      smul_eq_mul]
    ring
  have e1 : ℓ (mulL φm y) = ℓ (mulL ψm (u • W)) + u * u * ℓ (Γ W) + ℓ (mulL φm z) := by
    rw [hy_split, map_add, map_add, hφW]
  have hexp : Λ - 1 - u ^ 2 / 2 * (ν₂ + 2 * ∑' m : ℕ, ℓ (mulL q ((T₀ ^ (m + 1)) (mulL q v)))) =
      (ℓ (mulL φm v) - u ^ 2 / 2 * ν₂) + ℓ (mulL ψm (u • W)) + ℓ (mulL φm z) := by
    rw [hΛsplit, e1, hΓW]
    ring
  rw [hexp]
  have t1 : |ℓ (mulL φm v) - u ^ 2 / 2 * ν₂| ≤ 3 * |u| ^ 3 * G * S := by
    refine hℓΦv.trans ?_
    have : ν₂ ≤ S := by linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have t2 : |ℓ (mulL ψm (u • W))| ≤ 3 * C0 * |u| ^ 3 * G * S := by
    refine (hℓΨ _).trans ?_
    have h1 := mul_le_mul_of_nonneg_left hJuW (by positivity : (0:ℝ) ≤ 3 * u ^ 2 * G * sμ)
    have h2 := mul_le_mul_of_nonneg_left hsμν (by positivity : (0:ℝ) ≤ 3 * C0 * |u| ^ 3 * G)
    have e : 3 * u ^ 2 * G * sμ * (|u| * C0 * sν) = 3 * C0 * |u| ^ 3 * G * (sμ * sν) := by
      rw [← sq_abs u]; ring
    linarith
  have t3 : |ℓ (mulL φm z)| ≤ 3 * C3 * |u| ^ 3 * G * S := by
    refine (hℓΦ z).trans ?_
    have h1 := mul_le_mul_of_nonneg_left hNz (by positivity : (0:ℝ) ≤ 3 * |u| * sμ)
    have h2 := mul_le_mul_of_nonneg_left hsμsS (by positivity : (0:ℝ) ≤ 3 * C3 * |u| ^ 3 * G)
    have e : 3 * |u| * sμ * (C3 * u ^ 2 * G * sS) = 3 * C3 * |u| ^ 3 * G * (sμ * sS) := by
      rw [← sq_abs u]; ring
    linarith
  calc |ℓ (mulL φm v) - u ^ 2 / 2 * ν₂ + ℓ (mulL ψm (u • W)) + ℓ (mulL φm z)|
      ≤ |ℓ (mulL φm v) - u ^ 2 / 2 * ν₂| + |ℓ (mulL ψm (u • W))| + |ℓ (mulL φm z)| :=
        abs_add_three _ _ _
    _ ≤ 3 * |u| ^ 3 * G * S + 3 * C0 * |u| ^ 3 * G * S + 3 * C3 * |u| ^ 3 * G * S :=
        add_le_add (add_le_add t1 t2) t3
    _ = (3 + 3 * C0 + 3 * C3) * |u| ^ 3 * G * S := by ring

end

end ConditionedStableLaws.TriangularExpansion
