import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

/-!
# Independent compensated series in L²

Summable second moments of centered independent variables yield an L² random variable. Convergence
is proved using Hilbert-space orthogonality.
-/

open Filter MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace ConditionedStableLaws.CompensatedSeries

/-- Pairwise orthogonal vectors are summable when their squared norms are. -/
theorem summable_of_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : ℕ → E)
    (hf : Pairwise (fun i j => inner ℝ (f i) (f j) = 0))
    (hs : Summable (fun i => ‖f i‖ ^ 2)) : Summable f := by
  let G : ℕ → Submodule ℝ E := fun i => Submodule.span ℝ {f i}
  have hG : OrthogonalFamily ℝ (fun i => G i) (fun i => (G i).subtypeₗᵢ) := by
    intro i j hij v w
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.property
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp w.property
    change inner ℝ v.val w.val = 0
    rw [← ha, ← hb, inner_smul_left, inner_smul_right, hf hij]
    simp
  let v : ∀ i, G i := fun i => ⟨f i, Submodule.mem_span_singleton_self _⟩
  exact (hG.summable_iff_norm_sq_summable v).mpr hs

/-- The squared norm of an orthogonal series is the sum of squared norms. -/
theorem norm_tsum_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : ℕ → E)
    (hf : Pairwise (fun i j => inner ℝ (f i) (f j) = 0))
    (hs : Summable (fun i => ‖f i‖ ^ 2)) :
    ‖∑' i, f i‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have hnorm (s : Finset ℕ) : ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sum]
    simp_rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · exact real_inner_self_eq_norm_sq _
    · intro j _ hji
      exact hf hji
    · exact fun h => (h hi).elim
  have ht := ((summable_of_orthogonal f hf hs).hasSum.tendsto_sum_nat).norm.pow 2
  have ht' := hs.hasSum.tendsto_sum_nat
  simp_rw [hnorm] at ht
  exact tendsto_nhds_unique ht ht'

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
  (X : ℕ → Ω → ℝ) (hX : ∀ n, MemLp (X n) 2 P)

/-- Each variable as an element of the Hilbert space L². -/
def term (n : ℕ) : Lp ℝ 2 P := (hX n).toLp (X n)

/-- The compensated-series random variable, represented by the L² sum. -/
def sumLp : Lp ℝ 2 P := ∑' n, term P X hX n

def sumVariable : Ω → ℝ := sumLp P X hX

/-- The L² inner product is the cross moment. -/
theorem inner_term (i j : ℕ) :
    inner ℝ (term P X hX i) (term P X hX j) = ∫ ω, X i ω * X j ω ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hX i).coeFn_toLp, (hX j).coeFn_toLp] with ω hi hj
  simp only [term] at *
  rw [hi, hj, RCLike.inner_apply, conj_trivial]
  ring

/-- The norm squared is the second moment. -/
theorem norm_term_sq (i : ℕ) : ‖term P X hX i‖ ^ 2 = ∫ ω, (X i ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, inner_term]
  congr 1
  funext ω
  ring

/-- Independence and centering give orthogonality in L². -/
theorem orthogonal_terms (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0) :
    Pairwise (fun i j => inner ℝ (term P X hX i) (term P X hX j) = 0) := by
  intro i j hij
  rw [inner_term, (hi.indepFun hij).integral_fun_mul_eq_mul_integral
    (hX i).aestronglyMeasurable (hX j).aestronglyMeasurable, hc i, zero_mul]

/-- The centered independent L² terms form a summable series. -/
theorem summable_terms (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) : Summable (term P X hX) := by
  apply summable_of_orthogonal _ (orthogonal_terms P X hX hi hc)
  simpa only [norm_term_sq] using hs

/-- Finite partial sums use the original real random variables. -/
def partialSum (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range n, X i ω

theorem partialSum_ae (n : ℕ) :
    (fun ω => (∑ i ∈ Finset.range n, term P X hX i) ω) =ᵐ[P] partialSum X n := by
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n) (term P X hX),
    ae_all_iff.mpr (fun i => (hX i).coeFn_toLp)] with ω hω hterms
  rw [hω]
  simp only [Finset.sum_apply, partialSum]
  exact Finset.sum_congr rfl (fun i _ => hterms i)

include hX in
theorem memLp_partialSum (n : ℕ) : MemLp (partialSum X n) 2 P :=
  (Lp.memLp _).ae_eq (partialSum_ae P X hX n)

theorem measurable_sumVariable : Measurable (sumVariable P X hX) :=
  (Lp.stronglyMeasurable _).measurable

theorem memLp_sumVariable : MemLp (sumVariable P X hX) 2 P := Lp.memLp _

/-- The compensated sum is the L² limit of the finite sums. -/
theorem partialSum_tendsto_L2 (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, term P X hX i) atTop (𝓝 (sumLp P X hX)) :=
  (summable_terms P X hX hi hc hs).tendsto_sum_tsum_nat

/-- Convergence in the L² seminorm of the real random variables. -/
theorem partialSum_tendsto_eLpNorm (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) :
    Tendsto (fun n => eLpNorm (partialSum X n - sumVariable P X hX) 2 P) atTop (𝓝 0) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
    (partialSum_tendsto_L2 P X hX hi hc hs)
  apply ht.congr
  intro n
  exact eLpNorm_congr_ae ((partialSum_ae P X hX n).sub (EventuallyEq.rfl))

/-- L² convergence gives convergence in probability for the original sums. -/
theorem partialSum_tendstoInMeasure (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) :
    TendstoInMeasure P (partialSum X) atTop (sumVariable P X hX) :=
  tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (partialSum_tendsto_eLpNorm P X hX hi hc hs)

/-- On a probability space the finite sums also converge in law. -/
theorem partialSum_tendstoInDistribution [IsProbabilityMeasure P]
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) :
    TendstoInDistribution (partialSum X) atTop (sumVariable P X hX) (fun _ => P) P :=
  (partialSum_tendstoInMeasure P X hX hi hc hs).tendstoInDistribution
    (fun n => (memLp_partialSum P X hX n).aestronglyMeasurable.aemeasurable)

/-- The second moment of an L² representative is its squared Hilbert norm. -/
theorem norm_L2_sq (f : Lp ℝ 2 P) : ‖f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

/-- The variance of the infinite centered series is the sum of variances. -/
theorem sumVariable_secondMoment (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) :
    (∫ ω, (sumVariable P X hX ω) ^ 2 ∂P) = ∑' n, ∫ ω, (X n ω) ^ 2 ∂P := by
  rw [sumVariable, ← norm_L2_sq, sumLp, norm_tsum_sq _ (orthogonal_terms P X hX hi hc)]
  · simp only [norm_term_sq]
  · simpa only [norm_term_sq] using hs

/-- Exact mean-square error of every finite truncation. -/
theorem tail_secondMoment (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) (k : ℕ) :
    (∫ ω, (sumVariable P X hX ω - partialSum X k ω) ^ 2 ∂P) =
      ∑' n, ∫ ω, (X (n + k) ω) ^ 2 ∂P := by
  have he : sumLp P X hX - ∑ i ∈ Finset.range k, term P X hX i =
      ∑' n, term P X hX (n + k) := by
    have h := (summable_terms P X hX hi hc hs).sum_add_tsum_nat_add k
    exact sub_eq_iff_eq_add.mpr (by simpa only [sumLp, add_comm] using h.symm)
  have hae : (fun ω => (sumLp P X hX - ∑ i ∈ Finset.range k, term P X hX i) ω) =ᵐ[P]
      (sumVariable P X hX - partialSum X k) :=
    (Lp.coeFn_sub _ _).trans (EventuallyEq.rfl.sub (partialSum_ae P X hX k))
  have heint := integral_congr_ae (hae.fun_comp (fun x : ℝ => x ^ 2))
  change (∫ ω, ((sumLp P X hX - ∑ i ∈ Finset.range k, term P X hX i) ω) ^ 2 ∂P) =
    (∫ ω, (sumVariable P X hX ω - partialSum X k ω) ^ 2 ∂P) at heint
  rw [← heint, ← norm_L2_sq, he]
  have ho : Pairwise (fun i j => inner ℝ (term P X hX (i + k)) (term P X hX (j + k)) = 0) :=
    fun i j hij => orthogonal_terms P X hX hi hc (fun he => hij (Nat.add_right_cancel he))
  rw [norm_tsum_sq _ ho]
  · simp only [norm_term_sq]
  · simpa only [norm_term_sq] using (summable_nat_add_iff k).mpr hs

include hX in
/-- The expected value of every partial sum is zero. -/
theorem partialSum_mean [IsProbabilityMeasure P] (hc : ∀ n, ∫ ω, X n ω ∂P = 0) (k : ℕ) :
    (∫ ω, partialSum X k ω ∂P) = 0 := by
  change (∫ ω, ∑ i ∈ Finset.range k, X i ω ∂P) = 0
  rw [integral_finsetSum _ (fun i _ => (hX i).integrable (by norm_num))]
  simp only [hc, Finset.sum_const_zero]

/-- The limit is centered. -/
theorem sumVariable_mean [IsProbabilityMeasure P]
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) :
    (∫ ω, sumVariable P X hX ω ∂P) = 0 := by
  let c : Lp ℝ 2 P := (memLp_const (μ := P) (p := 2) (1 : ℝ)).toLp (fun _ => 1)
  have hid (f : Lp ℝ 2 P) : inner ℝ c f = ∫ ω, f ω ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (μ := P) (p := 2) (1 : ℝ)).coeFn_toLp] with ω hω
    change inner ℝ (((memLp_const (μ := P) (p := 2) (1 : ℝ)).toLp (fun _ => 1)) ω) (f ω) = f ω
    rw [hω]
    simp [RCLike.inner_apply]
  have hm (n : ℕ) : inner ℝ c (∑ i ∈ Finset.range n, term P X hX i) = 0 := by
    rw [hid, integral_congr_ae (partialSum_ae P X hX n)]
    exact partialSum_mean P X hX hc n
  have hh : Continuous (fun f : Lp ℝ 2 P => inner ℝ c f) := continuous_const.inner continuous_id
  have ht := (hh.tendsto (sumLp P X hX)).comp
    (partialSum_tendsto_L2 P X hX hi hc hs)
  change Tendsto (fun n => inner ℝ c (∑ i ∈ Finset.range n, term P X hX i)) atTop
    (𝓝 (inner ℝ c (sumLp P X hX))) at ht
  simp only [hm, hid] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Tail mean-square errors tend to zero. -/
theorem tail_secondMoment_tendsto_zero
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) :
    Tendsto (fun k => ∫ ω, (sumVariable P X hX ω - partialSum X k ω) ^ 2 ∂P) atTop (𝓝 0) := by
  simp_rw [tail_secondMoment P X hX hi hc hs]
  exact tendsto_sum_nat_add (fun n => ∫ ω, (X n ω) ^ 2 ∂P)

/-- Quantitative control of every tail in probability by its remaining variance. -/
theorem tail_probability_le [IsProbabilityMeasure P]
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hs : Summable (fun n => ∫ ω, (X n ω) ^ 2 ∂P)) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |sumVariable P X hX ω - partialSum X k ω|} ≤
      ENNReal.ofReal ((∑' n, ∫ ω, (X (n + k) ω) ^ 2 ∂P) / ε ^ 2) := by
  have hm := (memLp_sumVariable P X hX).sub (memLp_partialSum P X hX k)
  have hmean : (∫ ω, sumVariable P X hX ω - partialSum X k ω ∂P) = 0 := by
    rw [integral_sub ((memLp_sumVariable P X hX).integrable (by norm_num))
      ((memLp_partialSum P X hX k).integrable (by norm_num)),
      sumVariable_mean P X hX hi hc hs, partialSum_mean P X hX hc k, sub_self]
  have hv : variance (sumVariable P X hX - partialSum X k) P =
      ∑' n, ∫ ω, (X (n + k) ω) ^ 2 ∂P := by
    rw [variance_eq_integral hm.aestronglyMeasurable.aemeasurable]
    simp only [Pi.sub_apply, hmean, sub_zero]
    simpa only [sub_zero, Pi.sub_apply] using tail_secondMoment P X hX hi hc hs k
  simpa only [Pi.sub_apply, hmean, sub_zero, hv] using meas_ge_le_variance_div_sq hm hε

end ConditionedStableLaws.CompensatedSeries
