import ConditionedStableLaws.CountableSuperposition
import ConditionedStableLaws.PoissonCloudCounts
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Algebra.Order.Disjointed

/-!
# Independent finite Poisson clouds on an annular partition

The shells are `(1,∞]` and `(1/(n+2),1/(n+1)]`. A locally finite intensity restricts to a finite
measure on each shell. Its finite Poisson clouds are placed on a countable product probability
space.
-/

open Filter MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace ConditionedStableLaws.AnnularPoissonClouds

/-- Positive reciprocal cutoffs. -/
def cutoff (n : ℕ) : ℝ≥0 := 1 / (n + 1)

theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by unfold cutoff; positivity

theorem cutoff_antitone : Antitone cutoff := by
  intro i j hij
  unfold cutoff
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

/-- Increasing open tails, whose union is the whole extended positive half-line. -/
def openTail (n : ℕ) : Set ExtremeState := {x | (cutoff n : ℝ≥0∞) < x.val}

theorem openTail_monotone : Monotone openTail := by
  intro i j hij x hx
  exact (show (cutoff j : ℝ≥0∞) ≤ (cutoff i : ℝ≥0∞) by
    exact_mod_cast cutoff_antitone hij).trans_lt hx

theorem measurableSet_openTail (n : ℕ) : MeasurableSet (openTail n) :=
  measurableSet_lt measurable_const measurable_subtype_coe

theorem iUnion_openTail : (⋃ n, openTail n) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨ε, hε, hεx⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp x.property
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ≥0) < ε by exact_mod_cast hε)
  exact mem_iUnion.mpr ⟨n, (show (cutoff n : ℝ≥0∞) < (ε : ℝ≥0∞) by
    exact_mod_cast (show cutoff n < ε by simpa [cutoff] using hn)).trans hεx⟩

/-- Disjoint consecutive shells, retaining the endpoint convention `(a,b]`. -/
def annulus (n : ℕ) : Set ExtremeState := disjointed openTail n

@[simp] theorem annulus_zero : annulus 0 = {x : ExtremeState | 1 < x.val} := by
  simp [annulus, openTail, cutoff]

theorem annulus_succ (n : ℕ) : annulus (n + 1) =
    {x : ExtremeState | (cutoff (n + 1) : ℝ≥0∞) < x.val ∧ x.val ≤ cutoff n} := by
  rw [annulus, openTail_monotone.disjointed_add_one]
  ext x
  simp [openTail]

theorem annulus_subset_openTail (n : ℕ) : annulus n ⊆ openTail n :=
  disjointed_le openTail n

theorem annuli_disjoint : Pairwise (fun i j => Disjoint (annulus i) (annulus j)) :=
  disjoint_disjointed openTail

theorem measurableSet_annulus (n : ℕ) : MeasurableSet (annulus n) :=
  MeasurableSet.disjointed measurableSet_openTail n

theorem iUnion_annulus : (⋃ n, annulus n) = univ := by
  change (⋃ n, disjointed openTail n) = univ
  rw [iUnion_disjointed, iUnion_openTail]

/-- All sufficiently small shells are disjoint from a fixed positive tail. -/
theorem annuli_escape_zero (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → Disjoint (annulus n) (extremeTail ε) := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine ⟨k + 1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
      apply Set.disjoint_left.mpr
      intro x hx ht
      rw [annulus_succ] at hx
      have hm : k ≤ m := by omega
      have hmε : cutoff m < ε := (cutoff_antitone hm).trans_lt hk
      have hlt : (cutoff m : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hmε
      exact not_lt_of_ge (ht.trans hx.2) hlt

variable (υ : Measure ExtremeState)
  (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)

include hυ in
/-- Each annulus has finite mass for every intensity finite on positive tails. -/
theorem annulus_measure_lt_top (n : ℕ) : υ (annulus n) < ∞ :=
  lt_of_le_of_lt (measure_mono (fun x hx => (show (cutoff n : ℝ≥0∞) < x.val from annulus_subset_openTail n hx).le))
    (hυ (cutoff n) (cutoff_pos n))

/-- The original intensity is exactly the sum of its disjoint shell restrictions. -/
theorem sum_restrict_annulus : Measure.sum (fun n => υ.restrict (annulus n)) = υ := by
  rw [← Measure.restrict_iUnion annuli_disjoint measurableSet_annulus, iUnion_annulus,
    Measure.restrict_univ]

/-- The finite intensity of a single shell. -/
def componentIntensity (n : ℕ) : FiniteMeasure ExtremeState :=
  ⟨υ.restrict (annulus n), ⟨by
    rw [Measure.restrict_apply_univ]
    exact annulus_measure_lt_top υ hυ n⟩⟩

/-- A finite marked-cloud law with the correct restricted intensity. -/
def componentLaw (n : ℕ) : Measure FinitePoissonCloud.Sample :=
  FinitePoissonCloud.law (componentIntensity υ hυ n).mass (componentIntensity υ hυ n).normalize

instance componentLaw_probability (n : ℕ) : IsProbabilityMeasure (componentLaw υ hυ n) := by
  unfold componentLaw
  infer_instance

/-- Every component is a finite Poisson random measure. -/
theorem component_isPoisson (n : ℕ) :
    IsPoissonRandomMeasure FinitePoissonCloud.randomPointMeasure
      (componentLaw υ hυ n) (υ.restrict (annulus n)) := by
  have : Nonempty ExtremeState := ⟨⟨1, by simp⟩⟩
  have he : ((componentIntensity υ hυ n).mass : ℝ≥0∞) •
      ((componentIntensity υ hυ n).normalize : Measure ExtremeState) =
      υ.restrict (annulus n) :=
    congrArg (fun w : FiniteMeasure ExtremeState => (w : Measure ExtremeState))
      (componentIntensity υ hυ n).self_eq_mass_smul_normalize.symm
  rw [← he]
  exact FinitePoissonCloud.isPoissonRandomMeasure _ _

/-- The sample space and law are the countable product of cloud spaces. -/
abbrev Sample := ℕ → FinitePoissonCloud.Sample

def law : Measure Sample := Measure.infinitePi (componentLaw υ hυ)

instance law_probability : IsProbabilityMeasure (law υ hυ) := by
  unfold law
  infer_instance

/-- The n-th random cloud on the common product probability space. -/
def component (n : ℕ) : RandomPointMeasure Sample where
  toFun ω := FinitePoissonCloud.pointMeasure (ω n)
  measurable := FinitePoissonCloud.measurable_pointMeasure.comp (measurable_pi_apply n)

/-- The random cloud coordinates are independent for the product law. -/
theorem independent_components :
    iIndepFun (fun n ω => (component n).toFun ω) (law υ hυ) :=
  iIndepFun_infinitePi (fun _ => FinitePoissonCloud.measurable_pointMeasure)

/-- Finite-cloud evaluations are measurable on every measurable region. -/
theorem measurable_cloud_evaluation (A : Set ExtremeState) (hA : MeasurableSet A) :
    Measurable (fun ω : FinitePoissonCloud.Sample => (FinitePoissonCloud.pointMeasure ω).toMeasure A) := by
  have hm := (show Measurable (fun k : ℕ => (k : ℝ≥0∞)) by fun_prop).comp
    (FinitePoissonCloud.measurable_count A hA)
  convert hm using 1
  funext ω
  exact (FinitePoissonCloud.count_eq_mass A ω).symm

/-- Zero shell-complement intensity forces every component to stay in its own shell almost surely.
-/
theorem component_supported_ae (n : ℕ) :
    ∀ᵐ ω ∂componentLaw υ hυ n,
      (FinitePoissonCloud.pointMeasure ω).toMeasure (annulus n)ᶜ = 0 := by
  have hA := (measurableSet_annulus n).compl
  have hz : (υ.restrict (annulus n)) (annulus n)ᶜ = 0 := by
    rw [Measure.restrict_apply hA]
    simp
  apply (mem_ae_iff_prob_eq_one (measurableSet_eq_fun
    (measurable_cloud_evaluation _ hA) measurable_const)).mpr
  have h := (component_isPoisson υ hυ n).count_probability (annulus n)ᶜ hA
    (by rw [hz]; exact ENNReal.zero_ne_top) 0
  simpa only [hz, ENNReal.toNNReal_zero, NNReal.coe_zero, neg_zero, Real.exp_zero,
    pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one,
    Nat.cast_zero, FinitePoissonCloud.randomPointMeasure] using h

/-- All components of the product construction have their shell supports simultaneously almost
surely. -/
theorem supported_components_ae :
    ∀ᵐ ω ∂law υ hυ, ∀ n,
      ((component n).toFun ω).toMeasure (annulus n)ᶜ = 0 := by
  rw [ae_all_iff]
  intro n
  exact (measurePreserving_eval_infinitePi (componentLaw υ hυ) n).quasiMeasurePreserving.ae
    (component_supported_ae υ hυ n)

/-- The independent shell clouds form a locally finite superposition almost surely. -/
theorem good_components_ae :
    ∀ᵐ ω ∂law υ hυ,
      CountableSuperposition.EventuallyZeroOnTails (fun n => (component n).toFun ω) := by
  filter_upwards [supported_components_ae υ hυ] with ω hω
  exact CountableSuperposition.good_of_supported annulus annuli_escape_zero _ hω

/-- The fully defined vague-measurable superposition on the product sample space. -/
def randomMeasure : RandomPointMeasure Sample :=
  CountableSuperposition.randomSuperposition component

/-- Its evaluations are sums of the component evaluations almost surely, with one common exceptional
null set for every region. -/
theorem randomMeasure_apply_ae :
    ∀ᵐ ω ∂law υ hυ, ∀ A : Set ExtremeState,
      (randomMeasure.toFun ω).toMeasure A =
        ∑' n, ((component n).toFun ω).toMeasure A :=
  CountableSuperposition.randomSuperposition_apply_ae (law υ hυ) component
    (good_components_ae υ hυ)

/-- Natural-valued component counts have the restricted-intensity Poisson laws under the common
product law. -/
theorem component_count_hasLaw (n : ℕ) (A : Set ExtremeState) (hA : MeasurableSet A) :
    HasLaw (fun ω : Sample => FinitePoissonCloud.count A (ω n))
      (poissonMeasure ((υ.restrict (annulus n)) A).toNNReal) (law υ hυ) := by
  have : Nonempty ExtremeState := ⟨⟨1, by simp⟩⟩
  have he : ((componentIntensity υ hυ n).mass : ℝ≥0∞) •
      ((componentIntensity υ hυ n).normalize : Measure ExtremeState) =
      υ.restrict (annulus n) :=
    congrArg (fun w : FiniteMeasure ExtremeState => (w : Measure ExtremeState))
      (componentIntensity υ hυ n).self_eq_mass_smul_normalize.symm
  have hrate : (componentIntensity υ hυ n).mass *
      (((componentIntensity υ hυ n).normalize : Measure ExtremeState) A).toNNReal =
      ((υ.restrict (annulus n)) A).toNNReal := by
    rw [← he]
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
  have hc : HasLaw (FinitePoissonCloud.count A)
      (poissonMeasure ((υ.restrict (annulus n)) A).toNNReal) (componentLaw υ hυ n) := by
    rw [← hrate]
    exact FinitePoissonCloud.count_hasLaw _ _ A hA
  exact hc.comp ⟨(measurable_pi_apply n).aemeasurable,
    Measure.infinitePi_map_eval (componentLaw υ hυ) n⟩

/-- The count variables for any fixed region are independent across shells. -/
theorem independent_component_counts (A : Set ExtremeState) (hA : MeasurableSet A) :
    iIndepFun (fun n (ω : Sample) => FinitePoissonCloud.count A (ω n)) (law υ hυ) :=
  iIndepFun_infinitePi (fun _ => FinitePoissonCloud.measurable_count A hA)

/-- The shell masses sum to the original intensity on every region. -/
theorem tsum_restricted_mass (A : Set ExtremeState) :
    (∑' n, (υ.restrict (annulus n)) A) = υ A := by
  rw [← Measure.sum_apply_of_countable, sum_restrict_annulus]

include hυ in
/-- Coercing the natural Poisson rates back to ENNReal retains every shell mass. -/
theorem tsum_component_rates (A : Set ExtremeState) :
    (∑' n, ((((υ.restrict (annulus n)) A).toNNReal : ℝ≥0) : ℝ≥0∞)) = υ A := by
  have hfin (n : ℕ) : (υ.restrict (annulus n)) A ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono (subset_univ A))
    rw [Measure.restrict_apply_univ]
    exact annulus_measure_lt_top υ hυ n
  simp_rw [ENNReal.coe_toNNReal (hfin _)]
  exact tsum_restricted_mass υ A

include hυ in
/-- Finite intensity on a region gives a summable family of component Poisson rates. -/
theorem summable_component_rates (A : Set ExtremeState) (hA : υ A ≠ ∞) :
    Summable (fun n => ((υ.restrict (annulus n)) A).toNNReal) := by
  apply ENNReal.tsum_coe_ne_top_iff_summable.mp
  rwa [tsum_component_rates υ hυ]

/-- The entire finite vector of region counts in one shell is independent of the vectors in the
other shells, as a property of the product law. -/
theorem independent_count_rows {J : Type*} (A : J → Set ExtremeState)
    (hA : ∀ j, MeasurableSet (A j)) :
    iIndepFun (fun n (ω : Sample) j => ((component n).toFun ω).toMeasure (A j)) (law υ hυ) :=
  iIndepFun_infinitePi (fun _ => Measurable.of_eval (fun j => measurable_cloud_evaluation _ (hA j)))

end ConditionedStableLaws.AnnularPoissonClouds
