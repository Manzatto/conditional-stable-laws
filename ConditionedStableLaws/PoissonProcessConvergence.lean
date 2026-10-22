import ConditionedStableLaws.RareEventPoisson
import ConditionedStableLaws.IntervalRefinement
import ConditionedStableLaws.PoissonExistence
import ConditionedStableLaws.EmpiricalPaths
import ConditionedStableLaws.EndpointTrimming

/-!
# From quantitative rare-event estimates to vague Poisson convergence

The inputs are the explicit separated and excluded configuration bounds for every positive mixed
order. The conclusion is weak convergence of empirical point measures to the constructed Poisson
random measure.
-/

open Filter MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace ConditionedStableLaws

/-- A positive half-open interval has finite intensity under local finiteness, including an interval
ending at infinity. -/
theorem intensity_interval_lt_top (υ : Measure ExtremeState)
    (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞) (a b : ExtremeState) :
    υ (Ioc a b) < ∞ := by
  obtain ⟨ε, hε, hεa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp a.property
  exact lt_of_le_of_lt (measure_mono (fun x hx => hεa.le.trans hx.1.le))
    (hυ ε (by exact_mod_cast hε))

namespace IsPoissonRandomMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {N : RandomPointMeasure Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {υ : Measure ExtremeState}

/-- The integer count extracted from a finite-intensity region has its Poisson law, as a consequence
of the ENNReal evaluation law. -/
theorem countOn_hasLaw (hN : IsPoissonRandomMeasure N P υ)
    (A : Set ExtremeState) (hA : MeasurableSet A) (hf : υ A ≠ ∞) :
    HasLaw (fun ω => (N.toFun ω).countOn A) (poissonMeasure (υ A).toNNReal) P := by
  let c : ℝ≥0∞ → ℕ := fun x => ⌊x.toReal⌋₊
  have hc : Measurable c := measurable_id.ennreal_toReal.nat_floor
  have h := (hasLaw_map (P := poissonCountLaw (υ A)) hc.aemeasurable).comp
    (hN.count_law A hA hf)
  have he : (poissonCountLaw (υ A)).map c = poissonMeasure (υ A).toNNReal := by
    rw [poissonCountLaw, Measure.map_map hc (by fun_prop)]
    have hid : c ∘ (fun k : ℕ => (k : ℝ≥0∞)) = id := by
      funext k
      simp [c]
    rw [hid, Measure.map_id]
  rw [he] at h
  exact h

/-- Counts on a finite disjoint interval family have the product Poisson law, including
zero-intensity intervals. -/
theorem intervalCountVector_hasLaw (hN : IsPoissonRandomMeasure N P υ)
    (k : ℕ) (a b : Fin k → ExtremeState)
    (hd : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    HasLaw (fun ω j => (N.toFun ω).countOn (Ioc (a j) (b j)))
      (independentPoissonProbabilityMeasure (fun j => (υ (Ioc (a j) (b j))).toNNReal) :
        Measure (Fin k → ℕ)) P := by
  have hf (j : Fin k) : υ (Ioc (a j) (b j)) ≠ ∞ :=
    (intensity_interval_lt_top υ hN.intensity_locally_finite (a j) (b j)).ne
  have hc (j : Fin k) := hN.countOn_hasLaw (Ioc (a j) (b j)) measurableSet_Ioc (hf j)
  have hi := (hN.independent_counts k (fun j => Ioc (a j) (b j))
    (fun _ => measurableSet_Ioc) hd hf).comp
      (fun (_ : Fin k) (x : ℝ≥0∞) => ⌊x.toReal⌋₊) (fun _ => measurable_id.ennreal_toReal.nat_floor)
  exact hi.hasLaw_pi hc

end IsPoissonRandomMeasure

/-- An empirical measure has exactly the natural visit count. -/
theorem countOn_empirical {n : ℕ} (a : Fin n → ExtremeState) (A : Set ExtremeState) :
    (LocallyFinitePointMeasure.empirical a).countOn A =
      (Finset.univ.filter (fun i => a i ∈ A)).card := by
  simp [LocallyFinitePointMeasure.countOn, measureReal_def,
    LocallyFinitePointMeasure.empirical_apply_eq_card]

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

/-- Empirical point measures of a triangular array after its measurable
normalization or marking map into `(0,∞]`. -/
def markedEmpirical (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (g : ℕ → A → ExtremeState) (hg : ∀ n, Measurable (g n)) (n : ℕ) : RandomPointMeasure Ω :=
  RandomPointMeasure.empirical (fun i ω => g n (X n i ω))
    (fun i => (hg n).comp (hX n i))

/-- Empirical interval counts are the visit counts of the corresponding targets. -/
theorem markedEmpirical_countOn (X : ∀ n : ℕ, Fin n → Ω → A)
    (hX : ∀ n t, Measurable (X n t)) (g : ℕ → A → ExtremeState)
    (hg : ∀ n, Measurable (g n)) (n : ℕ) (B : Set ExtremeState) (ω : Ω) :
    ((markedEmpirical X hX g hg n).toFun ω).countOn B =
      (visitTimes (fun i => X n i ω) ((g n) ⁻¹' B)).card := by
  change (LocallyFinitePointMeasure.empirical (fun i => g n (X n i ω))).countOn B = _
  rw [countOn_empirical]
  rfl

/-- Quantitative input for one finite interval family: rare-event scaling and the configuration
estimates. -/
structure IntervalConfigurationEstimates (P : ℕ → Measure Ω)
    (X : ∀ n : ℕ, Fin n → Ω → A) (g : ℕ → A → ExtremeState)
    (υ : Measure ExtremeState) {k : ℕ} (a b : Fin k → ExtremeState) where
  probability : Fin k → ℕ → ℝ
  rate_limit : ∀ j, Tendsto (fun n : ℕ => (n : ℝ) * probability j n) atTop
    (𝓝 (υ (Ioc (a j) (b j))).toReal)
  configurations : ∀ r : Fin k → ℕ, 0 < ∑ j, r j →
    RareConfigurationEstimates P X (fun n j => (g n) ⁻¹' Ioc (a j) (b j)) probability r

/-- Convert convergence of visit laws to convergence toward the count vector of a PRM with the same
interval rates. -/
theorem poisson_interval_counts_of_visit_law
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q] (Nlimit : RandomPointMeasure Ω')
    (υ : Measure ExtremeState) (hN : IsPoissonRandomMeasure Nlimit Q υ)
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (g : ℕ → A → ExtremeState) (hg : ∀ n, Measurable (g n))
    (k : ℕ) (a b : Fin k → ExtremeState)
    (hd : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))))
    (ht : Tendsto (fun n => natVectorProbabilityLaw (P n)
      (visitCountVector (X n) (fun j => (g n) ⁻¹' Ioc (a j) (b j)))) atTop
      (𝓝 (independentPoissonProbabilityMeasure
        (fun j => (υ (Ioc (a j) (b j))).toNNReal)))) :
    TendstoInDistribution
      (fun n ω j => ((markedEmpirical X hX g hg n).toFun ω).countOn (Ioc (a j) (b j))) atTop
      (fun ω j => (Nlimit.toFun ω).countOn (Ioc (a j) (b j))) P Q := by
  have htarget := hN.intervalCountVector_hasLaw k a b hd
  have hm (n : ℕ) : Measurable
      (fun ω j => ((markedEmpirical X hX g hg n).toFun ω).countOn (Ioc (a j) (b j))) :=
    Measurable.of_eval (fun j =>
      (LocallyFinitePointMeasure.measurable_countOn_interval (a j).val (b j).val (a j).property).comp
        (markedEmpirical X hX g hg n).measurable)
  have hlimit : Measurable (fun ω j => (Nlimit.toFun ω).countOn (Ioc (a j) (b j))) :=
    Measurable.of_eval (fun j =>
      (LocallyFinitePointMeasure.measurable_countOn_interval (a j).val (b j).val (a j).property).comp
        Nlimit.measurable)
  refine ⟨fun n => (hm n).aemeasurable, hlimit.aemeasurable, ?_⟩
  have hlaw : (⟨Q.map (fun ω j => (Nlimit.toFun ω).countOn (Ioc (a j) (b j))),
      inferInstance⟩ : ProbabilityMeasure (Fin k → ℕ)) =
      independentPoissonProbabilityMeasure (fun j => (υ (Ioc (a j) (b j))).toNNReal) := by
    apply Subtype.ext
    exact htarget.map_eq
  rw [hlaw]
  apply ht.congr
  intro n
  apply ProbabilityMeasure.toMeasure_injective
  change (P n).map (visitCountVector (X n) (fun j => (g n) ⁻¹' Ioc (a j) (b j))) =
    (P n).map (fun ω j => ((markedEmpirical X hX g hg n).toFun ω).countOn (Ioc (a j) (b j)))
  have heq : visitCountVector (X n) (fun j => (g n) ⁻¹' Ioc (a j) (b j)) =
      (fun ω j => ((markedEmpirical X hX g hg n).toFun ω).countOn (Ioc (a j) (b j))) := by
    funext ω j
    exact (markedEmpirical_countOn X hX g hg n (Ioc (a j) (b j)) ω).symm
  rw [heq]

/-- Quantitative interval-visit estimates imply joint convergence to the corresponding count vector
of a given Poisson random measure. -/
theorem poisson_interval_counts_of_configuration_estimates
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q] (Nlimit : RandomPointMeasure Ω')
    (υ : Measure ExtremeState) (hN : IsPoissonRandomMeasure Nlimit Q υ)
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (g : ℕ → A → ExtremeState) (hg : ∀ n, Measurable (g n))
    (k : ℕ) (a b : Fin k → ExtremeState)
    (hd : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))))
    (est : IntervalConfigurationEstimates P X g υ a b) :
    TendstoInDistribution
      (fun n ω j => ((markedEmpirical X hX g hg n).toFun ω).countOn (Ioc (a j) (b j))) atTop
      (fun ω j => (Nlimit.toFun ω).countOn (Ioc (a j) (b j))) P Q := by
  have hu (n : ℕ) (j : Fin k) : MeasurableSet ((g n) ⁻¹' Ioc (a j) (b j)) :=
    measurableSet_Ioc.preimage (hg n)
  have hd' (n : ℕ) : Pairwise (fun i j =>
      Disjoint ((g n) ⁻¹' Ioc (a i) (b i)) ((g n) ⁻¹' Ioc (a j) (b j))) :=
    fun _ _ hij => (hd hij).preimage _
  have ht := independent_poisson_visit_counts_of_configuration_estimates P X hX
    (fun n j => (g n) ⁻¹' Ioc (a j) (b j)) hu hd' est.probability
    (fun j => (υ (Ioc (a j) (b j))).toNNReal) est.rate_limit est.configurations
  exact poisson_interval_counts_of_visit_law P Q Nlimit υ hN X hX g hg k a b hd ht

/-- Vague point-process convergence to a PRM, assembled from every finite disjoint interval family's
explicit configuration estimates. -/
theorem poisson_point_process_convergence_of_configuration_estimates
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q] (Nlimit : RandomPointMeasure Ω')
    (υ : Measure ExtremeState) (hN : IsPoissonRandomMeasure Nlimit Q υ)
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (g : ℕ → A → ExtremeState) (hg : ∀ n, Measurable (g n))
    (estimates : ∀ (k : ℕ) (a b : Fin k → ExtremeState), (∀ j, a j < b j) →
      Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      IntervalConfigurationEstimates P X g υ a b) :
    TendstoInDistribution (fun n => (markedEmpirical X hX g hg n).toFun) atTop
      Nlimit.toFun P Q := by
  apply kallenberg_random_point_measures P Q (markedEmpirical X hX g hg) Nlimit
  intro k a b hs hd
  exact poisson_interval_counts_of_configuration_estimates P Q Nlimit υ hN X hX g hg
    k a b hd (estimates k a b hs hd)

/-- The same theorem with the limit law constructed from the intensity. -/
theorem empirical_poisson_process_convergence
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (υ : Measure ExtremeState) (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (g : ℕ → A → ExtremeState) (hg : ∀ n, Measurable (g n))
    (estimates : ∀ (k : ℕ) (a b : Fin k → ExtremeState), (∀ j, a j < b j) →
      Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      IntervalConfigurationEstimates P X g υ a b) :
    TendstoInDistribution (fun n => (markedEmpirical X hX g hg n).toFun) atTop
      AnnularPoissonClouds.randomMeasure.toFun P (AnnularPoissonClouds.law υ hυ) :=
  poisson_point_process_convergence_of_configuration_estimates P (AnnularPoissonClouds.law υ hυ)
    AnnularPoissonClouds.randomMeasure υ (AnnularPoissonClouds.isPoissonRandomMeasure υ hυ)
    X hX g hg estimates

/-- A concrete endpoint-trimmed variant: only the probability of any hit in the removed strips is
needed, while every higher-order estimate is imposed on the trimmed observations. -/
structure TrimmedIntervalConfigurationEstimates (P : ℕ → Measure Ω)
    (X : ∀ n : ℕ, Fin n → Ω → A) (g : ℕ → A → ExtremeState)
    (υ : Measure ExtremeState) {k : ℕ} (a b : Fin k → ExtremeState) where
  probability : Fin k → ℕ → ℝ
  trimWidth : ℕ → ℕ
  rate_limit : ∀ j, Tendsto (fun n : ℕ => (n : ℝ) * probability j n) atTop
    (𝓝 (υ (Ioc (a j) (b j))).toReal)
  boundary_tendsto : Tendsto (fun n => (P n).real
    (EndpointTrimming.boundaryHit (trimWidth n) (X n)
      (fun j => (g n) ⁻¹' Ioc (a j) (b j)))) atTop (𝓝 0)
  configurations : ∀ r : Fin k → ℕ, 0 < ∑ j, r j →
    RareConfigurationEstimates P
      (fun n => EndpointTrimming.trimmedObservations (trimWidth n) (X n))
      (fun n => EndpointTrimming.liftedTargets (fun j => (g n) ⁻¹' Ioc (a j) (b j))) probability r

/-- Endpoint-trimmed estimates still give the limit for the original empirical interval counts,
after the boundary-hit transfer. -/
theorem poisson_interval_counts_of_trimmed_estimates
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q] (Nlimit : RandomPointMeasure Ω')
    (υ : Measure ExtremeState) (hN : IsPoissonRandomMeasure Nlimit Q υ)
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (g : ℕ → A → ExtremeState) (hg : ∀ n, Measurable (g n))
    (k : ℕ) (a b : Fin k → ExtremeState)
    (hd : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))))
    (est : TrimmedIntervalConfigurationEstimates P X g υ a b) :
    TendstoInDistribution
      (fun n ω j => ((markedEmpirical X hX g hg n).toFun ω).countOn (Ioc (a j) (b j))) atTop
      (fun ω j => (Nlimit.toFun ω).countOn (Ioc (a j) (b j))) P Q := by
  apply poisson_interval_counts_of_visit_law P Q Nlimit υ hN X hX g hg k a b hd
  exact EndpointTrimming.independent_poisson_of_trimmed_configuration_estimates P X hX
    (fun n j => (g n) ⁻¹' Ioc (a j) (b j))
    (fun n _ => measurableSet_Ioc.preimage (hg n))
    (fun _ _ _ hij => (hd hij).preimage _) est.trimWidth est.boundary_tendsto
    est.probability (fun j => (υ (Ioc (a j) (b j))).toNNReal)
    est.rate_limit est.configurations

/-- The full vague PPP limit for the original empirical measure, obtained
from trimmed configuration bounds and vanishing boundary-hit probabilities. -/
theorem empirical_poisson_process_convergence_of_trimmed_estimates
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (υ : Measure ExtremeState) (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)
    (X : ∀ n : ℕ, Fin n → Ω → A) (hX : ∀ n t, Measurable (X n t))
    (g : ℕ → A → ExtremeState) (hg : ∀ n, Measurable (g n))
    (estimates : ∀ (k : ℕ) (a b : Fin k → ExtremeState), (∀ j, a j < b j) →
      Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      TrimmedIntervalConfigurationEstimates P X g υ a b) :
    TendstoInDistribution (fun n => (markedEmpirical X hX g hg n).toFun) atTop
      AnnularPoissonClouds.randomMeasure.toFun P (AnnularPoissonClouds.law υ hυ) := by
  apply kallenberg_random_point_measures P (AnnularPoissonClouds.law υ hυ)
    (markedEmpirical X hX g hg) AnnularPoissonClouds.randomMeasure
  intro k a b hs hd
  exact poisson_interval_counts_of_trimmed_estimates P (AnnularPoissonClouds.law υ hυ)
    AnnularPoissonClouds.randomMeasure υ (AnnularPoissonClouds.isPoissonRandomMeasure υ hυ)
    X hX g hg k a b hd (estimates k a b hs hd)

section Paths
variable {M : Type*} [MeasurableSpace M]

/-- The normalized path observation, with the positive cemetery extension. -/
def pathNormalization (f : M → ℝ) (hf : ∀ x, 0 < f x)
    (B : ℕ → ℝ) (hB : ∀ n, 0 < B n) (n : ℕ) : Option M → ExtremeState :=
  RandomPointMeasure.normalizedObservation (positiveExtension f)
    (positiveExtension_pos hf) (B n) (hB n)

theorem measurable_pathNormalization (f : M → ℝ) (hm : Measurable f)
    (hf : ∀ x, 0 < f x) (B : ℕ → ℝ) (hB : ∀ n, 0 < B n) (n : ℕ) :
    Measurable (pathNormalization f hf B hB n) :=
  RandomPointMeasure.measurable_normalizedObservation (measurable_positiveExtension hm)
    (positiveExtension_pos hf) (B n) (hB n)

/-- Specialization to the normalized canonical-path empirical measure. The varying path laws may in
particular be the survival-conditioned laws. -/
theorem path_empirical_poisson_process_convergence
    (P : ℕ → Measure (CanonicalChain.Path M)) [∀ n, IsProbabilityMeasure (P n)]
    (υ : Measure ExtremeState) (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)
    (f : M → ℝ) (hm : Measurable f) (hf : ∀ x, 0 < f x)
    (B : ℕ → ℝ) (hB : ∀ n, 0 < B n)
    (estimates : ∀ (k : ℕ) (a b : Fin k → ExtremeState), (∀ j, a j < b j) →
      Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      IntervalConfigurationEstimates P
        (fun n (i : Fin n) (ω : CanonicalChain.Path M) => ω i)
        (pathNormalization f hf B hB) υ a b) :
    TendstoInDistribution (fun n => (pathEmpirical f hm hf n (B n) (hB n)).toFun) atTop
      AnnularPoissonClouds.randomMeasure.toFun P (AnnularPoissonClouds.law υ hυ) :=
  empirical_poisson_process_convergence P υ hυ
    (fun n (i : Fin n) (ω : CanonicalChain.Path M) => ω i)
    (fun _ i => measurable_pi_apply i.val)
    (pathNormalization f hf B hB) (measurable_pathNormalization f hm hf B hB) estimates

/-- The path empirical process also converges when the supplied configuration estimates are obtained
after endpoint trimming. -/
theorem path_empirical_poisson_process_convergence_of_trimmed_estimates
    (P : ℕ → Measure (CanonicalChain.Path M)) [∀ n, IsProbabilityMeasure (P n)]
    (υ : Measure ExtremeState) (hυ : ∀ ε : ℝ≥0, 0 < ε → υ (extremeTail ε) < ∞)
    (f : M → ℝ) (hm : Measurable f) (hf : ∀ x, 0 < f x)
    (B : ℕ → ℝ) (hB : ∀ n, 0 < B n)
    (estimates : ∀ (k : ℕ) (a b : Fin k → ExtremeState), (∀ j, a j < b j) →
      Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      TrimmedIntervalConfigurationEstimates P
        (fun n (i : Fin n) (ω : CanonicalChain.Path M) => ω i)
        (pathNormalization f hf B hB) υ a b) :
    TendstoInDistribution (fun n => (pathEmpirical f hm hf n (B n) (hB n)).toFun) atTop
      AnnularPoissonClouds.randomMeasure.toFun P (AnnularPoissonClouds.law υ hυ) :=
  empirical_poisson_process_convergence_of_trimmed_estimates P υ hυ
    (fun n (i : Fin n) (ω : CanonicalChain.Path M) => ω i)
    (fun _ i => measurable_pi_apply i.val)
    (pathNormalization f hf B hB) (measurable_pathNormalization f hm hf B hB) estimates

end Paths

end ConditionedStableLaws
