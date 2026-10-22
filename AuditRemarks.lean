import ConditionedStableLaws.Remarks
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let remarks : Array (String × Array Name) := #[
    ("remark.birkhoff_indexing", #[
      ``ConditionedStableLaws.birkhoffSum_endpoint_difference,
      ``ConditionedStableLaws.normalized_endpoint_bound,
      ``ConditionedStableLaws.bounded_average_succ_difference,
      ``ConditionedStableLaws.CanonicalChain.bounded_conditioned_indexing,
      ``ConditionedStableLaws.CanonicalChain.normalized_endpoint_probability_of_H,
      ``ConditionedStableLaws.CanonicalChain.normalized_reindexing_probability_of_H,
      ``ConditionedStableLaws.CanonicalChain.shifted_limit_of_H,
      ``ConditionedStableLaws.CanonicalChain.inclusive_sum_limit_of_H,
      ``ConditionedStableLaws.CanonicalChain.conditioned_endpoint_mean_nonneg_of_H,
      ``ConditionedStableLaws.CanonicalChain.lln_L1_reindexed]),
    ("rmk:no-kill", #[
      ``ConditionedStableLaws.eigenvalue_eq_one_of_conservative,
      ``ConditionedStableLaws.StandingHypothesis.SurvivalGapData.weight_eq_one_of_conservative,
      ``ConditionedStableLaws.StandingHypothesis.SurvivalGapData.weightedMeasure_eq_of_conservative,
      ``ConditionedStableLaws.CanonicalChain.conditionedMeasure_eq_of_conservative,
      ``ConditionedStableLaws.CanonicalChain.ae_always_live_of_conservative]),
    ("rmk:admissible", #[
      ``ConditionedStableLaws.isAdmissibleAt_of_continuousAt,
      ``ConditionedStableLaws.isAdmissiblePoint_of_continuousAt,
      ``ConditionedStableLaws.ae_tendsto_closedBall_abs_sub_average,
      ``ConditionedStableLaws.ae_tendsto_ball_abs_sub_average_of_absolutelyContinuous,
      ``ConditionedStableLaws.ae_tendsto_ball_abs_sub_average_off_set,
      ``ConditionedStableLaws.isRegularAt_addHaar,
      ``ConditionedStableLaws.isRegularAt_restrict_addHaar,
      ``ConditionedStableLaws.ae_isAdmissiblePoint_restrict_addHaar,
      ``ConditionedStableLaws.IsRegularAt.withDensity_of_continuousAt,
      ``ConditionedStableLaws.isRegularAt_coordinateVolumeDensity,
      ``ConditionedStableLaws.isRegularAt_of_sharp_ball_comparison,
      ``ConditionedStableLaws.HasRiemannianVolumeDensity.isRegularAt,
      ``ConditionedStableLaws.HasRiemannianVolumeDensity.isLocallyFiniteMeasure,
      ``ConditionedStableLaws.HasRiemannianVolumeDensity.isRegularAt_restrict,
      ``ConditionedStableLaws.HasRiemannianVolumeDensity.isAdmissibleAt_restrict_of_continuousAt,
      ``ConditionedStableLaws.HasRiemannianVolumeDensity.ae_tendsto_ball_abs_sub_average_restrict,
      ``ConditionedStableLaws.HasRiemannianVolumeDensity.ae_tendsto_ball_abs_sub_average_off_set,
      ``ConditionedStableLaws.HasRiemannianVolumeDensity.ae_isAdmissiblePoint_restrict,
      ``ConditionedStableLaws.ae_tendsto_ball_abs_sub_average_restrict_of_regular]),
    ("remark.independent_limiting_counts", #[
      ``ConditionedStableLaws.IsPoissonRandomMeasure.independent_countOn,
      ``ConditionedStableLaws.power_poisson_limit_isPoissonRandomMeasure,
      ``ConditionedStableLaws.not_indepFun_of_disjoint_positive_values,
      ``ConditionedStableLaws.not_independent_single_observation_counts,
      ``ConditionedStableLaws.CanonicalChain.initial_functions_independent,
      ``ConditionedStableLaws.CanonicalChain.initial_visit_counts_independent,
      ``ConditionedStableLaws.CanonicalChain.two_visit_counts_not_independent,
      ``ConditionedStableLaws.FiniteCountExample.refreshChain_hypothesisH,
      ``ConditionedStableLaws.FiniteCountExample.refresh_left_eigenmeasure,
      ``ConditionedStableLaws.FiniteCountExample.refresh_hypothesisH_and_singular_two_counts_dependent,
      ``ConditionedStableLaws.FiniteCountExample.threeStateHypothesisH,
      ``ConditionedStableLaws.FiniteCountExample.threeState_counts_dependent]),
    ("remark.continuous_multiplier_extension", #[
      ``ConditionedStableLaws.ContinuousMultiplier.stable_law_small_signed,
      ``ConditionedStableLaws.ContinuousMultiplier.residual_bound,
      ``ConditionedStableLaws.MultiplierReflection.rescale_normalizer_tendsto,
      ``ConditionedStableLaws.MultiplierReflection.absTrunc_const_mul,
      ``ConditionedStableLaws.MultiplierReflection.gaussian_map_sign,
      ``ConditionedStableLaws.CanonicalChain.limit_setCenterValue,
      ``ConditionedStableLaws.integral_setCenterValue,
      ``ConditionedStableLaws.integral_absTrunc_setCenterValue,
      ``ConditionedStableLaws.ContinuousMultiplier.stable_law_mid_signed,
      ``ConditionedStableLaws.ContinuousMultiplier.stable_law_boundary_signed,
      ``ConditionedStableLaws.ContinuousMultiplier.absolute_center_residual_tendsto,
      ``ConditionedStableLaws.ContinuousMultiplier.powerScale_multiplierTailConstant,
      ``ConditionedStableLaws.ContinuousMultiplier.stable_law_one_signed,
      ``ConditionedStableLaws.ContinuousMultiplier.bScale_multiplierTailConstant]),
    ("remark.poisson_target_start", #[
      ``ConditionedStableLaws.CanonicalChain.visitTimes_eq_one_add_afterInitial,
      ``ConditionedStableLaws.CanonicalChain.independent_poisson_after_initial_of_H,
      ``ConditionedStableLaws.CanonicalChain.conditional_poisson_after_initial_shrinking_targets,
      ``ConditionedStableLaws.CanonicalChain.conditional_poisson_target_start]),
    ("remark.mu_nu_integrability", #[
      ``ConditionedStableLaws.memLp_weighted_of_memLp,
      ``ConditionedStableLaws.memLp_weighted_iff,
      ``ConditionedStableLaws.eLpNorm_weighted_le,
      ``ConditionedStableLaws.eLpNorm_le_weighted,
      ``ConditionedStableLaws.integrability_reverse_inclusion_fails,
      ``ConditionedStableLaws.RefinedLLN.lln_L1,
      ``ConditionedStableLaws.RefinedLLN.lln_probability,
      ``ConditionedStableLaws.RefinedLLN.lln_L1_of_weight_bounded_below]),
    ("remark.canonical_q_process", #[
      ``ConditionedStableLaws.CanonicalChain.exists_qProcess_never_escapes,
      ``ConditionedStableLaws.CanonicalChain.IsQProcess.ae_always_stays,
      ``ConditionedStableLaws.CanonicalChain.IsQProcess.always_stays_eq_one,
      ``ConditionedStableLaws.CanonicalChain.IsQProcess.survival_eq_one,
      ``ConditionedStableLaws.CanonicalChain.IsQProcess.escaping_marginal_eq_zero]),
    ("remark.random_measure_semiring", #[
      ``ConditionedStableLaws.dissectingExtremeIntervals_isSetSemiring,
      ``ConditionedStableLaws.dissectingExtremeIntervals_measurable,
      ``ConditionedStableLaws.dissectingExtremeIntervals_nhds,
      ``ConditionedStableLaws.kallenberg_random_point_measures])]

  for (label, names) in remarks do
    for name in names do
      let axs ← collectAxioms name
      for ax in axs do
        unless standard.contains ax do
          throwError "Remark {label}: {name} depends on nonstandard axiom {ax}"
    logInfo m!"Remark {label}: {names.size} mapped declarations, no cited axiom."
