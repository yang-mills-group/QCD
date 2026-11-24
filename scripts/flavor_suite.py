"""Explicit inventory: flavor, higher-order running, and quantitative normalization."""
from semantic_suite import AUDITS as PREVIOUS

AUDITS = {m: PREVIOUS[m] for m in ['MassFitSpec','MassFitProof','FitStabilitySpec','FitStabilityProof']}
AUDITS.update({
    'FlavorSpec': [],
    'FlavorProof': ['matter_index_counts_flavors','trace_coefficient','running_coefficient',
        'flavor_screening_increment','six_flavor_target_coefficient','asymptotic_freedom_integer_range',
        'trajectory_budget_integer_range','flavor_test'],
    'ScreeningSpec': [],
    'ScreeningProof': ['bounded_log_error_gives_coefficient','fermion_screening_test',
        'many_flavor_screening','fermion_screening_nonvacuous'],
    'FlavorDeterminantSpec': [],
    'FlavorDeterminantProof': ['repeated_logdet','repeated_rectify_factor','repeated_response_factor',
        'flavor_determinant_test','response_flavor_increment','zero_flavor_response'],
    'TwoLoopSpec': [],
    'TwoLoopProof': ['log_over_scale_vanishes','arbitrary_loglog_same_leading_slope',
        'loglog_read_recovers_coefficient','leading_slope_does_not_fix_two_loop','distinct_loglog_limits',
        'log_corrected_eventually_positive','second_order_read_stable','log_corrected_derivative',
        'next_order_flow_detector','six_flavor_loglog_benchmark','two_loop_flow_selects_loglog',
        'two_loop_stiffness_bridge'],
    'BanksZaksSpec': [],
    'BanksZaksProof': ['one_loop_positive_iff','two_loop_negative_iff','bz_root_equation',
        'bz_root_positive','bz_root_is_zero','two_loop_factorization','positive_zero_unique',
        'two_loop_integer_window','six_flavor_no_two_loop_zero','sixteen_flavor_root',
        'bz_beta_derivative','bz_derivative_at_root','bz_derivative_positive','bz_flow_below',
        'bz_flow_above','bz_weak_limit','bz_window_fails_trajectory_budget','banks_zaks_test'],
    'RunningConventionSpec': [],
    'RunningConventionProof': ['g_flow_to_normalized_flow','g_flow_to_wilson_flow',
        'running_convention_test','six_loop_coefficients','sixteen_alpha_fixed_point',
        'one_loop_truncation_misses_six_flavor_term'],
    'BZTrajectorySpec': [],
    'BZTrajectoryProof': ['bounded_function_cannot_have_positive_tail_speed','beta_speed_lower',
        'truncated_trajectory_antitone','truncated_trajectory_ir_limit','truncated_trajectory_uv_limit',
        'bz_trajectory_test'],
    'BZHigherOrderSpec': [],
    'BZHigherOrderProof': ['corrected_root_distance','bz_remainder_test','three_loop_sixteen_bracket',
        'three_loop_six_no_small_root','three_loop_six_strong_root','three_loop_benchmark_test'],
    'NormalizationBoundSpec': [],
    'NormalizationBoundProof': ['axial_mass_residual','polar_mass_residual','fitted_mass_sum_lower',
        'fitted_mass_difference_lower','quantitative_normalization_test'],
})
MODULES = list(AUDITS)
PREFIX = 'YMReview.QCD.'
TARGETS = ['flavor_test','fermion_screening_test','flavor_determinant_test','banks_zaks_test',
    'leading_slope_does_not_fix_two_loop','second_order_read_stable','two_loop_stiffness_bridge',
    'running_convention_test','bz_trajectory_test','bz_remainder_test','three_loop_benchmark_test',
    'quantitative_normalization_test']
