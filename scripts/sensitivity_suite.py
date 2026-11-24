"""Running sensitivity, complete reference dynamics, and an actual QCD witness."""
from semantic_suite import AUDITS as SEMANTIC
from flavor_suite import AUDITS as FLAVOR

AUDITS = dict(SEMANTIC)
AUDITS.update(FLAVOR)
AUDITS.update({
    'DifferentialRunningSpec': [],
    'DifferentialRunningProof': ['bounded_error_over_diverging_scale','oscillation_bound',
        'oscillation_preserves_leading','oscillation_preserves_loglog','oscillating_running_derivative',
        'oscillating_running_derivative_positive','oscillating_derivative_has_no_limit',
        'differential_running_test'],
    'BZExistenceSpec': [],
    'BZExistenceProof': ['positive_log_derivative','positive_log_strictMono','positive_log_surjective',
        'positive_log_inverse_positive','positive_log_inverse_right','positive_log_inverse_continuous',
        'positive_log_inverse_derivative','truncated_trajectory_exists','bz_global_test',
        'bz_initial_value_test'],
    'BZInvariantSpec': [],
    'BZInvariantProof': ['bz_offset_positive','bz_offset_inverse','bz_offset_coefficient',
        'bz_clock_coordinate_positive','bz_clock_derivative','bz_clock_injective',
        'bz_finite_scale_test','bz_uniqueness_test'],
    'BZAsymptoticSpec': [],
    'BZAsymptoticProof': ['implicit_log_flow_leading','implicit_log_flow_subleading',
        'bz_inverse_uv_expansion','bz_uv_running_test'],
    'BZCriticalSpec': [],
    'BZCriticalProof': ['bz_gap_log_derivative','bz_gap_log_speed_limit','bz_gap_exponential_rate',
        'bz_critical_test'],
    'RunningSchemeSpec': [],
    'RunningSchemeProof': ['scheme_low_coefficients','running_scheme_test'],
    'RunningWitnessSpec': [],
    'RunningWitnessProof': ['six_flavor_coefficient_positive','cutoff_stiffness_positive',
        'running_witness_test'],
})
MODULES = list(AUDITS)
PREFIX = 'YMReview.QCD.'
TARGETS = ['differential_running_test','bz_initial_value_test','bz_finite_scale_test',
    'bz_uniqueness_test','bz_uv_running_test','bz_critical_test','running_scheme_test',
    'running_witness_test']
