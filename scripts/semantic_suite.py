"""Explicit module/theorem inventory for the November 18 correspondence checks."""
AUDITS = {
    'MassFitSpec': [],
    'MassFitProof': ['loss_gap','mass_fit_correct','six_pair_difference','example_accuracy'],
    'AcceptanceSpec': [],
    'ContinuumSpec': [],
    'ContinuumProof': ['correlator_limit_along_sites','literal_limit','continuum_acceptance'],
    'StressSpec': [],
    'StressProof': ['two_detected_candidates_exclude_stress','stress_exclusion','sector_controls','sector_no_collapse'],
    'StressControlProof': ['constant_tensor_rotates','constant_tensor_candidate','stress_control_test'],
    'CurrentSpec': [],
    'CurrentProof': ['divergence_with_spectators','current_ward_test','normalization_test',
                     'small_errors_do_not_force_additive_masses','residual_uniform_small',
                     'residual_derivative_stays_one','residual_bound_tends_zero'],
    'CouplingSpec': [],
    'CouplingProof': ['canonical_coefficient','cutoff_log_diverges','cutoff_beta_slope',
                      'bounded_read_preserves_slope','coupling_test','regulator_body_is_wilson',
                      'terminal_body_is_wilson','uv_jet_limit','variable_basis_can_hide_amplitude'],
    'FitStabilitySpec': [],
    'FitStabilityProof': ['fit_error_formula','weight_norm','difference_weight_norm',
                          'weighted_error_bound','fit_stability','target_fit_eq','target_mass_margins'],
}
MODULES = list(AUDITS)
TARGETS = ['continuum_acceptance','stress_exclusion','stress_control_test',
           'current_ward_test','normalization_test','coupling_test','fit_stability']
PREFIX = 'YMReview.QCD.'
