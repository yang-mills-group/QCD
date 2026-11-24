"""Sharper renP bound using the actual symmetry and separated positive masses."""
from semantic_suite import AUDITS as PREVIOUS

AUDITS = {m: PREVIOUS[m] for m in ['MassFitSpec','MassFitProof','AcceptanceSpec',
    'ContinuumSpec','ContinuumProof','FitStabilitySpec','FitStabilityProof']}
AUDITS.update({
    'SharpNormalizationSpec': [],
    'SharpNormalizationProof': ['sum_weight_norm','symmetric_residual_weight_norm',
        'sum_fit_error_formula','symmetric_residual_formula','sum_fit_error_bound',
        'symmetric_residual_bound','separated_reference_sum','sharp_normalization_test',
        'sharp_normalization_acceptance'],
})
MODULES = list(AUDITS)
PREFIX = 'YMReview.QCD.'
TARGETS = ['sharp_normalization_test','sharp_normalization_acceptance']
