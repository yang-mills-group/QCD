"""What a bounded higher-order correction does and does not guarantee."""
from flavor_suite import AUDITS as PREVIOUS

AUDITS = {m: PREVIOUS[m] for m in ['FlavorSpec','FlavorProof','BanksZaksSpec','BanksZaksProof',
    'BZHigherOrderSpec','BZHigherOrderProof']}
AUDITS.update({
    'BZRobustnessSpec': [],
    'BZRobustnessProof': ['plateau_continuous','plateau_bound','plateau_zero',
        'bound_alone_not_unique','corrected_bracket_derivative',
        'corrected_beta_derivative_at_zero','bz_robustness_test',
        'sixteen_three_loop_remainder_bounds','three_loop_corrected_beta','three_loop_robustness_test'],
})
MODULES = list(AUDITS)
PREFIX = 'YMReview.QCD.'
TARGETS = ['bound_alone_not_unique','bz_robustness_test','three_loop_robustness_test']
