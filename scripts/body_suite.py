"""Microscopic density reading and the active schedule flavor restriction."""
from semantic_suite import AUDITS as PREVIOUS
from flavor_suite import AUDITS as FLAVOR

AUDITS = {m: PREVIOUS[m] for m in ['AcceptanceSpec','ContinuumSpec','CouplingSpec','CouplingProof']}
AUDITS.update({m: FLAVOR[m] for m in ['FlavorSpec','FlavorProof']})
AUDITS.update({
    'BodyScopeSpec': [],
    'BodyScopeProof': ['regulator_body_flavor_blind','regulator_stiffness_flavor_blind',
        'regulator_marginal_keeps_flavors','body_scope_test'],
    'ScheduleBudgetSpec': [],
    'ScheduleBudgetProof': ['actual_schedule_margin','earlier_requires_eight_or_fewer',
        'actual_schedule_test'],
})
MODULES = list(AUDITS)
PREFIX = 'YMReview.QCD.'
TARGETS = ['body_scope_test','actual_schedule_test']
