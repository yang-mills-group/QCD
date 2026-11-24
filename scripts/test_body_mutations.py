#!/usr/bin/env python3
"""Check that the regulator marginal test detects removal of its determinant."""
import test_flavor_mutations as runner
from body_suite import AUDITS, MODULES, PREFIX

CASES = [
    ('wrong_schedule_range', 'ScheduleBudgetSpec',
        '(∀ F : ℕ, 0 < delta₀ F ↔ F ≤ 8)',
        '(∀ F : ℕ, 0 < delta₀ F ↔ F ≤ 9)', 'ScheduleBudgetProof'),
    ('unchanged', 'BodyScopeSpec', None, None, 'BodyScopeProof'),
    ('omitted_marginal_determinant', 'BodyScopeSpec',
        '(Wilson.bare R.β U : ℂ)*∏ i, (QCD.Lat.bareD R.t U (R.m i)).det',
        '(Wilson.bare R.β U : ℂ)', 'BodyScopeProof'),
]

if __name__ == '__main__':
    runner.AUDITS, runner.MODULES, runner.PREFIX = AUDITS, MODULES, PREFIX
    runner.CASES, runner.SUITE = CASES, 'body'
    runner.main()
