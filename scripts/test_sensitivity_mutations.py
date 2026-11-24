#!/usr/bin/env python3
"""Controls for the reference-flow and actual-witness additions.
Uses the same isolated, source-authenticated runner as the flavor controls.
"""
import test_flavor_mutations as runner
from sensitivity_suite import AUDITS, MODULES, PREFIX

CASES = [
    ('unchanged', 'RunningSchemeSpec', None, None, 'RunningSchemeProof'),
    ('wrong_scheme_transformation', 'RunningSchemeSpec', 'b₂-s*b₁+(t-s^2)*b₀',
        'b₂+s*b₁+(t-s^2)*b₀', 'RunningSchemeProof'),
    ('wrong_finite_scale_factor', 'BZInvariantSpec', '2*oneLoopCoefficient f*(t-s)',
        'oneLoopCoefficient f*(t-s)', 'BZInvariantProof'),
    ('wrong_ir_exponent', 'BZCriticalSpec', 'atBot (𝓝 (bzDerivative f)) ∧',
        'atBot (𝓝 (-bzDerivative f)) ∧', 'BZCriticalProof'),
    ('wrong_reference_wilson_units', 'BZAsymptoticSpec', '(6/(16*Real.pi^2))',
        '(3/(16*Real.pi^2))', 'BZAsymptoticProof'),
    ('overclaimed_current_accuracy', 'RunningWitnessSpec', '≤ 4/197',
        '≤ 1/197', 'RunningWitnessProof'),
]

if __name__ == '__main__':
    runner.AUDITS, runner.MODULES, runner.PREFIX = AUDITS, MODULES, PREFIX
    runner.CASES, runner.SUITE = CASES, 'sensitivity'
    runner.main()
