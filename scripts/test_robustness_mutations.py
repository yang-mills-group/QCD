#!/usr/bin/env python3
"""Positive and negative controls for higher-order fixed-point robustness."""
import test_flavor_mutations as runner
from robustness_suite import AUDITS, MODULES, PREFIX

CASES = [
    ('unchanged', 'BZRobustnessSpec', None, None, 'BZRobustnessProof'),
    ('reversed_plateau_correction', 'BZRobustnessSpec',
        '-twoLoopCoefficient f*max', 'twoLoopCoefficient f*max', 'BZRobustnessProof'),
    ('insufficient_derivative_bound', 'BZRobustnessSpec',
        'ρ < -twoLoopCoefficient f →', 'ρ < -2*twoLoopCoefficient f →', 'BZRobustnessProof'),
    ('reversed_three_loop_stability', 'BZRobustnessSpec',
        '0 < -2*a^2*(twoLoopCoefficient 16+2*threeLoopCoefficient 16*a)',
        '-2*a^2*(twoLoopCoefficient 16+2*threeLoopCoefficient 16*a) < 0', 'BZRobustnessProof'),
]

if __name__ == '__main__':
    runner.AUDITS, runner.MODULES, runner.PREFIX = AUDITS, MODULES, PREFIX
    runner.CASES, runner.SUITE = CASES, 'robustness'
    runner.main()
