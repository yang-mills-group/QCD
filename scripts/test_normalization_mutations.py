#!/usr/bin/env python3
"""Controls for the symmetric-reading normalization improvement."""
import test_flavor_mutations as runner
from normalization_suite import AUDITS, MODULES, PREFIX

CASES = [
    ('unchanged', 'SharpNormalizationSpec', None, None, 'SharpNormalizationProof'),
    ('wrong_symmetric_projector', 'SharpNormalizationSpec',
        '(if k=i ∧ l=j then 1/2 else 0)', '(if k=i ∧ l=j then 1/3 else 0)',
        'SharpNormalizationProof'),
    ('overclaimed_symmetric_accuracy', 'SharpNormalizationSpec',
        '|s.axial i j/(s.bMass i+s.bMass j)-1| ≤ 12/1489',
        '|s.axial i j/(s.bMass i+s.bMass j)-1| ≤ 11/1489', 'SharpNormalizationProof'),
]

if __name__ == '__main__':
    runner.AUDITS, runner.MODULES, runner.PREFIX = AUDITS, MODULES, PREFIX
    runner.CASES, runner.SUITE = CASES, 'normalization'
    runner.main()
