#!/usr/bin/env python3
"""Check that the contact proofs reject a wrong sign and a dropped remainder."""
import test_flavor_mutations as runner
from mass_current_suite import AUDITS, MODULES, PREFIX

CASES = [
    ('unchanged', 'MassCurrentProof', None, None, 'MassCurrentProof'),
    ('wrong_vector_contact_sign', 'MassCurrentProof',
     '-ber _ (R.density U *\n        (applyMark false (localF u 1 i j)',
     'ber _ (R.density U *\n        (applyMark false (localF u 1 i j)',
     'MassCurrentProof'),
    ('omit_axial_remainder', 'MassCurrentProof',
     '        axial_rest R i j u g5 U)) * y)',
     '        0)) * y)', 'MassCurrentProof'),
]

if __name__ == '__main__':
    runner.AUDITS, runner.MODULES, runner.PREFIX = AUDITS, MODULES, PREFIX
    runner.CASES, runner.SUITE = CASES, 'mass-current'
    runner.main()
