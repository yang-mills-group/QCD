#!/usr/bin/env python3
"""Regression controls for the offline receipt and manifest checker.

These tests use disposable files. They are packaging checks, separate from the
Lean declaration counts and the QCD specification-mutation controls.
"""
import hashlib
from pathlib import Path
import tempfile
import unittest

from verify_evidence import check_axiom_log, check_manifest
from test_flavor_mutations import has_infrastructure_error


class EvidenceCheckerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root/'provenance').mkdir()
        self.log = self.root/'compiler.log'
        self.report = "info: Example.lean:3:0: 'Review.example' depends on axioms: [propext, Quot.sound]\n"
        self.expected = {'Review.example': ['propext', 'Quot.sound']}

    def manifest(self, names):
        rows = [hashlib.sha256((self.root/name).read_bytes()).hexdigest()+'  '+name for name in names]
        (self.root/'provenance/review-files.sha256').write_text('\n'.join(rows)+'\n')

    def test_matching_axiom_receipt(self):
        self.log.write_text(self.report)
        check_axiom_log(self.log, self.expected)

    def test_changed_axiom_receipt_rejected(self):
        self.log.write_text(self.report)
        with self.assertRaisesRegex(SystemExit, 'matches compiler log'):
            check_axiom_log(self.log, {'Review.example': ['propext']})

    def test_unreported_axiom_rejected(self):
        self.log.write_text(self.report.replace('Quot.sound', 'sorryAx'))
        with self.assertRaisesRegex(SystemExit, 'matches compiler log'):
            check_axiom_log(self.log, self.expected)

    def test_duplicate_axiom_message_rejected(self):
        self.log.write_text(self.report*2)
        with self.assertRaisesRegex(SystemExit, 'duplicate axiom'):
            check_axiom_log(self.log, self.expected)

    def test_proof_hole_warning_rejected(self):
        self.log.write_text(self.report+"warning: declaration uses 'sorry'\n")
        with self.assertRaisesRegex(SystemExit, 'no proof holes'):
            check_axiom_log(self.log, self.expected)

    def test_empty_spec_log(self):
        self.log.write_text('')
        check_axiom_log(self.log, {})

    def test_resource_failure_is_not_a_successful_mutation(self):
        for diagnostic in ['error: maximum number of heartbeats has been reached',
                           'error: maximum recursion depth has been reached',
                           'error: (deterministic) timeout', 'error: Out of memory',
                           "error: unknown module prefix 'Missing'", 'error: Permission denied']:
            with self.subTest(diagnostic=diagnostic):
                self.assertTrue(has_infrastructure_error(diagnostic))
        self.assertFalse(has_infrastructure_error('error: Application type mismatch'))

    def test_complete_manifest(self):
        (self.root/'README.md').write_text('review\n')
        self.manifest(['README.md'])
        self.assertEqual(check_manifest(self.root), 1)

    def test_changed_file_rejected(self):
        (self.root/'README.md').write_text('review\n')
        self.manifest(['README.md'])
        (self.root/'README.md').write_text('changed\n')
        with self.assertRaisesRegex(SystemExit, 'review manifest README'):
            check_manifest(self.root)

    def test_omitted_evidence_rejected(self):
        (self.root/'README.md').write_text('review\n')
        self.manifest(['README.md'])
        (self.root/'evidence').mkdir()
        (self.root/'evidence/unlisted.json').write_text('{}\n')
        with self.assertRaisesRegex(SystemExit, 'manifest inventory: missing'):
            check_manifest(self.root)

    def test_duplicate_manifest_entry_rejected(self):
        (self.root/'README.md').write_text('review\n')
        self.manifest(['README.md', 'README.md'])
        with self.assertRaisesRegex(SystemExit, 'manifest unique entry'):
            check_manifest(self.root)

    def test_missing_packaged_file_rejected(self):
        (self.root/'README.md').write_text('review\n')
        self.manifest(['README.md'])
        (self.root/'README.md').unlink()
        with self.assertRaisesRegex(SystemExit, 'unexpected'):
            check_manifest(self.root)

    def test_path_escape_rejected(self):
        (self.root/'provenance/review-files.sha256').write_text('0'*64+'  ../outside\n')
        with self.assertRaisesRegex(SystemExit, 'manifest relative path'):
            check_manifest(self.root)


if __name__ == '__main__':
    unittest.main()
