"""Contact normalization and flavor compatibility; Lean-only supplement."""
AUDITS = {
    'MassFitSpec': [],
    'MassCurrentProof': [
        'mark_contact', 'finite_vector_contact', 'finite_axial_contact',
        'simultaneous_current_density_rescaling', 'nonzero_contact_fixes_scale',
        'common_scalar_requires_cycle', 'vector_example_antisymmetric',
        'vector_example_close', 'vector_example_no_common_mass',
        'axial_example_no_common_mass',
    ],
}
MODULES = list(AUDITS)
PREFIX = 'YMReview.QCD.'
