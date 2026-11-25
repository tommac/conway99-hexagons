#!/usr/bin/env python3
"""
crosscheck_lean.py — byte-for-byte cross-check of the combinatorial frame
between the Lean formalization and the Python constraint generator.

The Lean side (lean/frame_export.txt, produced by `lake exe export_frame`)
is COMPUTED FROM THE PROVEN DEFINITIONS in lean/Conway99/Group.lean: sigma
(a proven permutation of N(0) preserving the matching, for every wreath
element), tabulated through the canonical label order.  The Python side
(src/symmetry.py) is what actually generates the CNF lex constraints.

If the two agree line-for-line — 84 labels plus the 91 structured elements'
induced edge permutations, 3,486 entries each — then Python's tables match
a machine-checked reference implementation, and the soundness theorems in
lean/Conway99/LexLeader.lean apply to the constraints symbreak.py emits.

Exit codes: 0 = identical, 1 = mismatch (investigate before trusting any
symmetry-broken instance), 2 = export file missing (run
`lake exe export_frame` inside lean/ first).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import symmetry


def python_lines():
    lines = []
    for a, b in symmetry.outside_labels():
        lines.append('%d %d' % (a, b))
    for pi, s in symmetry.structured_elements():
        P = symmetry.element_edge_perm(pi, s)
        lines.append(' '.join(map(str, P)))
    return lines


def main():
    path = Path(__file__).parent.parent / 'lean' / 'frame_export.txt'
    if not path.exists():
        print('SKIP: lean/frame_export.txt not found — '
              'run `lake exe export_frame` in lean/ first')
        sys.exit(2)
    lean_lines = path.read_text().splitlines()
    py = python_lines()
    if len(lean_lines) != len(py):
        print('MISMATCH: %d lean lines vs %d python lines'
              % (len(lean_lines), len(py)))
        sys.exit(1)
    for i, (l, p) in enumerate(zip(lean_lines, py)):
        if l != p:
            print('MISMATCH at line %d:' % (i + 1))
            print('  lean  : %s' % l[:100])
            print('  python: %s' % p[:100])
            sys.exit(1)
    print('CROSS-CHECK PASS: %d lines identical (84 labels + 91 edge '
          'permutations x 3486 entries) — Python frame == Lean-proven frame'
          % len(py))


if __name__ == '__main__':
    main()
