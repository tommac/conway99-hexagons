#!/usr/bin/env python3
"""
verify.py — INDEPENDENT checker for a claimed strongly regular graph.

Deliberately shares no code with the encoder: it recomputes everything
directly from the adjacency matrix.  Any solution we ever announce must
pass this (and ideally a second, third-party checker) first.

Usage: python3 verify.py solution.json
where solution.json = {"params": [v,k,lam,mu], "adjacency": [[...], ...]}
"""

import json
import sys


def verify(params, A):
    v, k, lam, mu = params
    errors = []

    if len(A) != v or any(len(row) != v for row in A):
        return [f'adjacency matrix is not {v}x{v}']
    for i in range(v):
        if A[i][i] != 0:
            errors.append(f'self-loop at vertex {i}')
        for j in range(i + 1, v):
            if A[i][j] not in (0, 1) or A[i][j] != A[j][i]:
                errors.append(f'bad/asymmetric entry at ({i},{j})')

    for i in range(v):
        deg = sum(A[i])
        if deg != k:
            errors.append(f'vertex {i} has degree {deg}, expected {k}')

    for i in range(v):
        for j in range(i + 1, v):
            common = sum(1 for w in range(v)
                         if w != i and w != j and A[i][w] and A[j][w])
            want = lam if A[i][j] else mu
            if common != want:
                errors.append(
                    f'pair ({i},{j}) adj={A[i][j]}: {common} common '
                    f'neighbors, expected {want}')
                if len(errors) > 20:
                    errors.append('... (truncated)')
                    return errors
    return errors


def main():
    with open(sys.argv[1]) as f:
        data = json.load(f)
    errors = verify(data['params'], data['adjacency'])
    v, k, lam, mu = data['params']
    if errors:
        print(f'INVALID srg({v},{k},{lam},{mu}):')
        for e in errors[:20]:
            print('  -', e)
        sys.exit(1)
    print(f'VERIFIED: this is a genuine srg({v},{k},{lam},{mu}).')
    sys.exit(0)


if __name__ == '__main__':
    main()
