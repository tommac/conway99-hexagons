/-
Conway99.ExportFrame — export the combinatorial frame, COMPUTED FROM THE
PROVEN DEFINITIONS (`sigma` from Conway99.Group), for byte-for-byte
cross-checking against the Python implementation (`src/symmetry.py`).

Run:            lake exe export_frame          (from lean/)
Output:         lean/frame_export.txt
Cross-check:    python3 src/crosscheck_lean.py (from the repo root)

Format: 84 lines "a b" — the outside labels, 1-based, in the canonical
order — followed by 91 lines, one per structured group element in the exact
order of `symmetry.structured_elements()`, each holding the induced
edge-position permutation P as 3,486 space-separated integers
(P[t] = image position of slot t, so the lex constraint is X ≤ X∘P).
-/
import Conway99.Group

namespace Conway99.ExportFrame

open Conway99

/-- The 84 labels, 0-based ordered pairs, in the canonical (lex) order —
definitionally the same order as Python's `outside_labels()` after the
1-based shift. -/
def labelList : List (Fin 14 × Fin 14) :=
  (List.finRange 14).flatMap fun i =>
    (List.finRange 14).filterMap fun j =>
      if i < j ∧ pairOf i ≠ pairOf j then some (i, j) else none

/-- Row-major upper-triangle position index over 84 labels:
`edgeIdx a b` (a < b) = position of slot {a,b} in the canonical order. -/
def edgeIdx (a b : Nat) : Nat :=
  a * (2 * 84 - a - 1) / 2 + (b - a - 1)

/-- The induced edge-position permutation of a wreath element, one line of
3,486 integers, computed via the PROVEN `sigma`. -/
def elementLine (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) : String :=
  let imgIdx : Array Nat := (labelList.map fun p =>
    let x := sigma π s p.1
    let y := sigma π s p.2
    labelList.idxOf (if x < y then (x, y) else (y, x))).toArray
  let parts : List String :=
    (List.range 84).flatMap fun u =>
      (List.range 84).filterMap fun v =>
        if u < v then
          let iu := imgIdx[u]!
          let iv := imgIdx[v]!
          some (toString (edgeIdx (min iu iv) (max iu iv)))
        else none
  String.intercalate " " parts

/-- Sign vector supported on `{a, b}`. -/
def signOf (a : Fin 7) (sa : Bool) (b : Fin 7) (sb : Bool) : Fin 7 → Bool :=
  fun x => (decide (x = a) && sa) || (decide (x = b) && sb)

/-- The 91 structured elements, in the exact order of Python's
`symmetry.structured_elements()`: 7 single-pair flips, then for each pair
transposition a<b the sign patterns (0,0),(0,1),(1,0),(1,1). -/
def structuredElements : List (Equiv.Perm (Fin 7) × (Fin 7 → Bool)) :=
  ((List.finRange 7).map fun a =>
    ((1 : Equiv.Perm (Fin 7)), fun x => decide (x = a)))
  ++ ((List.finRange 7).flatMap fun a =>
      (List.finRange 7).flatMap fun b =>
        if a < b then
          [(false, false), (false, true), (true, false), (true, true)].map
            fun sasb => (Equiv.swap a b, signOf a sasb.1 b sasb.2)
        else [])

def main : IO Unit := do
  let mut lines : Array String := #[]
  for p in labelList do
    lines := lines.push s!"{p.1.val + 1} {p.2.val + 1}"
  for e in structuredElements do
    lines := lines.push (elementLine e.1 e.2)
  IO.FS.writeFile "frame_export.txt"
    (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"wrote frame_export.txt: {labelList.length} labels, {structuredElements.length} elements"

end Conway99.ExportFrame

def main : IO Unit := Conway99.ExportFrame.main
