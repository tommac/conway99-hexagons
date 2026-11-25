# If Conway's 99-graph exists, it has at least 209,781 induced hexagons

**Tom Maciejewski** · Preprint, 2026 · [Read the paper (PDF)](paper.pdf)

## Abstract

Conway's 99-graph problem asks whether a strongly regular graph with parameters $(99,14,1,2)$ exists. Reimbayev showed that such a graph has at least $209{,}286$ induced hexagons, with equality exactly when no two disjoint triangles are joined by exactly two edges; by a theorem of Makhnev, equality cannot hold. We prove that such a graph has at least $209{,}781$ induced hexagons, $495$ above Reimbayev's bound. The excess is the number of pairs of disjoint triangles joined by exactly two edges, for which the best bound we know of was $96$. The proof has two parts. A counting identity, proved by hand and in Lean, expresses this number through a local statistic $D(x)\le84$ at each vertex $x$. A SAT computation shows that $D(x)\le74$ at every vertex. Its refutation is accepted by two independent proof checkers, one of them formally verified, and the symmetry breaking it uses is proved sound in Lean as an abstract theorem; the translation of the problem into the instance is tested, not formally verified. The existence problem remains open.

## Contents

| File | What it is |
|---|---|
| [`paper.pdf`](paper.pdf) | The paper (7 pages) |
| [`paper.tex`](paper.tex) | Its LaTeX source |
| [`artifact/`](artifact/) | Code that regenerates every SAT instance and checks every proof, the certificate ledger, and the Lean development. Start with artifact/README.md. |

## Citing this paper

```bibtex
@misc{maciejewski2026conway99,
  author = {Maciejewski, Tom},
  title  = {If {Conway}'s 99-graph exists, it has at least 209,781 induced hexagons},
  year   = {2026},
  note   = {Preprint},
  url    = {https://github.com/tommac/conway99-hexagons},
}
```

## Status

This is a preprint and has not been peer reviewed. If you find an error, please open an issue.

## License

The paper is licensed under [CC BY 4.0](LICENSE). The code in `artifact/` is under the [MIT License](LICENSE-CODE).
