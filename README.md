# Search Algorithms on Directed Graphs in LEAN4

The [mathlib](https://github.com/leanprover-community/mathlib4) currently does not contain a description of weighted directed graphs or algorithms for it. This repo provides their definition and basic search algorithms for these graphs. We consider only finite graphs whose nodes and edges can be effectively enumerated or their existence can be effecrively tested, respectively. We define the following graph search algorithms:

- DFS
- BFS
- Dijksta
- A*

And prove their correctness. For A* we also provide a formalisation of admissability and the conditional proof that A* is finds optimal paths if an admissible heuristic is provided.

## Dependency Graph

![Dependency graph](dependencies.svg)

(Update this graph with `make dependencies.svg`.)
