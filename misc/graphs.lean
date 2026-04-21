import Mathlib

-- A SimpleGraph on a vertex type V is just a symmetric, irreflexive adjacency relation
-- structure SimpleGraph (V : Type*) where
  -- Adj : V → V → Prop
  -- symm : ∀ u v, Adj u v → Adj v u
  -- loopless : ∀ v, ¬ Adj v v

-- K3: complete graph on 3 vertices
def K3 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun i j => i ≠ j)

-- P4: path  0—1—2—3
def P4 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j => i.val + 1 = j.val)

-- C4: cycle  0—1—2—3—0
def C4 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j => (i.val + 1) % 4 = j.val)

-- Mathlib already has this:
#check SimpleGraph.emptyGraph   -- SimpleGraph V with no edges

variable {V : Type*} (G : SimpleGraph V)

-- Neighborhood of a vertex v: all vertices adjacent to v
-- G.neighborSet v          -- : Set V

-- Degree of v (when V is finite)
-- G.degree v               -- : ℕ

-- Edge set
-- G.edgeSet                -- : Set (Sym2 V)

-- Subgraph
-- G.IsSubgraph              -- another SimpleGraph is a subgraph

-- Finset of neighbors (needs [Fintype] and [DecidableRel])
-- G.neighborFinset v       -- : Finset V

example : K3.degree 0 = 2 := by
  decide
-- `decide` works for finite computable examples
