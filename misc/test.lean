import Mathlib

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Mantel

variable {V : Type}
variable (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/--
A graph is triangle-free if it contains no triple of vertices
u, v, w such that all three edges uv, vw, uw are present.
Formally: ∀ u v w, ¬(uv ∈ E ∧ vw ∈ E ∧ uw ∈ E).
-/
def TriangleFree : Prop :=
  ∀ ⦃u v w : V⦄, G.Adj u v → G.Adj v w → G.Adj u w → False

/--
n = |V| is the number of vertices in the graph.
-/
def n : ℕ := Fintype.card V

/--
m = |E| is the number of edges in the graph.
-/
def m : ℕ := G.edgeFinset.card

/--
A vertex v belongs to the neighborhood of u if and only if u and v are adjacent.
Formally: v ∈ N(u) ↔ uv ∈ E.
-/
lemma mem_neighborFinset_iff {u v : V} :
    v ∈ G.neighborFinset u ↔ G.Adj u v := by
  simp [SimpleGraph.neighborFinset]

/--
The size of the neighborhood of a vertex equals its degree.
Formally: |N(v)| = deg(v).
-/
lemma card_neighborFinset_eq_degree (v : V) :
    (G.neighborFinset v).card = G.degree v := by
  simp [SimpleGraph.degree]

/--
In a triangle-free graph, if uv is an edge, then there is no vertex w
adjacent to both u and v.
Formally: uv ∈ E ⇒ ¬∃ w, uw ∈ E ∧ vw ∈ E.
-/
lemma no_common_neighbor_of_adj
    (htri : G.TriangleFree) {u v w : V} (huv : G.Adj u v) :
    ¬ (G.Adj u w ∧ G.Adj v w) := by
  intro h
  rcases h with ⟨huw, hvw⟩
  exact htri huv hvw huw

/--
In a triangle-free graph, if uv is an edge, then the neighborhoods
of u and v are disjoint.
Formally: uv ∈ E ⇒ N(u) ∩ N(v) = ∅.
-/
lemma neighborFinset_disjoint_of_adj
    (htri : G.TriangleFree) {u v : V} (huv : G.Adj u v) :
    Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
  classical
  rw [Finset.disjoint_left]
  intro w huw hwv
  exact (no_common_neighbor_of_adj (G := G) htri huv) ⟨
    (mem_neighborFinset_iff (G := G)).mp huw,
    (mem_neighborFinset_iff (G := G)).mp hwv
  ⟩

/--
In a triangle-free graph, for any edge uv, the sum of degrees is bounded
by the number of vertices.
Formally: uv ∈ E ⇒ deg(u) + deg(v) ≤ |V|.
-/
lemma degree_add_degree_le_card_of_adj
    (htri : G.TriangleFree) {u v : V} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ Fintype.card V := by
  sorry

/--
(Handshaking Lemma)
The sum of degrees of all vertices equals twice the number of edges.
Formally: ∑_v deg(v) = 2|E|.
-/
lemma sum_degrees_eq_twice_edges :
    (∑ v, G.degree v) = 2 * G.edgeFinset.card := by
  simpa using G.sum_degrees_eq_twice_card_edges

/--
In a triangle-free graph, the number of edges satisfies:
4|E| ≤ |V|^2.
This is the key inequality leading to Mantel's theorem.
-/
lemma four_mul_edges_le_sq_card
    (htri : G.TriangleFree) :
    4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by
  sorry

/--
Mantel's Theorem:
A triangle-free graph on n vertices has at most n^2 / 4 edges.
Formally: |E| ≤ |V|^2 / 4.
-/
theorem mantel
    (htri : G.TriangleFree) :
    G.edgeFinset.card ≤ (Fintype.card V ^ 2) / 4 := by
  sorry

end Finite
end Mantel
