import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option warningAsError false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
open Finset

namespace Mantel

variable {V : Type}
variable {G : SimpleGraph V}

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/--
A graph is triangle-free if it contains no triple of vertices
u, v, w such that all three edges uv, vw, uw are present.
Formally: ∀ u v w, ¬(uv ∈ E ∧ vw ∈ E ∧ uw ∈ E).
-/
def TriangleFree : Prop :=
  ∀ (u v w : V), G.Adj u v → G.Adj v w → G.Adj u w → False

/--
A vertex v belongs to the neighborhood of u if and only if u and v are adjacent.
Formally: v ∈ N(u) ↔ uv ∈ E.
-/
lemma mem_neighborFinset_iff_adj {u v : V} :
  v ∈ G.neighborFinset u ↔ G.Adj u v := by
  sorry

/--
The size of the neighborhood of a vertex equals its degree.
Formally: |N(v)| = deg(v).
-/
lemma card_neightFinset_eq_degree (v : V) :
  (G.neighborFinset v).card = G.degree v := by
  sorry

/--
In a triangle-free graph, if uv is an edge, then there is no vertex w
adjacent to both u and v.
Formally: uv ∈ E ⇒ ¬∃ w, uw ∈ E ∧ vw ∈ E.
-/
lemma no_common_neighbor_of_edge
  (htri : TriangleFree (G := G)) {u v w : V} (huv : G.Adj u v) :
  ¬ (G.Adj u w ∧ G.Adj v w) := by
  sorry

/--
In a triangle-free graph, if uv is an edge, then the neighborhoods
of u and v are disjoint.
Formally: uv ∈ E ⇒ N(u) ∩ N(v) = ∅.
-/
lemma neighborFinsets_disjoint_for_edge
  (htri : TriangleFree (G := G)) {u v w : V} (huv : G.Adj u v) :
  (G.neighborFinset u) ∩ (G.neighborFinset v) = ∅ := by
  sorry

/--
In a triangle-free graph, for any edge uv, the sum of degrees is bounded
by the number of vertices.
Formally: uv ∈ E ⇒ deg(u) + deg(v) ≤ |V|.
-/
lemma sum_of_degree_le_card_of_vertex_set
  (htri : TriangleFree (G := G)) {u v : V} (huv : G.Adj u v) :
  G.degree u + G.degree v ≤ Fintype.card V := by
  sorry

/--
(Handshaking Lemma)
The sum of degrees of all vertices equals twice the number of edges.
Formally: ∑_v deg(v) = 2|E|.
-/
lemma handshake_lemma :
  (∑ v : V, G.degree v) = 2 * G.edgeFinset.card := by
  sorry

/--
In a triangle-free graph, the number of edges satisfies:
4|E| ≤ |V|^2.
This is the key inequality leading to Mantel's theorem.
-/
lemma four_mul_edges_le_sq_vertex_set_card
  (htri : TriangleFree (G := G)) :
  4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by
  sorry

/--
Mantel's Theorem:
A triangle-free graph on n vertices has at most n^2 / 4 edges.
Formally: |E| ≤ |V|^2 / 4.
-/
theorem mantel
  (htri : TriangleFree (G := G)) :
  G.edgeFinset.card ≤ (Fintype.card V ^ 2) / 4 := by
  sorry

end Finite
end Mantel
