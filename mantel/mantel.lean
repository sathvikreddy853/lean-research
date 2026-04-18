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
  simp [SimpleGraph.mem_neighborFinset]

/--
The size of the neighborhood of a vertex equals its degree.
Formally: |N(v)| = deg(v).
-/
lemma card_neighborFinset_eq_degree (v : V) :
  (G.neighborFinset v).card = G.degree v := by
  simp [SimpleGraph.card_neighborFinset_eq_degree]

/--
In a triangle-free graph, if uv is an edge, then there is no vertex w
adjacent to both u and v.
Formally: uv ∈ E ⇒ ¬∃ w, uw ∈ E ∧ vw ∈ E.
-/
lemma no_common_neighbor_of_edge
  (htri : TriangleFree (G := G)) {u v w : V} (huv : G.Adj u v) :
  ¬ (G.Adj u w ∧ G.Adj v w) := by
  intro h
  rcases h with ⟨huw, hvw⟩
  exact htri u v w huv hvw huw

/--
In a triangle-free graph, if uv is an edge, then the neighborhoods
of u and v are disjoint.
Formally: uv ∈ E ⇒ N(u) ∩ N(v) = ∅.
-/
lemma neighborFinsets_disjoint_for_edge
  (htri : TriangleFree (G := G)) {u v : V} (huv : G.Adj u v) :
  Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
  rw [disjoint_left]
  intro w huw hvw
  rw [mem_neighborFinset_iff_adj] at huw hvw
  exact no_common_neighbor_of_edge htri huv ⟨huw, hvw⟩

/--
In a triangle-free graph, for any edge uv, the sum of degrees is bounded
by the number of vertices.
Formally: uv ∈ E ⇒ deg(u) + deg(v) ≤ |V|.
-/
lemma sum_of_degree_le_card_of_vset
  (htri : TriangleFree (G := G)) {u v : V} (huv : G.Adj u v) :
  G.degree u + G.degree v ≤ Fintype.card V := by
    rw [← card_neighborFinset_eq_degree u]
    rw [← card_neighborFinset_eq_degree v]
    have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) :=
      neighborFinsets_disjoint_for_edge htri huv
    rw [← Finset.card_union_of_disjoint hdisj]
    apply Finset.card_le_univ

/--
(Handshaking Lemma)
The sum of degrees of all vertices equals twice the number of edges.
Formally: ∑_v deg(v) = 2|E|.
-/
lemma handshaking_lemma :
  (∑ v : V, G.degree v) = 2 * G.edgeFinset.card := by
  exact SimpleGraph.sum_degrees_eq_twice_card_edges G

/--
The sum of squares of degrees is bounded by the product of the number of vertices and edges.
Formally: ∑_v deg(v)^2 ≤ |V||E|
-/
lemma sum_sq_degree_le_card_vset_mul_card_edges :
  (∑ v : V, (G.degree v)^2 ) ≤ G.edgeFinset.card * Fintype.card V := by
  apply?

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
