import Mathlib
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option warningAsError false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset
open scoped BigOperators

namespace Mantel

variable {V : Type u}
variable (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/--
A graph is triangle-free if it contains no triple of vertices
u, v, w such that all three edges uv, vw, uw are present.

Formally:
∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → False.
-/
def TriangleFree : Prop :=
  ∀ ⦃u v w : V⦄, G.Adj u v → G.Adj v w → G.Adj u w → False

/--
A vertex v belongs to the neighborhood of u if and only if u and v are adjacent.

Formally:
v ∈ N(u) ↔ uv ∈ E.
-/
lemma mem_neighborFinset_iff_adj {u v : V} :
  v ∈ G.neighborFinset u ↔ G.Adj u v := by
  simp [SimpleGraph.mem_neighborFinset]

/--
The size of the neighborhood of a vertex equals its degree.

Formally:
|N(v)| = deg(v).
-/
lemma card_neighborFinset_eq_degree (v : V) :
  (G.neighborFinset v).card = G.degree v := by
  simp [SimpleGraph.card_neighborFinset_eq_degree]

/--
In a triangle-free graph, if uv is an edge, then there is no vertex w
adjacent to both u and v.

Formally:
uv ∈ E ⇒ ¬∃ w, uw ∈ E ∧ vw ∈ E.
-/
lemma no_common_neighbor_of_edge
  (htri : TriangleFree (G := G)) {u v w : V} (huv : G.Adj u v) :
  ¬ (G.Adj u w ∧ G.Adj v w) := by
  intro h
  rcases h with ⟨huw, hvw⟩
  exact htri huv hvw huw

/--
In a triangle-free graph, if uv is an edge, then the neighborhoods
of u and v are disjoint.

Formally:
uv ∈ E ⇒ N(u) ∩ N(v) = ∅.
-/
lemma neighborFinsets_disjoint_for_edge
  (htri : TriangleFree (G := G)) {u v : V} (huv : G.Adj u v) :
  Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
  rw [disjoint_left]
  intro w huw hvw
  rw [mem_neighborFinset_iff_adj] at huw hvw
  exact no_common_neighbor_of_edge (G := G) htri huv ⟨huw, hvw⟩

/--
In a triangle-free graph, the neighborhoods of the endpoints of any edge are disjoint.
This implies that the sum of their degrees is bounded by the total number of vertices.

Mathematically:
If uv ∈ E, then
deg(u) + deg(v) ≤ |V|.
-/
lemma sum_of_degree_le_card_of_vset
  (htri : TriangleFree (G := G)) {u v : V} (huv : G.Adj u v) :
  G.degree u + G.degree v ≤ Fintype.card V := by
    rw [← card_neighborFinset_eq_degree (G := G) u]
    rw [← card_neighborFinset_eq_degree (G := G) v]
    have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) :=
      neighborFinsets_disjoint_for_edge (G := G) htri huv
    rw [← Finset.card_union_of_disjoint hdisj]
    apply Finset.card_le_univ

/--
(Handshaking Lemma)

The sum of the degrees of all vertices equals twice the number of edges.

Mathematically:
∑_{v ∈ V} deg(v) = 2|E|.
-/
lemma handshaking_lemma :
  (∑ v : V, G.degree v) = 2 * G.edgeFinset.card := by
  exact SimpleGraph.sum_degrees_eq_twice_card_edges G

set_option linter.flexible false in
/--
Cauchy–Schwarz inequality applied to the degree sequence.

Mathematically:
(∑_{v ∈ V} deg(v))^2 ≤ |V| · ∑_{v ∈ V} deg(v)^2.
-/
lemma sq_sum_degrees_le_card_vset_mul_sum_sq_degrees :
  (∑ x : V, G.degree x) ^ 2 ≤
    Fintype.card V * (∑ x : V, G.degree x ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (s := Finset.univ)
    (f := fun x : V => G.degree x)
    (g := fun _ : V => (1 : ℕ))
  simp [Finset.sum_const] at h
  simp [Nat.mul_comm] at h
  exact h


/--
In a triangle-free graph, the sum of squares of vertex degrees
is at most the number of edges times the number of vertices.

Formally:
∑_{v ∈ V} deg(v)^2 ≤ |E| · |V|.
-/
lemma sum_sq_degrees_le_card_edges_mul_card_vset
  (htri : TriangleFree (G := G)) :
  (∑ x : V, G.degree x ^ 2) ≤ G.edgeFinset.card * Fintype.card V := by
  sorry

/--
Key inequality leading to Mantel's theorem.

Formally:
4|E| ≤ |V|^2.
-/
lemma four_mul_edges_le_sq_card_vset
  (htri : TriangleFree (G := G)) :
  4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by
  have h1 :=
    sq_sum_degrees_le_card_vset_mul_sum_sq_degrees (G := G)
  have h2 :=
    sum_sq_degrees_le_card_edges_mul_card_vset (G := G) htri
  rw [handshaking_lemma] at h1
  have h3 : (2 * G.edgeFinset.card) ^ 2 ≤ G.edgeFinset.card * (Fintype.card V) ^ 2 := by
    apply le_trans h1
    have h2' := Nat.mul_le_mul_left (Fintype.card V) h2
    simp only [Nat.mul_comm] at h2'
    rw [← Nat.mul_assoc] at h2'
    simp only [← pow_two] at h2'
    conv => rhs; rw [Nat.mul_comm]
    exact h2'
  simp only [mul_pow] at h3
  norm_num at h3
  conv at h3 =>
    lhs;
    simp only [pow_two]
    rw [← mul_assoc]
    rw [← mul_comm]
  by_cases hE : G.edgeFinset.card = 0
  · simp [hE]
  · have hE' : 0 < G.edgeFinset.card := Nat.pos_of_ne_zero hE
    exact Nat.le_of_mul_le_mul_left h3 hE'

/--
Mantel's theorem.

A triangle-free graph on n vertices has at most n^2 / 4 edges.

Formally:
|E| ≤ |V|^2 / 4.
-/
theorem mantel
  (htri : TriangleFree (G := G)) :
  G.edgeFinset.card ≤ (Fintype.card V)^2 / 4 := by
  have h : 4 * G.edgeFinset.card ≤ (Fintype.card V)^2 :=
    four_mul_edges_le_sq_card_vset (G := G) htri
  omega

end Finite
end Mantel
