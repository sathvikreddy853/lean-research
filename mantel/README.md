# Mantel's Theorem
This module formalizes Mantel's Theorem in Lean using `SimpleGraph`.

### Statement of Mantel's Theorem

Let $G = (V, E)$ be a finite simple graph with no triangles. Then:

$$
|E| \leq \frac{|V|^2}{4}
$$

## Definitions

### Triangle-Free Graph

A graph is triangle-free if:

$$
\forall\; u,v,w \in V,\quad \neg\big((u, v) \in E \land (v, w) \in E \land (u,w) \in E\big)
$$

## Lemmas Used

The theorem is built through the following sequence of lemmas:

### 1. Neighborhood Characterization

$$
v \in N(u) \iff (u, v) \in E
$$

### 2. Degree via Neighborhood Size

$$
|N(v)| = \deg(v)
$$

### 3. No Common Neighbor

If $(u, v) \in E$, then:

$$
\nexists\; w \in V \text{ such that } (u, w) \in E \land (v, w) \in E
$$

### 4. Disjoint Neighborhoods

If $(u, v) \in E$, then:

$$
N(u) \cap N(v) = \varnothing
$$

### 5. Degree Bound on Edges

For any edge $(u, v) \in E$:

$$
\deg(u) + \deg(v) \leq |V|
$$

### 6. Handshaking Lemma

$$
\sum_{v \in V} \deg(v) = 2|E|
$$

### 7. Sum of Squared Degrees Bound

$$
\sum_{v \in V} \deg(v)^2 \leq |V| \cdot |E|
$$

### 8. The Main Inequality

Using Cauchy-Schwarz:

$$
\left( \sum_{v \in V} \deg(v) \right)^2
\leq |V| \sum_{v \in V} \deg(v)^2
$$

Substitute:

$$
(2|E|)^2 \leq |V|^2 |E|
$$

### 9. Final Bound

$$
4|E|^2 \leq |V|^2 |E|
\Rightarrow
|E| \leq \frac{|V|^2}{4}
$$
