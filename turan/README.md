# Turán's Theorem

This module formalizes Turán’s Theorem in Lean using `SimpleGraph`.

### Statement of Turán’s Theorem

Let $G = (V, E)$ be a finite simple graph with no clique of size $r+1$ (i.e., $K_{r+1}$-free). Then:

$$
|E| \leq |E(T_r(n))|
$$

where $n = |V|$ and $T_r(n)$ is the complete $ r $-partite graph with parts as equal as possible.

Equivalently,

$$
|E| \leq \frac{r-1}{2r} |V|^2
$$

## Definitions

### $K_{r+1}$-Free Graph

A graph is $K_{r+1}$-free if:

$$
\forall\; v_1, \dots, v_{r+1} \in V,\quad
\neg\Big( \bigwedge_{i < j} (v_i, v_j) \in E \Big)
$$

### Complete $r$-Partite Graph

A graph is complete $r$-partite if:

- $V = V_1 \sqcup \cdots \sqcup V_r$
- No edges inside each $V_i$
- All edges exist between $V_i$ and $V_j$ for $i \ne j$

### Turán Graph

Let $n = qr + s$, where $0 \le s < r$. Then:

- $s$ parts have size $q+1$
- $r-s$ parts have size $q$

## Lemmas Used

The theorem is built through the following sequence of lemmas:

### 1. Edge Count in Complete Multipartite Graph

If part sizes are $n_1, \dots, n_r$, then:

$$
|E| = \sum_{i < j} n_i n_j
= \frac12 \left( |V|^2 - \sum_{i=1}^r n_i^2 \right)
$$

### 2. Balancing Lemma

If $a \ge b + 2$, then:

$$
(a-1)^2 + (b+1)^2 < a^2 + b^2
$$

This implies moving vertices between unequal parts increases edge count.

### 3. Optimal Partition Structure

Among all partitions of $ n $ into $ r $ parts:

$$
\sum n_i^2 \text{ is minimized when } |n_i - n_j| \le 1
$$

Thus edge count is maximized when parts are balanced.

### 4. Symmetrization Step

Let $u, v \in V$ be non-adjacent.

If $\deg(u) \le \deg(v)$, replace the neighborhood of $u$ by that of $ v $.

Then:

- Number of edges does not decrease
- Graph remains $K_{r+1}$-free

### 5. Neighborhood Equality

In an extremal graph:

$$
u \not\sim v \;\Rightarrow\; N(u) = N(v)
$$

### 6. Partition into Independent Sets

Define relation:

$$
u \sim v \iff u = v \text{ or } u \not\sim_G v
$$

Then:

- This is an equivalence relation
- Each class is an independent set

### 7. Complete Multipartite Structure

The graph becomes:

- Complete between distinct equivalence classes
- Empty inside each class

Thus $G$ is complete $t$-partite.

### 8. Clique Bound on Number of Parts

Since $G$ is $K_{r+1}$-free:

$$
t \le r
$$

Otherwise picking one vertex from each part gives a $K_{r+1}$.

### 9. Increasing Number of Parts Increases Edges

If $t < r$, splitting a part increases edge count.

Thus maximum occurs when:

$$
t = r
$$

### 10. Main Inequality

For balanced $r$-partition:

$$
|E| \le |E(T_r(n))|
$$

### 11. Final Bound

Using explicit formula:

$$
|E(T_r(n))|
\le \frac{r-1}{2r} |V|^2
$$

## Equality Case

Equality holds if and only if:

- $G$ is complete $r$-partite
- All parts differ in size by at most $1$

i.e.,

$$
G \cong T_r(n)
$$
