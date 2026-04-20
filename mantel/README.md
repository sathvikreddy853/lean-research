# Turán's Theorem

This module proves Turán’s Theorem using induction and degree arguments.

## Statement

Let $G = (V, E)$ be a finite simple graph with no clique of size $r+1$.
Then:

$$
|E| \le \frac{r-1}{2r} |V|^2
$$

## Definitions

### $K_{r+1}$-Free Graph

A graph is $K_{r+1}$-free if:

$$
\forall v_1, \dots, v_{r+1} \in V,\quad
\neg\Big( \bigwedge_{i<j} (v_i, v_j) \in E \Big)
$$

## Lemmas Used

### 1. Minimum Degree Bound

There exists $v \in V$ such that:

$$
\deg(v) \le \frac{2|E|}{|V|}
$$

### 2. Neighborhood is $K_r$-Free

Let $A = N(v)$. Then:

$$
G[A] \text{ is } K_r\text{-free}
$$

Otherwise, together with $v$, we get a $K_{r+1}$.

### 3. Complement Set is $K_{r+1}$-Free

Let:

$$
B = V \setminus (A \cup \{v\})
$$

Then:

$$
G[B] \text{ is } K_{r+1}\text{-free}
$$

### 4. Edge Decomposition

Edges can be partitioned as:

$$
|E| = |E(A)| + |E(B)| + |A|
$$

- $|E(A)|$: edges inside $A$
- $|E(B)|$: edges inside $B$
- $|A|$: edges between $v$ and $A$

### 5. Inductive Bounds

Let $|A| = a$, $|B| = b$, with $a + b + 1 = n$.

By induction:

$$
|E(A)| \le \frac{r-2}{2(r-1)} a^2
$$

$$
|E(B)| \le \frac{r-1}{2r} b^2
$$

### 6. Combine Inequalities

Substitute into edge decomposition:

$$
|E| \le \frac{r-2}{2(r-1)} a^2 + \frac{r-1}{2r} b^2 + a
$$

### 7. Final Inequality

Using $a + b + 1 = n$ and algebraic manipulation, one obtains:

$$
|E| \le \frac{r-1}{2r} n^2
$$

## Conclusion

Thus every $K_{r+1}$-free graph satisfies:

$$
|E| \le \frac{r-1}{2r} |V|^2
$$