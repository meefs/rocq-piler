# Term Sharing via Hash-Consing

Prove correctness and size properties of a DAG-based sharing representation
for a dependently typed calculus with inductives, and prove that direct
DAG-level substitution is correct for closed terms.

## Language

Same term language as `indexed_ind.v` — variables, Sort, Pi, Lam, App, Fix,
Ind, Roll (inductive constructors), Case (dependent elimination).

## Representation

A **node** is like a term constructor but with `nat` indices (into a table)
instead of subterm trees. A **dag** is `list node`. Sharing works by
**interning**: before adding a node, check if an identical node already exists
in the table; if so, reuse its index.

- `intern : node → dag → dag × nat` — lookup-or-append
- `share : tm → dag → dag × nat` — bottom-up conversion (children first)
- `unfold : dag → fuel → nat → option tm` — expand back to tree

## Theorems

### 1. Round-trip correctness

```
unfold (share t []) = Some t
```

Sharing a term and unfolding it recovers the original.

### 2. Size bound (DAG ≤ tree)

```
dag_nodes (share t []) ≤ tm_size t
```

The DAG never has more nodes than the tree has constructors.

### 3. Strict improvement for duplicated subterms

```
tm_size t ≥ 1 →
dag_nodes (share (tApp t t) []) < tm_size (tApp t t)
```

When a subterm appears twice, sharing strictly reduces size.

### 4. DAG-level substitution for closed terms

```
closed u →
unfold (dag_subst_closed (share t ∘ share u) ...) = Some (subst0 u t)
```

Direct substitution on the DAG (replacing variable nodes, shifting under
binders) is correct when the substitutee is closed. Closedness means the
DAG for `u` is valid at every binder depth without shifting.

## Key difficulties

- **Monotonicity of `intern`**: the table only grows; existing entries are
  preserved. Needed for composing `share` calls and showing `unfold` still
  works on a grown table.
- **Fuel sufficiency**: `unfold` uses a fuel parameter; must show
  `length tbl` is always enough for well-formed DAGs built by `share`.
- **Sharing idempotence**: re-sharing an already-shared term adds no new
  nodes. Needed for the strict improvement theorem.
- **Binder tracking in DAG substitution**: `dag_subst_closed` increments
  the target variable under binders (Pi, Lam, Fix, Case motive). Must show
  this matches tree-level `up_sub` when the substitutee is closed.

## Constraints

- Copy `benchmarks/incomplete/sharing.v` to `benchmarks/complete/sharing.v`
  and work exclusively on that copy.
- Do NOT modify the incomplete file.

## Files

`benchmarks/incomplete/sharing.v` — the challenge (4 Admitted)
`benchmarks/complete/sharing.v` — write your solution here
