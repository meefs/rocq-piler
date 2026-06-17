# PCF + References: Type Preservation

Prove the **type preservation** theorem for a PCF language extended with
mutable references (allocation, dereference, assignment).

## Language

- **Types:** `TyNat | TyBool | TyArrow : ty -> ty -> ty | TyRef : ty -> ty`
- **Terms:** natural numbers, booleans, succ/pred/iszero, conditionals,
  lambda/application/fixpoint, reference allocation/dereference/assignment
- **Store:** a heap of `(location, value)` pairs with a store typing `list ty`

## Theorem

```
forall t mu t' mu' T S,
  has_type [] S t T ->
  step t mu t' mu' ->
  heap_ok mu S ->
  length mu >= length S ->
  exists S',
    extends S' S /\
    heap_ok mu' S' /\
    has_type [] S' t' T.
```

## What you need to prove

The file `pcf_ref.v` contains the complete language definition and the
preservation theorem with `Admitted`. You must:

1. Prove any necessary auxiliary lemmas (weakening, substitution, heap
   invariants, store extension lemmas, etc.)
2. Complete the preservation proof with no remaining admits

## Constraints

- Copy `benchmarks/incomplete/pcf_ref.v` to `benchmarks/complete/pcf_ref.v`
  and work exclusively on that copy. Do NOT modify the incomplete file.
- You MUST use the rocq-piler MCP tools to complete the proof — do NOT
  edit the `.v` file directly with text edits. Use `stratify`,
  `insert_tactics`, `close_admits`, `add_lemma`, etc.
- Do NOT read or inspect any existing proof or solution. The ground truth
  in `benchmarks/complete/pcf_ref.v` is the target, not a reference to
  consult.

## Files

`benchmarks/incomplete/pcf_ref.v` — the challenge (Admitted)
`benchmarks/complete/pcf_ref.v` — write your solution here
