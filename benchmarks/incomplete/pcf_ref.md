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

## File

`benchmarks/incomplete/pcf_ref.v` — the challenge (Admitted)
`benchmarks/complete/pcf_ref.v` — ground truth (all Qed)
