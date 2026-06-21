# Contextual Equivalence ≡ Applicative Bisimilarity for PCF

Prove that contextual equivalence and applicative bisimilarity coincide
for PCF (a simply-typed lambda calculus with naturals and general recursion).

## Language

PCF with de Bruijn indices:
- **Types:** `Nat | A → B`
- **Terms:** variables, lambda, application, zero, succ, pred, ifzero, fix
- **Values:** lambdas, zero, succ of value
- **Semantics:** big-step evaluation (`eval t v`)

## Definitions

**Contextual equivalence** (`ctx_equiv T t1 t2`): Two closed terms of
type `T` are contextually equivalent if for every context `C` that produces
a closed term of type `Nat`, `C[t1]` terminates iff `C[t2]` terminates.

**Applicative bisimulation** (`is_bisimulation R`): A type-indexed relation
`R` on closed terms such that:
- At `Nat`: related terms evaluate to the same natural number value
- At `A → B`: applying related terms to any well-typed argument yields
  related results at type `B`

**Bisimilarity** (`bisimilar T t1 t2`): There exists an applicative
bisimulation `R` with `R T t1 t2`.

## Theorems

### Soundness (bisimilarity ⊆ contextual equivalence)

```
bisimilar T t1 t2 → ctx_equiv T t1 t2
```

### Completeness (contextual equivalence ⊆ bisimilarity)

```
ctx_equiv T t1 t2 → bisimilar T t1 t2
```

## Key difficulties

- **Soundness** requires showing that bisimilar terms behave the same in
  every context. Typically proved by induction on the context or by showing
  bisimilarity is a congruence.
- **Completeness** is the harder direction. Standard approaches use a
  CIU (Closed Instances of Uses) theorem to reduce universal context
  quantification, then show that contextual equivalence itself is a
  bisimulation.
- **Substitution lemmas**: typing preservation under substitution is needed
  for both directions.
- **Fix/recursion**: the unfolding rule for `fix` introduces non-termination,
  requiring careful treatment in bisimulation arguments.

## Conjecture pairs

Each theorem is stated alongside its negation. Prove exactly one of each
pair. Either direction is a valid solution.

## Constraints

- Copy `benchmarks/incomplete/pcf_bisim.v` to `benchmarks/complete/pcf_bisim.v`
  and work exclusively on that copy.
- Do NOT modify the incomplete file.

## Files

`benchmarks/incomplete/pcf_bisim.v` — the challenge (4 Admitted, 2 pairs)
`benchmarks/complete/pcf_bisim.v` — write your solution here
