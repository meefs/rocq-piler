# Open Bisimulation Reflexivity for CBV PCF

Prove that bisimilar substitutions applied to the same well-typed term
produce bisimilar results. This is the "fundamental theorem" of
applicative bisimilarity — the key lemma that unlocks Howe's method.

## Statement

```
open_bisim_refl : forall G T t, has_type G t T -> open_bisim G T t t
```

Where `open_bisim G T t1 t2` means: for all substitutions `σ1`, `σ2`
that map each variable in `G` to bisimilar closed values,
`bisimilar T (apply_sub σ1 t1) (apply_sub σ2 t2)`.

## What's already proved (47 Qed)

- PCF syntax, typing, big-step CBV evaluation
- Preservation, determinism, canonical forms
- Substitution typing (`apply_sub_typing`, `subst0_typing`)
- `bisim_refl` (bisimilarity is reflexive on closed terms)

## Proof approach

By induction on `has_type G t T`. For each typing rule, construct
a bisimulation witness `R` relating the two substituted terms.

Key cases:
- **tVar x**: `σ1 x` and `σ2 x` are bisimilar by hypothesis
- **tZero**: both give `tZero`, use `bisim_refl`
- **tSucc t**: IH gives bisimilar results at TNat; construct R wrapping tSucc
- **tLam A t**: both give lambdas; when applied with arg `u`:
  `subst0 vu (apply_sub (up_sub σ) t) = apply_sub (scons vu σ) t`,
  then IH with extended substitutions `(scons vu σ1)`, `(scons vu σ2)`
- **tApp f u**: IH on f gives bisimilar functions, IH on u gives bisimilar args;
  compose via the bisimulation condition at arrow type

## Key difficulty

The **tApp** case: the bisimulation condition at `TArr A B` tests
functions with the SAME argument, but our substitutions produce DIFFERENT
(bisimilar) arguments. Need to bridge from `bisimilar B (v1 (σ1 u)) (v2 (σ1 u))`
(same arg) to `bisimilar B (v1 (σ1 u)) (v2 (σ2 u))` (different args)
using the IH on `u`.

## Conjecture pairs

The theorem is stated alongside its negation. Prove exactly one.

## Constraints

- Copy `benchmarks/incomplete/open_bisim.v` to `benchmarks/complete/open_bisim.v`
  and work exclusively on that copy.
- Do NOT modify the incomplete file.

## Files

`benchmarks/incomplete/open_bisim.v` — the challenge (47 Qed, 2 Admitted)
`benchmarks/complete/open_bisim.v` — write your solution here
