# Indexed Inductive Families: Preservation & Progress

Prove **type preservation** and **progress** for a CIC fragment with
inductive families described by signatures, dependent case analysis
with motives, and general recursion (Fix).

## Language

Based on the term language from [Scidonia/cyclic](https://github.com/Scidonia/cyclic).

- **Types:** `Sort i | Pi A B | Ind I`
- **Terms:** variables, lambda/application, fixpoint, inductive constructors (`Roll`),
  dependent case analysis with motive
- **Signatures:** `ind_sig` / `ctor_sig` describing constructor arities and
  recursive argument counts
- **Substitution:** parallel substitution reimplementing Autosubst core
  (`rename`, `apply_sub`, `subst0`, `shift`, `up_sub`)

## Theorems

### Preservation (subject reduction)

```
forall Σenv Γ t t' T,
  has_type Σenv Γ t T ->
  step t t' ->
  has_type Σenv Γ t' T.
```

### Progress

```
forall Σenv t T,
  has_type Σenv [] t T ->
  value t \/ exists t', step t t'.
```

## What you need to prove

1. Auxiliary lemmas (renaming, substitution, weakening, inversion, etc.)
2. A substitution lemma for dependent types
3. Properties of `apps`, `mk_pis`, `motive_inst`
4. Complete both theorems with no remaining admits

## Key difficulties (compared to PCF+Ref)

- **Dependent types**: types contain terms, so substitution lemma is harder
- **Motive instantiation**: `motive_inst` involves complex variable shifting
  (`tRoll I c [var(m-1)...var 0]` substituted into motive, remaining vars shifted by m)
- **`apps br args`**: the case-roll reduction applies a branch to *all* constructor
  arguments; the typing of this multi-application must be shown correct via `mk_pis`
- **Telescope contexts**: `ctx_lookup` shifts types on lookup (de Bruijn telescopes)

## Constraints

- Copy `benchmarks/incomplete/indexed_ind.v` to `benchmarks/complete/indexed_ind.v`
  and work exclusively on that copy.
- Do NOT modify the incomplete file.

## Files

`benchmarks/incomplete/indexed_ind.v` — the challenge (2 Admitted)
`benchmarks/complete/indexed_ind.v` — write your solution here
