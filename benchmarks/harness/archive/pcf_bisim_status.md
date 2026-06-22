# PCF Bisimulation Proof Status

## Definition Fix

The original `is_bisimulation` definition was too weak at arrow type —
it only required `forall u, R B (tApp t1 u) (tApp t2 u)` without
co-termination. DeepSeek correctly refuted soundness by constructing
`Rdiv`, relating `Ω` (self-loop, diverges) with `λx.Ω` (value whose
body diverges). Both diverge on all inputs but the latter is a value
observable by a forcing context `(λ_.0) [·]`.

**Fix**: Arrow-type bisimulation now requires co-termination:
```
(forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\ forall u, R B (v1 u) (v2 u))
/\ (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\ forall u, R B (v1 u) (v2 u))
```

## Current Proof Status

| Theorem | Status | Lines |
|---------|--------|-------|
| bisim_complete | **Qed** | ~130 lines of proof |
| eval_ctx_equiv | Admitted | key dependency |
| bisim_sound | Admitted | requires Howe's method |
| bisim_sound_neg | Admitted (correct) | soundness IS true |
| bisim_complete_neg | Admitted (correct) | completeness IS true |

Infrastructure: 44 lemmas proved (Qed), including preservation,
determinism, canonical forms, numeral discriminators (eqf family),
context composition, forcing contexts.

## Remaining Work

### eval_ctx_equiv (medium, ~50 lines)

**Statement**: `eval t v → ctx_equiv T t v`  
A term is contextually equivalent to its value.

**Approach**: Prove `apply_sub_closed` (closed terms are substitution-invariant),
then induction on the eval derivation showing `terminates(plug C t) ↔ terminates(plug C v)`.
The closed-substitution invariance handles binder cases (cLam, cFix, cIfzE)
where the context gets substituted but the closed hole term stays unchanged.

**Alternative**: Derive from bisim_sound — construct trivial bisimulation
`R T s1 s2 := (s1=s2) \/ (s1=t /\ s2=v /\ T'=T)`, show it's a bisimulation,
then bisim_sound gives ctx_equiv.

### bisim_sound (hard, ~200 lines)

**Statement**: `bisimilar T t1 t2 → ctx_equiv T t1 t2`

**Approach**: Howe's method — the standard technique for showing applicative
bisimilarity is a congruence in call-by-value lambda calculi.

1. Define Howe closure `~^H` of bisimilarity `~`
2. Show `~^H` is reflexive and contains `~`
3. Show `~^H` is substitutive (closed under substitution)
4. Show `~^H` is a bisimulation (the key lemma)
5. Conclude `~^H = ~` (hence `~` is a congruence)
6. Congruence + adequacy at TNat gives soundness

**Reference**: Pitts, "Howe's method for higher-order languages" (2011),
or Lassen, "Bisimulation in Untyped Lambda Calculus" (1999).

## MCP Ergonomics Notes

- `insert_tactics` failed repeatedly with "Syntax error: illegal begin of vernac"
  on the /tmp file. Direct file editing with `edit` was more reliable.
- `focus_proof` worked well for inspecting goal state.
- `check_file` cold-start timeout (now 300s) was essential.
- The MCP was most useful for the EXPLORATION phase (checking goals, testing
  tactics). For PRODUCTION proofs at this complexity level, direct file writing
  and `coqc` compilation was faster than interactive tactic insertion.
