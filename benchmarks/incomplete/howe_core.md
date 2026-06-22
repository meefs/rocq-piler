# Howe's Method: Bisimilarity is a Congruence for CBV PCF

Complete the proof that applicative bisimilarity equals contextual equivalence
for a call-by-value PCF by filling in the Howe closure infrastructure.

## What's already proved (56 Qed)

- PCF syntax, typing, big-step CBV evaluation (deterministic)
- Type preservation, eval determinism, canonical forms
- Numeral discriminators (`eqf` family) for testing nat values
- Context composition (`ccompose`, `plug_compose`)
- Closed-term substitution invariance (`apply_sub_closed_gen`, `plug_subst_closed`)
- `bisim_refl`, `bisim_adequate`, `howe_implies_bisimilar`
- `bisim_sound` (from `bisim_congruence` + `bisim_adequate`)
- `bisim_complete` (ctx_equiv is a bisimulation, using `eqf` discriminators)

## What you need to prove (6 Howe core lemmas)

The main theorems (`bisim_sound`, `bisim_complete`) are Qed but depend
transitively on unproved axioms. Your task: fill in the Howe infrastructure
so `Print Assumptions bisim_sound` and `Print Assumptions bisim_complete`
return `Closed under the global context`.

### 1. `open_bisim_refl` (~30 lines)
Bisimilar substitutions applied to the same term give bisimilar results.
Proved by induction on typing, constructing ad-hoc bisimulation witnesses.

### 2. `howe_refl` (~20 lines)
The Howe closure is reflexive. By induction on typing using `open_bisim_refl`.

### 3. `howe_substitutive` (~40 lines)
The Howe closure is preserved under substitution. By induction on the
`howe` derivation, using the closed-substitution infrastructure.

### 4. `howe_is_bisimulation` (~50 lines)
THE main Howe lemma. The Howe closure at closed terms satisfies the
bisimulation conditions. Uses `howe_substitutive` for the arrow-type
case (applying a Howe-related lambda to an argument).

### 5. `bisim_congruence` (~20 lines)
Bisimilarity is preserved by all contexts. By induction on the context,
using `howe_refl` + `howe_substitutive` + `howe_implies_bisimilar`.

### 6. `eval_ctx_equiv` (~10 lines)
A term is contextually equivalent to its value. Corollary of `bisim_sound`:
construct a trivial bisimulation relating `t` and `v`.

## Key difficulties

- **Circularity**: `open_bisim_refl` needs congruence, `bisim_congruence`
  needs `howe_is_bisimulation`, which needs `howe_substitutive`.
  The resolution: prove all three in the specific order above.
- **Ad-hoc bisimulations**: Each case of `open_bisim_refl` requires
  constructing a bisimulation witness that wraps the term constructor
  around the IH.
- **Substitution composition**: The arrow-type cases require showing
  `subst0 vu (apply_sub (up_sub σ) t) = apply_sub (scons vu σ) t`,
  using `apply_sub_comp` and `subst0_shift1`.

## Conjecture pairs

Each Howe lemma is stated alongside its negation. Prove exactly one of
each pair.

## Constraints

- Copy `benchmarks/incomplete/howe_core.v` to `benchmarks/complete/howe_core.v`
  and work exclusively on that copy.
- Do NOT modify the incomplete file.

## Files

`benchmarks/incomplete/howe_core.v` — the challenge (56 Qed, 14 Admitted)
`benchmarks/complete/howe_core.v` — write your solution here
