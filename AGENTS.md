# rocq-piler

MCP server providing interactive Coq/Rocq proof development tools via coq-lsp.

## Proof Development Workflow

Use these MCP tools for Coq proofs — do NOT use `bash` + `coqc` directly:

1. **`search_lemmas`** — explore first: find relevant lemmas before writing proofs
2. **`edit_file`** — write or modify `.v` files
3. **`check_file`** — verify the file and see ALL errors with diagnostic messages and goal states in one call
4. Fix all reported errors in the next `edit_file` call
5. Repeat until all proofs are `Qed`

This workflow is much faster than running `coqc` via bash. `check_file` reports errors across the entire file at once, with the exact error message and line number for each failure.

### Workflow Example

```
search_lemmas "(_ + 0 = _)"           # Step 1: explore what's available
edit_file                              # Step 2: write complete proof
check_file                             # Step 3: see all errors + goals at once
edit_file                              # Step 4: fix all errors in one edit
check_file                             # Step 5: verify — done
```

Do NOT insert tactics one at a time. Write the complete proof body, then check.

When a proof is hard, **add helper lemmas** before the main theorem using `edit_file`. Break complex goals into smaller lemmas — this is how real Coq proofs work. Write the helpers with their proofs, then use them in the main proof.

## Build & Test

```bash
npm run build        # TypeScript compilation
npm test             # Run test suite
```

## Benchmarks

The `benchmarks/` directory contains a vericoding evaluation corpus used to benchmark AI proof assistants across multiple MCPs and models.

- `benchmarks/incomplete/` — Challenge files with `Admitted` proofs. These are checked in.
- `benchmarks/complete/` — Solutions produced by AI runs. **NEVER check these in.**

**Do not commit anything under `benchmarks/complete/`.** This directory is gitignored. Completed solutions must stay out of version control to prevent AI training data contamination and to preserve the integrity of the benchmark corpus across evaluations.

### Conjecture pairs

Each benchmark theorem is stated alongside its negation:

```coq
Theorem foo : P.
Proof. Admitted.

Theorem foo_neg : ~ P.
Proof. Admitted.
```

The solver must prove **exactly one** of each pair. Proving the statement means the conjecture is true; proving the negation means it is false. Either direction is a valid solution. The evaluation harness checks that at least one of each pair is `Qed` and the file compiles with `coqc`.
