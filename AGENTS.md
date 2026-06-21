# rocq-piler

MCP server providing interactive Coq/Rocq proof development tools via coq-lsp.

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
