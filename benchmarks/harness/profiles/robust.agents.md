# rocq-piler

MCP server providing interactive Coq/Rocq proof development tools via coq-lsp.

## Tools

- **`search_lemmas`** — find relevant lemmas in the Coq environment by name or pattern
- **`edit_file`** — write or modify `.v` files (supports `find`/`replace` or range-based edits)
- **`check_file`** — verify the file and report errors with diagnostic messages and goal states. Supports `mode: "errors"` (compact: only failures/admitted) and `mode: "first"` (one error at a time)
- **`focus_proof`** — inspect proof state: goals, bullet stack, admits
- **`insert_tactics`** — insert tactics into a proof, optionally targeting a specific admit by hash
- **`stratify`** — case-split a proof and auto-close easy cases
- **`close_admits`** — batch-close surviving admits with a portfolio of tactics
- **`reset_proof`** — wipe a proof body and start fresh with Admitted

Most non-trivial proofs need **helper lemmas** (e.g. substitution, weakening, inversion). Add them before the main theorem.

## When to use stratify

`edit_file` + `check_file` is faster for most proofs — write the proof directly and iterate.

`stratify` is **only** for hard proofs with many cases where you cannot guess the structure (e.g. theorems requiring induction over a relation with 10+ constructors). It is slower than direct editing because it involves per-case LSP round-trips. Do not reach for it on simple proofs.

When you need it:

1. **`stratify`** — split and auto-close easy cases:
   - `skeleton`: e.g. `"induction Hstep; intros; inversion Ht; subst"`
   - `portfolio`: e.g. `["eauto", "econstructor; eauto", "lia"]`
   - Returns hash-addressable admits for survivors.

2. **`insert_tactics admit_hash=<hash>`** — prove survivors one at a time
3. **`close_admits`** — batch-close survivors with a tactic portfolio
4. **`reset_proof`** — start over if stuck
