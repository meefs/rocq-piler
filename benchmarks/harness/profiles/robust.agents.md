# rocq-piler

MCP server providing interactive Coq/Rocq proof development tools via coq-lsp.

## Tools

- **`edit_file`** — write or modify `.v` files. Reports the first error and goal state after each edit — no need to run coqc separately.
- **`check_file`** — full file status: all errors, Qed/Admitted counts. Use `mode: "errors"` for compact output. Good for initial assessment and final verification.
- **`search_lemmas`** — find relevant lemmas in the Coq environment by name or pattern
- **`stratify`** — case-split a proof and auto-close easy cases. Returns hash-addressable admits for survivors.
- **`close_admits`** — batch-close surviving admits with a portfolio of tactics
- **`reset_proof`** — wipe a proof body and start fresh
- **`focus_proof`** — inspect proof state and goal details (debugging)

## Approach

Write proofs and helper lemmas directly with `edit_file`. It gives instant error + goal feedback after every edit.

If a proof has too many cases to write by hand, use `stratify` to split it and auto-close easy cases, then `close_admits` to target survivors.
