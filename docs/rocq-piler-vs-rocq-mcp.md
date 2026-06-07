# rocq-piler vs rocq-mcp

| | rocq-piler | rocq-mcp |
|---|---|---|
| **Language** | TypeScript | Python (FastMCP) |
| **Coq interface** | coq-lsp (LSP protocol) | petanque subprocess + coqc |
| **Proof state** | Document-based, bullet-stack aware | State-based, snapshots via petanque |
| **Admit tracking** | Per-bullet `admit.` lines, MD5 hashes, `admit_hash` replacement | File-level regex for `Admitted`/`admit.`; `Print Assumptions` for axiom detection |
| **Incremental proof** | `insert_tactic` — step-by-step, auto-bullet prefix, auto-Qed | `rocq_step_multi` — runs petanque batch, no bullet management |
| **Verification** | Implicit via coq-lsp document checking | Explicit `rocq_verify` — sandboxed `coqc` compile, checks admits/axioms/mismatches |
| **`given_up` handling** | Blocks auto-Qed when `nGivenUp > 0` (prior bug: false positives from `{ }` blocks) | Reports `given_up_goals` count, does not gate completion |
| **Resource limits** | None | RSS cap (50% RAM, max 16 GB), per-call timeouts |

## Key design difference

**rocq-piler** is an interactive proof assistant — it manages proof state at the bullet
level, letting you incrementally replace admitted subgoals with tactics. It knows
which bullet you're in, seals unfinished branches, and auto-applies Qed when done.

**rocq-mcp** is a verification pipeline — it compiles entire files, checks for
admitted/axiom dependencies, and reports closed vs suspicious status. Its
interactive mode runs petanque steps but doesn't track or seal individual admits.

Neither supersedes the other. rocq-piler's admit-hash system is unique and has no
equivalent in rocq-mcp.
