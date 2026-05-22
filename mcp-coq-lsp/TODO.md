# mcp-coq-lsp TODO

## High priority

- [ ] **`coq_search` tool** — Search for lemmas/theorems without polluting the source file. Runs `Search <pattern>.` speculatively via a temp state and returns results as messages. Equivalent to `Search` in Proof General.

- [ ] **`coq_check_term` / `coq_about` tools** — Check the type of a term, print its definition, or get info. Same speculative approach as search.

- [ ] **`coq_undo` tool** — Remove the last N tactics from the file and re-sync. Currently the LLM must compute inverse text edits manually.

- [ ] **`coq_try_tactic` combined tool** — Single call: `try_tactic(file, position, tactic) → {new_state_id, goals}`, collapsing the current 3-call speculative flow (`get_state_at_pos` → `run_tactic` → `goals_for_state`) into one.

- [ ] **Fix `follow_with_goals` in `coq_insert_tactic`** — Currently queries goals at the *insertion point*. Should query goals at the position *after* the newly inserted text, so the caller sees the effect of the tactic.

## Medium priority

- [ ] **Human-readable goal formatting** — Add a `format` option that returns goals as structured plaintext (hypotheses + goal separator), matching Proof General / coqtop output. The raw JSON `ty`/`hyps` fields are machine-parseable but hard to read.

- [ ] **`coq_script` tool** — Return the full proof script (content of the .v file) so the LLM can see what's been built so far without reading the file via a separate tool.

- [ ] **`coq_fill_hole` workflow tool** — High-level: "take this Admitted proof, replace it with these tactics, and verify". Combines open, edit, replace, check into one call.

## Low priority

- [x] **Dynamic workspace switching** — When a file is opened, the server walks up from its directory looking for `_CoqProject`/`_RocqProject`/`dune-project` and restarts coq-lsp with the correct workspace root automatically.

- [ ] **`coq_reset` tool** — Reset the document to a known state (useful after speculative exploration).

- [ ] **Multi-file project support** — Track open documents across multiple .v files in the same project, sharing a coq-lsp instance.

- [ ] **Error message formatting** — Return diagnostics in a more readable form (currently raw JSON).

## Done

- [x] `coq_open_goals` — query goals at a position
- [x] `coq_proof_state` — richer proof context
- [x] `coq_get_state_at_pos` — Pétanque state identifier
- [x] `coq_run_tactic` — speculative tactic execution
- [x] `coq_goals_for_state` — goals from a state ID
- [x] `coq_apply_edit` — apply text edits and re-sync
- [x] `coq_insert_tactic` — insert tactic helper
- [x] `coq_check` — force document checking
- [x] `coq_check_range` — check a specific line range
- [x] `coq_search` — speculative `Search` via Pétanque
- [x] `coq_check_term` / `coq_about` — speculative `Check` / `About`
- [x] `coq_undo` — remove last N spans and re-sync
- [x] `coq_try_tactic` — single-call speculative tactic execution
- [x] Fix `follow_with_goals` — query goals after inserted text, not at insertion point
- [x] Dynamic workspace switching — auto-detect project root from file path

## Indentation nesting bug (partial fix in 4c41c66)
After closing a `-` bullet in an induction, a new `-` for the next case gets deeper indent because `proof/goals` reports remaining induction cases in the stack. The `hasActiveBullet` check doesn't help because the newly-prepended bullet IS active. Proper fix: need to distinguish between induction-case stack entries (root level) and actual bullet nesting entries (subgoals).

## Induction bullets: can't extend compound semicolon tactics
After `induction Hstep; ...` with semicolons partially closes cases, any remaining goal is at the top level (not inside any specific induction case). Additional tactics like `inversion Hty` run outside the induction context. Workaround: use explicit bullets `-` for each case instead of semicolons.

## Bullet system overall: fragile for 21-case inductions
The auto-bullet system works for simple proofs but breaks down for large inductions. The indent nesting and bullet detection issues make the proof script visually wrong even if Coq accepts it. Coq doesn't care about indentation (only bullet chars matter for grouping), but the visual misalignment is confusing for an LLM.
