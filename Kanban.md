# Kanban — MCP coq-lsp Tool Issues

## Backlog

### CRITICAL

**C1. `proof/goals` returns 0 goals after compound tactics**
When inserting `induction 1; simpl; intros.` (compound with semicolons),
`proof/goals` returns empty goals even when subgoals remain.
This causes `coq_insert_tactic` to report "done" when the proof isn't.
Separate from genuinely-done proofs where eauto closes everything.
Root cause unknown — needs rocq-lsp investigation.
*Observed: `induction Ht; simpl; intros ...` in substitution lemma, `induction Hok.` in extends_heap_ok.*

**C2. `coq_add_lemma` + `coq_reset_proof` corrupt file when chained**
Cursor tracking between tools is unreliable after adding/resetting lemmas.
Causes file corruption (missing lemma headers, duplicate Proof/Qed, stray Admitted).
*Observed: PCF proofs — multiple corruption events, required undo/apply_edit to fix.*
*Mitigated: name-based `before:` parameter in `coq_add_lemma` (pending verification).*

### HIGH

**H1. No proof context shown in `coq_insert_tactic` response**
Returns goals but not the proof script. Caller can't see what tactics are already
written without separate `coq_focus` calls. Makes it hard to track proof progress.
*Fix: include proof script lines in response.*

**H2. `coq_focus` auto-remove of `Admitted.` leaves empty proof body**
When `Proof.\nAdmitted.` has nothing between, auto-remove creates an empty
proof body with 0 goals. The tool doesn't confirm what was removed.
*Mitigation: check for empty body before removal; log what was removed.*

**H3. `coq_apply_edit` requires manual line number computation**
Absolute line ranges are error-prone. I computed wrong ranges twice during PCF.
A text-replace or diff-based interface would prevent off-by-one corruption.
*Fix: accept `oldText`/`newText` search-and-replace instead of line ranges.*

### MEDIUM

**M1. `coq_reset_proof` doesn't return cursor to reset proof's body**
After resetting, the cursor stays at the old position, which may be inside
the reset range. Subsequent `coq_insert_tactic` goes to wrong place.
*Fix: set cursor to first line inside reset proof body.*

**M2. `coq_add_lemma` indent in generated stub is wrong**
Lemma stub has `Proof.\nAdmitted.\n` but both lines should be indented
relative to the lemma statement. Generated stubs are at column 0.
*Fix: add 2-space indent to Proof. and Admitted. lines.*

**M3. Auto-bullet "prefix" includes verbose message text**
`proof/goals` returns `"Focus next goal with bullet -."` or
`"The current bullet - is unfinished"` as the bullet field.
Extraction regex needs to handle both forms robustly.
*Fix: use `rawBullet?.match(/[-+*]+/)` which should handle both (pending verification).*

**M4. `coq_focus` takes `Proof.` line position — should advance into body**
When given `Proof.` line, cursor lands BEFORE `Proof.` or at it.
Should auto-advance to first meaningful line INSIDE the proof.
*Current behavior: insertPosition does advance, but inconsistently.*

**M5. Goal display doesn't distinguish "0 at focus but N in background"**
When bullet closes a focus goal, the response says "0 goals" without
mentioning the remaining background goal. Caller gets confused.
*Fix: merged into stateMsg already ("bullet closed, 1 in background").*
*Status: partial — works in `coq_insert_tactic` but not in `coq_open_goals`.*

### LOW

**L1. File clean-up needed after bulk edits**
`coq_apply_edit` with multi-range edits leaves the file in a messy state.
Need a `coq_format` or `coq_cleanup` tool.
*Fix: add `coq_format_file` tool that re-indents and normalizes.*

**L2. `coq_check` summary shows too many items**
Debug output includes `Inductive`/`Definition`/`Fixpoint` as "open".
Should only show `Lemma`/`Theorem` items with Qed/Admitted status.
*Fix: filter summary to only proof-bearing toplevel items.*

## In Progress

(none)

## Done

- [x] **D1.** `coq_reset_proof` reports proof name (commit 43534f1)
- [x] **D2.** `coq_focus`/`coq_reset_proof`/`coq_add_lemma` use names not positions (eef2d4e)
- [x] **D3.** "done" → "done — try Qed" (40e6a4b)
- [x] **D4.** Auto-indent based on bullet stack depth (b84f696)
- [x] **D5.** Tool description: prefer explicit `as` clauses (9824885)
- [x] **D6.** `coq_check` reports admitted count + line numbers (1a98364)
- [x] **D7.** State messages: "bullet closed, N in background" (26ee254)
- [x] **D8.** Qed replaces Admitted (3a6de0b)
- [x] **D9.** History-based undo (fix for issue #5 from axiomander docs)
- [x] **D10.** `coq_add_lemma` tool (0e3c4dd)
- [x] **D11.** `coq_reset_proof` tool (1465173)
