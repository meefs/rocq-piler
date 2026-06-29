# Kanban: MCP Ergonomics Fixes

Based on the indexed_ind benchmark analysis. Four pain points, ordered by time wasted.

## Context

- `edit_file` tool exists at `src/index.ts:363-401` (schema) and `src/index.ts:914-989` (handler), enabled by default (disable with `ROCQ_PILER_DISABLE_EDIT_FILE=1`)
- It already does the close/reopen LSP resync pattern (lines 965-978)
- All proof tools use petanque: `petanque/get_state_at_pos`, `petanque/run`, `petanque/goals`
- DocumentManager tracks versions and sends `textDocument/didChange` with full-text sync
- The desync problem: external edits bypass DocumentManager, LSP never gets `didChange`

---

## P1: LSP Desync (60% of wasted time)

Root cause: any file edit outside DocumentManager (bash/sed/Python) leaves the LSP with stale text. All subsequent petanque calls operate on the old document.

### TODO

- [x] **P1.1 — Enable `edit_file` by default**
  - Inverted gate: `ROCQ_PILER_ENABLE_EDIT_FILE=1` → `ROCQ_PILER_DISABLE_EDIT_FILE=1`
  - `edit_file` is now always in the tool list unless explicitly disabled
  - POSITIONAL_ONLY overrides the disable flag (edit_file is required in that mode)

- [x] **P1.2 — Add disk-mismatch detection to `ensureDocumentOpened`**
  - `ensureDocumentOpened` now does close+reopen (not just `updateDocument`) when disk text diverges
  - Logs: `"Document modified externally, re-syncing: <path>"`
  - Safety net for any external edit (bash, editor, git checkout)

- [x] **P1.3 — Extract the close/reopen resync into a reusable function**
  - Extracted `forceResync(file, label)` — close → reopen → `coq/getDocument` wait
  - Replaced 9 copy-paste sites across edit_file, insert_tactics, stratify, close_admits, delete_lemma

---

## P2: Opaque Goal State (25% of wasted time)

Root cause: on tactic failure, the agent gets only the Coq error string, not the goal state at the failure point. No way to inspect intermediate states after `simpl` or partial tactic chains.

### TODO

- [x] **P2.1 — Enhance `insert_tactics` failure response to include goal state**
  - Both main failure paths (admit_hash speculative + main speculative) now query `petanque/goals` on the pre-tactic state
  - Returns full hypothesis list + goal at the failure point alongside the Coq error
  - Captures `preState` before the try/catch so it's available in the error path

- [ ] **P2.2 — Support partial tactic chains in `insert_tactics dry_run`**
  - Allow `tactic` to be a semicolon-separated chain like `"simpl; rewrite foo"`
  - On `dry_run:true`, if the full chain fails, try progressively shorter prefixes: `"simpl; rewrite foo"` → `"simpl"` → show the goals after the last successful prefix
  - This directly solves the "what does the goal look like after `simpl`" problem
  - Implementation: split on top-level `;`, try `petanque/run` on prefixes, report the longest successful prefix + its goals

- [x] **P2.3 — Add `show_goals` as a mode of `focus_proof`**
  - Added `at_line` parameter to `focus_proof`
  - When provided, queries goals at that specific line instead of the proof cursor
  - Uses existing proof/goals + petanque fallback machinery

---

## P3: Multi-lemma / Definition Addition (10% of wasted time)

Root cause: `add_lemma` (src/index.ts:3063-3147) only emits `Lemma name : statement. Proof. Admitted.`. Cannot add `Fixpoint`, `Section`/`End`, `Definition`, `Ltac`, `Notation`, or other vernacular.

### TODO

- [x] **P3.1 — Add `add_block` tool for arbitrary vernacular insertion**
  - `add_block { file, content, before? }` — inserts raw vernacular text
  - `before` names a definition/proof to insert above; omit to append at EOF
  - Handles Section/End, Fixpoint, Definition, Ltac, Notation — everything `add_lemma` can't
  - Uses `forceResync` after insertion

- [x] **P3.2 — Support batch mode in `add_block`**
  - `content` now accepts `string | string[]` — array elements joined with `\n\n`
  - Single resync at the end regardless of number of blocks

---

## P4: Lemma Positioning (5% of wasted time)

Root cause: no tool to move a definition from one position to another. Had to use bash to reorder `rename_shift1` before `ctx_ext`.

### TODO

- [x] **P4.1 — Add `move_lemma` tool**
  - `move_lemma { file, name, before }` — extracts block and re-inserts before target
  - Handles Lemma/Theorem/Definition/Fixpoint/Inductive/Record
  - Adjusts line numbers correctly when source is before/after target
  - Uses `forceResync` after move

---

## Dependency Graph

```
P1.3 (extract resync) ← P1.2 (mismatch detection)
                       ← P1.1 (enable edit_file)
                       ← P3.1 (add_block uses resync)
                       ← P4.1 (move_lemma uses resync)

P2.1 (goal on failure) — independent
P2.2 (partial chains)  — independent
P2.3 (show_goals)      — independent

P3.1 (add_block)       ← P3.2 (batch mode)
```

## Suggested Implementation Order

1. **P1.3** — Extract resync (prerequisite, small, reduces code duplication)
2. **P1.1** — Enable edit_file (flip the flag + test)
3. **P1.2** — Disk mismatch detection (safety net)
4. **P2.1** — Goal state on failure (highest debugging value)
5. **P3.1** — add_block (enables definition insertion through MCP)
6. **P2.2** — Partial tactic chains (nice-to-have for debugging)
7. **P4.1** — move_lemma (rare need, low priority)
8. **P3.2** — Batch add_block (optimization)
9. **P2.3** — show_goals at position (covered partially by P2.1 and P2.2)
