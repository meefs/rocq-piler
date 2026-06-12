# Tool Problems

Problems encountered while using the MCP coq-lsp tools interactively.

## Ideas

### "AI Split" tactic for Iris

**Status:** Idea (from the `benchmarks/complete/challenge.v` Iris exercise)

We might want to add an "AI Split" to Iris that would allow us to more easily
perform the proofs. When proving a goal of the form `P1 ∗ P2 ∗ ... ∗ Pn`
(possibly under `∃ x, ...`), the manual-effort hotspot is deciding how to
distribute the spatial context across the conjuncts (`iSplitL`/`iSplitR` with
explicit hypothesis lists) and picking existential witnesses — in challenge.v
this was choosing the leased-set `L` and routing the `own`/`cinv_own`
resources between the kept world, the stash, and the wand closures.

Sketch: an `iAISplit` (or MCP-side `coq_ai_split`) that

1. reads the proof-mode environment (spatial/intuitionistic hyps + goal),
2. asks an oracle (LLM and/or syntactic resource-matching search) for a
   partition of the spatial hyps per ∗-conjunct and candidate existential
   witnesses,
3. emits the concrete, replayable script (`iExists ...; iSplitL "H1 H2"; ...`)
   rather than an opaque proof, so the result stays auditable and
   cache-friendly.

This composes well with the existing speculative execution tools
(`coq_try_step`/`exec_tactic`): candidates can be validated speculatively and
only written to the file once a split succeeds.

## 1. `proof/goals` returns 0 goals after compound tactics

**Severity:** High
**Status:** Cannot reproduce (2026-06-11) — integration test added

Tested with `induction n.` and `split.` — `insert_tactic` correctly reports
2 focused goals in both cases. May have been fixed in the meantime or was
specific to particular hypothesis-laden induction contexts.

**Integration test:** `tests/integration/tool_bugs.test.ts` — Bug #1 suite

**Workaround:** Try `Qed.` — if it fails, the proof wasn't complete.

## 2. `coq_focus` auto-remove of Admitted can corrupt file

**Severity:** Medium
**Status:** Cannot reproduce (2026-06-11) — integration test added

`focus_proof` no longer modifies files at all — it reads-only. If auto-removal
existed in a prior version, it has been removed. File stays valid through
multiple `focus_proof` calls.

**Integration test:** `tests/integration/tool_bugs.test.ts` — Bug #2 suite

## 3. `coq_reset_proof` can target wrong proof

**Severity:** Medium
**Status:** Cannot reproduce (2026-06-11) — integration test added

Tested with two adjacent proofs (`bug_reset_target_a` and `bug_reset_target_b`).
Resetting `b` leaves `a` untouched (tactics preserved). The `findProofLine`
search correctly uses the supplied name to locate the right `Proof.` line.

**Integration test:** `tests/integration/tool_bugs.test.ts` — Bug #3 suite

## 4. `coq_add_lemma` positioning unreliable

**Severity:** Medium
**Status:** Cannot reproduce (2026-06-11) — integration test added

Tested insertion before a multi-line lemma statement (`bug_multiline_stmt`)
and a single-line one. Both position correctly above the target. The
`before` parameter search resolves to the correct keyword line.

**Integration test:** `tests/integration/tool_bugs.test.ts` — Bug #9 suite

## 5. "done" response doesn't suggest Qed

**Severity:** Low
**Status:** Fixed (40e6a4b)

Changed "done" to "done — try Qed" to explicitly guide the user.

## 6. No proof shape/context in insert response

**Severity:** Medium
**Status:** Partially fixed — response now includes `script` lines and goals

`insert_tactic` response now includes `-- proof script --` block showing the
tactic history, `-- admits --` with hashes, and structured data (`script`
array, `goals`, `next` hint). The context the caller needs is already present.

## 7. `coq_reset_proof` doesn't report which proof was reset

**Severity:** Medium
**Status:** Fixed (2026-06-11) — integration test confirms

Now reports `reset "proofName" to Admitted.` with the extracted lemma name.
The backward search from `Proof.` correctly finds the `Lemma`/`Theorem` keyword
and includes it in the response.

**Verified by:** `tests/integration/tool_bugs.test.ts` — Bug #7 suite

## 8. `coq_add_lemma` + `coq_reset_proof` corrupt file when used together

**Severity:** High
**Status:** Cannot reproduce (2026-06-11) — integration test added

Tested both directions:
1. Add lemma → insert tactic → reset new lemma: file valid, existing proofs intact.
2. Add lemma → reset original (not new) lemma: file valid, new lemma still exists.

The cursor tracking is driven by explicit name parameters (`name`/`before`),
not by a shared cursor, so cross-tool interference doesn't occur.

**Integration test:** `tests/integration/tool_bugs.test.ts` — Bug #8 suite

## 9. `coq_add_lemma` positions lemma mid-statement instead of above

**Severity:** High
**Status:** Same as #4 — cannot reproduce

Duplicate of #4 — both describe the same positioning issue. See #4 for test results.
**Integration test:** `tests/integration/tool_bugs.test.ts` — Bug #9 suite
