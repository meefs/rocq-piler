# Refinement-Workflow Experiment: `shift_at_preserves`

## Hypothesis

Hole-addressed proof construction (`refine_proof` / `list_holes` / `try_fill` /
`fill_hole`) is more call- and token-efficient than tactic-mode
(`insert_tactic` + bullets) for multi-case induction proofs, because:

1. Named holes give direct goal addressing (tactic bullets only target goal 1,
   which caused repeated undo/reset thrash in the baseline).
2. `try_fill` is speculative, eliminating the insert/observe-no-progress/undo
   cycle (the baseline had ~7 zero-progress insertions it could not detect
   up front).
3. Hole reports (closed/new/remaining) are compact compared to full
   multi-goal dumps.

## Setup

- **File:** `benchmarks/completed/pcf_ref_refine.v`
- **Target:** `Lemma shift_at_preserves` (L144, currently `Admitted`).
  Everything else in the file is `Qed` and the file checks cleanly.
- **Available:** all earlier lemmas in the file, including the helper
  `nth_error_shift_var` (L139). See *Baseline adjustments* below.

## Rules for the test model

**Allowed tools:**
`refine_proof`, `list_holes`, `try_fill`, `fill_hole`,
`search_lemmas`, `inspect_term`, `inspect_about`, `locate_term`,
`check_file`, `open_goals`.

**Forbidden:**
- `insert_tactic`, `focus_proof` bullets, `edit_file`, `undo_step`,
  `delete_step`, raw file edits of the proof body.
- Reading `benchmarks/completed/pcf_ref.v` (it contains the full solution)
  or reading the proof bodies of other lemmas in the test file.
- `reset_proof` is allowed but counts as a failure event (record it).

**Suggested workflow shape** (mechanism only, not the solution — we are
testing workflow efficiency, not tool discovery):

1. `refine_proof` with a skeleton term, e.g. a single `?[body]` hole.
2. `fill_hole` on `body` with a *single-sentence* fan-out script
   (e.g. an induction sentence with `try solve [...]` closers); surviving
   subgoals become addressable holes `body_1 .. body_n`.
3. `list_holes` to see survivors; close each with `fill_hole`
   (`[h]: { ... }` bursts), using `try_fill` first whenever uncertain.

## Metrics to record (append a Results section to this file)

| metric | value |
|---|---|
| total tool calls (all kinds) | |
| `try_fill` attempts / failures | |
| `fill_hole` attempts / failures | |
| `reset_proof` events | |
| zero-progress events (call that changed nothing) | |
| final status (`check_file`: target must be `Qed`, file 0 admitted) | |
| approximate response-token footprint (if measurable) | |

## Baseline (tactic-mode, recorded 2026-06-12, same lemma)

- **~35-37 tool calls** from first `focus_proof` to `Qed`.
- **3 × `reset_proof`**, **~5 × `undo_step`**.
- **~7 zero-progress insertions** (tactic reported inserted, goal set
  unchanged; not detectable without a follow-up dump).
- Several full 5-goal / 12-goal state dumps (~3-5k tokens each), plus
  quadratic re-echo of the accumulated proof script on every insertion.
- Failure modes were all goal-addressing: bullets target goal 1 only;
  `match goal` patterns broke on auto-generated IH names
  (`IHhas_type` vs `IHhas_type1`).

### Baseline adjustments (fairness caveats)

1. The baseline count **includes 3 calls** spent inventing and proving the
   helper `nth_error_shift_var`. That helper now exists in the test file.
   If the test model uses it: compare against ~32 baseline calls.
   The final baseline proof's Var case did **not** use the helper
   (direct `nth_error_app1/app2` rewrites), so not using it is also fine.
2. `subst_preserves` (already `Qed` in the test file) was solved *after*
   the target in the baseline session, so its presence leaks no technique
   the baseline had access to at the same point — but its statement order
   differs from the original benchmark file. Minor.

## Success criteria

1. `check_file` on `pcf_ref_refine.v` reports `shift_at_preserves [Qed]`
   and 0 admitted.
2. No forbidden tools used.
3. Metrics table filled in.

## What would falsify the hypothesis

- Call count ≥ baseline (~32-37), or
- The fan-out/fill loop degenerates into its own retry thrash
  (e.g. `fill_hole` failures ≥ baseline zero-progress events), or
- Hole reports turn out as verbose as goal dumps, erasing the token win.
