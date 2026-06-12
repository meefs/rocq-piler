# Term Refinement Design — Hole-Addressed Proof Construction

**Status:** Implemented (branch `term-refinement-experiment`) — tools
`list_holes` / `refine_proof` / `fill_hole` / `try_fill` in `src/index.ts`,
helpers in `src/coq-utils.ts`, tests in `tests/integration/refinement.test.ts`
(23 tests, all passing; full suite 168 integration + 154 unit, no regressions)
**Date:** 2026-06-11
**Experiments:** `experiments/refinement_experiment.v`, `experiments/evar_probe.v`
(verified against coq-lsp 0.2.5 / Rocq 9.1.1 via petanque)

## Motivation

The current tactic-insertion interface addresses open goals via three mechanisms,
all approximations of the same need:

| Mechanism | Weakness |
|---|---|
| Bullets (`-`/`+`/`*`) | Positional + ordered; depth tracking caused most TODO.md bugs (auto-bullet injection, seal logic, indent computation) |
| Admit hashes | Hash = md5 of goal text; identical goals collide; goal drift invalidates the address |
| Cursor tracking | Stateful, cross-tool interference (historical bug #8) |

Hypothesis-name fragility is a second pain point: `induction`/`inversion`
auto-generate `H2`, `H4`, … which made the `pcf_ref.v` proofs brittle.

Coq's native refinement machinery (named existential variables + goal
selectors) solves both problems with stock features.

## The core invariant

> **Every open goal has a name, always.**

Names are chosen by the agent when it writes a skeleton (`?[base]`, `?[step]`),
are stable across edits, are order-independent, and never collide (the tool
validates freshness). The tools' job is to never let an unnamed goal exist in
the file.

A second principle: **opinionated about addressing, hybrid about content.**
The plus_comm experiment used `refine` for the induction skeleton but tactics
(`rewrite`, `reflexivity`) for the leaves. Equational chains as raw `eq_ind`
terms are impractical, and `lia`/`eauto`/`set_solver`/Iris proofmode are
irreplaceable search procedures. So: holes are the only *addressing*
mechanism; each *fill* may be a term or a tactic burst.

## Verified primitives (experiment results)

1. **`unshelve refine` is mandatory.** On `exists n, n = 2` with
   `refine (ex_intro _ ?[witness] ?[proof])`:
   - plain `refine` silently *shelves* the dependent `?witness` (1 goal surfaced);
   - `unshelve refine` surfaces both (`nat` and `?witness = 2`).
   - Noise is bounded: holes solved by unification/elaboration (e.g. the
     predicate `_`) are *not* surfaced.

2. **Holes can vanish by unification.** `[proof]: reflexivity.` alone finished
   the whole proof — unifying `?witness := 2` as a side effect. Tools must
   re-query the hole set after every fill; never assume one-fill-one-hole.

3. **Evar names are obtainable — but mind the ordering.** `petanque/goals`
   does not label goals with evar names. Two complementary sources exist:

   - `Show Existentials.` returns all evars with contexts and shelved status,
     **in CREATION order**:

     ```
     Existential 1 = ?witness : [ |- nat] (shelved)
     Existential 2 = ?proof : [ |- ?witness = 2]
     ```

   - `Set Printing Goal Names. Show.` returns the focused goals with names
     **in GOAL-LIST order**:

     ```
     3 goals, goal 1 (?Goal) … goal 2 (?Goal0) is: … goal 3 (?eq) is: …
     ```

   These orders DIFFER as soon as a selector fill creates new goals (the new
   children sit at the front of the goal list but at the end of the evar
   creation order). Joining `Show Existentials` positionally with the goal
   list is therefore wrong — found the hard way: it renamed a *named* hole.
   Implementation rule: **goal positions/names come from `Show.` (with
   `Printing Goal Names`); `Show Existentials` is used only for shelved
   holes.** Also note auto-named goals (`?Goal`, `?Goal0`) are NOT addressable
   via `[Goal]:` selectors ("No such goal") — positional selectors (`1:`) are
   required for the renaming pass.

4. **Goal selectors work everywhere.** `[name]: tactic` and `[name]: { ... }`
   lines compile in files (including **out-of-order** fills), and execute fine
   from position-derived petanque states. No coq-lsp changes needed.

5. **The auto-bullet logic is the only enemy.** Reproduced: `insert_tactic`
   prepended a bullet, writing `- [gb]: reflexivity.` — Coq accepted it but it
   left a half-open bullet focused on the sibling goal. Selector lines must be
   inserted verbatim, bypassing all bullet machinery.

6. **`refine ?[x].` as goal renaming — verified.** `1: refine ?[named_left].`
   renames an anonymous goal in place; the renamed hole is then addressable by
   `[named_left]:` selectors, out of order. This is the escape hatch that
   restores the naming invariant after arbitrary goal-creating tactics.

7. **Auto-Qed gating — implementation note.** Post-write hole re-queries can
   be flaky (empty table on a transient LSP error). Never conflate an empty
   table with "no holes": gate auto-Qed exclusively on petanque's
   `proof_finished` flag from the speculative run of the committed script.

## Tool surface (4 verbs)

```
refine_proof(file, lemma, term)        — start the skeleton
fill_hole(file, lemma, hole, script)   — fill one named hole
try_fill(file, lemma, hole, script)    — speculative twin (no file change)
list_holes(file, lemma)                — the readout (absorbed into focus_proof)
```

### `refine_proof(file, lemma, term)`

- Inserts `unshelve refine (term).` after `Proof.`
- Rejects skeletons containing unnamed *proof* holes (inference `_` is fine —
  only unsolved holes surface).
- Spec-checked via petanque before any file write.
- On a non-virgin proof: error unless `replace: true`.
- Returns the hole table (see `list_holes`).

### `fill_hole(file, lemma, hole, script)`

Inserts a selector line **verbatim** — no bullet logic exists in this path.
Shape chosen automatically from the spec-check result:

- script **closes** the hole → `[hole]: { script }`
  (tactic bursts welcome — this is where the hybrid lives; `{ }` requires
  closure so the shape is self-enforcing)
- script **leaves goals** → must be a single `unshelve refine (term).` sentence
  whose new holes are all named and globally fresh in this proof.

**Escape hatch** (pending verification of `refine ?[x].`): a fill like
`[h]: induction n.` that leaves unnamed goals is repaired by auto-appending
`1: refine ?[h_1]. 1: refine ?[h_2].` — restoring the invariant so any tactic
remains usable.

Response (always re-queried, because of unification side effects):

```
filled [step] → closed: [step] (+[witness] by unification)
new holes: [step_base] (n:nat, IHn:… ⊢ …), [step_rec] (…)
remaining: 2 — auto-Qed at 0
```

Auto-Qed: when the hole count reaches 0, replace `Admitted.` with `Qed.`
(no bullet/seal special cases — the gate is simply "no holes").

### `list_holes(file, lemma)`

Joins `petanque/goals` with one speculative `Show Existentials.`:

- per hole: **name**, hypotheses, goal, **shelved flag**
- **depends-on**: evars occurring in the hole's type (e.g.
  `?proof : ?witness = 2`) — tells the agent that filling `?proof` may solve
  `?witness` by unification, or that filling `?witness` first refines
  `?proof`'s type.

### Kept / deleted

- **Deleted from this path:** auto-bullet injection, bullet-indent tracking,
  `admit_hash` addressing, `sealOpenGoals`. (Source of 5/8 historical bugs.)
- **Kept unchanged:** `snap_state`/`exec_tactic`/`state_goals` (these
  *implement* the new verbs), `search_lemmas`/`inspect_*`/`locate_term`/
  `require_lib`, `check_file`/`check_range`, `edit_file`, `add_lemma`/
  `delete_lemma`/`reset_proof`, `undo_step`.

## File format the tools maintain

```coq
Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof.
  unshelve refine (fun n => nat_ind (fun n0 => forall m, n0 + m = m + n0)
                     ?[base] ?[step] n).
  [step]: unshelve refine (fun n0 IHn m => ?[step_eq]).
  [base]: { intro m. rewrite (plus_n_O m). reflexivity. }
  [step_eq]: { simpl. rewrite (IHn m). rewrite (Nat.add_succ_r m n0) at 2.
               reflexivity. }
Qed.        (* auto: Admitted. until hole count = 0 *)
```

Properties: flat (no nesting discipline needed — names are proof-global),
order-independent, replayable, every line independently spec-checked, and
explicit binder names in skeletons eliminate auto-generated hypothesis-name
fragility (`H2`/`H4` churn).

## Worked example (from the experiment)

`plus_comm` proven via the workflow:

1. `snap_state` at `Proof.` → state with goal `forall n m, n + m = m + n`
2. `exec_tactic`:
   `refine (fun n => nat_ind (fun n0 => forall m, n0 + m = m + n0) (fun m => _) (fun n0 IHn m => _) n).`
   → 2 subgoals (`0 + m = m + 0`; step case with `IHn`)
3. Fill 1: `rewrite (plus_n_O m). simpl. reflexivity.`
4. Fill 2: `simpl. simpl in IHn. rewrite (IHn m). rewrite (Nat.add_succ_r m n0). reflexivity.`
   → `proof_finished=true`
5. Commit to file, `Qed`.

Note scope discipline: the skeleton's `nat_ind … n` requires `n` bound by the
term itself (`fun n => … n`) — at `Proof.` nothing is introduced yet.

## Iris note

`refine` on Iris proofmode goals manipulates the raw environment
representation and is effectively unusable; Iris fills will be tactic-kind
(`iIntros`/`iFrame`/…) almost always. This is fine under hybrid content: the
skeleton/hole structure still applies at the Coq level (e.g. splitting into
lemma-level obligations), with proofmode bursts inside `{ }` fills.

## Migration & decision experiment

1. Implement the four verbs alongside the existing tools (no removals).
2. Verify `refine ?[x].` renaming idiom; check selector + `{ }` interaction in
   long proofs.
3. **Decisive benchmark:** re-prove `benchmarks/incomplete/` (pcf_ref.v,
   mergesort.v, …) in refinement mode; compare tool calls, failure rate, and
   retries against the recorded tactic-mode runs.
4. Retire the losing path (or keep both if the data says they dominate in
   different domains — e.g. selectors for structured inductions, bullets never).

## Risks

- `unshelve refine` may surface typeclass holes the agent didn't intend to
  manage (esp. with Iris/stdpp `Decision`/`Countable` instances); mitigation:
  auto-`typeclasses eauto` pass on surfaced instance goals before reporting.
- Goal display of evar-laden types (`?witness = 2`) may confuse term
  generation; `list_holes` should annotate which names are still open.
- Multi-sentence fills inside `{ }` must fully close; the spec-check rejects
  otherwise — agents need the failure message to include the remaining
  subgoals (include them in the `try_fill`/`fill_hole` error reply).
