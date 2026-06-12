# Prove SnakeletWp.v

The file `examples/SnakeletWp.v` has 4 admitted lemmas — all Iris weakest-precondition
proofs for a small imperative language. Two helper lemmas are already Qed.
Close every admit and any additional lemmas you introduce. The file must end with
zero `Admitted.` and must pass `check_file`.

## File structure

- `SnakeletLang.v` — the language AST, operational semantics, Iris instantiation
- `SnakeletWp.v` — the proofs you need to complete
- `_CoqProject` — load path config (Iris resolves from opam automatically)

The 4 admitted lemmas are all inside a `Section wp` with an Iris `Context`:

```
Section wp.
  Context `{!irisGS_gen hlc SnakeletLang.snakelet_lang Σ}.
  ...
  Lemma wp_binop ...      (* Admitted *)
  Lemma wp_let ...        (* Admitted *)
  Lemma wp_if_true ...    (* Admitted *)
  Lemma wp_if_false ...   (* Admitted *)
End wp.
```

The two Qed helper lemmas (`reducible_pure_step`, `reducible_no_obs_pure_step`)
are outside the section but are used inside the WP proofs.

## Tool limitation — read carefully

The `insert_tactic` and `focus_proof` tools **cannot query goal states** inside Iris
proofmode proofs (after `iIntros`, `iApply`, `iModIntro`, etc.). You will see:

- `proof/goals` timeout or `illegal begin of vernac`
- `state_goals` returning null
- tactics being rolled back automatically

**Do NOT** use `insert_tactic` to build Iris proofs step-by-step. Instead, use
the `edit_file` tool with `find`/`replace` to write the complete proof block
in one operation, then run `check_file` to verify.

Example workflow — replace an admitted proof block:
```
edit_file(
  file="examples/SnakeletWp.v",
  find="Lemma wp_binop ...\nProof.\nAdmitted.",
  replace="Lemma wp_binop ...\nProof.\n  ...your tactics...\nQed."
)
check_file(file="examples/SnakeletWp.v")
```

## Hints

The four lemmas follow the same pattern — you can reuse structure across them.
The Iris lifting lemma `wp_lift_pure_step_no_fork` is the key.
Look at `SnakeletLang.v` for the pure-step constructors (PureBinOp, PureLet,
PureIfTrue, PureIfFalse).
