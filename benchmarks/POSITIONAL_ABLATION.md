# Positional vs Content-Addressed Ablation

This experiment responds to SEFM reviewer weakness #3 / suggestion #3: provide a
comparison against a *positional* proof-interaction baseline to justify the
content-addressed obligation model.

## Hypothesis

Content-addressed obligations + batch moves (`stratify`, `close_admits`,
hash-targeted `insert_tactics`) let an LLM agent close a multi-case proof with
fewer API calls, lower cost, and fewer failed steps than a purely *positional*
editing surface (plain text edits + diagnostics).

## Tool-surface modes (one codebase, env-gated)

The server registers tools conditionally based on environment variables
(`src/index.ts`):

| Mode | Env | Tools exposed |
|------|-----|---------------|
| **Full** (treatment) | _(none)_ | 13 content-addressed tools: `focus_proof`, `insert_tactics`, `stratify`, `close_admits`, `add_lemma`, `delete_lemma`, `reset_proof`, `check_file`, `search_lemmas`, `inspect_term`, `inspect_about`, `locate_term`, `require_lib` |
| **Full + edit_file** | `ROCQ_PILER_ENABLE_EDIT_FILE=1` | the 13 above **plus** `edit_file` |
| **Positional** (baseline) | `ROCQ_PILER_POSITIONAL_ONLY=1` | **only** `edit_file` + `check_file` |

In positional-only mode the dispatcher also refuses any other tool if called
directly, so the ablation surface is airtight.

> Note: `edit_file` was pruned from the default tool set in v0.8.0. It is
> re-added here *only* behind a flag, so the production default is unchanged.

## Reproducing

```bash
# Build from this branch (exp/positional-baseline)
npm run build

# Verify the three surfaces:
printf '%s\n' \
  '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"t","version":"0"}}}' \
  '{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}' \
  | ROCQ_PILER_POSITIONAL_ONLY=1 node dist/index.js   # → check_file edit_file
```

### MCP client config for each arm

**Positional baseline:**
```json
{ "mcpServers": { "rocq-piler": {
  "command": "node",
  "args": ["/path/to/rocq-piler/dist/index.js", "--workspace-root", "/path/to/rocq-piler/benchmarks"],
  "env": { "ROCQ_PILER_POSITIONAL_ONLY": "1" }
}}}
```

**Full (treatment):** same, with `env` omitted.

## Task

Identical for both arms: prove type preservation for PCF + references.

- Challenge: `benchmarks/incomplete/pcf_ref.v`
- Instructions: `benchmarks/incomplete/pcf_ref.md` (copy to `benchmarks/complete/`)
- Success: `complete/pcf_ref.v` compiles with `Qed` on all 9 lemmas + the theorem,
  no remaining `Admitted`.

Run each arm with the same model(s) and the same prompt. For the positional arm,
the agent may only use `edit_file` (write whole tactics/lemmas as text) and
`check_file` (read diagnostics).

## Metrics to record (per run)

- Model + version
- Reached `Qed`? (yes / no / partial — how many admits left)
- Total API calls / tool calls
- Wall-clock time
- Actual provider cost
- Failed tool calls (and failure mode: stale position, syntax, wrong goal, …)
- Notes (where the positional arm stalls vs where content-addressing helps)

Save raw transcripts and token reports under `benchmarks/` named by arm + model,
e.g. `positional-<model>-pcf_ref-<sha>.txt`,
`full-<model>-pcf_ref-<sha>.txt`.

## Results

| Arm | Model | Qed? | API calls | Cost | Failed calls | Time |
|-----|-------|------|-----------|------|--------------|------|
| Full | DeepSeek V4 | yes | 50 | $0.04 | 3 survivors | — |
| Positional | _TBD_ | _TBD_ | _TBD_ | _TBD_ | _TBD_ | _TBD_ |
| _add rows per run_ | | | | | | |

(The Full/DeepSeek row is the existing main-branch run, included for reference;
re-run it from this branch for a strictly like-for-like comparison.)
