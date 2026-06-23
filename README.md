# 🤖 rocq-piler

![rocq-piler](assets/header.png)

**Let rocq-piler do the heavy lifting for your proofs.**

## Overview

rocq-piler is an MCP server for interactive Coq/Rocq proof development via coq-lsp. It provides a tool suite that lets AI agents explore, write, verify, and refine proofs with immediate feedback.

## Tools

| Tool | Description |
|------|-------------|
| `search_lemmas` | Find relevant lemmas in the Coq environment by name or pattern |
| `edit_file` | Write or modify `.v` files — auto-reports errors and goal state after each edit |
| `check_file` | Full file verification with modes: `full`/`errors`/`first` for compact feedback |
| `stratify` | Case-split a proof and auto-close easy cases; returns hash-addressable admits for survivors |
| `close_admits` | Batch-close surviving admits with a portfolio of tactics (supports multi-line with bullets) |
| `reset_proof` | Wipe a proof body and start fresh |
| `focus_proof` | Inspect proof state: goals, bullet stack, admit hashes, proof script |

## Workflow Discipline

The most effective approach for AI proof assistants:

1. **`edit_file` first** — write proofs and helper lemmas directly. Instant error + goal feedback per edit. No need for `bash` + `coqc`.
2. **`check_file` for status** — use `mode: "errors"` (compact) for quick verification, `mode: "first"` for tight feedback loops.
3. **`stratify` to escalate** — when a proof has too many cases to write by hand, split it with stratify. Returns hash-addressable admits for survivors.
4. **`close_admits` to finish** — batch-close survivors by hash. Tactics support multi-line scripts with bullets.
5. **`reset_proof` when stuck** — wipe and restart cleanly. Auto-detect thrashing after 5 consecutive same-error edits.

## Benchmarks

| Problem | Profile | Duration | Cost | Tokens (in/out/think) | Tools |
|---------|---------|----------|------|----------------------|-------|
| pcf_ref | robust | 1181s | $0.06 | 1K / 8K / 51K | 31 (6 edit, 5 check, 3 stratify, 2 close_admits) |
| insertion_sort | lean | 206s | $0.03 | 23K / 4K / 17K | 24 (10 search, 5 check, 5 edit) |
| dep_vec | lean | 565s | $0.07 | 18K / 9K / 57K | 31 (14 edit, 6 check) |
| mergesort | lean | 1018s | $0.19 | — | 104 |

**Stats are updated as runs complete.** All benchmarks use DeepSeek V4 Pro.

### pcf_ref — PCF + References Type Preservation

A PCF language extended with mutable references (allocation, dereference, assignment), heap semantics, and store typing. The preservation theorem proves that well-typed programs remain well-typed after reduction, with the store typing possibly extended.

**21** step constructors, **10** helper lemmas, **311** lines, solved in **1181s** ($0.06).

Auxiliary lemmas: `extends_refl`, `extends_app`, `extends_nth_error`, `weaken_append`, `has_type_store_weaken`, `heap_ok_store_weaken`, `heap_lookup_typed`, `heap_update_ok`, `shift_closed`, `subst_lemma`.

## Profiles

| Profile | Tools | Use case |
|---------|-------|----------|
| `lean` | search_lemmas, edit_file, check_file | Fast iteration for simple proofs |
| `robust` | lean + stratify, close_admits, reset_proof, focus_proof | Complex multi-case proofs |
| `full` | All tools | Maximum capability, more overhead |
| `rocq-mcp` | rocq-mcp tools only | Baseline comparison |

## Architecture

rocq-piler uses a **content-addressed admit system**: every open goal has a unique hash computed from its goal text. Stratify and focus_proof return hashes for survivors, and close_admits targets them by hash — close all matching admits at once across any bullet depth.

```
edit_file → instant feedback → check_file → stratify → close_admits → Qed
```

## Getting Started

### Prerequisites
```bash
opam install coq-lsp
```

### Installation
```bash
cd rocq-piler
npm install
npm run build
npm test                 # unit tests
npm run test:integration # integration tests
```

### Usage with OpenCode

Add to `~/.config/opencode/opencode.json`:
```json
{
  "mcp": {
    "rocq-piler": {
      "type": "local",
      "command": ["node", "/path/to/rocq-piler/dist/index.js", "--coq-lsp-path", "coq-lsp"],
      "enabled": true
    }
  }
}
```

## Running Benchmarks

```bash
# Single run
bash benchmarks/harness/run.sh --model deepseek/deepseek-v4-pro --problem pcf_ref --profile robust

# Batch sweep
bash benchmarks/harness/batch.sh --profiles lean,robust --problems insertion_sort,dep_vec,pcf_ref

# Evaluate
bash benchmarks/harness/evaluate.sh benchmarks/complete/pcf_ref.v
```

## License

MIT
