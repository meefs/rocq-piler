# SEFM 2026 Submission - rocq-piler Tool Paper

## Submission Details

- **Conference**: SEFM 2026 (24th International Conference on Software Engineering and Formal Methods)
- **Location**: Malta
- **Date**: November 25-27, 2026 (Workshops: Nov 23-24)
- **Submission Type**: Tool Paper (8 pages + 1 page bibliography)

## Important Deadlines (AoE = UTC-12h)

- **Abstract submission**: June 16, 2026
- **Paper submission**: June 23, 2026
- **Author notification**: August 30, 2026
- **Camera ready**: September 14, 2026

## Submission Link

https://easychair.org/my/conference?conf=sefm2026

## Paper Details

- **Title**: rocq-piler: A Content-Addressed Proof Oracle for LLM-Driven Discharge of Separation-Logic Obligations
- **Author**: Gavin Mendel-Gleason (Scidonia, Dublin, Ireland)
- **File**: `rocq-piler-sefm2026.tex` (replaces the old `rocq-robot-sefm2026.tex`)
- **Format**: Springer LNCS (will need actual llncs.cls for final submission)
- **Current length**: 7 pages (within 8-page limit)

## Paper Structure

1. **Introduction** (1 page)
   - Residual obligations of deductive verifiers as the problem
   - Content-addressed obligations as the core idea
   - Contributions + tool availability

2. **Motivation: the Residual Obligations of a Deductive Verifier** (~0.75 page)
   - axiomander emits Iris separation-logic obligations
   - Automation discharges most; ~20% need an expert
   - rocq-piler as the tunable oracle for that tail (prototype integration)

3. **The Content-Addressed Obligation Model** (~1 page)
   - From positions to hashes (stability + coalescence)
   - The core focus/insert loop

4. **Tool Architecture and Higher-Level Moves** (~1.5 pages)
   - MCP/LSP-Pétanque/workspace layers
   - Core obligation tools
   - `stratify` + `close_admits` batch moves
   - Speculative execution, knowledge search, incremental cache

5. **Case Study: Type Preservation for PCF + References** (~1.5 pages)
   - Problem (typed store, store extension, de Bruijn substitution)
   - Autonomous process (add_lemma → stratify → close survivors by hash)
   - Results: 21 cases, 9 lemmas, ~50 calls, ~$0.04; two models

6. **Related Work** (0.5 pages)
   - Iris/separation logic; LLM proving (Baldur, LeanDojo); prover interfaces (coq-lsp, CoqPIE, Proof General)

7. **Status, Lessons, Future Work** (0.5 pages)

8. **Conclusion** + **Bibliography** (7 references)

## Key Strengths for SEFM

✅ **Topic match**: deductive verification + formal methods + LLM automation
✅ **Concrete problem**: automating the ~20% residual tail of an Iris-based verifier (axiomander)
✅ **Novel abstraction**: content-addressed proof obligations + batch, speculative, non-regressing closing moves
✅ **Reproducible case study**: type preservation for PCF+references (21 cases, 9 lemmas) closed by two LLMs for a few cents
✅ **Open-source tool**: MIT, npm-published, actively developed
✅ **Industrial relevance**: an oracle that plugs into a verifier's inner loop

## To-Do Before Submission

### By June 16 (Abstract Deadline)

1. ✅ Draft paper completed
2. ⬜ Install proper LNCS class (`texlive-publishers` or manual download)
3. ⬜ Compile with actual LNCS format and verify 8-page limit
4. ⬜ Add video URL (if available)
5. ⬜ Add Zenodo DOI for tool artifact
6. ⬜ Submit abstract to EasyChair

### By June 23 (Full Paper Deadline)

7. ⬜ Final proofreading
8. ⬜ Verify all citations are correct
9. ⬜ Check LNCS formatting guidelines compliance
10. ⬜ Submit full paper PDF to EasyChair

## LNCS Installation (Required for Final Submission)

### Option 1: Install via package manager
```bash
sudo apt-get install texlive-publishers
```

### Option 2: Manual download from Springer
1. Visit: https://www.springer.com/gp/computer-science/lncs
2. Download "LaTeX2e Proceedings Templates (zip)"
3. Extract `llncs.cls` to paper directory

### Option 3: Use Overleaf
- Upload project to Overleaf (has LNCS built-in)

## Current Status

- ✅ Paper rewritten around content-addressed obligations + axiomander oracle framing (`rocq-piler-sefm2026.tex`)
- ✅ Compiled with article class (temporary), 7 pages
- ✅ Within page limit (7/8 pages)
- ✅ Case study updated to actual figures (21 cases, 9 lemmas, ~50 calls, ~$0.04)
- ⬜ Needs LNCS class for final formatting
- ⬜ Needs abstract submission
- ⬜ Needs full paper submission

## Notes

- Current version uses `article` class as temporary substitute
- Final submission MUST use `\documentclass[runningheads]{llncs}`
- LNCS format may slightly change page count (typically ±0.5 pages)
- Bibliography currently ~7 references (added Iris)
- The old `rocq-robot-sefm2026.tex` is superseded by `rocq-piler-sefm2026.tex`
- axiomander integration is described as an in-progress prototype; the PCF+Ref
  proof is the reproducible stand-in for its residual obligations
