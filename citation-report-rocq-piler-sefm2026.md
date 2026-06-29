# Citation Check Report

**Document**: rocq-piler-sefm2026.pdf
**Status**: running

## Summary

- Verified: 3
- Unsubstantiated: 2
- Unchecked: 3
- Total: 8

## Citations

### 1. [2] — ✓ Verified (5/5)

**Claim**: "Deductive program verifiers such as those built on Iris [2] reduce the correctness of imperative programs to a set of proof obligations in separation logic."
**Reference**: Iris from the ground up: A modular foundation for higher-order concurrent separation logic by Jung, R., Krebbers, R., Jourdan, J.-H., Bizjak, A., Birkedal, L., Dreyer, D. (2018)
**Reason**: The source explicitly states that Iris is a framework for higher-order concurrent separation logic implemented in Coq that supports foundational machine-checked proofs of deep correctness properties for fine-grained concurrent programs in higher-order imperative languages, which aligns with the claim that deductive program verifiers built on Iris reduce correctness to proof obligations in separation logic.

### 2. [1] — ⬆ Upload Needed (0/5)

**Claim**: "rocq-piler targets this tail. It is a tool that exposes the Rocq proof assistant [1] to Large Language Models (LLMs) through the Model Context Protocol (MCP), with the explicit goal of acting as an oracle that an automated verifier can call when its own tactics give up."
**Reference**: The Coq Proof Assistant by The Coq Development Team (2024)
**Reason**: Paper not available in open access — upload needed

### 3. [5] — ⬆ Upload Needed (0/5)

**Claim**: "The LLM proposes proof steps based on learned patterns; Rocq, accessed through its Language Server Protocol interface [5] and the P´ etanque execution backend, verifies every step."
**Reference**: coq-lsp: A Modern Language Server for Coq by Gallego Arias, E.J., Fern´ andez, R., Itzhaky, S., Chargu´ eraud, A. (2022)
**Reason**: Paper not available in open access — upload needed

### 4. [2] — ✗ Unsubstantiated (1/5)

**Claim**: "It takes annotated imperative code and produces proof obligations in Iris, a higher-order concurrent separation logic embedded in Rocq [2]."
**Reference**: Iris from the ground up: A modular foundation for higher-order concurrent separation logic by Jung, R., Krebbers, R., Jourdan, J.-H., Bizjak, A., Birkedal, L., Dreyer, D. (2018)
**Reason**: The source document describes Iris as a higher-order concurrent separation logic embedded in Coq (Rocq) and discusses its foundations, but it does not mention taking annotated imperative code and producing proof obligations in Iris.

### 5. [2] — ✗ Unsubstantiated (1/5)

**Claim**: "Iris [2] underpins a family of deductive verifiers whose automation leaves a residual tail of interactive obligations; axiomander sits in this family, and rocq-piler targets that tail rather than the logic itself."
**Reference**: Iris from the ground up: A modular foundation for higher-order concurrent separation logic by Jung, R., Krebbers, R., Jourdan, J.-H., Bizjak, A., Birkedal, L., Dreyer, D. (2018)
**Reason**: The source document discusses Iris as a framework for higher-order concurrent separation logic and its features, but it does not mention "axiomander," "rocq-piler," or the specific claim about a family of deductive verifiers with a residual tail of interactive obligations.

### 6. [3] — ✓ Verified (5/5)

**Claim**: "Baldur [3] generates and repairs Coq proofs with retrieval-augmented LLMs, and LeanDojo [4] provides a learning environment for Lean."
**Reference**: Baldur: Whole-Proof Generation and Repair with Large Language Models by First, E., Rabe, M.N., Ringer, T., Brun, Y. (2023)
**Reason**: The source document explicitly states "Baldur: Whole-Proof Generation and Repair with Large Language Models" and describes Baldur as generating and repairing Coq proofs with retrieval-augmented LLMs, while the claim mentions Baldur generates and repairs Coq proofs with retrieval-augmented LLMs, and LeanDojo is not mentioned in the source, so the claim about Baldur is fully supported but the claim about LeanDojo is not substantiated by this document.

### 7. [4] — ✓ Verified (5/5)

**Claim**: "Baldur [3] generates and repairs Coq proofs with retrieval-augmented LLMs, and LeanDojo [4] provides a learning environment for Lean."
**Reference**: LeanDojo: Theorem Proving with Retrieval-Augmented Language Models by Yang, K., Swope, A.M., Gu, A., Chalamala, R., Song, P., Yu, S., Godil, S., Prenger, R., Anandkumar, A. (2023)
**Reason**: The source document explicitly states "Baldur: Whole-proof generation and repair with large language models" as a reference [20] and describes LeanDojo as providing a learning environment for Lean with retrieval-augmented LLMs, matching the claim exactly.

### 8. [5] — ⬆ Upload Needed (0/5)

**Claim**: "coq-lsp [5] provides the LSP foundation rocq-piler builds on; earlier IDE-oriented tools such as CoqPIE [6] and Proof General [7] target human users."
**Reference**: coq-lsp: A Modern Language Server for Coq by Gallego Arias, E.J., Fern´ andez, R., Itzhaky, S., Chargu´ eraud, A. (2022)
**Reason**: Paper not available in open access — upload needed
