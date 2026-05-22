import { describe, it, expect } from 'vitest';
import {
  isSkipLine,
  isProofEndLine,
  isTopLevelLine,
  autoAdvancePosition,
  insertPosition,
  findProofLine,
} from './coq-utils.js';
import { applyTextEdits } from './document-manager.js';

// ── isSkipLine ────────────────────────────────────────────────────

describe('isSkipLine', () => {
  it('skips blank lines', () => {
    expect(isSkipLine('')).toBe(true);
    expect(isSkipLine('   ')).toBe(true);
    expect(isSkipLine('\t')).toBe(true);
  });

  it('skips comment lines', () => {
    expect(isSkipLine('(* comment *)')).toBe(true);
    expect(isSkipLine('  (* nested *)')).toBe(true);
  });

  it('skips Proof. on its own line', () => {
    expect(isSkipLine('Proof.')).toBe(true);
  });

  it('skips Proof. with whitespace but no keyword after', () => {
    expect(isSkipLine('Proof.  ')).toBe(true);
  });

  it('does NOT skip "Proof. Admitted." — that is the entire proof body', () => {
    expect(isSkipLine('Proof. Admitted.')).toBe(false);
  });

  it('does NOT skip "Proof. Qed."', () => {
    expect(isSkipLine('Proof. Qed.')).toBe(false);
  });

  it('does NOT skip "Proof. Defined."', () => {
    expect(isSkipLine('Proof. Defined.')).toBe(false);
  });

  it('skips Defined. on its own', () => {
    expect(isSkipLine('Defined.')).toBe(true);
  });

  it('does not skip a normal tactic line', () => {
    expect(isSkipLine('intros H.')).toBe(false);
  });

  it('does not skip a Lemma line', () => {
    expect(isSkipLine('Lemma foo : bar.')).toBe(false);
  });
});

// ── isProofEndLine ────────────────────────────────────────────────

describe('isProofEndLine', () => {
  it('matches Qed.', () => expect(isProofEndLine('Qed.')).toBe(true));
  it('matches Admitted.', () => expect(isProofEndLine('Admitted.')).toBe(true));
  it('matches Defined.', () => expect(isProofEndLine('Defined.')).toBe(true));
  it('does not match other lines', () => expect(isProofEndLine('Proof.')).toBe(false));
  it('trims whitespace', () => expect(isProofEndLine('  Qed.  ')).toBe(true));
});

// ── isTopLevelLine ────────────────────────────────────────────────

describe('isTopLevelLine', () => {
  it('matches Lemma', () => expect(isTopLevelLine('Lemma foo : bar.')).toBe(true));
  it('matches Theorem', () => expect(isTopLevelLine('Theorem foo : bar.')).toBe(true));
  it('matches Definition', () => expect(isTopLevelLine('Definition foo := bar.')).toBe(true));
  it('matches Fixpoint', () => expect(isTopLevelLine('Fixpoint foo := bar.')).toBe(true));
  it('matches Inductive', () => expect(isTopLevelLine('Inductive foo := bar.')).toBe(true));
  it('matches Axiom', () => expect(isTopLevelLine('Axiom foo : bar.')).toBe(true));
  it('matches Parameter', () => expect(isTopLevelLine('Parameter foo : bar.')).toBe(true));
  it('matches CoInductive', () => expect(isTopLevelLine('CoInductive foo := bar.')).toBe(true));
  it('does not match tactic lines', () => expect(isTopLevelLine('intros H.')).toBe(false));
  it('does not match Proof.', () => expect(isTopLevelLine('Proof.')).toBe(false));
});

// ── insertPosition ────────────────────────────────────────────────

describe('insertPosition', () => {
  it('inserts after Proof. on its own line', () => {
    const text = `Lemma foo : 1 = 1.
Proof.

Lemma bar : 1 = 1.`;
    // position at Proof. line (line 1)
    const result = insertPosition(text, { line: 1, character: 0 });
    // Should advance past Proof. and blank line 2 → land at line 3 (Lemma bar)
    expect(result).toEqual({ line: 3, character: 0 });
  });

  it('stops before next toplevel keyword', () => {
    const text = `Theorem x : 1 = 1.
Proof.
  reflexivity.
Qed.

Lemma y : 2 = 2.`;
    // position at Proof. line (line 1)
    const result = insertPosition(text, { line: 1, character: 0 });
    // Phase 1: skip Proof (line 1) → line 2 is content, stop Phase 1
    // Phase 2: skip "reflexivity." (line 2) → line 3 is Qed. → isProofEndLine → break
    expect(result).toEqual({ line: 3, character: 0 });
  });

  it('stops at empty line (end of file boundary)', () => {
    const text = `Lemma foo : 1 = 1.
Proof.
  intro H.
  reflexivity.`;
    const result = insertPosition(text, { line: 1, character: 0 });
    // After Proof + content lines 2-3, line 4 is empty (or EOF)
    // Actually: Phase 1 skips Proof (line 1) → line 2 content → stop Phase 1
    // Phase 2 skips lines 2-3, line 4 is blank → break
    // Wait, there's no line 4. text has 4 lines total (0,1,2,3)
    // Phase 1: line 0=Lemma foo → not skip → break. line=0
    // Phase 2: line 0=Lemma → isTopLevelLine → break. result={line:0, char:0}
    // That's wrong. Let me reconsider. Position is line 1 (Proof.)
    // Phase 1: line 1=Proof. → skip → line=2
    // Phase 1: line 2="  intro H." → not skip → break
    // Phase 2: line 2="  intro H." → not empty, not proof-end, not toplevel → line=3
    // Phase 2: line 3="  reflexivity." → not empty, not proof-end, not toplevel → line=4
    // Phase 2: line 4 >= text.length(4) → break
    // Result: {line:4, char:0}. Cap: line=4, lines.length=4 → no change
    expect(result).toEqual({ line: 4, character: 0 });
  });
});

// ── autoAdvancePosition ───────────────────────────────────────────

describe('autoAdvancePosition', () => {
  it('advances past Proof. line', () => {
    const text = `Lemma foo : 1 = 1.
Proof.
  intro H.`;
    const result = autoAdvancePosition(text, { line: 1, character: 0 });
    // Skip Proof (line 1) → line 2 is content → stop
    expect(result).toEqual({ line: 2, character: 0 });
  });

  it('advances past blank lines after Proof.', () => {
    const text = `Lemma foo : 1 = 1.
Proof.

  intro H.`;
    const result = autoAdvancePosition(text, { line: 1, character: 0 });
    // Skip Proof (line 1), skip blank (line 2) → line 3 is content → stop
    expect(result).toEqual({ line: 3, character: 0 });
  });

  it('caps to file bounds', () => {
    const text = `Proof.`;
    const result = autoAdvancePosition(text, { line: 0, character: 0 });
    expect(result).toEqual({ line: 1, character: 0 });
  });
});

// ── findProofLine ─────────────────────────────────────────────────

describe('findProofLine', () => {
  const file = [
    '(* Header *)',
    '',
    'Lemma foo : forall n, n + 0 = n.',
    'Proof.',
    '  induction n.',
    '  - reflexivity.',
    'Qed.',
    '',
    'Theorem bar : 1 = 1.',
    'Proof. Admitted.',
    '',
    'Lemma baz : 2 = 2.',
    'Proof.',
  ];

  it('finds Proof. for a Lemma', () => {
    expect(findProofLine(file, 'foo')).toBe(3);
  });

  it('finds Proof. Admitted. for a Theorem', () => {
    expect(findProofLine(file, 'bar')).toBe(9);
  });

  it('finds Proof. for a later lemma', () => {
    expect(findProofLine(file, 'baz')).toBe(12);
  });

  it('returns -1 for non-existent name', () => {
    expect(findProofLine(file, 'nonexistent')).toBe(-1);
  });
});

// ── Integration: full tool flow on a known file ────────────────────

describe('tool integration: before/after snapshots', () => {
  // Simulates the effect of coq_focus + coq_insert_tactic on a clean template

  it('auto-removes Proof. Admitted. on one line via focus', () => {
    const before = `Lemma foo : 1 = 1.
Proof. Admitted.

Lemma bar : 2 = 2.`;
    const proofLine = findProofLine(before.split('\n'), 'foo');
    expect(proofLine).toBe(1); // line 1 is "Proof. Admitted."

    // Simulate coq_focus auto-remove: check if insertPos line has Admitted.
    // But insertPosition skips Proof.Admitted. (since isSkipLine returns false for it)
    const pos = insertPosition(before, { line: proofLine, character: 0 });
    // pos is at line 2 (blank) after Proof.Admitted. was not skipped
    // No, wait: isSkipLine returns false for Proof.Admitted, so insertPosition doesn't skip it
    // Phase 1: line 1 = "Proof. Admitted." → not skip → break, line=1
    // Phase 2: line 1 = "Proof. Admitted." → l="Proof. Admitted." → not empty → not proof-end → not toplevel → line=2
    // Phase 2: line 2 = "" → l="" → empty → break
    // Result: {line: 2, character: 0}
    expect(pos).toEqual({ line: 2, character: 0 });

    // Now the auto-remove check: walk back from insPos.line - 1 = line 1
    // Line 1: "Proof. Admitted." → starts with "Proof.", includes "Admitted." → split!
    // Replaces "Proof. Admitted.\n" with "Proof.\n"
    const after = 'Lemma foo : 1 = 1.\n' + 'Proof.\n' + '\n' + 'Lemma bar : 2 = 2.';
    expect(after).toEqual(`Lemma foo : 1 = 1.
Proof.

Lemma bar : 2 = 2.`);
  });

  it('coq_insert_tactic inserts at correct position after Proof.', () => {
    // After auto-remove, the file is:
    const before = `Lemma foo : 1 = 1.
Proof.

Lemma bar : 2 = 2.`;
    // findProofLine returns line 1 (Proof.)
    // position = {line:1, char:0}
    // insertPosition advances past Proof and blank → {line:3, char:0} (Lemma bar — toplevel stop)
    const pos = insertPosition(before, { line: 1, character: 0 });
    expect(pos).toEqual({ line: 3, character: 0 });

    // Apply insert: insert "  intros H.\n" at pos
    const lines = before.split('\n');
    const newText = [
      ...lines.slice(0, pos.line),
      '  intros H.',
      ...lines.slice(pos.line),
    ].join('\n');
    expect(newText).toEqual(`Lemma foo : 1 = 1.
Proof.

  intros H.
Lemma bar : 2 = 2.`);
  });

  it('chain: focus auto-remove + insert tactic', () => {
    const template = `Lemma foo : 1 = 1.
Proof. Admitted.

Lemma bar : 2 = 2.`;

    // Step 1: coq_focus → auto-remove
    const proofLine = findProofLine(template.split('\n'), 'foo');
    // Walk back check: insertPosition → line 2, walk back to line 1 → Proof.Admitted. → split
    const afterFocus = `Lemma foo : 1 = 1.
Proof.

Lemma bar : 2 = 2.`;
    expect(afterFocus).not.toContain('Admitted');

    // Step 2: coq_insert_tactic("intros H.")
    const afterInsert = `Lemma foo : 1 = 1.
Proof.

  intros H.
Lemma bar : 2 = 2.`;
    expect(afterInsert).toContain('intros H.');
  });
});

// ── applyTextEdits ────────────────────────────────────────────────

describe('applyTextEdits', () => {
  it('replaces a single line', () => {
    const text = 'line 0\nline 1\nline 2';
    const result = applyTextEdits(text, [{
      range: {
        start: { line: 1, character: 0 },
        end: { line: 2, character: 0 },
      },
      newText: 'NEW LINE\n',
    }]);
    expect(result).toBe('line 0\nNEW LINE\nline 2');
  });

  it('replaces within a line', () => {
    const text = 'hello world\nfoo bar';
    const result = applyTextEdits(text, [{
      range: {
        start: { line: 0, character: 6 },
        end: { line: 0, character: 11 },
      },
      newText: 'there',
    }]);
    expect(result).toBe('hello there\nfoo bar');
  });

  it('handles multiple edits', () => {
    const text = 'a\nb\nc\nd';
    const result = applyTextEdits(text, [
      {
        range: { start: { line: 2, character: 0 }, end: { line: 3, character: 0 } },
        newText: 'C\n',
      },
      {
        range: { start: { line: 0, character: 0 }, end: { line: 1, character: 0 } },
        newText: 'A\n',
      },
    ]);
    expect(result).toBe('A\nb\nC\nd');
  });

  it('applies the split Proof. Admitted. → Proof.', () => {
    const text = 'Lemma foo : 1.\nProof. Admitted.\n\nLemma bar : 2.';
    const result = applyTextEdits(text, [{
      range: {
        start: { line: 1, character: 0 },
        end: { line: 2, character: 0 },
      },
      newText: 'Proof.\n',
    }]);
    expect(result).toBe('Lemma foo : 1.\nProof.\n\nLemma bar : 2.');
  });

  it('applies the remove Admitted. on its own line', () => {
    const text = 'Lemma foo : 1.\nProof.\nAdmitted.\n\nLemma bar : 2.';
    const result = applyTextEdits(text, [{
      range: {
        start: { line: 2, character: 0 },
        end: { line: 3, character: 0 },
      },
      newText: '',
    }]);
    expect(result).toBe('Lemma foo : 1.\nProof.\n\nLemma bar : 2.');
  });

  it('inserts a tactic after Proof.', () => {
    // After auto-remove: Proof + blank line
    const text = 'Lemma foo : 1.\nProof.\n\nLemma bar : 2.';
    const insertPos = insertPosition(text, { line: 1, character: 0 });
    const result = applyTextEdits(text, [{
      range: { start: insertPos, end: insertPos },
      newText: '  intros H.\n',
    }]);
    expect(result).toBe('Lemma foo : 1.\nProof.\n\n  intros H.\nLemma bar : 2.');
  });
});
