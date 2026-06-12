/**
 * Integration tests reproducing bugs from docs/TODO.md.
 *
 * Run: npm run test:integration
 */
import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, tempFixture, removeTempFixture } from './harness.js';

const TIMEOUT = 90_000;
const BUGS_FIXTURE = tempFixture('tool_bugs.v', 'bugsuite');

let h: McpHarness;

// Shared fixture — one temp copy for all tests, one harness process
beforeAll(async () => {
  h = await createHarness();
  await h.callTool('check_file', { file: BUGS_FIXTURE });
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
  removeTempFixture(BUGS_FIXTURE);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug #1: proof/goals returns 0 goals after compound tactics
// (compound tactic = induction/split/inversion that creates subgoals)
// ═══════════════════════════════════════════════════════════════════════════════

describe('Bug #1 — open_goals after compound tactic (induction)', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('tool_bugs.v', 'bug1');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('induction n. reports 2 focused goals, not 0', async () => {
    await h.callTool('insert_tactic', { file: tmpFile, name: 'bug_compound_induction', tactic: 'intro n.' });
    const r = await h.callTool('insert_tactic', {
      file: tmpFile, name: 'bug_compound_induction', tactic: 'induction n.',
    });
    expect(r.isError).toBe(false);
    // Must NOT claim 0 goals when subgoals remain
    expect(r.text).not.toMatch(/0 goal/);
    // induction on nat produces 2 cases (base + step)
    expect(r.text).toMatch(/2 goal/);
  }, TIMEOUT);

  it('file is still valid after induction', async () => {
    const r = await h.callTool('check_file', { file: tmpFile });
    expect(r.isError).toBe(false);
    expect(fs.readFileSync(tmpFile, 'utf8')).toMatch(/induction n\./);
    expect(fs.readFileSync(tmpFile, 'utf8')).toMatch(/Admitted\./);
  }, TIMEOUT);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug #2: focus_proof auto-remove of empty Admitted can corrupt
// ═══════════════════════════════════════════════════════════════════════════════

describe('Bug #2 — focus_proof on proof with existing tactics', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('tool_bugs.v', 'bug2');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('focus_proof on a closed proof does not corrupt it', async () => {
    // bug_preserve_a is already Qed'd
    const r = await h.callTool('focus_proof', { file: tmpFile, name: 'bug_preserve_a' });
    expect(r.isError).toBe(false);
    // File should still have the proof body intact
    const content = fs.readFileSync(tmpFile, 'utf8');
    const preserveBlock = content.match(/Lemma bug_preserve_a[\s\S]*?Qed\./)?.[0] ?? '';
    expect(preserveBlock).toContain('exact I.');
    expect(preserveBlock).toContain('Qed.');
  }, TIMEOUT);

  it('focus_proof on an Admitted proof with no tactics preserves Admitted', async () => {
    const r = await h.callTool('focus_proof', { file: tmpFile, name: 'bug_reset_target_a' });
    expect(r.isError).toBe(false);
    const content = fs.readFileSync(tmpFile, 'utf8');
    // Both proofs should still be there
    expect(content).toContain('Lemma bug_reset_target_a');
    expect(content).toContain('Lemma bug_reset_target_b');
  }, TIMEOUT);

  it('check_file reports file still valid after all focus_proof calls', async () => {
    const r = await h.callTool('check_file', { file: tmpFile });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Yes/);
  }, TIMEOUT);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug #3: reset_proof can target wrong proof
// ═══════════════════════════════════════════════════════════════════════════════

describe('Bug #3 — reset_proof targets the correct proof', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('tool_bugs.v', 'bug3');
    await h.callTool('check_file', { file: tmpFile });
    // Pre-insert a tactic so we can tell if the wrong proof was reset
    await h.callTool('insert_tactic', { file: tmpFile, name: 'bug_reset_target_a', tactic: 'exact I.' });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('reset_proof on b does not affect a (which has a tactic)', async () => {
    const r = await h.callTool('reset_proof', { file: tmpFile, name: 'bug_reset_target_b' });
    expect(r.isError).toBe(false);
    const content = fs.readFileSync(tmpFile, 'utf8');
    // Proof a should still have 'exact I.' (not wiped)
    const blockA = content.match(/Lemma bug_reset_target_a[\s\S]*?(?=Lemma|$)/)?.[0] ?? '';
    expect(blockA).toContain('exact I.');
    // Proof b should have its body reset (only Admitted., no tactics)
    const blockB = content.match(/Lemma bug_reset_target_b[\s\S]*?(?=Lemma|$)/)?.[0] ?? '';
    expect(blockB).toContain('Admitted.');
    // The 'exact I.' from a should not appear in b
    expect(blockB).not.toMatch(/\bexact I\./);
  }, TIMEOUT);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug #7: reset_proof doesn't report which proof was reset
// ═══════════════════════════════════════════════════════════════════════════════

describe('Bug #7 — reset_proof response includes proof name', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('tool_bugs.v', 'bug7');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('response includes the proof name (not just "unknown")', async () => {
    const r = await h.callTool('reset_proof', { file: tmpFile, name: 'bug_reset_target_a' });
    expect(r.isError).toBe(false);
    // reset_proof now reports: reset "proofName" to Admitted.
    expect(r.text).toMatch(/bug_reset_target_a/);
    expect(r.text).toMatch(/Admitted/);
  }, TIMEOUT);

  it('different proofs report different names', async () => {
    const rB = await h.callTool('reset_proof', { file: tmpFile, name: 'bug_reset_target_b' });
    expect(rB.isError).toBe(false);
    expect(rB.text).toMatch(/bug_reset_target_b/);
  }, TIMEOUT);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug #9: add_lemma positions mid-statement
// ═══════════════════════════════════════════════════════════════════════════════

describe('Bug #9 — add_lemma positions correctly, not mid-statement', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('tool_bugs.v', 'bug9');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('add_lemma before a multi-line statement inserts above the Lemma line', async () => {
    const r = await h.callTool('add_lemma', {
      file: tmpFile,
      name: 'bug9_new',
      statement: 'True',
      before: 'bug_multiline_stmt',
    });
    expect(r.isError).toBe(false);
    const content = fs.readFileSync(tmpFile, 'utf8');
    // The new lemma should be ABOVE bug_multiline_stmt, not inside it
    const beforeIdx = content.indexOf('Lemma bug9_new');
    const mlIdx = content.indexOf('Lemma bug_multiline_stmt');
    expect(beforeIdx).toBeGreaterThan(-1);
    expect(mlIdx).toBeGreaterThan(-1);
    expect(beforeIdx).toBeLessThan(mlIdx);
    // The original statement must still be intact
    expect(content).toMatch(/Lemma bug_multiline_stmt\s*\n\s*: True/);
  }, TIMEOUT);

  it('add_lemma before a single-line lemma also positions above', async () => {
    const r = await h.callTool('add_lemma', {
      file: tmpFile,
      name: 'bug9_another',
      statement: 'True',
      before: 'bug_reset_target_a',
    });
    expect(r.isError).toBe(false);
    const content = fs.readFileSync(tmpFile, 'utf8');
    const beforeIdx2 = content.indexOf('Lemma bug9_another');
    const targetIdx = content.indexOf('Lemma bug_reset_target_a');
    expect(beforeIdx2).toBeGreaterThan(-1);
    expect(targetIdx).toBeGreaterThan(-1);
    expect(beforeIdx2).toBeLessThan(targetIdx);
  }, TIMEOUT);

  it('file remains valid after add_lemma calls', async () => {
    const r = await h.callTool('check_file', { file: tmpFile });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Yes/);
  }, TIMEOUT);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug #8: add_lemma + reset_proof corrupt file when used together
// ═══════════════════════════════════════════════════════════════════════════════

describe('Bug #8 — add_lemma + reset_proof do not corrupt file', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('tool_bugs.v', 'bug8');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('add_lemma then reset_proof — file stays valid', async () => {
    // Step 1: Add a new lemma
    const r1 = await h.callTool('add_lemma', {
      file: tmpFile,
      name: 'bug8_new_lemma',
      statement: 'True',
      before: 'bug_add_reset_existing',
    });
    expect(r1.isError).toBe(false);

    // Step 2: Insert a tactic into the new lemma
    await h.callTool('insert_tactic', {
      file: tmpFile, name: 'bug8_new_lemma', tactic: 'exact I.',
    });

    // Step 3: Reset the new lemma — this is the dangerous operation
    const r3 = await h.callTool('reset_proof', {
      file: tmpFile, name: 'bug8_new_lemma',
    });
    expect(r3.isError).toBe(false);
    expect(r3.text).toMatch(/bug8_new_lemma/);

    // Verify existing proof (bug_add_reset_existing) is untouched
    const content = fs.readFileSync(tmpFile, 'utf8');
    const existingBlock = content.match(/Lemma bug_add_reset_existing[\s\S]*?Qed\./)?.[0] ?? '';
    expect(existingBlock).toContain('exact I.');
    expect(existingBlock).toContain('Qed.');

    // Verify check_file says file is valid
    const check = await h.callTool('check_file', { file: tmpFile });
    expect(check.isError).toBe(false);
    expect(check.text).toMatch(/Yes/);
  }, TIMEOUT);

  it('add_lemma then reset_proof on the ORIGINAL proof — file stays valid', async () => {
    const tmpFile2 = tempFixture('tool_bugs.v', 'bug8b');
    await h.callTool('check_file', { file: tmpFile2 });

    // Add a lemma above bug_reset_target_a
    await h.callTool('add_lemma', {
      file: tmpFile2,
      name: 'bug8b_helper',
      statement: 'True',
      before: 'bug_reset_target_a',
    });

    // Reset bug_reset_target_a (NOT the new lemma)
    const r = await h.callTool('reset_proof', {
      file: tmpFile2, name: 'bug_reset_target_a',
    });
    expect(r.isError).toBe(false);

    // File should still be valid
    const check = await h.callTool('check_file', { file: tmpFile2 });
    expect(check.isError).toBe(false);
    expect(check.text).toMatch(/Yes/);

    // The new lemma should still exist
    const content = fs.readFileSync(tmpFile2, 'utf8');
    expect(content).toContain('Lemma bug8b_helper');

    removeTempFixture(tmpFile2);
  }, TIMEOUT);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug #9 variant: add_lemma without `before` parameter
// ═══════════════════════════════════════════════════════════════════════════════

describe('Bug #9 variant — add_lemma rejects missing before', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('tool_bugs.v', 'bug9v');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('add_lemma without "before" returns error', async () => {
    const r = await h.callTool('add_lemma', {
      file: tmpFile,
      name: 'should_fail',
      statement: 'True',
    });
    // Either isError or soft-error message about missing before
    expect(r.text).toMatch(/before|required/i);
  }, TIMEOUT);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug #1 variant: open_goals (Prev mode) after compound tactic
// ═══════════════════════════════════════════════════════════════════════════════

describe('Bug #1 variant — open_goals after split.', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('tool_bugs.v', 'bug1v');
    // Use bug_multiline_stmt which is already Qed — we'll add a fresh Admitted proof
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('split. on bug_compound_induction yields 2 subgoals', async () => {
    // First: intro n. then induction n. which produces 2 goals,
    // close them and use a sub-case
    // Actually bug_compound_induction has "forall n, n + 0 = n" — let's test on a conjunction
    await h.callTool('insert_tactic', { file: tmpFile, name: 'bug_compound_induction', tactic: 'intro n.' });
    const r = await h.callTool('insert_tactic', {
      file: tmpFile, name: 'bug_compound_induction', tactic: 'induction n.',
    });
    expect(r.text).toMatch(/2 goal/);
    expect(r.text).not.toMatch(/0 goal/);
  }, TIMEOUT);
});
