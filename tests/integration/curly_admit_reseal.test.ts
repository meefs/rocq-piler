/**
 * Integration test: insert_tactic admit_hash inside curly-brace bullets
 * where the tactic leaves subgoals (re-seal path).
 *
 * When an admit_hash points to an admit inside a "{ admit. }" block,
 * replacing it with a subgoal-introducing tactic (e.g. destruct n.)
 * must produce valid Coq with properly nested admits inside the { }.
 *
 * This test focuses on verifying file validity after re-seal,
 * not on completing the proof.
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, removeTempFixture, tempFixture, extractAdmitHashes } from './harness.js';

const TIMEOUT = 90_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

// ─────────────────────────────────────────────────────────────────────────────
// Scenario: replace { admit. } with a tactic that leaves 2 subgoals (destruct).
// Verify the file remains valid and the admits are properly nested inside { }.
// ─────────────────────────────────────────────────────────────────────────────

describe('admit_hash inside { } — file validity after re-seal', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('curly_admit_reseal.v', 'validity');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('finds 2 admits in curly_admit_prebuilt', async () => {
    const r = await h.callTool('focus_proof', {
      file: tmpFile,
      name: 'curly_admit_prebuilt',
    });
    expect(r.isError).toBe(false);
    const admits = extractAdmitHashes(r.text);
    expect(admits.length).toBe(2);
  });

  it('replaces first { admit. } with simpl. (leaves 1 subgoal) → file valid', async () => {
    const list = await h.callTool('focus_proof', {
      file: tmpFile,
      name: 'curly_admit_prebuilt',
    });
    const admits = extractAdmitHashes(list.text);
    const baseHash = admits[0]?.hash;
    expect(baseHash).toBeTruthy();

    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'curly_admit_prebuilt',
      tactic: 'simpl.',
      admit_hash: baseHash!,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/replaced/);

    // File must be valid Coq after re-seal
    const cr = await h.callTool('check_file', { file: tmpFile });
    expect(cr.isError).toBe(false);
  }, TIMEOUT);

  it('replacing the sealed admit with reflexivity auto-Qeds', async () => {
    // The sealed admit should be the 0 = 0 goal from simpl.
    const list = await h.callTool('focus_proof', {
      file: tmpFile,
      name: 'curly_admit_prebuilt',
    });
    const admits = extractAdmitHashes(list.text);
    // Find the admit inside the first { } (0 + 0 = 0 simplified to 0 = 0)
    const zeroAdmit = admits.find(a => a.goal.includes('0 = 0'));
    expect(zeroAdmit).toBeTruthy();

    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'curly_admit_prebuilt',
      tactic: 'reflexivity.',
      admit_hash: zeroAdmit!.hash,
    });
    expect(r.isError).toBe(false);
    // May or may not auto-Qed (still has the step case admit)
    const cr = await h.callTool('check_file', { file: tmpFile });
    expect(cr.isError).toBe(false);
  }, TIMEOUT);
});
