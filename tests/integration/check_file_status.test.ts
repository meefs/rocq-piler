/**
 * Regression test: check_file must not show [Qed] for proofs
 * that Coq rejected with errors.
 *
 * Bug: status labels were determined by text scanning (looking for "Qed.")
 * rather than Coq verification. A proof like `Lemma bad : False. Proof.
 * exact I. Qed.` would show [Qed] even though Coq rejects it.
 *
 * Fix: collect LSP diagnostics (errors) and mark items containing
 * errors as [FAILED] instead of [Qed].
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, fixture } from './harness.js';

const TIMEOUT = 90_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('check_file status on failed proofs', () => {
  it('marks broken proofs as FAILED, not Qed', async () => {
    const r = await h.callTool('check_file', {
      file: fixture('check_file_failed.v'),
    });
    expect(r.isError).toBe(false);

    expect(r.text).toMatch(/good_before.*\[Qed\]/);
    expect(r.text).toMatch(/also_good.*\[Qed\]/);

    expect(r.text).toMatch(/broken_proof.*\[FAILED\]/);
    expect(r.text).not.toMatch(/broken_proof.*\[Qed\]/);
  });

  it('does not mark valid proofs after a broken one as FAILED', async () => {
    const r = await h.callTool('check_file', {
      file: fixture('check_file_failed.v'),
    });
    expect(r.text).toMatch(/unreachable_qed.*\[Qed\]/);
    expect(r.text).toMatch(/also_unreachable.*\[Qed\]/);
  });
});
