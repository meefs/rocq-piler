/**
 * Regression test: insert_tactics dry_run sends wrong position to petanque.
 *
 * The dry_run code path computes insPos via insertPosition(), which advances
 * past "Proof." and lands on the "Admitted." line.  It then sends that
 * position to petanque/get_state_at_pos.  coq-lsp returns the state AFTER
 * "Admitted." is processed (proof closed), so petanque/run rejects the
 * tactic with "Syntax error: illegal begin of vernac".
 *
 * The non-dry_run path and focus_proof path both work because they either:
 *   - modify the file first (non-dry_run), or
 *   - use admitSnapPosition which snaps to the end of the Proof. line
 *     (focus_proof / queryAdmitHashes).
 *
 * Fix: the dry_run cursor-based path should fall back to admitSnapPosition
 * when the initial insPos state fails, OR it should detect that insPos is on
 * a proof-ending line and adjust before querying.
 *
 * The fixture also includes Unicode (multibyte UTF-8) definitions to verify
 * there is no additional encoding-related regression.
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, fixture, tempFixture, removeTempFixture } from './harness.js';

const TIMEOUT = 90_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('insert_tactics dry_run position bug', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('unicode_offset.v', 'unicode');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('check_file sees all proofs as Admitted', async () => {
    const r = await h.callTool('check_file', { file: tmpFile });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/ascii_control.*Admitted/);
    expect(r.text).toMatch(/unicode_preceding.*Admitted/);
    expect(r.text).toMatch(/ascii_oneline.*Admitted/);
  });

  // ── Bug: dry_run fails on Proof.\nAdmitted. (ASCII) ─────────────────────
  it('dry_run on Proof./Admitted. (ASCII-only preceding)', async () => {
    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'ascii_control',
      tactic: 'reflexivity.',
      dry_run: true,
    });
    expect(r.isError).toBe(false);
    expect(r.text).not.toMatch(/illegal begin of vernac/);
    expect(r.text).toMatch(/goal|proof finished/i);
  });

  // ── Bug: dry_run fails on Proof.\nAdmitted. (Unicode preceding) ─────────
  it('dry_run on Proof./Admitted. (Unicode preceding)', async () => {
    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'unicode_preceding',
      tactic: 'reflexivity.',
      dry_run: true,
    });
    expect(r.isError).toBe(false);
    expect(r.text).not.toMatch(/illegal begin of vernac/);
    expect(r.text).toMatch(/goal|proof finished/i);
  });

  // ── Control: focus_proof works (uses admitSnapPosition) ──────────────────
  it('focus_proof works (uses admitSnapPosition correctly)', async () => {
    const r = await h.callTool('focus_proof', { file: tmpFile, name: 'unicode_preceding' });
    expect(r.isError).toBe(false);
    expect(r.text).not.toMatch(/could not query/);
  });

  // ── Control: non-dry_run works (modifies file first) ─────────────────────
  it('non-dry_run insert_tactics works (modifies file)', async () => {
    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'unicode_preceding',
      tactic: 'reflexivity.',
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Qed|done|proof finished/i);
  });

  // ── Control: one-liner works ─────────────────────────────────────────────
  it('Proof. Admitted. one-liner works', async () => {
    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'ascii_oneline',
      tactic: 'exact I.',
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Qed|done|proof finished/i);
  });
});
