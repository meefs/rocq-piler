/**
 * Two-level stratify: total solution of sstep_det in 3 tool calls.
 *
 * The fixture is the classic "eliminate twice" pattern: determinism of a
 * small-step relation needs induction on the first derivation, then
 * inversion on the second derivation INSIDE each case.
 *
 *   call 1: outer stratify (induction skeleton)  → solves SPlusV/SIfT/SIfF,
 *           SPlusL + SPlusR survive (their inner sub-cases mix
 *           congruence-via-IH with impossibility)
 *   call 2: nested stratify on SPlusL (admit_hash) → solves 3/3
 *   call 3: nested stratify on SPlusR (admit_hash) → solves 3/3 → auto-Qed
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, removeTempFixture, tempFixture } from './harness.js';

const TIMEOUT = 300_000;

let h: McpHarness;

beforeAll(async () => { h = await createHarness(); }, TIMEOUT);
afterAll(async () => { await h.teardown(); });

describe('nested stratify on sstep_det', () => {
  let tmpFile: string;

  beforeAll(() => { tmpFile = tempFixture('sstep_det.v', 'nested'); }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('solves the whole theorem in 3 stratify calls (outer + 2 nested)', async () => {
    // ── call 1: outer stratify — induction on the first derivation ──
    const r1 = await h.callTool('stratify', {
      file: tmpFile,
      name: 'sstep_det',
      skeleton: 'intros e e1 Hs1; induction Hs1; intros f Hs2',
      portfolio: [
        'inversion Hs2; subst; first [ reflexivity | exfalso; eapply num_nostep; eassumption ]',
      ],
      cases_from: 'sstep',
    }, TIMEOUT);
    expect(r1.isError).toBe(false);
    expect(r1.text).toMatch(/solved 3\/5/);

    // Survivor hashes are reported inline — no focus_proof round-trip needed
    const survivors = [...r1.text.matchAll(/survivor: (\w+):([0-9a-f]{8})/g)]
      .map(m => ({ name: m[1], hash: m[2] }));
    expect(survivors.map(s => s.name)).toEqual(['SPlusL', 'SPlusR']);

    // ── calls 2+3: nested stratify inside each survivor — inversion on
    //    the second derivation, congruence-via-IH vs impossibility ──
    for (const s of survivors) {
      const r = await h.callTool('stratify', {
        file: tmpFile,
        name: 'sstep_det',
        admit_hash: s.hash,
        skeleton: 'inversion Hs2; subst',
        portfolio: [
          'f_equal; auto',
          'exfalso; eapply num_nostep; eassumption',
        ],
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/nested in/);
      expect(r.text).toMatch(/solved 3\/3/);
    }

    // ── total solution: no admits, auto-Qed applied ──
    const content = fs.readFileSync(tmpFile, 'utf8');
    const proofPart = content.slice(content.indexOf('Theorem sstep_det'));
    expect(proofPart).not.toMatch(/\badmit\b/);
    expect(proofPart).not.toMatch(/Admitted/);
    expect(proofPart).toMatch(/Qed\./);

    // ── the proof actually checks ──
    const rc = await h.callTool('check_file', { file: tmpFile }, TIMEOUT);
    expect(rc.isError).toBe(false);
    expect(rc.text).not.toMatch(/ERROR|error/);
  }, TIMEOUT);
});
