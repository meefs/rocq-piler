/**
 * Integration tests for stratify output correctness.
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, removeTempFixture, tempFixture } from './harness.js';

const TIMEOUT = 300_000;

let h: McpHarness;

const PORTFOLIO = [
  "exists STy; split; [apply extends_refl|split; [assumption|constructor]]",
  "exists STy; split; [apply extends_refl|split; [assumption|assumption]]",
  "edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]]",
];

function countLinesWhere(file: string, pattern: RegExp): number {
  return fs.readFileSync(file, 'utf8').split('\n').filter(l => pattern.test(l)).length;
}

beforeAll(async () => { h = await createHarness(); }, TIMEOUT);
afterAll(async () => { await h.teardown(); });

describe('stratify output fixes', () => {
  // ── Fix 1: no duplicate Proof/Admitted ──
  it('no duplicate Proof. or Admitted. after stratify', async () => {
    const tmpFile = tempFixture('pcf_ref_stratify.v', 'outfix1');
    await h.callTool('stratify', {
      file: tmpFile, name: 'preservation',
      skeleton: "intros t mu t' mu' T S Ht Hstep Hok Hlen; revert T S Ht Hok Hlen; induction Hstep; intros Ty STy Ht Hok Hlen; inversion Ht; subst; clear Ht",
      portfolio: PORTFOLIO, cases_from: 'step',
    }, TIMEOUT);
    // Count Proof/Admitted only within the preservation theorem area
    const lines = fs.readFileSync(tmpFile, 'utf8').split('\n');
    const presStart = lines.findIndex(l => l.includes('Theorem preservation'));
    const nextTheorem = lines.findIndex((l, i) => i > presStart && /\b(?:Lemma|Theorem|Inductive|Fixpoint)\b/.test(l));
    const presEnd = nextTheorem < 0 ? lines.length : nextTheorem;
    const presLines = lines.slice(presStart, presEnd);
    const proofCount = presLines.filter(l => /^\s*Proof\.\s*$/.test(l.trim())).length;
    const admittedCount = presLines.filter(l => /^\s*Admitted\.\s*$/.test(l.trim())).length;
    expect(proofCount).toBeLessThanOrEqual(1);
    expect(admittedCount).toBeLessThanOrEqual(1);
    // Each { admit. } must carry an 8-char hex hash in the label
    const admitLines = presLines.filter(l => /admit\.\s*\}\s*$/.test(l.trim()));
    for (const line of admitLines) {
      expect(line).toMatch(/:[0-9a-f]{8}/);
    }
    removeTempFixture(tmpFile);
  }, TIMEOUT);

  // ── Fix 2: focus_proof sees individual { admit. } hashes ──
  it('focus_proof finds individual { admit. } hashes for survivors', async () => {
    const tmpFile = tempFixture('pcf_ref_stratify.v', 'outfix2');
    await h.callTool('stratify', {
      file: tmpFile, name: 'preservation',
      skeleton: "intros t mu t' mu' T S Ht Hstep Hok Hlen; revert T S Ht Hok Hlen; induction Hstep; intros Ty STy Ht Hok Hlen; inversion Ht; subst; clear Ht",
      portfolio: PORTFOLIO, cases_from: 'step',
    }, TIMEOUT);
    const r = await h.callTool('focus_proof', { file: tmpFile, name: 'preservation' }, TIMEOUT);
    const hashLines = (r.text.match(/^\s+[0-9a-f]{8}\s+L\d+/gm) || []);
    expect(hashLines.length).toBeGreaterThanOrEqual(5);
    expect(r.text).not.toMatch(/\(no goals\)/);
    removeTempFixture(tmpFile);
  }, TIMEOUT);
});
