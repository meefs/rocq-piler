/**
 * Quick integration test: run stratify on preservation.
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, removeTempFixture, tempFixture } from './harness.js';

const TIMEOUT = 300_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('stratify on preservation', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('pcf_ref_stratify.v', 'stratrun');
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('closes 16 of 21 cases, leaves 5 survivors', async () => {
    const r = await h.callTool('stratify', {
      file: tmpFile,
      name: 'preservation',
      skeleton: `intros t mu t' mu' T S Ht Hstep Hok Hlen; revert T S Ht Hok Hlen; induction Hstep; intros Ty STy Ht Hok Hlen; inversion Ht; subst; clear Ht`,
      portfolio: [
        'exists STy; split; [apply extends_refl|split; [assumption|constructor]]',
        'exists STy; split; [apply extends_refl|split; [assumption|assumption]]',
        "edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]]",
      ],
      cases_from: 'step',
      attempt_timeout_ms: 15_000,
    }, TIMEOUT);
    console.log('stratify result:', JSON.stringify({ isError: r.isError, text: r.text.slice(0, 500) }));
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/solved 16\/21/);
    // Survivors: the 5 hard cases
    expect(r.text).not.toMatch(/S_IfTrue/);
    expect(r.text).not.toMatch(/S_IfFalse/);
    expect(r.text).toMatch(/S_AppAbs/);
    expect(r.text).toMatch(/S_Fix/);
    expect(r.text).toMatch(/S_RefV/);
    expect(r.text).toMatch(/S_DerefLoc/);
    expect(r.text).toMatch(/S_AssignV/);
  }, TIMEOUT);
});
