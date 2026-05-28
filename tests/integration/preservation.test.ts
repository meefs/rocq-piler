/**
 * Integration tests for list_admitted on the PCF+Ref preservation proof.
 *
 * Verifies that list_admitted correctly queries goal states at admit. lines
 * (the character-position fix works), and that insert_tactic admit_hash
 * can replace matching admits.
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, removeTempFixture, tempFixture } from './harness.js';

const TIMEOUT = 90_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('list_admitted on preservation', () => {
  const PCF_REF = '/home/gavin/dev/Scidonia/rocq-robot/examples/pcf_ref.v';

  // Warm up the file
  beforeAll(async () => {
    await h.callTool('check_file', { file: PCF_REF });
  }, TIMEOUT);

  it('finds 21 admits', async () => {
    const r = await h.callTool('list_admitted', { file: PCF_REF, name: 'preservation' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/21 admit/);
  });

  it('returns real hashes for bullet admits, not error', async () => {
    const r = await h.callTool('list_admitted', { file: PCF_REF, name: 'preservation' });
    // Each admit line should have a real 8-char hex hash, not "error"
    const hashLines = r.text.split('\n').filter(l => /^[0-9a-f]{8}\s/.test(l));
    expect(hashLines).toHaveLength(21);
    const errorLines = r.text.split('\n').filter(l => l.startsWith('error'));
    expect(errorLines).toHaveLength(0);
  });

  it('at least one admit shows a goal text', async () => {
    const r = await h.callTool('list_admitted', { file: PCF_REF, name: 'preservation' });
    // Goal text should appear after "Ln: " for at least some admits
    const goalLines = r.text.split('\n').filter(l => /:\s+\S/.test(l));
    expect(goalLines.length).toBeGreaterThan(0);
  });
});

describe('insert_tactic admit_hash on preservation', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('pcf_ref.v', 'preserv', '/home/gavin/dev/Scidonia/rocq-robot/examples');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('replaces first admit line via admit_hash', async () => {
    // List admits and get the first real hash
    const list = await h.callTool('list_admitted', { file: tmpFile, name: 'preservation' });
    const hash = list.text.match(/^([0-9a-f]{8})\s/m)?.[1];
    expect(hash).toBeTruthy();

    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'preservation',
      tactic: 'exact I.',
      admit_hash: hash,
    });
    expect(r.isError).toBe(false);
    // Should have replaced some admits
    expect(r.text).toMatch(/replaced/);
  });
});
