/**
 * Integration tests for stratify admit-hash mismatch and edit_file replaceAll.
 *
 * Run: npm run test:integration
 */
import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, tempFixture, removeTempFixture } from './harness.js';

const TIMEOUT = 90_000;
const FIXTURE_FILE = tempFixture('stratify_edit_bugs.v', 'stratifyfix');

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
  await h.callTool('check_file', { file: FIXTURE_FILE });
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
  removeTempFixture(FIXTURE_FILE);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug: edit_file find/replace only replaces first occurrence (replaceAll broken)
// ═══════════════════════════════════════════════════════════════════════════════

describe('edit_file replaceAll', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('stratify_edit_bugs.v', 'replall');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('replaceAll:true replaces ALL occurrences of find string', async () => {
    // marker_a, marker_b, marker_c all contain 'exact I.' — replaceAll should hit all 3
    const r = await h.callTool('edit_file', {
      file: tmpFile,
      find: 'exact I.',
      replace: 'constructor.',
      replaceAll: true,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/3 occurrences/);

    const content = fs.readFileSync(tmpFile, 'utf8');
    // All three should now have 'constructor.' instead of 'exact I.'
    const exactCount = (content.match(/exact I\./g) || []).length;
    expect(exactCount).toBe(0);
    const constrCount = (content.match(/constructor\./g) || []).length;
    expect(constrCount).toBe(3);
  }, TIMEOUT);

  it('replaceAll:false (default) replaces only first occurrence', async () => {
    const tmpFile2 = tempFixture('stratify_edit_bugs.v', 'replone');
    await h.callTool('check_file', { file: tmpFile2 });

    const r = await h.callTool('edit_file', {
      file: tmpFile2,
      find: 'exact I.',
      replace: 'constructor.',
      replaceAll: false,
    });
    expect(r.isError).toBe(false);
    // Should NOT mention "occurrences" (plural), just a single replacement
    expect(r.text).not.toMatch(/occurrences/);

    const content = fs.readFileSync(tmpFile2, 'utf8');
    // First should be replaced, others not
    const exactCount = (content.match(/exact I\./g) || []).length;
    expect(exactCount).toBe(2);
    const constrCount = (content.match(/constructor\./g) || []).length;
    expect(constrCount).toBe(1);

    removeTempFixture(tmpFile2);
  }, TIMEOUT);

  it('replaceAll on non-existent string returns found:false', async () => {
    const r = await h.callTool('edit_file', {
      file: tmpFile,
      find: 'nonexistent_string_xyz',
      replace: 'whatever',
      replaceAll: true,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/not found/);
  }, TIMEOUT);

  it('file remains valid after replaceAll', async () => {
    const r = await h.callTool('check_file', { file: tmpFile });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Yes/);
  }, TIMEOUT);
});

// ═══════════════════════════════════════════════════════════════════════════════
// Bug: stratify creates admits; insert_tactics with admit_hash should find them
// ═══════════════════════════════════════════════════════════════════════════════

describe('stratify → insert_tactics admit_hash round-trip', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('stratify_edit_bugs.v', 'stratifysync');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('stratify on color_eq_dec produces unique admit hashes', async () => {
    // First focus to set up the proof
    await h.callTool('focus_proof', { file: tmpFile, name: 'color_eq_dec' });

    // stratify with induction on c1
    const r = await h.callTool('stratify', {
      file: tmpFile,
      name: 'color_eq_dec',
      skeleton: 'intros c1 c2; destruct c1',
      portfolio: ['fail_tactic_xyz'],
      cases_from: 'color',
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/survivor/);

    // Verify file has admits
    const content = fs.readFileSync(tmpFile, 'utf8');
    expect(content).toContain('admit.');

    // Extract admit hashes from stratify output
    const hashesFromReport = [...r.text.matchAll(/survivor: \w+:([0-9a-f]{8})/g)].map(m => m[1]);
    expect(hashesFromReport.length).toBeGreaterThan(1);

    // Verify focus_proof sees proper unique non-empty hashes (not all d41d8cd9)
    const f = await h.callTool('focus_proof', { file: tmpFile, name: 'color_eq_dec' });
    expect(f.isError).toBe(false);

    // Parse the "admits" section, extract hashes
    const admitSection = f.text.match(/-- admits[\s\S]*?^next:/m)?.[0] ?? '';
    const admitHashes = [...admitSection.matchAll(/^\s+([0-9a-f]{8})\s+L\d+:/gm)].map(m => m[1]);
    expect(admitHashes.length).toBeGreaterThan(1);

    // The outer admit (theorem-level) can be ignored. Focus on bullet admits:
    // All bullet admits should share the same hash...
    // Wait, in the old broken version, ALL admits were d41d8cd9.
    // In the fixed version, each admit should have its own unique hash.
    const uniqueBulletHashes = [...new Set(admitHashes)];
    expect(uniqueBulletHashes.length).toBeGreaterThan(1);
    expect(admitHashes).not.toContain('d41d8cd9');

    // Insert a tactic targeting one of the reported hashes
    const targetHash = hashesFromReport[0];
    const ins = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'color_eq_dec',
      tactic: 'destruct c2; auto.',
      admit_hash: targetHash,
    });
    expect(ins.isError).toBe(false);
    // Should have actually modified the file (not "no admit found")
    expect(ins.text).not.toMatch(/No admit found/);

    // The file should still be valid
    const check = await h.callTool('check_file', { file: tmpFile });
    expect(check.isError).toBe(false);
  }, TIMEOUT);
});
