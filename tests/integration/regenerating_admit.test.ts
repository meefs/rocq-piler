import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness } from './harness.js';
import * as fs from 'fs';
import * as path from 'path';

const TIMEOUT = 90_000;
const FIXTURES_DIR = path.resolve(import.meta.dirname, 'fixtures');

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

function writeTemp(suffix: string, content: string): string {
  const p = path.join(FIXTURES_DIR, `_tmp_rga_${suffix}_${process.pid}.v`);
  fs.writeFileSync(p, content);
  return p;
}

// close_admits now uses solve[] to verify tactics fully close.
// Partial tactics that leave subgoals are REJECTED (not sealed)
// to prevent the "regenerating admit with mangled context" bug.
describe('close_admits solve[] guard', () => {
  it('rejects partial tactics that leave subgoals open', async () => {
    const f = writeTemp('partial_reject', [
      'Lemma test : True /\\ True.',
      'Proof.',
      '  { (* test:aaaaaaaa *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'split; [exact I| ]' }],
      }, TIMEOUT);
      // Should be rejected — not closed
      expect(r.text).toMatch(/did not fully close|not closed/);
      // File should be unchanged — no partial commit
      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toMatch(/admit\./);
      expect(content).not.toMatch(/split/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('accepts complete tactics that fully close all subgoals', async () => {
    const f = writeTemp('complete_accept', [
      'Lemma test : True /\\ True.',
      'Proof.',
      '  { (* test:bbbbbbbb *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'split; [exact I|exact I]' }],
      }, TIMEOUT);
      expect(r.text).toMatch(/closed 1/);
      // File should have Qed
      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toMatch(/Qed\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('rejects wrong tactics with Coq errors', async () => {
    const f = writeTemp('wrong_reject', [
      'Lemma test : True.',
      'Proof.',
      '  { (* test:cccccccc *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'exact bogus' }],
      }, TIMEOUT);
      expect(r.text).toMatch(/did not fully close|not closed/);
      // File unchanged
      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toMatch(/admit\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('does not produce regenerating admits', async () => {
    // The core test: a partial tactic must NOT leave a sealed admit
    // that can't be closed later. It should leave the original admit intact.
    const f = writeTemp('no_regen', [
      'Lemma test : True /\\ True.',
      'Proof.',
      '  { (* test:dddddddd *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      // Attempt partial tactic — should be rejected
      await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'split; [exact I| ]' }],
      }, TIMEOUT);

      // Now try the complete tactic — should succeed
      const r2 = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'split; [exact I|exact I]' }],
      }, TIMEOUT);
      expect(r2.text).toMatch(/closed 1/);

      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toMatch(/Qed\./);
      expect(content).not.toMatch(/admit\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });
});
