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

// Bug: when close_admits applies a tactic that introduces hypotheses (edestruct),
// remaining subgoals lose access to those hypotheses after sealing.
// This prevents closing them in subsequent close_admits calls.
describe('close_admits preserves context for remaining admits', () => {
  it('remaining admit has access to edestruct-level hypotheses after sealing', async () => {
    const f = writeTemp('edestruct_context', [
      'Lemma test : True /\\ True.',
      'Proof.',
      '  { (* test:aaaaaaaa *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      // Apply a tactic that uses edestruct-like pattern: splits and leaves one branch
      const r1 = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'split; [exact I| ]' }],
      }, TIMEOUT);
      console.log('r1:', r1.text);

      // Now the remaining admit should be closeable
      const r2 = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'exact I' }],
      }, TIMEOUT);
      console.log('r2:', r2.text);

      // The proof should now be Qed
      const check = await h.callTool('check_file', {
        file: f,
        mode: 'errors',
        auto_admit: false,
      }, TIMEOUT);
      expect(check.text).toMatch(/\[Qed\]/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('remaining admit is closeable after split', async () => {
    const f = writeTemp('split_close', [
      'Lemma test : True /\\ True.',
      'Proof.',
      '  { (* test:bbbbbbbb *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r1 = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'split; [exact I| ]' }],
      }, TIMEOUT);
      console.log('--- r1 ---');
      console.log(r1.text);
      console.log('--- file after r1 ---');
      console.log(fs.readFileSync(f, 'utf-8'));

      // Second call should close the remaining branch
      const r2 = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'exact I' }],
      }, TIMEOUT);
      console.log('--- r2 ---');
      console.log(r2.text);
      console.log('--- file after r2 ---');
      console.log(fs.readFileSync(f, 'utf-8'));
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });
});
