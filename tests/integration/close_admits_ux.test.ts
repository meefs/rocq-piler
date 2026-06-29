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
  const p = path.join(FIXTURES_DIR, `_tmp_ca2_${suffix}_${process.pid}.v`);
  fs.writeFileSync(p, content);
  return p;
}

describe('close_admits UX fixes', () => {
  it('rejects { ... } blocks with a clear error', async () => {
    const f = writeTemp('brace', [
      'Lemma test : True.',
      'Proof.',
      '  { (* test:aaaaaaaa *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'assert (I : True). { exact I. }' }],
      }, TIMEOUT);
      expect(r.text).toMatch(/contains.*\{|Use.*by/i);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('does not claim all closed when admits remain', async () => {
    const f = writeTemp('remaining', [
      'Lemma test : True /\\ True.',
      'Proof.',
      '  { (* test:cccccccc *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('close_admits', {
        file: f,
        name: 'test',
        portfolio: [{ hashes: '*', tactic: 'split; [exact I| ]' }],
      }, TIMEOUT);
      expect(r.text).not.toMatch(/all closed/);
      expect(r.text).toMatch(/admit\(s\) remaining/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });
});
