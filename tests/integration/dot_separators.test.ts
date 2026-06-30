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
  const p = path.join(FIXTURES_DIR, `_tmp_dot_${suffix}_${process.pid}.v`);
  fs.writeFileSync(p, content);
  return p;
}

// Regression test: the model writes tactics with . between commands
// (e.g. "exists S'. split. auto. split. auto."). These . break the
// solve[] wrapper parser, producing "Syntax error: '|' or ']' expected".
// Fix: . is converted to ; before wrapping in solve[].
describe('close_admits accepts .-separated tactics', () => {
  it('handles destructure with dots', async () => {
    const f = writeTemp('destruct_dots', [
      'Inductive color := Red | Green | Blue.',
      'Lemma t : forall c:color, True.',
      'Proof.',
      '  intros c.',
      '  { (* t:aaaaaaaa *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('close_admits', {
        file: f,
        name: 't',
        portfolio: [{ hashes: '*', tactic: 'destruct c. exact I. exact I. exact I.' }],
      }, TIMEOUT);
      expect(r.text).toMatch(/closed 1/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('handles exists + dots', async () => {
    const f = writeTemp('exists_dots', [
      'Lemma t : True /\\ True.',
      'Proof.',
      '  { (* t:bbbbbbbb *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('close_admits', {
        file: f,
        name: 't',
        portfolio: [{ hashes: '*', tactic: 'split. exact I. exact I.' }],
      }, TIMEOUT);
      expect(r.text).toMatch(/closed 1/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('handles multi-step with dots and eauto', async () => {
    const f = writeTemp('multi_dots', [
      'Lemma t : True /\\ True /\\ True.',
      'Proof.',
      '  { (* t:cccccccc *) admit. }',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('close_admits', {
        file: f,
        name: 't',
        portfolio: [{ hashes: '*', tactic: 'split. exact I. split. exact I. exact I.' }],
      }, TIMEOUT);
      expect(r.text).toMatch(/closed 1/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });
});
