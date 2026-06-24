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
  const p = path.join(FIXTURES_DIR, `_tmp_qedreg_${suffix}_${process.pid}.v`);
  fs.writeFileSync(p, content);
  return p;
}

describe('edit_file Qed regression warning', () => {
  it('warns when an edit removes a Qed proof', async () => {
    const f = writeTemp('drop', [
      'Lemma a : True.',
      'Proof. exact I. Qed.',
      'Lemma b : nat.',
      'Proof. exact 42. Qed.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        find: 'Lemma b : nat.\nProof. exact 42. Qed.',
        replace: '',
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/Qed count dropped from 2 to 1/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('does NOT warn when Qed count stays the same', async () => {
    const f = writeTemp('same', [
      'Lemma a : True.',
      'Proof. exact I. Qed.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        find: 'exact I.',
        replace: 'exact I.',
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).not.toMatch(/Qed count dropped/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('does NOT warn when Qed count increases', async () => {
    const f = writeTemp('incr', [
      'Lemma a : True.',
      'Proof. exact I. Qed.',
      '',
      'Lemma b : nat.',
      'Proof.',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        find: 'Proof.\nAdmitted.',
        replace: 'Proof. exact 42. Qed.',
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).not.toMatch(/Qed count dropped/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('warns when all Qed proofs are removed', async () => {
    const f = writeTemp('zero', [
      'Lemma a : True.',
      'Proof. exact I. Qed.',
      'Lemma b : nat.',
      'Proof. exact 42. Qed.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        find: 'Lemma a : True.\nProof. exact I. Qed.\nLemma b : nat.\nProof. exact 42. Qed.',
        replace: '',
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/Qed count dropped from 2 to 0/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });
});
