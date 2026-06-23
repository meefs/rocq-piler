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

function writeTempV(suffix: string, content: string): string {
  const p = path.join(FIXTURES_DIR, `_tmp_autoadmit_${suffix}_${process.pid}.v`);
  fs.writeFileSync(p, content);
  return p;
}

describe('check_file auto_admit', () => {
  it('converts FAILED proof with standalone Qed to hash-addressable admit', async () => {
    const f = writeTempV('standalone', [
      'Lemma a : True.',
      'Proof.',
      '  exact bogus.',
      'Qed.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/auto-admit:[a-f0-9]{8}/);
      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toMatch(/\{ \(\* a:[a-f0-9]{8} \*\) admit\. \}/);
      expect(content).toMatch(/Admitted\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('converts FAILED proof with inline Qed', async () => {
    const f = writeTempV('inline', [
      'Lemma b : nat.',
      'Proof. exact bogus. Qed.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/auto-admit:[a-f0-9]{8}/);
      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toMatch(/\{ \(\* b:[a-f0-9]{8} \*\) admit\. \}/);
      expect(content).toMatch(/Admitted\./);
      expect(content).not.toMatch(/Qed\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('does NOT convert Qed proofs that compile', async () => {
    const f = writeTempV('clean', [
      'Lemma c : True.',
      'Proof. exact I. Qed.',
      '',
      'Lemma d : nat.',
      'Proof. exact 42. Qed.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/\[Qed\]/);
      expect(r.text).not.toMatch(/auto-admit/);
      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toMatch(/Qed\./);
      expect(content).not.toMatch(/admit\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('can be disabled with auto_admit: false', async () => {
    const f = writeTempV('disabled', [
      'Lemma e : True.',
      'Proof. exact bogus. Qed.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('check_file', {
        file: f,
        auto_admit: false,
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/\[FAILED\]/);
      expect(r.text).not.toMatch(/auto-admit/);
      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toMatch(/Qed\./);
      expect(content).not.toMatch(/admit\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('converts multiple FAILED proofs in one call', async () => {
    const f = writeTempV('multi', [
      'Lemma f1 : True.',
      'Proof. exact bogus1. Qed.',
      '',
      'Lemma f2 : nat.',
      'Proof. exact bogus2. Qed.',
    ].join('\n') + '\n');
    try {
      await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      const content = fs.readFileSync(f, 'utf-8');
      const admitCount = (content.match(/admit\./g) || []).length;
      expect(admitCount).toBe(2);
      expect(content).toMatch(/f1:[a-f0-9]{8}/);
      // f2 hash may be 'unknown' if goal query times out
      expect(content).toMatch(/f2:[a-f0-9]{8}|f2:unknown/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });
});
