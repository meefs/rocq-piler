import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, tempFixture, removeTempFixture } from './harness.js';
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
  const p = path.join(FIXTURES_DIR, `_tmp_autocheck_${suffix}_${process.pid}.v`);
  fs.writeFileSync(p, content);
  return p;
}

describe('edit_file auto-check', () => {
  it('reports ✓ no errors when edit produces a valid file', async () => {
    const f = writeTempV('clean', 'Lemma foo : True.\nProof. exact I. Qed.\n');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        find: 'exact I.',
        replace: 'constructor.',
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/✓ no errors/);
      expect(r.text).not.toMatch(/✗/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('reports first error with message when edit introduces a bug', async () => {
    const f = writeTempV('broken', 'Lemma foo : True.\nProof. exact I. Qed.\n');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        find: 'exact I.',
        replace: 'exact bogus.',
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/✗/);
      expect(r.text).toMatch(/bogus/i);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('includes goal state at the error position', async () => {
    const f = writeTempV('goal', 'Lemma bar : 1 + 1 = 2.\nProof. exact bogus. Qed.\n');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        find: 'exact bogus.',
        replace: 'exact wrong.',
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/goal:/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('reports error count when multiple errors exist', async () => {
    const f = writeTempV('multi', [
      'Lemma a : True. Proof. exact bogus1. Qed.',
      'Lemma b : True. Proof. exact bogus2. Qed.',
    ].join('\n') + '\n');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        find: 'bogus1',
        replace: 'bogus3',
      }, TIMEOUT);
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/more error/);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('detects thrashing after 5 consecutive edits with same error', async () => {
    const f = writeTempV('thrash', 'Lemma foo : True.\nProof. (* v0 *) exact bogus. Qed.\n');
    try {
      for (let i = 0; i < 5; i++) {
        const r = await h.callTool('edit_file', {
          file: f,
          find: `(* v${i} *)`,
          replace: `(* v${i + 1} *)`,
        }, TIMEOUT);
        expect(r.isError).toBe(false);
        expect(r.text).toMatch(/bogus/);
        if (i < 4) {
          expect(r.text).not.toMatch(/consecutive edits/);
        } else {
          expect(r.text).toMatch(/consecutive edits/);
          expect(r.text).toMatch(/reset_proof|focus_proof/);
        }
      }
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });
});
