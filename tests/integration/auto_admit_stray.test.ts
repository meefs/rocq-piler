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
  const p = path.join(FIXTURES_DIR, `_tmp_stray_${suffix}_${process.pid}.v`);
  fs.writeFileSync(p, content);
  return p;
}

describe('auto_admit does not create stray admits', () => {
  it('does not duplicate Admitted. when Qed is inline above existing Admitted', async () => {
    // This simulates the stray admit bug: Qed on one line, Admitted on the next
    const f = writeTemp('inline_qed', [
      'Lemma a : True.',
      'Proof. exact I. Qed.',
      '',
      'Lemma b : True.',
      'Proof. exact bogus. Qed.',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      const content = fs.readFileSync(f, 'utf-8');
      // Should have exactly one Admitted. for lemma b, not two
      const admitCount = (content.match(/^Admitted\.$/gm) || []).length;
      expect(admitCount).toBe(1);
      // Should have exactly one admit block
      const hashAdmitCount = (content.match(/\(\* b:[a-f0-9]{8} \*\) admit\./g) || []).length;
      expect(hashAdmitCount).toBe(1);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('does not duplicate Admitted. when Qed is standalone above existing Admitted', async () => {
    const f = writeTemp('standalone', [
      'Lemma c : True.',
      'Proof.',
      '  exact bogus.',
      'Qed.',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      const content = fs.readFileSync(f, 'utf-8');
      const admitCount = (content.match(/^Admitted\.$/gm) || []).length;
      expect(admitCount).toBe(1);
      expect(content).toMatch(/\(\* c:[a-f0-9]{8} \*\) admit\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('inserts one Admitted. when there was none before', async () => {
    const f = writeTemp('none', [
      'Lemma d : True.',
      'Proof.',
      '  exact bogus.',
      'Qed.',
    ].join('\n') + '\n');
    try {
      await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      const content = fs.readFileSync(f, 'utf-8');
      const admitCount = (content.match(/^Admitted\.$/gm) || []).length;
      expect(admitCount).toBe(1);
      expect(content).toMatch(/\(\* d:[a-f0-9]{8} \*\) admit\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('handles inline Qed with no following Admitted', async () => {
    const f = writeTemp('inline_no_admit', [
      'Lemma e : True.',
      'Proof. exact bogus. Qed.',
    ].join('\n') + '\n');
    try {
      await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      const content = fs.readFileSync(f, 'utf-8');
      const admitCount = (content.match(/^Admitted\.$/gm) || []).length;
      expect(admitCount).toBe(1);
      expect(content).toMatch(/\(\* e:[a-f0-9]{8} \*\) admit\./);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });

  it('ok for other admitted lemma was already QEd', async () => {
    // Simulates the real-world case: one valid Qed, one broken Qed with Admitted already
    const f = writeTemp('real', [
      'Lemma ok : True.',
      'Proof. exact I. Qed.',
      '',
      'Lemma broken : True /\ True.',
      'Proof. split.',
      '  - exact I.',
      '  - exact I.',
      'Qed.',
      'Admitted.',
    ].join('\n') + '\n');
    try {
      await h.callTool('check_file', {
        file: f,
        auto_admit: true,
      }, TIMEOUT);
      const content = fs.readFileSync(f, 'utf-8');
      // ok should still be Qed (not converted)
      expect(content).toMatch(/Lemma ok[\s\S]*exact I\. Qed\./);
      // Only one Admitted. line total
      const admitCount = (content.match(/^Admitted\.$/gm) || []).length;
      expect(admitCount).toBe(1);
    } finally {
      try { fs.unlinkSync(f); } catch {}
    }
  });
});
