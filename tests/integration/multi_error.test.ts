import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, fixture } from './harness.js';

const TIMEOUT = 90_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('check_file multi-error reporting', () => {
  it('reports all errors across multiple proofs in one call', async () => {
    const r = await h.callTool('check_file', {
      file: fixture('multi_error.v'),
    }, TIMEOUT);
    expect(r.isError).toBe(false);

    expect(r.text).toMatch(/correct_proof.*\[Qed\]/);
    expect(r.text).toMatch(/good_def.*\[open\]/);
    expect(r.text).toMatch(/admitted_proof.*\[Admitted\]/);
    expect(r.text).toMatch(/another_correct.*\[Qed\]/);

    expect(r.text).toMatch(/tactic_error.*\[FAILED\]/);
    expect(r.text).toMatch(/type_mismatch.*\[FAILED\]/);
    expect(r.text).toMatch(/late_error.*\[FAILED\]/);
  });

  it('includes error messages for each failed proof', async () => {
    const r = await h.callTool('check_file', {
      file: fixture('multi_error.v'),
    }, TIMEOUT);

    expect(r.text).toMatch(/tactic_error.*FAILED[\s\S]*ERROR.*nonexistent_lemma/i);
    expect(r.text).toMatch(/type_mismatch.*FAILED[\s\S]*ERROR/);
    expect(r.text).toMatch(/late_error.*FAILED[\s\S]*ERROR/);
  });

  it('reports errors from different proofs independently', async () => {
    const r = await h.callTool('check_file', {
      file: fixture('multi_error.v'),
    }, TIMEOUT);

    const lines = r.text.split('\n');
    const failedCount = lines.filter((l: string) => l.includes('[FAILED]')).length;
    expect(failedCount).toBe(3);

    const errorCount = lines.filter((l: string) => l.includes('ERROR L')).length;
    expect(errorCount).toBeGreaterThanOrEqual(3);
  });
});
