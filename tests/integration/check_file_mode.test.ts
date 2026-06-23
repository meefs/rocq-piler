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

describe('check_file mode flag', () => {
  it('mode:"full" shows all items including open definitions (default)', async () => {
    const r = await h.callTool('check_file', {
      file: fixture('multi_error.v'),
    }, TIMEOUT);
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/\[open\]/);
    expect(r.text).toMatch(/\[Qed\]/);
    expect(r.text).toMatch(/\[FAILED\]/);
    expect(r.text).toMatch(/\[Admitted\]/);
  });

  it('mode:"errors" skips open and Qed, shows only failures/admitted', async () => {
    const r = await h.callTool('check_file', {
      file: fixture('multi_error.v'),
      mode: 'errors',
    }, TIMEOUT);
    expect(r.isError).toBe(false);
    expect(r.text).not.toMatch(/\[open\]/);
    expect(r.text).not.toMatch(/\[Qed\]$/m);
    expect(r.text).toMatch(/\[FAILED\]/);
    expect(r.text).toMatch(/\[Admitted\]/);
    expect(r.text).toMatch(/\d+ Qed/);
  });

  it('mode:"first" shows only the first FAILED item', async () => {
    const r = await h.callTool('check_file', {
      file: fixture('multi_error.v'),
      mode: 'first',
    }, TIMEOUT);
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/\[FAILED\]/);
    const failedMatches = r.text.match(/\[FAILED\]/g);
    expect(failedMatches?.length).toBe(1);
    expect(r.text).toMatch(/\d+ FAILED/);
  });

  it('mode:"errors" output is shorter than mode:"full"', async () => {
    const full = await h.callTool('check_file', {
      file: fixture('multi_error.v'),
    }, TIMEOUT);
    const errors = await h.callTool('check_file', {
      file: fixture('multi_error.v'),
      mode: 'errors',
    }, TIMEOUT);
    expect(errors.text.length).toBeLessThan(full.text.length);
  });
});
