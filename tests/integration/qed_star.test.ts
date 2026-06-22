import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, fixture } from './harness.js';
const TIMEOUT = 90_000;
let h: McpHarness;
beforeAll(async () => { h = await createHarness(); }, TIMEOUT);
afterAll(async () => { await h.teardown(); });

describe('check_file Qed* dependency tracking', () => {
  it('marks Qed depending on Admitted as Qed*', async () => {
    const r = await h.callTool('check_file', { file: fixture('qed_star.v') }, TIMEOUT);
    console.log('OUTPUT:', r.text);
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/bar.*\[Qed\*\].*foo/);
    expect(r.text).toMatch(/baz.*\[Qed\]/);
    expect(r.text).not.toMatch(/baz.*\[Qed\*\]/);
  });
});
