/**
 * Workspace-level integration tests.
 *
 * Verifies automatic workspace switching across separate _CoqProject
 * directories using real LSP calls. Primary verification via check_file;
 * inspect_term is used only after a warmup check_file to avoid races.
 *
 * Run: npm run test:integration
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, fixture } from './harness.js';

const TIMEOUT = 90_000;

const WS_A_LIB = fixture('ws_a/lib_a.v');
const WS_B_LIB = fixture('ws_b/lib_b.v');
const WS_BROKEN = fixture('ws_broken/broken.v');

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
  await h.callTool('check_file', { file: fixture('basic.v') });
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('workspace auto-switching', () => {
  it('check_file on workspace A finds greet_a', async () => {
    const r = await h.callTool('check_file', { file: WS_A_LIB });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/greet_a/);
    expect(r.text).toMatch(/Qed/);
  });

  it('fluidly switches to workspace B via check_file', async () => {
    const c = await h.callTool('check_file', { file: WS_B_LIB });
    expect(c.isError).toBe(false);
    // Workspace B's file has greet_b, not greet_a
    expect(c.text).toMatch(/greet_b/);
    expect(c.text).not.toMatch(/greet_a/);
    expect(c.text).toMatch(/Qed/);
  });

  it('switches back to workspace A, greet_a present again', async () => {
    const c = await h.callTool('check_file', { file: WS_A_LIB });
    expect(c.isError).toBe(false);
    expect(c.text).toMatch(/greet_a/);
    expect(c.text).toMatch(/Qed/);
  });

  it('unterminated proof reports open status, not Qed', async () => {
    const r = await h.callTool('check_file', { file: WS_BROKEN });
    expect(r.isError).toBe(false);
    // Unterminated proof should NOT show Qed
    expect(r.text).not.toMatch(/\[Qed\]/);
    expect(r.text).toMatch(/bad/);
  });

  it('after broken workspace, healthy workspace A still accessible', async () => {
    const c = await h.callTool('check_file', { file: WS_A_LIB });
    expect(c.isError).toBe(false);
    expect(c.text).toMatch(/greet_a/);
    expect(c.text).toMatch(/Qed/);
  });
});
