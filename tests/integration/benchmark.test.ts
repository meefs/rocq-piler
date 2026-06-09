/**
 * Performance benchmark test.
 *
 * Measures check_file completion time on real-world-sized Coq files.
 * All callTool timeouts use the vitest TIMEOUT (120s).
 *
 * Run: npm run test:integration
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, fixture } from './harness.js';

const TIMEOUT = 150_000;

const BASIC   = fixture('basic.v');
const PCF_REF = '/home/gavin/dev/Scidonia/rocq-piler/examples/pcf_ref.v';
const SWP     = '/home/gavin/dev/Scidonia/rocq-piler/examples/SnakeletWp.v';

let h: McpHarness;
const timings: Record<string, number> = {};

beforeAll(async () => {
  h = await createHarness();

  // Pre-warm the examples workspace (cold LSP start with Stdlib)
  console.log('[bench] measuring cold start...');
  const t0 = Date.now();
  const warm = await h.callTool('check_file',
    { file: PCF_REF, timeout_ms: 120000, retry_timeout_ms: 180000 }, TIMEOUT);
  timings['pcf_ref.v COLD'] = Date.now() - t0;
  if (warm.isError) console.log('[bench] COLD error:', warm.text.slice(0, 200));
  else console.log('[bench] COLD complete:', warm.text.slice(0, 120));

  // Also warm the fixtures workspace (already done by basic.v)
}, TIMEOUT);

afterAll(async () => {
  console.log('\n=== BENCHMARK TIMINGS ===');
  for (const [name, ms] of Object.entries(timings)) {
    console.log(`  ${name}: ${ms}ms`);
  }
  await h.teardown();
});

describe('benchmark: check_file on real files', () => {
  it('basic.v (31 lines, no imports)', async () => {
    const t0 = Date.now();
    const r = await h.callTool('check_file', { file: BASIC }, TIMEOUT);
    timings['basic.v (31L) warm'] = Date.now() - t0;
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/spans/);
  }, TIMEOUT);

  it('pcf_ref.v (~330 lines, Stdlib) warm', async () => {
    const t0 = Date.now();
    const r = await h.callTool('check_file',
      { file: PCF_REF, timeout_ms: 30000 }, TIMEOUT);
    timings['pcf_ref.v (330L) warm'] = Date.now() - t0;
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/preservation.*Qed/);
  }, TIMEOUT);

  it('SnakeletWp.v warm (22 lemmas, all Qed)', async () => {
    const t0 = Date.now();
    const r = await h.callTool('check_file',
      { file: SWP, timeout_ms: 30000 }, TIMEOUT);
    timings['SnakeletWp.v (405L) warm'] = Date.now() - t0;
    expect(r.isError).toBe(false);
    // All 22 lemmas must be Qed, no admits
    expect(r.text).not.toMatch(/Admitted/);
    expect(r.text).toMatch(/wp_alloc.*Qed/);
    expect(r.text).toMatch(/wp_binop.*Qed/);
  }, TIMEOUT);
});
