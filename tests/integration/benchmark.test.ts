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
  console.log('[bench] warming examples workspace...');
  const t0 = Date.now();
  const warm = await h.callTool('check_file',
    { file: PCF_REF, timeout_ms: 90000 }, TIMEOUT);
  timings['pcf_ref.v COLD'] = Date.now() - t0;
  if (warm.isError) console.log('[bench] warmup error:', warm.text);

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

  it('SnakeletWp.v warm', async () => {
    const t0 = Date.now();
    const r = await h.callTool('check_file',
      { file: SWP, timeout_ms: 30000 }, TIMEOUT);
    timings['SnakeletWp.v (55L) warm'] = Date.now() - t0;
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/wp_binop/);
    expect(r.text).toMatch(/Admitted/);
  }, TIMEOUT);
});
