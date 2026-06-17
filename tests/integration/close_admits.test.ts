/**
 * Integration test for close_admits tool: batch-close admits by hash.
 */
import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, removeTempFixture, tempFixture } from './harness.js';

const TIMEOUT = 120_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('close_admits', () => {
  it('resolves "*" and closes all admits', async () => {
    const tmpFile = tempFixture('close_admits.v', 'closeadm');
    try {
      const r = await h.callTool('close_admits', {
        file: tmpFile,
        name: 'close_admits_test',
        portfolio: [
          { hashes: '*', tactic: 'exact I' },
        ],
      }, TIMEOUT);
      console.log('close_admits result:', JSON.stringify({ isError: r.isError, text: r.text }));
      expect(r.isError).toBe(false);
      // 3 admits share the same True hash → 1 unique hash closed
      expect(r.text).toMatch(/closed 1/);
      expect(r.text).not.toMatch(/not closed/);
    } finally {
      removeTempFixture(tmpFile);
    }
  }, TIMEOUT);

  it('closes mixed-hash admits leaving remainder for "*"', async () => {
    const tmpFile = tempFixture('close_admits.v', 'closeadm2');
    try {
      // close_admits_mixed: 2× True (f827cf46), 1× (1=1) (different hash)
      const r = await h.callTool('close_admits', {
        file: tmpFile,
        name: 'close_admits_mixed',
        portfolio: [
          { hashes: '*', tactic: 'exact I' },
        ],
      }, TIMEOUT);
      console.log('close_admits mixed result:', JSON.stringify({ isError: r.isError, text: r.text }));
      expect(r.isError).toBe(false);
      // Closes True admits, (1=1) remains
      expect(r.text).toMatch(/closed 1/);
      expect(r.text).toMatch(/not closed 1/);
    } finally {
      removeTempFixture(tmpFile);
    }
  }, TIMEOUT);

  it('reports errors for hashes that fail to close', async () => {
    const tmpFile = tempFixture('close_admits.v', 'closeadm3');
    try {
      const r = await h.callTool('close_admits', {
        file: tmpFile,
        name: 'close_admits_test',
        portfolio: [
          { hashes: '*', tactic: 'apply conj_fail' },
        ],
      }, TIMEOUT);
      console.log('close_admits error result:', JSON.stringify({ isError: r.isError, text: r.text }));
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/not closed 1/);
    } finally {
      removeTempFixture(tmpFile);
    }
  }, TIMEOUT);
});
