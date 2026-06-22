import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, tempFixture, removeTempFixture } from './harness.js';

const TIMEOUT = 90_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

// Regression tests for edit_file argument validation.
//
// Both failure modes below were observed in benchmark transcripts where the
// model emitted slightly-wrong arguments and edit_file crashed with a cryptic
// Node error instead of returning a helpful message:
//   - "Cannot destructure property 'start' of 'edit.range' as it is undefined."
//     (edits entry with newText but no range)
//   - "The \"paths[1]\" argument must be of type string. Received undefined"
//     (model sent `filePath` instead of `file`)
describe('edit_file argument validation', () => {
  it('returns a helpful error when an edits entry has no range (no crash)', async () => {
    const f = tempFixture('multi_error.v', 'editval_norange');
    try {
      const r = await h.callTool('edit_file', {
        file: f,
        edits: [{ newText: 'Lemma foo : True.\nProof. exact I. Qed.\n' }],
      }, TIMEOUT);
      // Must not be the raw destructure crash.
      expect(r.text).not.toMatch(/destructure/i);
      expect(r.text).toMatch(/range|find.*replace/i);
    } finally {
      removeTempFixture(f);
    }
  });

  it('accepts filePath as an alias for file', async () => {
    const f = tempFixture('multi_error.v', 'editval_filepath');
    try {
      const r = await h.callTool('edit_file', {
        filePath: f,
        find: 'Theorem',
        replace: 'Theorem',
      }, TIMEOUT);
      expect(r.text).not.toMatch(/paths\[1\]|type string/i);
      expect(r.isError).toBe(false);
    } finally {
      removeTempFixture(f);
    }
  });

  it('returns a clear error when file is missing entirely', async () => {
    const r = await h.callTool('edit_file', {
      edits: [{ newText: 'x' }],
    }, TIMEOUT);
    expect(r.text).toMatch(/missing required "file"/i);
    expect(r.text).not.toMatch(/paths\[1\]|destructure/i);
  });
});
