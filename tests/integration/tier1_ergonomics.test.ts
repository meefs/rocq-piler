import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, tempFixture, removeTempFixture } from './harness.js';

const TIMEOUT = 120_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
}, TIMEOUT);

describe('Tier 1: Self-documenting insert_tactics failures', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('ergonomic.v', 'selfdoc');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('dry_run failure includes goal context with hypotheses', async () => {
    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'ergonomic_intro',
      tactic: 'exact 42.',
      dry_run: true,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/tactic failed/i);
    expect(r.text).toMatch(/n\s*:/);
  }, TIMEOUT);

  it('spec-check failure includes goal at failure point', async () => {
    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'ergonomic_split',
      tactic: 'exact 42.',
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/FAILED|failed/i);
    expect(r.text).toMatch(/Goal at failure|True/);
  }, TIMEOUT);
});

describe('Tier 1: Tactic script (list) support', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('ergonomic.v', 'script');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('successful multi-step tactic script inserts all tactics', async () => {
    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'ergonomic_multi',
      tactics: ['intros n', 'split', 'reflexivity', 'reflexivity'],
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/inserted|done|Qed/i);
    expect(r.text).toMatch(/split/);
    expect(r.text).toMatch(/reflexivity/);
  }, TIMEOUT);

  it('partial failure reports which tactics succeeded and goal at failure', async () => {
    const tmp2 = tempFixture('ergonomic.v', 'scriptfail');
    try {
      await h.callTool('check_file', { file: tmp2 });
      const r = await h.callTool('insert_tactics', {
        file: tmp2,
        name: 'ergonomic_intro',
        tactics: ['intros n', 'exact 42.'],
      });
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/tactic script failed/i);
      expect(r.text).toMatch(/step 2/);
      expect(r.text).toMatch(/Succeeded.*1/);
      expect(r.text).toMatch(/n\s*:\s*nat/i);
    } finally {
      removeTempFixture(tmp2);
    }
  }, TIMEOUT);

  it('rejects empty tactics array', async () => {
    const r = await h.callTool('insert_tactics', {
      file: tmpFile,
      name: 'ergonomic_split',
      tactics: [],
    });
    expect(r.isError).toBe(true);
  }, TIMEOUT);
});
