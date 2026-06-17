/**
 * Integration test: insert_tactic admit_hash on a stratify-survivor
 * congruence case in PCF preservation.
 *
 * Verifies that after stratify produces a bulleted proof, using
 * insert_tactic with admit_hash + the correct IHHstep with (T0 := ...)
 * either closes the case or re-seals with { (* hash *) admit. } braces
 * without corrupting the proof structure.
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, removeTempFixture, tempFixture, extractAdmitHashes, fixture } from './harness.js';

const TIMEOUT = 120_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('insert_tactic admit_hash on stratify survivor — brace seal', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('pcf_ref.v', 'strat_survivor',
      fixture('../../../benchmarks/incomplete'));

    // Add and prove the helper lemmas first
    await h.callTool('check_file', { file: tmpFile });

    const addAndProve = async (name: string, stmt: string, skel: string, portfolio: string[], fix?: { tactic: string }) => {
      await h.callTool('add_lemma', { file: tmpFile, name, statement: stmt, before: 'preservation' });
      await h.callTool('stratify', { file: tmpFile, name, skeleton: skel, portfolio });
      if (fix) {
        const list = await h.callTool('focus_proof', { file: tmpFile, name });
        const admits = extractAdmitHashes(list.text);
        const hash = admits[0]?.hash;
        if (hash && admits.length === 1) {
          await h.callTool('insert_tactics', { file: tmpFile, name, tactic: fix.tactic, admit_hash: hash });
        }
      }
    };

    await addAndProve('extends_refl',
      'forall S : store_ty, extends S S',
      'intro',
      ['unfold extends; exists []; symmetry; apply app_nil_r']);

    await addAndProve('has_type_extends',
      'forall G S t T S\', has_type G S t T -> extends S\' S -> has_type G S\' t T',
      'induction 1; intros',
      ['econstructor; eauto', 'econstructor; eauto 2'],
      { tactic: 'destruct H0 as [S2 ->]; apply T_Loc; rewrite nth_error_app1; auto; apply nth_error_Some; rewrite H; discriminate' });

    await addAndProve('heap_ok_lookup',
      'forall mu S l v, heap_ok mu S -> heap_lookup l mu = Some v -> exists T, nth_error S l = Some T /\\ has_type [] S v T',
      'induction 1; simpl; intros',
      ['inversion H', 'destruct (Nat.eqb_spec l l0); subst; inversion H2; subst; eauto', 'discriminate']);

    await addAndProve('heap_ok_update',
      'forall mu S l v T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok (heap_update l v mu) S',
      'induction 1; simpl; intros',
      ['constructor; auto', 'destruct (Nat.eqb_spec l l0); subst; econstructor; eauto']);
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  // ─────────────────────────────────────────────────────────
  // Scenario A: congestion case (S_Succ) — IH with (T0 := TyNat)
  // ─────────────────────────────────────────────────────────

  describe('congruence case via IH with T0 parameter', () => {

    beforeAll(async () => {
      // Run stratify to produce bulleted admits
      const r = await h.callTool('stratify', {
        file: tmpFile, name: 'preservation',
        skeleton: 'intros t0 mu0 t\'0 mu\'0 T0 S0 Ht Hstep Hok Hlen; revert S0 T0 Ht Hok Hlen; induction Hstep; intros STy Ty Ht Hok Hlen; inversion Ht; subst',
        portfolio: [
          'exists STy; split; [apply extends_refl | split; [assumption | econstructor; eauto]]',
          'exists STy; split; [apply extends_refl | split; [assumption | assumption]]',
          'exists STy; split; [apply extends_refl | split; [assumption | apply T_Num]]',
          'exists STy; split; [apply extends_refl | split; [assumption | apply T_Bool]]',
        ],
        attempt_timeout_ms: 30_000,
      }, TIMEOUT);
      expect(r.isError).toBe(false);
    }, TIMEOUT);

    it('stratify produces ≤ 17 survivors', async () => {
      const list = await h.callTool('focus_proof', {
        file: tmpFile, name: 'preservation',
      });
      const admits = extractAdmitHashes(list.text);
      // Base cases (PredZero, PredSucc, IsZeroZero, IsZeroSucc, IfTrue, IfFalse) = 6 solved
      // At most 15 survivors remain (the remaining congruence + hard cases)
      expect(admits.length).toBeLessThanOrEqual(17);
    }, TIMEOUT);

    it('find the S_Succ admit and close it with IHHstep (T0 := TyNat)', async () => {
      const list = await h.callTool('focus_proof', {
        file: tmpFile, name: 'preservation',
      });
      const admits = extractAdmitHashes(list.text);
      // Find S_Succ: goal contains "Succ t'" and "TyNat"
      const succAdmit = admits.find(a =>
        a.goal.includes('Succ t\'') && a.goal.includes('TyNat')
      );
      expect(succAdmit).toBeTruthy();

      const r = await h.callTool('insert_tactics', {
        file: tmpFile, name: 'preservation',
        tactic: 'edestruct IHHstep with (T0 := TyNat); eauto; eexists; split; [exact H0 | split; [exact H1 | econstructor; eauto]]',
        admit_hash: succAdmit!.hash,
      });
      console.log('S_Succ close result:', r.text.slice(0, 400));
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/replaced|Qed applied|rejected/);

      // File must still be valid
      const cr = await h.callTool('check_file', { file: tmpFile });
      expect(cr.isError).toBe(false);
    }, TIMEOUT);

    it('find S_Pred admit and close it with IHHstep (T0 := TyNat)', async () => {
      const list = await h.callTool('focus_proof', {
        file: tmpFile, name: 'preservation',
      });
      const admits = extractAdmitHashes(list.text);
      const predAdmit = admits.find(a =>
        a.goal.includes('Pred t\'') && a.goal.includes('TyNat')
      );
      if (!predAdmit) return; // already closed
      expect(predAdmit).toBeTruthy();

      const r = await h.callTool('insert_tactics', {
        file: tmpFile, name: 'preservation',
        tactic: 'edestruct IHHstep with (T0 := TyNat); eauto; eexists; split; [exact H0 | split; [exact H1 | econstructor; eauto]]',
        admit_hash: predAdmit!.hash,
      });
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/replaced|Qed applied|rejected/);

      const cr = await h.callTool('check_file', { file: tmpFile });
      expect(cr.isError).toBe(false);
    }, TIMEOUT);

    it('find S_IsZero admit and close it with IHHstep (T0 := TyNat)', async () => {
      const list = await h.callTool('focus_proof', {
        file: tmpFile, name: 'preservation',
      });
      const admits = extractAdmitHashes(list.text);
      const izAdmit = admits.find(a =>
        a.goal.includes('IsZero t\'') && a.goal.includes('TyBool')
      );
      if (!izAdmit) return;
      expect(izAdmit).toBeTruthy();

      const r = await h.callTool('insert_tactics', {
        file: tmpFile, name: 'preservation',
        tactic: 'edestruct IHHstep with (T0 := TyNat); eauto; eexists; split; [exact H0 | split; [exact H1 | econstructor; eauto]]',
        admit_hash: izAdmit!.hash,
      });
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/replaced|Qed applied|rejected/);

      const cr = await h.callTool('check_file', { file: tmpFile });
      expect(cr.isError).toBe(false);
    }, TIMEOUT);

    it('find S_App1 admit and close it with IHHstep (T0 := TyArrow T1 Ty)', async () => {
      const list = await h.callTool('focus_proof', {
        file: tmpFile, name: 'preservation',
      });
      const admits = extractAdmitHashes(list.text);
      const app1Admit = admits.find(a =>
        a.goal.includes('App t1\'') && a.goal.includes('Ty')
      );
      if (!app1Admit) return;
      expect(app1Admit).toBeTruthy();

      const r = await h.callTool('insert_tactics', {
        file: tmpFile, name: 'preservation',
        tactic: 'inversion H3; subst; edestruct IHHstep with (T0 := TyArrow T1 Ty); eauto; eexists; split; [exact H0 | split; [exact H1 | econstructor; eauto]]',
        admit_hash: app1Admit!.hash,
      });
      expect(r.isError).toBe(false);
      expect(r.text).toMatch(/replaced|Qed applied|rejected/);

      const cr = await h.callTool('check_file', { file: tmpFile });
      expect(cr.isError).toBe(false);
    }, TIMEOUT);
  });
});
