import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
const t = new StdioClientTransport({ command: 'node', args: ['dist/index.js', '--coq-lsp-path', '/home/gavin/.opam/rocq-9/bin/coq-lsp'], cwd: '/home/gavin/dev/Scidonia/rocq-piler' });
const c = new Client({ name: 'test', version: '0' }, { capabilities: {} });
await c.connect(t);

const file = 'benchmarks/complete/pcf_ref.v';
// Reset preservation to Admitted first
await c.callTool({ name: 'reset_proof', arguments: { file, name: 'preservation' } });
console.log('reset done');

// Run stratify
const r = await c.callTool({ name: 'stratify', arguments: {
  file, name: 'preservation',
  skeleton: 'intros t mu t\' mu\' T S Ht Hstep Hok Hlen; revert T S Ht Hok Hlen; induction Hstep; intros Ty STy Ht Hok Hlen; inversion Ht; subst; clear Ht',
  portfolio: [
    'exists STy; split; [apply extends_refl|split; [assumption|constructor]]',
    'exists STy; split; [apply extends_refl|split; [assumption|assumption]]',
    'edestruct IHHstep as (S\' & Hext & Hok\' & Ht\'); eauto; exists S\'; split; [exact Hext|split; [exact Hok\'|econstructor; eauto using has_type_extends]]',
  ],
  cases_from: 'step',
  attempt_timeout_ms: 15_000,
}}, 300000);
console.log(r.content[0].text);
process.exit(0);
