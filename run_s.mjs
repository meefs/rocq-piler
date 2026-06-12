import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
const t = new StdioClientTransport({ command: 'node', args: ['/home/gavin/dev/Scidonia/rocq-piler/dist/index.js', '--coq-lsp-path', '/home/gavin/.opam/rocq-9/bin/coq-lsp'] });
const c = new Client({ name: 'x', version: '0' }, { capabilities: {} });
await c.connect(t);
const r = await c.callTool({ name: 'stratify', arguments: {
  file: 'benchmarks/complete/pcf_ref.v', name: 'preservation',
  skeleton: "intros t mu t' mu' T S Ht Hstep Hok Hlen; revert T S Ht Hok Hlen; induction Hstep; intros Ty STy Ht Hok Hlen; inversion Ht; subst; clear Ht",
  portfolio: [
    "exists STy; split; [apply extends_refl|split; [assumption|constructor]]",
    "exists STy; split; [apply extends_refl|split; [assumption|assumption]]",
    "edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]]",
  ],
  cases_from: 'step',
}}, 300000);
console.log(r.content[0].text);
process.exit(0);
