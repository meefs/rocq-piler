#!/usr/bin/env node

/**
 * MCP server for Coq/Rocq integration via coq-lsp/rocq-lsp
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  ListResourcesRequestSchema,
  ReadResourceRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';

import { RocqLspClient } from './lsp-client.js';
import { DocumentManager, applyTextEdits } from './document-manager.js';
import { detectProjectConfig, mergeProjectArgs, findProjectRoot } from './project-config.js';
import { isSkipLine, isProofEndLine, isTopLevelLine, autoAdvancePosition, insertPosition, findProofLine, computeBulletIndent, proofBounds, findAdmitLines, findTacticAdmitLines, admitSnapPosition, bulletInsertPos, admitPrefix, replaceAdmitLine, replaceAllMatchingAdmits, nextChildBullet, sealOpenGoals, applyAutoQed } from './coq-utils.js';
import type {
  Position,
  Range,
  GoalAnswer,
  ProofInfo,
  RunResult,
  GoalConfig,
  RunOpts,
} from './types.js';
import * as fs from 'fs';
import { dirname, resolve as resolvePath } from 'path';
import { fileURLToPath } from 'url';
import { createHash } from 'crypto';

const __dirname = dirname(fileURLToPath(import.meta.url));

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function retryDocumentNotReady<T>(
  action: () => Promise<T>,
  opts?: { timeoutMs?: number; initialDelayMs?: number; maxDelayMs?: number }
): Promise<T> {
  const timeoutMs = opts?.timeoutMs ?? 30_000;
  let delayMs = opts?.initialDelayMs ?? 50;
  const maxDelayMs = opts?.maxDelayMs ?? 500;
  const start = Date.now();

  for (;;) {
    try {
      return await action();
    } catch (err) {
      const message = err instanceof Error ? err.message : String(err);
      const isNotReady = message.includes('Document is not ready');
      const isWorkspaceSwitch = message.includes('Switching workspace');
      const isLspStart = message.includes('LSP client not started');

      if (!(isNotReady || isWorkspaceSwitch || isLspStart) || Date.now() - start > timeoutMs) {
        throw err;
      }

      // For workspace switches and LSP restarts, use longer initial delays
      if (isWorkspaceSwitch || isLspStart) {
        delayMs = Math.max(delayMs, 500);
      }
      await sleep(delayMs);
      delayMs = Math.min(Math.floor(delayMs * 1.5), maxDelayMs);
    }
  }
}

// Parse command-line arguments for configuration
function parseArgs() {
  const args = process.argv.slice(2);
  const config: {
    rocqLspPath?: string;
    rocqLspArgs?: string[];
    workspaceRoot?: string;
  } = {};

  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--coq-lsp-path' && i + 1 < args.length) {
      config.rocqLspPath = args[++i];
    } else if (args[i] === '--workspace-root' && i + 1 < args.length) {
      config.workspaceRoot = args[++i];
    } else if (args[i] === '--coq-lsp-args' && i + 1 < args.length) {
      config.rocqLspArgs = args[++i].split(' ');
    }
  }

  if (config.workspaceRoot) {
    config.workspaceRoot = resolvePath(config.workspaceRoot);
  }

  return config;
}

async function main() {
  const config = parseArgs();

  // Global crash logging — write to same debug log as lsp-client
  const DBG = '/tmp/mcp-coq-lsp-debug.log';
  function crash(msg: string) {
    try { fs.appendFileSync(DBG, `[${new Date().toISOString()}] CRASH: ${msg}\n`); } catch {}
  }
  process.on('uncaughtException', (err) => {
    crash(`uncaughtException: ${err.stack || err.message || String(err)}`);
    console.error('[mcp-coq-lsp] CRASH:', err);
    process.exit(1);
  });
  process.on('unhandledRejection', (reason: any) => {
    crash(`unhandledRejection: ${reason?.stack || reason?.message || String(reason)}`);
    console.error('[mcp-coq-lsp] UNHANDLED REJECTION:', reason);
  });

  // Determine workspace root
  const workspaceRoot = config.workspaceRoot || process.cwd();

  // Auto-detect project configuration (for logging/debugging purposes)
  // Note: coq-lsp will auto-detect _CoqProject/_RocqProject itself, but we log what we find
  // to help diagnose any issues with project configuration
  const projectConfig = detectProjectConfig(workspaceRoot);

  console.error('[mcp-coq-lsp] Workspace root:', workspaceRoot);
  console.error('[mcp-coq-lsp] Detected load paths:', projectConfig.loadPaths);
  
  if (projectConfig.loadPaths.length === 0) {
    console.error('[mcp-coq-lsp] WARNING: No _CoqProject/_RocqProject/dune config found!');
    console.error('[mcp-coq-lsp] coq-lsp may not be able to resolve imports correctly.');
  }

  // Base user-provided args
  const baseRocqLspArgs = config.rocqLspArgs || [];
  let finalRocqLspArgs = [...baseRocqLspArgs];

  console.error('[mcp-coq-lsp] coq-lsp args:', finalRocqLspArgs);

  /**
   * Compute coq-lsp CLI args for a given workspace root.
   * Maps the coq/ source directory (if it exists) to the root logical path
   * so that bare imports like `Require Import Wp` resolve correctly.
   */
  function computeRocqLspArgs(root: string): string[] {
    const args = [...baseRocqLspArgs];
    try {
      const srcDir = resolvePath(root, 'coq');
      if (fs.existsSync(srcDir)) {
        args.push('-R', `${srcDir},Imp`);
      }
    } catch {}
    return args;
  }

  // Initialize with initial workspace root
  finalRocqLspArgs = computeRocqLspArgs(workspaceRoot);

  // Track the active project root for dynamic workspace switching
  let activeWorkspaceRoot = workspaceRoot;

  // Speculative imports per file URI — persisted across tool calls
  const speculativeImports = new Map<string, string[]>();

  // File history per file path — used by coq_undo to restore previous versions
  const fileHistory = new Map<string, Array<{text: string, proof: string | null}>>();
  const MAX_HISTORY = 50;
  // Track the last insertion per file — used by coq_insert_tactics replace:true
  const lastInsertion = new Map<string, { range: Range }>();
  // Track the active proof per file — used by coq_undo to scope undo to current proof
  const currentProof = new Map<string, string>();
  // Track position of last replaced admit — used by insert_tactics to land on reopened bullet
  const lastAdmitReplaced = new Map<string, number>();

  /** Clamp a position to be within [0, lines.length-1] — never past EOF. */
  function safePos(pos: Position, text: string): Position {
    const maxLine = Math.max(0, text.split('\n').length - 1);
    return { line: Math.min(pos.line, maxLine), character: 0 };
  }

  function pushFileHistory(path: string, text: string, proof?: string | null) {
    if (!fileHistory.has(path)) fileHistory.set(path, []);
    const stack = fileHistory.get(path)!;
    stack.push({ text, proof: proof ?? null });
    if (stack.length > MAX_HISTORY) stack.shift();
    fileHistory.set(path, stack);
  }

  function bulletTokenFromMessage(message?: string): string | undefined {
    return message?.match(/[-+*]+/)?.[0];
  }


  function bulletLineInfo(line: string): { indent: number; token: string } | undefined {
    const trimmed = line.trimStart();
    const match = trimmed.match(/^([-+*]+)(?=\s|$)/);
    if (!match) return undefined;
    return { indent: line.length - trimmed.length, token: match[1] };
  }

  function findLastBulletIndent(
    lines: string[],
    startLineExclusive: number,
    proofLine: number,
    token?: string,
  ): number | undefined {
    for (let i = startLineExclusive - 1; i > proofLine; i--) {
      const info = bulletLineInfo(lines[i] || '');
      if (info && (!token || info.token === token)) return info.indent;
    }
    return undefined;
  }

  /**
   * Open a document, first detecting and switching to its project root if needed.
   * This allows files from different Coq projects to be opened without restarting
   * the MCP server.
   */
  async function ensureDocumentOpened(path: string) {
    const absPath = resolvePath(path);
    const projectRoot = findProjectRoot(absPath);

    if (projectRoot && resolvePath(projectRoot) !== resolvePath(activeWorkspaceRoot)) {
      console.error('[mcp-coq-lsp] Switching workspace root:',
        activeWorkspaceRoot, '->', projectRoot);

      activeWorkspaceRoot = projectRoot;
      docManager.clear();
      speculativeImports.clear();
      fileHistory.clear();
      currentProof.clear();

      // Await the restart, then retry — no need for the caller to retry manually.
      try {
        await lspClient.restart({
          workspaceRoot: projectRoot,
          rocqLspArgs: computeRocqLspArgs(projectRoot),
        });
        console.error('[mcp-coq-lsp] Workspace switch complete');
      } catch (err) {
        console.error('[mcp-coq-lsp] Workspace switch failed:', err);
        throw new Error('Workspace switch failed for ' + projectRoot);
      }

      // Retry document open with the new workspace
      try {
        return await docManager.openDocument(path);
      } catch (err: any) {
        if (err?.message?.includes('not ready') || err?.message?.includes('not started')) {
          // Give the LSP a moment to finish initializing
          await sleep(500);
          return await docManager.openDocument(path);
        }
        throw err;
      }
    }

    try {
      const doc = await docManager.openDocument(path);
      const freshText = await fs.promises.readFile(absPath, 'utf-8');
      if (freshText !== doc.text) {
        return await docManager.updateDocument(path, freshText);
      }
      return doc;
    } catch (err: any) {
      if (err?.message === 'LSP client not started') {
        // LSP isn't running — restart it and wait for it to be ready
        console.error('[mcp-coq-lsp] LSP not started, restarting...');
        try {
          await lspClient.restart({
            workspaceRoot: activeWorkspaceRoot,
            rocqLspArgs: computeRocqLspArgs(activeWorkspaceRoot),
          });
          console.error('[mcp-coq-lsp] Auto-restart complete, retrying document open');
          await sleep(200);
          return await docManager.openDocument(path);
        } catch (restartErr: any) {
          console.error('[mcp-coq-lsp] Auto-restart failed:', restartErr);
          throw new Error('LSP client not started — please retry');
        }
      }
      throw err;
    }
  }

  // === LSP client setup ===

  // Create LSP client and document manager
  const lspClient = new RocqLspClient({
    rocqLspPath: config.rocqLspPath,
    rocqLspArgs: finalRocqLspArgs,
    workspaceRoot: workspaceRoot,
    checkOnlyOnRequest: false,
    ppType: 0, // String output
    goalAfterTactic: true,
  });

  const docManager = new DocumentManager(
    lspClient,
    workspaceRoot
  );

  // Start LSP client
  await lspClient.start();

  // Create MCP server
  const server = new Server(
    {
      name: 'rocq-piler',
      version: '0.1.0',
    },
    {
      capabilities: {
        tools: {},
        resources: {},
      },
    }
  );

  // ── MCP Resources ──

  // Load skill guide content at startup
  const skillGuideUri = 'coq://skill-guide';
  const skillGuideContent = fs.readFileSync(
    resolvePath(__dirname, '../src/skill.md'), 'utf-8'
  );

  server.setRequestHandler(ListResourcesRequestSchema, async () => ({
    resources: [
      {
        uri: skillGuideUri,
        name: 'Coq Proof Skill Guide',
        description: 'Comprehensive reference for proving Coq/Rocq theorems using MCP coq-lsp tools. Covers proof strategy, bullet system, lemma management, common tactics, and troubleshooting.',
        mimeType: 'text/markdown',
      },
    ],
  }));

  server.setRequestHandler(ReadResourceRequestSchema, async (request) => {
    if (request.params.uri === skillGuideUri) {
      return {
        contents: [{ uri: skillGuideUri, mimeType: 'text/markdown', text: skillGuideContent }],
      };
    }
    throw new Error(`Unknown resource: ${request.params.uri}`);
  });

  // ── Tools ──

  // Tool: coq_open_goals
  server.setRequestHandler(ListToolsRequestSchema, async () => {
    return {
      tools: [






        {
           name: 'insert_tactics',
          description:
            'Insert a tactic (or composition) into a proof and return updated goals. ' +
            'Use admit_hash to target a specific admitted bullet (the 8-char hash from stratify or focus_proof). ' +
            'Use dry_run:true to speculatively evaluate without modifying the file — test a tactic against ' +
            'a hash-targeted admit before committing. Auto-prepends brace prefix when Coq requires a bullet. ' +
            'Pass replace:true to undo the last insertion and retry. ' +
            'Compound tactics (e.g. "pose proof ...; destruct ...; exists ...; split ...") are inserted atomically; ' +
            'if they leave open focused goals, the tool seals them as nested hash-addressable admit blocks.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              name: { type: 'string', description: 'Proof name (e.g. "preservation")' },
              tactic: { type: 'string' },
              follow_with_goals: { type: 'boolean', description: 'Query goals after inserting' },
              replace: { type: 'boolean', description: 'Replace the last inserted tactic' },
              admit_hash: { type: 'string', description: 'Hash from focus_proof admits section — replace this admit with tactic' },
              dry_run: { type: 'boolean', description: 'Speculative check only — does not modify the file' },
            },
            required: ['file', 'name', 'tactic'],
          },
        },
        {
          name: 'search_lemmas',
          description:
            'Search the Coq environment for lemmas and theorems. Simple names auto-quote (e.g. "plus_n_O"). ' +
            'Use parentheses for patterns: "(_ + 0 = _)" or just "_ + 0 = _". ' +
            'Runs speculatively, no file changes.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (used to obtain a proof state)',
              },
              pattern: {
                type: 'string',
                description: 'Search pattern for lemmas/theorems',
              },
            },
            required: ['file', 'pattern'],
          },
        },
        {
          name: 'inspect_term',
          description:
            'Check the type of a term speculatively. Runs `Check <term>.` and returns the result.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (used to obtain a proof state)',
              },
              term: {
                type: 'string',
                description: 'Term to check the type of',
              },
            },
            required: ['file', 'term'],
          },
        },
        {
          name: 'inspect_about',
          description:
            'Get information about a term/definition speculatively. Runs `About <term>.` and returns the result.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (used to obtain a proof state)',
              },
              term: {
                type: 'string',
                description: 'Term to get information about',
              },
            },
            required: ['file', 'term'],
          },
        },

        {
          name: 'stratify',
          description:
            'Case-split a proof and discharge the easy cases in one call. Runs a ' +
            'skeleton tactic (e.g. "induction H; intros; inversion Ht; subst"), then ' +
            'independently attempts each resulting subgoal with every tactic in a ' +
            'closing portfolio (each attempt wrapped in solve [...]). Writes the result ' +
            'into the file: solved cases get their winning tactic inlined as a bullet; ' +
            'survivors become labelled, hash-addressable ' +
            '"{ (* CaseName:hash *) admit. }" bullets (hash is 8 hex chars). ' +
            'Report lists survivors by hash and goal. Use close_admits to batch-close ' +
            'survivors with a portfolio of hash→tactic mappings. Or target individually ' +
            'via insert_tactics admit_hash=<hash>, or stratify again with admit_hash=<hash>.' +
            'Use write=false for a dry run. This is the primary entry point for ' +
            'multi-case induction proofs.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              name: { type: 'string', description: 'Proof name' },
              skeleton: {
                type: 'string',
                description: 'Skeleton tactic run first, e.g. "induction Hstep; intros; inversion Ht; subst; clear Ht"',
              },
              portfolio: {
                type: 'array',
                items: { type: 'string' },
                description: 'Closing tactics tried per subgoal, in order. Each is wrapped in solve [...] so partial progress never leaks.',
              },
              cases_from: {
                type: 'string',
                description: 'Optional: name of the inductive the skeleton case-splits on (e.g. "step") — labels subgoals by constructor',
              },
              admit_hash: {
                type: 'string',
                description: 'Optional: hash of a surviving admit (from a previous stratify or focus_proof) — runs the skeleton+portfolio nested inside that admit block instead of replacing the whole proof body',
              },
              write: { type: 'boolean', description: 'Write results into the file (default true). false = dry-run report only.' },
              attempt_timeout_ms: { type: 'number', description: 'Timeout per portfolio attempt in ms (default 10000)' },
            },
            required: ['file', 'name', 'skeleton', 'portfolio'],
          },
        },
        {
          name: 'close_admits',
          description:
            'Use after stratify to batch-close the survivors. ' +
            'Give it a portfolio of {hashes: [...], tactic: "..."} entries mapping ' +
            'admit hashes to closing tactics; entries are processed in order. ' +
            'The special hash "*" expands to all currently-unclosed admits (not ' +
            'already matched by earlier entries). Per-hash speculative dry-run ' +
            'first: if the tactic closes the goal, the edit is committed; ' +
            'otherwise the admit is left as-is. ' +
            'Returns which hashes were closed and which were not (with errors).',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to a .v file' },
              name: { type: 'string', description: 'Proof name (e.g. "preservation")' },
              portfolio: {
                type: 'array',
                items: {
                  type: 'object',
                  properties: {
                    hashes: {
                      anyOf: [
                        { type: 'string' },
                        { type: 'array', items: { type: 'string' } },
                      ],
                      description: 'Hash(es) to target. Use "*" to match all currently-unclosed admits not yet processed.',
                    },
                    tactic: { type: 'string', description: 'Tactic to try on each target admit' },
                  },
                  required: ['hashes', 'tactic'],
                },
              },
            },
            required: ['file', 'name', 'portfolio'],
          },
        },
        {
          name: 'check_file',
          description: 'Force document checking and return completion status',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              start_line: { type: 'number', description: 'Optional: 0-based start line for paginated summary' },
              count: { type: 'number', description: 'Optional: max items to return (boundary-expanding)' },
              timeout_ms: { type: 'number', description: 'Optional: per-request timeout in ms (default 15000)' },
              retry_timeout_ms: { type: 'number', description: 'Optional: total retry timeout in ms for cold starts (default 30000)' },
            },
            required: ['file'],
          },
        },

        {
          name: 'require_lib',
          description:
            'Require a library speculatively. Runs `Require Import <lib>.` against the file environment. ' +
            'Subsequent speculative queries on the same file will see the library. Does not modify the file.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (provides the import environment)',
              },
              lib: {
                type: 'string',
                description: 'Library/module name to import (e.g. "Arith", "Coq.Lists.List")',
              },
            },
            required: ['file', 'lib'],
          },
        },
        {
          name: 'locate_term',
          description:
            'Find where a library, module, or term is defined. Runs `Locate <thing>.` speculatively. ' +
            'Useful before Require to check if a module exists.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (used to obtain a proof state)',
              },
              thing: {
                type: 'string',
                description: 'Name to locate (e.g. "Nat", "Coq.Lists.List", "plus_n_O")',
              },
            },
            required: ['file', 'thing'],
          },
        },
        {
          name: 'focus_proof',
          description:
            'Get full proof tree: current goals, bullet stack depth/levels, ' +
            'and the proof script up to the given position. ' +
            'Sets the file cursor — subsequent coq_insert_tactics/coq_try_tactic calls ' +
            'use this cursor automatically. Auto-removes empty Admitted stubs. ' +
            'Accepts proof name (e.g. "has_type_weaken") or explicit position.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to a .v file' },
              position: {
                type: 'object',
                properties: { line: { type: 'number' }, character: { type: 'number' } },
                required: ['line', 'character'],
              },
              name: { type: 'string', description: 'Proof name (alternative to position)' },
            },
            required: ['file'],
          },
        },
        {
          name: 'reset_proof',
          description:
            'Wipe the proof body (from Proof. to Qed./Admitted.) and replace with fresh Admitted. ' +
            'Use this to start over on a broken proof.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to a .v file' },
              name: { type: 'string', description: 'Proof name (e.g. "has_type_weaken")' },
            },
            required: ['file', 'name'],
          },
        },
        {
          name: 'add_lemma',
          description:
            'Insert a lemma stub (Lemma name : statement. Proof. Admitted.) ' +
            'above a specified proof. Use "before" to name which proof it goes above. ' +
            'Cursor moves to the new proof.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to a .v file' },
              name: { type: 'string', description: 'Lemma name (e.g. "my_helper")' },
              statement: { type: 'string', description: 'The lemma statement after the colon' },
              before: { type: 'string', description: 'Proof name to insert above (e.g. "preservation")' },
            },
            required: ['file', 'name', 'statement'],
          },
        },
        {
          name: 'delete_lemma',
          description:
            'Delete named lemmas/theorems and their proofs from a .v file. ' +
            'Accepts a single name or array. Forces LSP re-sync after deletion.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to a .v file' },
              name: {
                description: 'Lemma/theorem name or array of names',
                anyOf: [{ type: 'string' }, { type: 'array', items: { type: 'string' } }],
              },
            },
            required: ['file', 'name'],
          },
        },
      ],
    };
  });

  // Tool handler
  server.setRequestHandler(CallToolRequestSchema, async (request) => {
    const { name, arguments: args } = request.params;

    function formatSemi(data: unknown, indent = 0): string {
      const pad = '  '.repeat(indent);
      if (data === null || data === undefined) return pad + 'null';
      if (typeof data === 'string') return data;
      if (typeof data === 'number' || typeof data === 'boolean') return pad + String(data);
      if (Array.isArray(data)) {
        if (data.length === 0) return '[]';
        const allSimple = data.every(v => typeof v !== 'object' || v === null);
        if (allSimple) return data.map((v, i) => `[${i}]: ${formatSemi(v, 0)}`).join(', ');
        return data.map((v, i) => `[${i}]:\n${formatSemi(v, indent + 1)}`).join('\n');
      }
      if (typeof data === 'object') {
        const entries = Object.entries(data as Record<string, unknown>);
        if (entries.length === 0) return '{}';
        return entries.map(([k, v]) => {
          if (v === null || v === undefined) return pad + k + ': null';
          if (typeof v === 'object') return pad + k + ':\n' + formatSemi(v, indent + 1);
          return pad + `${k}: ${formatSemi(v, 0)}`;
        }).join('\n');
      }
      return pad + String(data);
    }

    function reply(summary: string, data: unknown) {
      const d = data as Record<string, unknown>;
      const parts: string[] = [summary];
      if (d?.goals) {
        const goalsWrapped = Array.isArray(d.goals) ? { goals: d.goals } : d.goals;
        const gl = (goalsWrapped as any)?.goals || [];
        if (gl.length > 0) {
          parts.push('');
          parts.push(formatGoals(goalsWrapped));
        }
      }
      if (Array.isArray(d?.feedback) && d.feedback.length > 0) parts.push(formatFeedback(d.feedback));
      const text = parts.join('\n');
      return {
        content: [
          { type: 'text' as const, text },
        ],
      };
    }

    function err(summary: string, detail?: string) {
      return {
        content: [
          { type: 'text' as const, text: detail ?? summary },
          { type: 'text' as const, text: summary },
        ],
        isError: true,
      };
    }

    /**
     * Run all pending speculative imports for a document URI on a given state.
     * Returns the final state after all imports.
     */
    async function runPendingImports(uri: string, stateId: number): Promise<number> {
      const pending = speculativeImports.get(uri);
      if (!pending || pending.length === 0) return stateId;
      let st = stateId;
      for (const lib of pending) {
        const r = await lspClient.sendRequest<RunResult<number>>(
          'petanque/run',
          { st, tac: `Require Import ${lib}.`, opts: { memo: true, hash: true } }
        );
        st = r.st;
      }
      return st;
    }

    function formatGoals(goals: any): string {
      const gl = goals?.goals || [];
      if (gl.length === 0) {
        const prog = goals?.program?.length || 0;
        const msgs = (goals?.messages || []).filter((m: any) => m.level === 1).map((m: any) => m.text).join('; ');
        return 'no goals' + (prog ? ` (${prog} program items)` : '') + (msgs ? '\n  messages: ' + msgs : '');
      }
      return gl.map((g: any, i: number) => {
        const total = gl.length;
        const idx = `Goal [${i + 1} of ${total}]: `;
        const hyps = (g.hyps || []).map((h: any) => {
          const name = h.names ? h.names.join(', ') : (h.name || '?');
          return `  ${name}: ${h.ty || h.type}`;
        }).join('\n');
        const ty = (g.ty || '').replace(/\s+/g, ' ');
        return (idx ? idx.trim() + '\n' : '') + (hyps ? hyps + '\n' : '') + '  ════════════════════════════════════\n  ' + ty;
      }).join('\n\n');
    }

    function compactGoalSummary(goals: any): string {
      const gl = goals?.goals || [];
      if (gl.length === 0) return '';
      if (gl.length === 1 && gl[0]) {
        const g = gl[0];
        const hnames = (g.hyps || []).map((h: any) => h.names ? h.names.join(',') : (h.name || '?')).join('; ');
        const parts: string[] = [];
        if (hnames) parts.push(`hyps: ${hnames}`);
        const oneline = (g.ty || '').replace(/\s+/g, ' ');
        if (oneline) parts.push(`⊢ ${oneline}`);
        return parts.join(' | ');
      }
      return `${gl.length} goals`;
    }

    function nextHint(gc: any): string {
      const goals = gc?.goals || [];
      const stack = gc?.stack || [];
      const bullet = gc?.bullet;

      const bgGoals = stack.reduce(
        (s: number, [b, a]: any[]) => s + (b?.length || 0) + (a?.length || 0), 0
      );
      const total = goals.length + bgGoals;

      if (total === 0) {
        const nGivenUp = gc?.given_up?.length || 0;
        if (nGivenUp > 0) {
          return `${nGivenUp} goal(s) admitted — use focus_proof to see them with hashes.`;
        }
        return 'Proof complete. Qed auto-applied.';
      }
      if (goals.length === 0 && bgGoals > 0) return `Bullet closed. ${bgGoals} goal(s) in background. Insert next { }.`;
      if (goals.length === 1) {
        if (bgGoals > 0) return `Bullet open [${bullet || '-'}]. 1 goal at focus, ${bgGoals} in background.`;
        return '1 goal. Insert a tactic.';
      }
      const summary = compactGoalSummary(gc);
      if (bgGoals > 0) return `Bullet open [${bullet || '-'}]. ${goals.length} goals at focus, ${bgGoals} in background. ${summary}`;
      return `${goals.length} goals at focus. ${summary}${bullet ? ' [bullet ' + bullet + ']' : ''}`;
    }

    function formatFeedback(fb: Array<[number, string]>): string {
      return fb.map(([lvl, msg]) => {
        const tag = lvl === 1 ? 'ERR' : lvl === 3 ? 'WARN' : lvl === 4 ? 'INFO' : 'DBG';
        return `  [${tag}] ${msg}`;
      }).join('\n');
    }

    /**
   * Query the goal hash for every addressable admit in a proof.
   * Includes tactic-level `admit.` lines AND the root `Admitted.` when
   * no tactic admits exist.  Returns one entry per admit.
   */
  async function queryAdmitHashes(
    doc: { uri: string; text: string },
    docLines: string[],
    bounds: { proofLine: number; endLine: number },
  ): Promise<Array<{ hash: string; line: number; goal: string; hyps: string }>> {
    const admitLineNums = findAdmitLines(docLines, bounds.proofLine, bounds.endLine);
    const admitted: Array<{ hash: string; line: number; goal: string; hyps: string }> = [];
    for (const line of admitLineNums) {
      try {
        const { snapLine, snapChar } = admitSnapPosition(docLines, line, bounds.proofLine);
        const stateR = await retryDocumentNotReady(() =>
          lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
            uri: doc.uri, position: { line: snapLine, character: snapChar }, opts: { memo: false },
          })
        );
        // Use compact: true for reliable goal extraction (hash computation)
        const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
          st: stateR.st, opts: { compact: true },
        });
        const goals = goalsR.goals || [];
        const goalText = goals.map((g: any) => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
        const hash = createHash('md5').update(goalText).digest('hex').slice(0, 8);
        // Also fetch hypotheses with compact: false for display
        let hyps = '';
        try {
          const goalsFullR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
            st: stateR.st, opts: { compact: false },
          });
          const fullGoal = (goalsFullR.goals || [])[0];
          if (fullGoal?.hyps) {
            hyps = (fullGoal.hyps as any[]).map((h: any) => {
              const names = Array.isArray(h.names) ? h.names.join(', ') : (h.name || '?');
              const ty = (h.ty || '').replace(/\s+/g, ' ');
              return `${names} : ${ty}`;
            }).join('; ');
          }
        } catch {}
        admitted.push({ hash, line: line + 1, goal: goalText || '(no goals)', hyps });
      } catch {
        admitted.push({ hash: 'error', line: line + 1, goal: '(could not query)', hyps: '' });
      }
    }
    return admitted;
  }

  function fileLine(file: string, line: number): string {
      const base = file.split('/').pop() || file;
      return `${base}:${line + 1}`;
    }

    try {
      switch (name) {


        case 'focus_proof': {
          const { file, name } = args as {
            file: string;
            name: string;
          };

          if (!name || !file) throw new Error('file and name are required');
          currentProof.set(file, name.trim());

          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');

          const pLine = findProofLine(docLines, name);
          if (pLine < 0) throw new Error(`Proof not found: "${name}"`);
          const position = { line: pLine, character: 0 };

          const lastPoint = insertPosition(doc.text, position);

          // Query goals — try proof/goals first (standard Coq), fall back to petanque (Iris proofmode)
          let goalsResult: GoalAnswer<string> | null = null;
          let usePetanque = false;
          try {
            goalsResult = await retryDocumentNotReady(() =>
              lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                textDocument: { uri: doc.uri, version: doc.version },
                position: lastPoint,
                pp_format: 'Str',
                mode: 'Prev',
              })
            );
            // proof/goals may succeed but return empty/null for Iris proofmode
            if (!goalsResult?.goals?.goals && !goalsResult?.goals?.stack?.length) {
              usePetanque = true;
            }
          } catch {
            usePetanque = true;
          }

          if (usePetanque) {
            // Fall back to petanque — works for Iris proofmode
            const stateR = await retryDocumentNotReady(() =>
              lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                uri: doc.uri, position: lastPoint, opts: { memo: false },
              })
            );
            const petGoalsR = await lspClient.sendRequest<any>('petanque/goals', {
              st: stateR.st, opts: { compact: false },
            });
            // Wrap in a GoalAnswer-shaped object for formatGoals
            const pg = petGoalsR?.goals ?? [];
            goalsResult = {
              textDocument: { uri: doc.uri, version: doc.version },
              position: lastPoint,
              messages: [],
              goals: { goals: pg, stack: [], bullet: undefined, shelf: [], given_up: [] },
            };
          }

          // Extract proof script from file content (no LSP query)
          let scriptLines: string[] = [];
          const allLines = doc.text.split('\n');
          const scriptEnd = insertPosition(doc.text, position);
          scriptLines = allLines.slice(position.line, scriptEnd.line);

          const gc = goalsResult?.goals;
          const goals = gc?.goals || [];
          const stack = gc?.stack || [];
          const bullet = gc?.bullet;
          const shelf = gc?.shelf || [];
          const givenUp = gc?.given_up || [];

          // Format proof tree as text
          const parts: string[] = [];
          parts.push(`${fileLine(file, position.line)}`);

          // Petanque fallback indicator
          if (usePetanque) parts.push('  (via petanque)');

          // Bullet level
          if (bullet) parts.push(`  bullet: ${bullet}`);
          parts.push(`  goals: ${goals.length} at focus`);

          // Stack levels
          if (stack.length > 0) {
            parts.push(`  stack depth: ${stack.length}`);
            for (let i = 0; i < stack.length; i++) {
              const [before, after] = stack[i];
              parts.push(`    level ${i + 1}: ${before.length} before, ${after.length} after`);
            }
          }

          // Shelved / given-up
          if (shelf.length > 0) parts.push(`  shelved: ${shelf.length}`);
          if (givenUp.length > 0) parts.push(`  given-up: ${givenUp.length}`);

          // Admit hashes — compute first so we know whether to show full goals
          const bounds = proofBounds(docLines, name);
          const admitted = bounds ? await queryAdmitHashes(doc, docLines, bounds) : [];

          // Show formatted goals when there are no tactic-level admits.
          // The full formatted goal (with hypotheses) is most useful when the LLM
          // needs to understand what to prove next. Once tactic-level admits exist,
          // the admits section covers each goal; the full block is redundant noise.
          // The root Admitted. alone (unstarted proof) still shows the full goal.
          const hasTacticAdmits = bounds
            ? findTacticAdmitLines(docLines, bounds.proofLine, bounds.endLine).length > 0
            : false;
          if (!hasTacticAdmits) {
            if (goals.length > 0) {
              const goalText = formatGoals(gc);
              parts.push('');
              parts.push(goalText);
            } else {
              parts.push('  (no goals at focus)');
            }
          }

          // Proof script
          if (scriptLines.length > 0) {
            parts.push('');
            parts.push('-- proof script ----------');
            scriptLines.forEach(l => parts.push(`  ${l}`));
          }

          // Admits section — hash, hypotheses, and goal for each open admit
          if (admitted.length > 0) {
            parts.push('');
            parts.push(`-- admits (${admitted.length}) ----------`);
            admitted.forEach(a => {
              const nGoals = a.goal ? a.goal.split(' | ').length : 1;
              const isRootAdmitted = (docLines[a.line - 1] || '').trim() === 'Admitted.';
              parts.push(`  ${a.hash}  L${a.line}:`);
              if (a.hyps) {
                parts.push(`    hyps: ${a.hyps}`);
              }
              parts.push(`    goal: ${a.goal}`);
              if (isRootAdmitted && nGoals > 1) {
                parts.push(`    ^ ${nGoals} focused goals — insert ${nGoals} brace admits ({ }) to address each individually, then use their hashes`);
              }
            });
          }

          const hint = gc ? nextHint(gc) : (bounds && (docLines[bounds.endLine] || '').trim() === 'Qed.'
            ? 'Proof complete. Qed auto-applied.'
            : 'Proof state could not be queried.');
          // If there are any admits (including petanque failures like
          // "(could not query)"), the proof is not complete even if the
          // goals query returned 0.  This happens with Iris proofmode
          // states where petanque can't snapshot but the file has real
          // admit. lines.
          const hasAnyAdmits = admitted.length > 0;
          const effectiveHint = (hasAnyAdmits && hint.startsWith('Proof complete'))
            ? `${admitted.length} admit(s) remaining.`
            : hint;
          parts.push('');
          parts.push(`next: ${effectiveHint}`);

          return reply(parts.join('\n'), {
            bullet,
            goals_at_focus: goals.length,
            stack_depth: stack.length,
            stack: stack.map(([before, after]: any) => ({
              before: before.length,
              after: after.length,
            })),
            shelved: shelf.length,
            given_up: givenUp.length,
            script: scriptLines,
            auto_removed: false,
            next: hint,
            error: goalsResult?.error || null,
          });
        }





        case 'insert_tactics': {
          const rawPos = (args as any).position as Position | undefined;
          const { file, name, tactic: rawTactic, follow_with_goals, replace, admit_hash, dry_run } = args as {
            file: string;
            name: string;
            tactic: string;
            follow_with_goals?: boolean;
            replace?: boolean;
            admit_hash?: string;
            dry_run?: boolean;
          };

          currentProof.set(file, name);

          await ensureDocumentOpened(file);
          let doc = docManager.getDocument(file)!;

          // If replacing, delete the last inserted tactic text from the file first
          let historyAlreadyPushed = false;
          if (replace) {
            const last = lastInsertion.get(file);
            if (last) {
              pushFileHistory(file, doc.text, currentProof.get(file));
              historyAlreadyPushed = true;
              const cleanedText = docManager.applyEdits(doc.text, [{
                range: last.range,
                newText: '',
              }]);
              await docManager.updateDocument(file, cleanedText);
              await docManager.saveDocument(file);
              lastInsertion.delete(file);
            }
          }

          // Resolve position from name
          let docLines = doc.text.split('\n');
          let proofLine = findProofLine(docLines, name);

          // If Proof. line is missing, try to find the theorem and inject one
          let injectedProof = false;
          if (proofLine < 0) {
            // Find the theorem/lemma declaration line
            const s = name.trim();
            let theoLine = -1;
            for (let i = 0; i < docLines.length; i++) {
              const l = docLines[i].trim();
              const kw = l.split(/\s+/)[0];
              if ((kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' || kw === 'Example') &&
                  l.includes(s + ' :')) {
                theoLine = i;
                break;
              }
            }
            if (theoLine < 0) throw new Error(`Proof not found: "${name}"`);
            // Scan from theoLine+1 to find where Proof. should go — before first non-blank content
            let insertHere = theoLine + 1;
            while (insertHere < docLines.length && (docLines[insertHere] || '').trim() === '') {
              insertHere++;
            }
            // Inject Proof. line
            const withProof = docManager.applyEdits(doc.text, [{
              range: { start: { line: insertHere, character: 0 }, end: { line: insertHere, character: 0 } },
              newText: 'Proof.\n',
            }]);
            await docManager.updateDocument(file, withProof);
            await docManager.saveDocument(file);
            // Refresh doc and retry
            doc = docManager.getDocument(file)!;
            docLines = doc.text.split('\n');
            proofLine = findProofLine(docLines, name);
            if (proofLine < 0) throw new Error(`Proof not found: "${name}"`);
            injectedProof = true;
          }

          const position = { line: proofLine, character: 0 };

          // Advance past Proof. and blank lines to the actual insert point
          let insPos: Position;
          let fromAdmitReplacement = false;
          const admitPos = lastAdmitReplaced.get(file);
          if (admitPos !== undefined) {
            insPos = { line: admitPos, character: bulletInsertPos(docLines[admitPos] || '') };
            fromAdmitReplacement = true;
            lastAdmitReplaced.delete(file);
          } else {
            insPos = insertPosition(doc.text, position);
          }

          // Handle "Proof. Admitted." on one line: split so tactic goes between them
          // and Admitted. is preserved at the end
          let oneLineSplit = false;
          if (insPos.line > 0) {
            const prev = (docLines[insPos.line - 1] || '').trim();
            if (prev.startsWith('Proof.') && prev !== 'Proof.' &&
                (prev.includes('Admitted.') || prev.includes('Qed.') || prev.includes('Defined.'))) {
              oneLineSplit = true;
              insPos = { line: insPos.line - 1, character: 0 };
            }
          }

          // Auto-bullet: query proof state to determine if bullet prefix is needed
          let tactic = rawTactic.trim();
          // Auto-`.`: append period if caller forgot it (e.g. "intros H" → "intros H.")
          if (tactic.length > 0 && !tactic.endsWith('.')) {
            tactic = tactic + '.';
          }

          // Dry-run: speculative execution only, no file modification.
          if (dry_run) {
            if (admit_hash) {
              // Hash-targeted dry run: find admit, run tactic, return result
              const docLines = doc.text.split('\n');
              const bounds = proofBounds(docLines, name);
              if (!bounds) throw new Error(`Proof not found: "${name}"`);
              const admitLines = findAdmitLines(docLines, bounds.proofLine, bounds.endLine);
              for (const line of admitLines) {
                try {
                  const { snapLine, snapChar } = admitSnapPosition(docLines, line, bounds.proofLine);
                  const stateR = await retryDocumentNotReady(() =>
                    lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                      uri: doc.uri, position: { line: snapLine, character: snapChar }, opts: { memo: false },
                    })
                  );
                  const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                    st: stateR.st, opts: { compact: true },
                  });
                  const goalText = (goalsR.goals || []).map((g: any) => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
                  const h = createHash('md5').update(goalText).digest('hex').slice(0, 8);
                  if (h !== admit_hash) continue;
                  const runResult = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
                    st: stateR.st, tac: tactic, opts: { memo: false },
                  });
                  const postGoals = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                    st: runResult.st, opts: { compact: true },
                  });
                  const nGoals = postGoals.goals?.length ?? 0;
                  const finished = runResult.proof_finished ? ' (proof finished!)' : '';
                  const goalTextOut = postGoals.goals?.length ? '\n' + formatGoals(postGoals) : '';
                  return reply(
                    `"${tactic}" at ${fileLine(file, line)} → ${nGoals} goal(s)${finished}${goalTextOut}`,
                    { state_id: runResult.st, proof_finished: runResult.proof_finished, goals: postGoals, feedback: runResult.feedback }
                  );
                } catch {}
              }
              throw new Error(`No admit found with hash "${admit_hash}"`);
            }
            // Cursor-based dry run: get state at insPos, run tactic, return result.
            // If the cursor is outside proof mode, fall back to admit lines.
            {
              let stateId: number | null = null;
              let locLine = proofLine;
              try {
                const stateR = await retryDocumentNotReady(() =>
                  lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                    uri: doc.uri, position: insPos, opts: { memo: true },
                  })
                );
                stateId = stateR.st;
              } catch {}
              if (stateId === null) {
                // Try admit lines + toplevel Admitted. as fallback
                const docLines = doc.text.split('\n');
                const bounds = proofBounds(docLines, name);
                if (bounds) {
                  // Collect all candidate positions: tactical admits + toplevel Admitted.
                  const candidates: number[] = [];
                  for (const l of findAdmitLines(docLines, bounds.proofLine, bounds.endLine)) {
                    candidates.push(l);
                  }
                  if (candidates.length === 0 && bounds.endLine > bounds.proofLine) {
                    candidates.push(bounds.endLine); // toplevel Admitted.
                  }
                  for (const line of candidates) {
                    try {
                      const { snapLine, snapChar } = admitSnapPosition(docLines, line, bounds.proofLine);
                      const sr = await retryDocumentNotReady(() =>
                        lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                          uri: doc.uri, position: { line: snapLine, character: snapChar }, opts: { memo: true },
                        })
                      );
                      const preGoals = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                        st: sr.st, opts: { compact: true },
                      });
                      if ((preGoals.goals?.length ?? 0) > 0 || line === bounds.endLine) {
                        stateId = sr.st;
                        locLine = line;
                        break;
                      }
                    } catch { continue; }
                  }
                }
              }
              if (stateId === null) {
                return reply(
                  `"${tactic}" at ${fileLine(file, proofLine)} → no active proof state found`,
                  { proof_finished: false, goals: null, feedback: [], error: 'no active proof state' }
                );
              }
              try {
                const runR = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
                  st: stateId, tac: tactic, opts: { memo: false },
                });
                const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                  st: runR.st, opts: { compact: true },
                });
                const nGoals = goalsR.goals?.length ?? 0;
                const finished = runR.proof_finished ? ' (proof finished!)' : '';
                const goalText = goalsR.goals?.length ? '\n' + formatGoals(goalsR) : '';
                return reply(
                  `"${tactic}" at ${fileLine(file, locLine)} → ${nGoals} goal(s)${finished}${goalText}`,
                  { state_id: runR.st, proof_finished: runR.proof_finished, goals: goalsR, feedback: runR.feedback }
                );
              } catch (e: any) {
                const msg = e?.message || String(e);
                return reply(
                  `"${tactic}" at ${fileLine(file, locLine)} → tactic failed: ${msg}`,
                  { proof_finished: false, goals: null, feedback: [], error: msg }
                );
              }
            }
          }

          // If admit_hash is provided, find and replace the admit with the new tactic
          if (admit_hash) {
            // Re-fetch doc to ensure we have the latest version from disk
            const freshDoc = await ensureDocumentOpened(file);
            const docLines = freshDoc.text.split('\n');
            const bounds = proofBounds(docLines, name);
            if (!bounds) throw new Error(`Proof not found: "${name}"`);
            const admitLines = findAdmitLines(docLines, bounds.proofLine, bounds.endLine);
            // Collect ALL admit lines matching this hash
            const targetLines: number[] = [];
            for (const line of admitLines) {
              try {
                const { snapLine, snapChar } = admitSnapPosition(docLines, line, bounds.proofLine);
                const stateR = await retryDocumentNotReady(() =>
                  lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                    uri: freshDoc.uri, position: { line: snapLine, character: snapChar }, opts: { memo: false },
                  })
                );
                const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                  st: stateR.st, opts: { compact: true },
                });
                const goalText = (goalsR.goals || []).map(g => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
                const h = createHash('md5').update(goalText).digest('hex').slice(0, 8);
                if (h === admit_hash) targetLines.push(line);
              } catch {}
            }
            if (targetLines.length === 0) throw new Error(`No admit found with hash "${admit_hash}"`);

            // Save parent bullet context from original document before replacement
            const origDocLines = freshDoc.text.split('\n');
            const parentBulletLine = origDocLines[targetLines[0]] || '';

            // Speculative check: run the tactic via Pétanque before modifying the file.
            // This catches Coq errors (e.g. apply with non-matching types) and avoids
            // silently sealing goals that the tactic cannot close.
            {
              const firstLine = targetLines[0];
              const { snapLine, snapChar } = admitSnapPosition(
                origDocLines, firstLine, bounds.proofLine
              );
              try {
                const stateR = await retryDocumentNotReady(() =>
                  lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                    uri: freshDoc.uri,
                    position: { line: snapLine, character: snapChar },
                    opts: { memo: false },
                  })
                );
                await lspClient.sendRequest<RunResult<number>>('petanque/run', {
                  st: stateR.st, tac: tactic, opts: { memo: false },
                });
              } catch (e: any) {
                const msg = e?.message || String(e);
                return reply(
                  `${fileLine(file, firstLine)} — tactic rejected by Coq — NOT applied\n  Coq says: ${msg}`,
                  { applied: false, error: msg }
                );
              }
            }

            // Apply tactic to ALL matching admits using shared replaceAllMatchingAdmits.
            // getGoalText calls the LSP — same function as focus_proof admits section uses.
            const preEditText = freshDoc.text;
            pushFileHistory(file, preEditText, null);
            const { text: finalText, count: totalReplaced } = await replaceAllMatchingAdmits(
              freshDoc.text, name, tactic, admit_hash,
              async (line, currentText) => {
                try {
                  const tempDoc = await docManager.updateDocument(file, currentText);
                  const currentLines = currentText.split('\n');
                  const currentBounds = proofBounds(currentLines, name);
                  const { snapLine, snapChar } = admitSnapPosition(
                    currentLines, line, currentBounds?.proofLine ?? 0
                  );
                  const stateR = await retryDocumentNotReady(() =>
                    lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                      uri: tempDoc.uri, position: { line: snapLine, character: snapChar }, opts: { memo: false },
                    })
                  );
                  const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                    st: stateR.st, opts: { compact: true },
                  });
                  return (goalsR.goals || []).map(g => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
                } catch { return null; }
              }
            );

            if (totalReplaced === 0) throw new Error(`No admit found with hash "${admit_hash}"`);
            await docManager.updateDocument(file, finalText);
            await docManager.saveDocument(file);
            const firstTargetLine = 0; // approximate — used for reply location only

            // Force LSP re-sync before querying goals
            try {
              await docManager.closeDocument(file);
              await ensureDocumentOpened(file);
            } catch {}

            // Re-seal open goals and auto-Qed using shared coq-utils helpers.
            let sealMsg = '';
            let autoQedMsg = '';
            try {
              const freshDoc = docManager.getDocument(file)!;
              const firstLine = targetLines[0];
              const docLines = finalText.split('\n');
              const tacticLines = (tactic.match(/\n/g) || []).length + 1;
              const tacticEndLine = firstLine + tacticLines - 1;
              // Query goals at the END of the last tactic line (After mode) to
              // see what goals remain directly after the tactic, not at the next bullet.
              const tacticEndChar = (docLines[tacticEndLine] || '').length;
               const goalsR = await retryDocumentNotReady(() =>
                 lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                   textDocument: { uri: freshDoc.uri, version: freshDoc.version },
                   position: { line: tacticEndLine, character: tacticEndChar },
                   pp_format: 'Str', mode: 'After',
                 })
               );
               // Check for tactic errors — roll back and report instead of sealing.
               const tacticErrors = (goalsR?.messages || []).filter((m: any) => m.level === 1);
               if (tacticErrors.length > 0) {
                 await docManager.updateDocument(file, preEditText);
                 await docManager.saveDocument(file);
                 const errMsg = tacticErrors.map((m: any) => m.text || m.message).join('; ');
                 return reply(
                   `${fileLine(file, targetLines[0])} — tactic error — rolled back\n  Coq says: ${errMsg}`,
                   { applied: false, error: errMsg, rolled_back: true }
                 );
               }
               const nF = goalsR?.goals?.goals?.length ?? 0;
              const nBgAfter = (goalsR?.goals?.stack || []).reduce(
                (s: number, [b, a]: any[]) => s + (b?.length || 0) + (a?.length || 0), 0
              );
              // Re-seal if the tactic left focused goals open at the tactic end position.
              if (nF > 0) {
                const goals = goalsR?.goals?.goals || [];
                const sealHashes = goals.map((g: any) => {
                  const goalText = (g.ty || '').replace(/\s+/g, ' ');
                  return createHash('md5').update(goalText).digest('hex').slice(0, 8);
                });
                const { text: sealed, sealMsg: msg } = sealOpenGoals(
                  finalText, tacticEndLine, nF, parentBulletLine, sealHashes
                );
                sealMsg = ` (${msg})`;
                await docManager.updateDocument(file, sealed);
                await docManager.saveDocument(file);
              }
            } catch { /* best-effort */ }

            try {
              const currentDoc = docManager.getDocument(file)!;
              const currentLines = currentDoc.text.split('\n');
              const currentBounds = proofBounds(currentLines, name);
              // Before auto-Qed, check there are no focused goals remaining at Admitted.
              // applyAutoQed only checks for tactic-level admit. lines, not focused goals.
              let hasFocusedGoals = false;
              if (currentBounds) {
                const admittedLine = currentBounds.endLine;
                if (currentLines[admittedLine]?.trim() === 'Admitted.') {
                  try {
                    const { snapLine: sl, snapChar: sc } = admitSnapPosition(
                      currentLines, admittedLine, currentBounds.proofLine
                    );
                    const sR = await retryDocumentNotReady(() =>
                      lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                        uri: currentDoc.uri, position: { line: sl, character: sc }, opts: { memo: false },
                      })
                    );
                    const gR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                      st: sR.st, opts: { compact: true },
                    });
                    const nFocused = gR.goals?.length ?? 0;
                    const nBg = (gR.stack || []).reduce(
                      (s: number, [b, a]: any[]) => s + (b?.length || 0) + (a?.length || 0), 0
                    );
                    hasFocusedGoals = nFocused > 0 || nBg > 0;
                  } catch {}
                }
              }
              if (!hasFocusedGoals) {
                const { text: qedText, applied } = applyAutoQed(currentDoc.text, name);
                if (applied) {
                  await docManager.updateDocument(file, qedText);
                  await docManager.saveDocument(file);
                  autoQedMsg = ' — Qed applied';
                }
              }
            } catch { /* best-effort */ }

            const n = targetLines.length;
            let remainingMsg = '';
            let currentGoalMsg = '';
            try {
              const finalDoc = docManager.getDocument(file)!;
              const finalLines = finalDoc.text.split('\n');
              const finalBounds = proofBounds(finalLines, name);
              if (finalBounds) {
                // Current goal at insertion point
                const queryLine = Math.min(targetLines[0] + (tactic.match(/\n/g) || []).length, finalLines.length - 1);
                try {
                  const goalR = await retryDocumentNotReady(() =>
                    lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                      textDocument: { uri: finalDoc.uri, version: finalDoc.version },
                      position: { line: queryLine, character: (finalLines[queryLine] || '').length },
                      pp_format: 'Str', mode: 'After',
                    })
                  );
                  const goals = goalR?.goals?.goals || [];
                  if (goals.length > 0) {
                    currentGoalMsg = '\ncurrent: ' + goals.map((g: any) => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
                  }
                } catch {}

                // Remaining admits — show hash, hyps, and goal for each
                const admitLines = findAdmitLines(finalLines, finalBounds.proofLine, finalBounds.endLine);
                if (admitLines.length > 0) {
                  const remaining: string[] = [];
                  for (const line of admitLines) {
                    try {
                      const { snapLine, snapChar } = admitSnapPosition(finalLines, line, finalBounds.proofLine);
                      const stateR = await retryDocumentNotReady(() =>
                        lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                          uri: finalDoc.uri,
                          position: { line: snapLine, character: snapChar },
                          opts: { memo: false },
                        })
                      );
                      const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                        st: stateR.st, opts: { compact: true },
                      });
                      const goals = goalsR.goals || [];
                      const goalText = goals.map((g: any) => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
                      const hash = createHash("md5").update(goalText).digest("hex").slice(0, 8);
                      let hyps = '';
                      try {
                        const goalsFullR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                          st: stateR.st, opts: { compact: false },
                        });
                        const fullGoal = (goalsFullR.goals || [])[0];
                        if (fullGoal?.hyps) {
                          hyps = (fullGoal.hyps as any[]).map((h: any) => {
                            const names = Array.isArray(h.names) ? h.names.join(', ') : (h.name || '?');
                            const ty = (h.ty || '').replace(/\s+/g, ' ');
                            return `${names} : ${ty}`;
                          }).join('; ');
                        }
                      } catch {}
                      remaining.push(`${hash}  L${line + 1}:`);
                      if (hyps) remaining.push(`  hyps: ${hyps}`);
                      remaining.push(`  goal: ${goalText || '(no goals)'}`);
                    } catch {
                      remaining.push(`error  L${line + 1}: (could not query)`);
                    }
                  }
                  remainingMsg = `\n${admitLines.length} admit(s) remaining:\n` + remaining.join('\n');
                } else if (autoQedMsg === '') {
                  remainingMsg = '\n0 admits remaining';
                }
              }
            } catch {}

            return reply(
              `${fileLine(file, targetLines[0])} — replaced ${n} admit(s) with "${tactic.trim()}"${sealMsg}${autoQedMsg}${currentGoalMsg}${remainingMsg}`,
              { applied: true, count: n }
            );
          }


          // Determine whether the user already supplied a bullet prefix.
          // Used both inside and outside the bullet-logic try block.
          const tacticFirstWord = tactic.split(/\s+/)[0];
          const hasBullet = /^[-+*]+$/.test(tacticFirstWord) || tacticFirstWord === '{';

          if (!fromAdmitReplacement) {
          try {
            // Query at end of previous non-blank line to get correct stack depth
            // after bullet closure (insPos is the start of a blank/clean line,
            // which still reports the previous bullet context as active in Prev mode)
            let queryLine = insPos.line - 1;
            while (queryLine >= 0 && (docLines[queryLine] || '').trim() === '') {
              queryLine--;
            }
            const queryPos = queryLine >= 0
              ? { line: queryLine, character: (docLines[queryLine] || '').length }
              : insPos;
            const stateResult = await retryDocumentNotReady(() =>
              lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                textDocument: { uri: doc.uri, version: doc.version },
                position: queryPos,
                pp_format: 'Str',
                mode: 'After',
              })
            );
            const bgCount = (stateResult.goals?.stack || []).reduce(
              (s: number, [b, a]: any[]) => s + (b?.length || 0) + (a?.length || 0), 0
            );
            const focusedGoals = stateResult.goals?.goals?.length || 0;
            const totalRemaining = focusedGoals + bgCount;
            const lspBullet = stateResult.goals?.bullet;
            const lspBulletChar = bulletTokenFromMessage(lspBullet);
            const lspSuggestsNext = !!lspBullet?.includes('Focus next goal');
            const lspUnfinished = !!lspBullet?.includes('unfinished') || !!lspBullet?.includes('not finished');
            let bullet: string | undefined;

            const atLineStart = insPos.character === 0;
            let indent = '';

            if (lspSuggestsNext && lspBulletChar) {
              // Coq says a sibling/current-level bullet is mandatory — use brace.
              bullet = '{';
              const suggestedIndent = findLastBulletIndent(docLines, insPos.line, proofLine, bullet);
              indent = ' '.repeat(suggestedIndent ?? 0);
            } else if (lspUnfinished && lspBulletChar && focusedGoals > 1) {
              // Current bullet has multiple focused goals. Open a child brace.
              bullet = '{';
              const parentIndent = findLastBulletIndent(docLines, insPos.line, proofLine, lspBulletChar)
                ?? computeBulletIndent(doc.text, insPos, proofLine).length;
              indent = ' '.repeat(parentIndent + 2);
            } else if (!lspBullet && totalRemaining > 1 && !hasBullet && computeBulletIndent(doc.text, insPos, proofLine)) {
              // Inside an existing bullet structure with no active bullet context —
              // auto-open the next sibling with brace.
              bullet = '{';
              indent = '';
            } else if (atLineStart) {
              indent = computeBulletIndent(doc.text, insPos, proofLine);
            }

            if (bullet && !hasBullet && tactic !== 'Qed.' && tactic !== 'Defined.' && tactic !== 'Admitted.') {
              tactic = `${indent}${bullet} ${tactic}`;
            } else if (atLineStart) {
              tactic = `${indent}${tactic}`;
            }

          } catch {
            // state query is best-effort for bullets
          }
          }

          // Speculative check: run tactic via Pétanque before editing the file.
          // If it fails, report the Coq error without modifying the file.
          // If it succeeds, show the resulting goals before committing.
          let speculativeError: string | null = null;
          let specGoals: GoalConfig<string> | null = null;
          let specFinished = false;
          try {
            const stateResult = await retryDocumentNotReady(() =>
              lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                uri: doc.uri,
                position: insPos,
                opts: { memo: false },
              })
            );
            const runResult = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
              st: stateResult.st,
              tac: tactic,
              opts: { memo: false },
            });
            // Query resulting goals to preview what the tactic will do
            try {
              const g = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                st: runResult.st,
                opts: { compact: true },
              });
              specGoals = g;
              specFinished = runResult.proof_finished;
            } catch {
              // goal query is best-effort
            }
          } catch (e: any) {
            const msg = e?.message || String(e);
            if (msg.includes('timeout') || msg.includes('Timeout')) {
              speculativeError = `proof check timed out — tactic may be too slow. Try a simpler tactic or split into steps.`;
            } else if (msg.includes('illegal begin of vernac') ||
                msg.includes('No proof-editing in progress') ||
                msg.includes('proof-editing') ||
                (tactic === 'Qed.' || tactic === 'Defined.' || tactic === 'Admitted.')) {
              // Allow Qed, Admitted, and proof-mode guard errors to pass through
            } else if (msg.includes('No more subgoals') || msg.includes('No focused proof') ||
                       msg.includes('nothing to admit')) {
              // admit. with no open goal — reject
              speculativeError = msg;
            } else {
              speculativeError = msg;
            }
          }

          if (speculativeError) {
            return reply(
              `${fileLine(file, proofLine)} — spec check FAILED: \"${tactic}\"\n  Coq says: ${speculativeError}`,
              { applied: false, error: speculativeError, tactic }
            );
          }

          // Build preview from spec goals
          let specPreview = '';
          if (specGoals) {
            const nSpecGoals = specGoals.goals?.length || 0;
            const specSummary = compactGoalSummary(specGoals);
            if (specFinished) {
              specPreview = '  (proof finished — Qed will be accepted)';
            } else if (nSpecGoals === 1 && specGoals.goals[0]) {
              const g = specGoals.goals[0];
              const hypsFormatted = (g.hyps || []).map((h: any) => {
                const names = h.names ? h.names.join(', ') : (h.name || '?');
                const ty = (h.ty || '').replace(/\s+/g, ' ');
                return `  ${names} : ${ty}`;
              }).join('\n');
              const goalTy = (g.ty || '').replace(/\s+/g, ' ');
              specPreview = `  (after tactic — 1 goal):\n${hypsFormatted}\n  ⊢ ${goalTy}`;
            } else if (nSpecGoals > 0) {
              specPreview = `  (${nSpecGoals} goal(s) after: ${specSummary})`;
            } else {
              specPreview = `  (${specSummary || 'no open goals'})`;
            }
          }

          // Insert tactic at insert point
          let insertText: string;
          let editEnd: Position;
          if (oneLineSplit) {
            insertText = `Proof.\n${tactic}\nAdmitted.\n`;
            editEnd = { line: insPos.line + 1, character: 0 };
          } else {
            insertText = tactic.endsWith('\n') ? `${tactic}\n` : `${tactic}\n`;
            const curLine = (docLines[insPos.line] || '').trim();
            editEnd = (tactic === 'Qed.' && (curLine === 'Admitted.' || curLine === 'Qed.' || curLine === 'Defined.'))
              ? { line: insPos.line, character: (docLines[insPos.line] || '').length }
              : insPos;
          }
          const insertLines = insertText.split('\n');
          const contentLines = insertLines.slice(0, -1); // exclude trailing empty from \n
          const lastIdx = contentLines.length - 1;
          const insertedLinesCount = contentLines.length;
          const insertedUntil: Position = {
            line: insPos.line + insertedLinesCount,
            character: 0,
          };
          const nextTacticPosition: Position = {
            line: insPos.line + lastIdx,
            character: lastIdx === 0
              ? (insPos.character || 0) + contentLines[0].length
              : contentLines[lastIdx].length,
          };
          if (!historyAlreadyPushed) {
            pushFileHistory(file, doc.text, currentProof.get(file));
          }
          const preEditVersion = doc.version;
          const preEditText = doc.text;

          const newText = docManager.applyEdits(doc.text, [
            {
              range: {
                start: insPos,
                end: editEnd,
              },
              newText: insertText,
            },
          ]);

          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          let goals = null;
          if (follow_with_goals ?? true) {
            try {
              const updatedDoc = docManager.getDocument(file)!;
              const goalsQueryPos = safePos({ line: insertedUntil.line, character: 0 }, updatedDoc.text);
              const goalsResult = await retryDocumentNotReady(() =>
                lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                  textDocument: {
                    uri: updatedDoc.uri,
                    version: updatedDoc.version,
                  },
                  position: goalsQueryPos,
                  pp_format: 'Str',
                  mode: 'Prev',
                })
              );
              if (goalsResult.error) {
                console.error('Goals query error:', goalsResult.error);
              }
              goals = goalsResult;
              
            } catch (err) {
              console.error('Failed to get goals:', err);
            }
          }

          // If goals query failed, roll back the tactic insertion.
          // A slow tactic may have been inserted but the state is unknown.
          const gcAfter = goals?.goals;
          if (!gcAfter && !oneLineSplit) {
            await docManager.updateDocument(file, preEditText);
            await docManager.saveDocument(file);
            return reply(
              `${fileLine(file, position.line)} — inserted "${tactic.trim()}" but goals query failed — tactic rolled back`,
              { applied: false, error: 'goals query failed after insertion', rolled_back: true }
            );
          }

          // If the tactic produced Coq errors (e.g. mid-line reference error
          // in a multi-tactic one-liner), roll back and report the error.
          const hasErrors = (goals?.messages || []).some((m: any) => m.level === 1);
          if (hasErrors) {
            const errMsg = (goals?.messages || []).filter((m: any) => m.level === 1).map((m: any) => m.text || m.message).join('; ');
            await docManager.updateDocument(file, preEditText);
            await docManager.saveDocument(file);
            return reply(
              `${fileLine(file, position.line)} — tactic error — rolled back\n  Coq says: ${errMsg}`,
              { applied: false, error: errMsg, rolled_back: true }
            );
          }
          const nFocus = gcAfter?.goals?.length ?? 0;
          const nBg = (gcAfter?.stack || []).reduce(
            (s: number, [b, a]: any[]) => s + (b?.length || 0) + (a?.length || 0), 0
          );
          const nGivenUp = gcAfter?.given_up?.length ?? 0;

          const hint = gcAfter ? nextHint(gcAfter) : '';

          const stateMsg = goals?.error
            ? `error: ${goals?.error}`
            : oneLineSplit ? 'inserted'
            : gcAfter === undefined || gcAfter === null
            ? 'goals query failed'
            : nFocus === 0 && nBg === 0 ? 'done — Qed applied'
            : nFocus === 0 && nGivenUp > 0 ? `bullet closed (${nGivenUp} admitted), ${nBg} in background`
            : nFocus === 0 ? `bullet closed, ${nBg} in background`
            : nBg > 0 ? `${nFocus} at focus, ${nBg} in background (bullet open)`
            : `${nFocus} goal(s)`;

          // Auto-close: when all focused + background goals are done,
          // replace Admitted. with Qed.  We deliberately don't block on
          // nGivenUp because the petanque API can report false positives
          // for given-up goals (e.g. { } blocks after rewrite).
          // The real gate is applyAutoQed, which checks for text-level
          // admit. lines inside the proof.
          const canAutoClose = nFocus === 0 && nBg === 0 &&
            gcAfter !== undefined && gcAfter !== null && !hasErrors;
          if (canAutoClose) {
            try {
              const currentDoc = docManager.getDocument(file)!;
              const { text: qedText, applied } = applyAutoQed(currentDoc.text, name);
              if (applied) {
                await docManager.updateDocument(file, qedText);
                await docManager.saveDocument(file);
              }
            } catch { /* best-effort */ }
          }

          // Extract proof script for context
          const scriptLines: string[] = [];
          {
            const fLines = doc.text.split('\n');
            let pl = insertedUntil.line;
            for (; pl >= 0; pl--) {
              const t = (fLines[pl] || '').trim();
              if (t === 'Proof.' || t.startsWith('Proof. ')) break;
            }
            if (pl >= 0) {
              for (let i = pl + 1; i <= insertedUntil.line; i++) {
                const l = fLines[i];
                if (!l) continue;
                const t = l.trim();
                if (t === '' || t === 'Proof.') continue;
                if (isSkipLine(l)) continue;
                if (isTopLevelLine(l)) break;
                scriptLines.push(l);
              }
            }
          }
          const scriptBlock = scriptLines.length > 0
            ? '\n-- proof script ----------\n' + scriptLines.map(l => `  ${l}`).join('\n')
            : '';

          // Build a focused goals object for the reply — strip background (stack) goals
          // to avoid confusing the display with Admitted-continuation state.
          let focusedGoals = goals?.goals || null;
          if (focusedGoals && nBg > 0) {
            focusedGoals = { ...focusedGoals, stack: [] };
          }

          // Compact summary of the new focus state for the response text
          const focusSummary = gcAfter ? compactGoalSummary(gcAfter) : '';

          // Store this insertion for potential replace:true retry
          lastInsertion.set(file, {
            range: { start: insPos, end: nextTacticPosition },
          });

          const summary = `${fileLine(file, position.line)} — inserted "${tactic.trim()}" → ${stateMsg}` +
            `${specPreview ? '\n' + specPreview : ''}${focusSummary ? '\n  ' + focusSummary : ''}${scriptBlock}${hint ? '\n  next: ' + hint : ''}`;

          return reply(summary,
            {
              applied: true,
              inserted_until: insertedUntil,
              next_tactic_position: nextTacticPosition,
              next: hint,
              goals: focusedGoals,
              script: scriptLines,
              messages: goals?.messages || [],
              error: goals?.error || null,
            }
          );
        }

        case 'check_file': {
          const { file, start_line, count, timeout_ms, retry_timeout_ms } = args as { file: string; start_line?: number; count?: number; timeout_ms?: number; retry_timeout_ms?: number };

          try {
            const doc = await ensureDocumentOpened(file);
            const reqTimeout = timeout_ms ?? 15000;
            const retryOpts = retry_timeout_ms !== undefined ? { timeoutMs: retry_timeout_ms } : undefined;

            const result = await retryDocumentNotReady(() =>
              lspClient.sendRequest<{
                spans: Array<{ range: Range }>;
                completed: { status: string; range: Range };
              }>('coq/getDocument', {
                textDocument: {
                  uri: doc.uri,
                  version: doc.version,
                },
                ast: false,
                goals: 'Str',
              }, reqTimeout),
              retryOpts
            );

            const spanCount = result.spans?.length || 0;
            const range = result.completed?.range;
            const loc = range ? `L${range.start.line}-L${range.end.line}` : '?';

            // Count Admitted. occurrences and locate them
            const docLines = doc.text.split('\n');
            let admittedCount = 0;
            const admittedAt: number[] = [];
            const admittedGoals: string[] = [];
            for (let i = 0; i < docLines.length; i++) {
              if (docLines[i].trim() === 'Admitted.') { admittedCount++; admittedAt.push(i); }
            }
            // For each admitted position, query the proof goals to report what remains.
            for (const line of admittedAt) {
              try {
                const gResult = await retryDocumentNotReady(() =>
                  lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                    textDocument: { uri: doc.uri, version: doc.version },
                    position: { line, character: 0 },
                    pp_format: 'Str',
                    mode: 'Prev',
                  }, reqTimeout),
                  retryOpts
                );
                const nG = gResult.goals?.goals?.length || 0;
                if (nG > 0) {
                  admittedGoals.push(`L${line + 1}: ${nG} goal(s)`);
                }
              } catch {}
            }

            const admittedInfo = admittedCount > 0
              ? `, ${admittedCount} admitted (${admittedAt.map(l => l + 1).join(', ')})` +
                (admittedGoals.length > 0 ? ` — ${admittedGoals.join(', ')}` : '')
              : '';

            // Summary: scan file for toplevel names, status, and line ranges
            const PROOF_KWS = ['Lemma', 'Theorem', 'Corollary', 'Example'];
            const DEF_KWS = ['Definition', 'Fixpoint', 'Inductive'];
            const ALL_KWS = [...PROOF_KWS, ...DEF_KWS];
            const items: Array<{ text: string; startLine: number }> = [];
            for (let i = 0; i < docLines.length; i++) {
              const l = docLines[i].trim();
              const kw = l.split(/\s+/)[0];
              const isDef = DEF_KWS.includes(kw);
              const isProof = PROOF_KWS.includes(kw);
              if (isDef || isProof) {
                // Extract bare name: first non-keyword word before : or :=
                const afterKw = l.slice(l.indexOf(kw) + kw.length).trim();
                const nameMatch = afterKw.match(/^([^\s(:]+)/);
                const namePart = nameMatch ? nameMatch[1] : afterKw.split(':')[0].replace(kw, '').trim();
                // Find end line
                let endLine = i;
                for (let j = i + 1; j < docLines.length; j++) {
                  const t = docLines[j].trim();
                  // Terminators
                  if (t === 'Qed.' || t === 'Admitted.' || t === 'Defined.') { endLine = j; break; }
                  // Inline termination (e.g. "Proof. exact I. Qed.")
                  if (isProof && /\bQed\.\s*$/.test(t)) { endLine = j; break; }
                  if (isProof && /\bAdmitted\.\s*$/.test(t)) { endLine = j; break; }
                  // Next top-level: for definitions stop immediately; for proofs use guard
                  if (isTopLevelLine(docLines[j] || '')) {
                    if (isDef || j > i + 20) { endLine = j - 1; break; }
                  }
                  if (j === docLines.length - 1) { endLine = j; }
                }
                // Status discovery
                let status = '?';
                for (let j = i; j <= endLine; j++) {
                  const t = docLines[j].trim();
                  if (t === 'Qed.' || /\bQed\.\s*$/.test(t)) { status = 'Qed'; break; }
                  if (t === 'Admitted.' || /\bAdmitted\.\s*$/.test(t)) { status = 'Admitted'; break; }
                }
                if (isDef && status === '?') status = 'open';
                if (!isDef && !isProof) status = 'open';
                const rangeStr = `L${i}-L${endLine}`;
                let entry: string;
                if (isDef) {
                  entry = `${kw} ${namePart} [${rangeStr}] [${status}]`;
                } else {
                  const colonIdx = l.indexOf(':');
                  let typeStr = '';
                  if (colonIdx >= 0) {
                    typeStr = l.slice(colonIdx + 1).trim();
                    for (let c = i + 1; c < endLine; c++) {
                      const cl = docLines[c].trim();
                      if (!cl || cl === 'Proof.') break;
                      typeStr += ' ' + cl;
                    }
                    typeStr = typeStr.replace(/\.$/, '').trim();
                  }
                  if (typeStr.length > 120) typeStr = typeStr.slice(0, 117) + '...';
                  entry = `${kw} ${namePart} : ${typeStr || '?'} [${rangeStr}] [${status}]`;
                }
                items.push({ text: entry, startLine: i });
                i = endLine;
              }
            }

            // Paginate with boundary expansion
            const MAX_ITEMS = 40;
            let startIdx = 0;
            let endIdx = items.length;
            let paginated = false;
            if (start_line !== undefined && count !== undefined && count > 0) {
              paginated = true;
              startIdx = items.findIndex(it => it.startLine >= start_line);
              if (startIdx < 0) startIdx = items.length;
              while (startIdx > 0 && items[startIdx]?.startLine > start_line) startIdx--;
              endIdx = Math.min(items.length, startIdx + count);
            }
            const pageItems = items.slice(startIdx, endIdx);
            const truncated = paginated ? endIdx < items.length : items.length > MAX_ITEMS;

            const summary = pageItems.length > 0
              ? (paginated
                  ? `\n[${startIdx}-${endIdx-1}/${items.length}]` +
                    (truncated ? ` (more after L${items[endIdx]?.startLine ?? 0})` : '')
                  : (items.length > MAX_ITEMS
                      ? `\n[0-${pageItems.length-1}/${items.length}] (truncated at ${MAX_ITEMS} items)`
                      : ''))
                + '\n' + pageItems.map(it => it.text).join('\n')
              : (items.length > 0 ? `\n${items.length} items total (use count parameter to paginate)` : '');

            return reply(
              `${fileLine(file, 0)} — ${result.completed?.status || 'unknown'}, ${spanCount} spans (${loc}) [ws: ${activeWorkspaceRoot}]` + admittedInfo + summary,
              { file, completed: result.completed?.status, span_count: spanCount, completed_range: loc, admitted: admittedCount, admitted_lines: admittedAt, success: true, workspace_root: activeWorkspaceRoot }
            );
          } catch (error) {
            return err(
              `${fileLine(file, 0)} — check failed: ${error instanceof Error ? error.message : String(error)}`,
              error instanceof Error ? error.message : String(error)
            );
          }
        }


        case 'search_lemmas': {
          const { file, pattern } = args as {
            file: string;
            pattern: string;
          };

          const doc = await ensureDocumentOpened(file);

          const docInfo = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc.uri, version: doc.version },
              ast: false,
            })
          );

          const targetPos: Position =
            (docInfo.spans && docInfo.spans.length > 0)
              ? docInfo.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc.uri,
              position: targetPos,
              opts: { memo: true, hash: true },
            })
          );

          // Run pending speculative imports, then the query
          const searchSt = await runPendingImports(doc.uri, stateResult.st);

          // Pass pattern to Coq's Search command.
          // Simple identifiers get quoted string search: Search "plus_n_O".
          // Patterns like "_ + 0 = _" need to be wrapped in parens: Search (_ + 0 = _).
          // Other forms like "leb" or "leb_le : ..." pass through as-is.
          const searchText = (() => {
            if (/^[a-zA-Z_][a-zA-Z0-9_']*$/.test(pattern))
              return `Search "${pattern}".`;
            if (/^_ [^:]+ _/.test(pattern) && !pattern.startsWith('('))
              return `Search (${pattern}).`;
            return `Search ${pattern}.`;
          })();

          let runResult: RunResult<number>;
          let errorMsg: string | null = null;
          try {
            runResult = await lspClient.sendRequest<RunResult<number>>(
              'petanque/run',
              { st: searchSt, tac: searchText, opts: { memo: false, hash: false } }
            );
          } catch (e: any) {
            // Try fallback: if the literal form failed and pattern has quotes, try without
            errorMsg = e?.message || String(e);
            runResult = { st: stateResult.st, proof_finished: false, feedback: [] };
          }

          const msgs = (runResult.feedback || []).map(([level, msg]: [number, string]) => ({ level, message: msg }));
          const results = msgs.length > 0
            ? msgs.map(m => m.message).join('\n')
            : errorMsg || '(no results)';
          return reply(
            `Search "${pattern}" → ${msgs.length} result(s)\n${results}`,
            { messages: msgs, error: errorMsg }
          );
        }

        case 'inspect_term': {
          const { file, term } = args as {
            file: string;
            term: string;
          };

          const doc3 = await ensureDocumentOpened(file);

          const docInfo3 = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc3.uri, version: doc3.version },
              ast: false,
            })
          );

          const targetPos3: Position =
            (docInfo3.spans && docInfo3.spans.length > 0)
              ? docInfo3.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult3 = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc3.uri,
              position: targetPos3,
              opts: { memo: true, hash: true },
            })
          );

          const checkSt = await runPendingImports(doc3.uri, stateResult3.st);

          const runResult3 = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
            st: checkSt,
            tac: `Check ${term}.`,
            opts: { memo: false, hash: false },
          });

          const msgs3 = runResult3.feedback.map(([level, msg]) => ({ level, message: msg }));
          return reply(
            `Check ${term} → ${msgs3.length} message(s): ${msgs3.map(m => m.message).join('; ')}`,
            { messages: msgs3 }
          );
        }

        case 'inspect_about': {
          const { file, term } = args as {
            file: string;
            term: string;
          };

          const doc4 = await ensureDocumentOpened(file);

          const docInfo4 = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc4.uri, version: doc4.version },
              ast: false,
            })
          );

          const targetPos4: Position =
            (docInfo4.spans && docInfo4.spans.length > 0)
              ? docInfo4.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult4 = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc4.uri,
              position: targetPos4,
              opts: { memo: true, hash: true },
            })
          );

          const aboutSt = await runPendingImports(doc4.uri, stateResult4.st);

          const runResult4 = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
            st: aboutSt,
            tac: `About ${term}.`,
            opts: { memo: false, hash: false },
          });

          const msgs4 = runResult4.feedback.map(([level, msg]) => ({ level, message: msg }));
          return reply(
            `About ${term} → ${msgs4.length} message(s): ${msgs4.map(m => m.message).join('; ')}`,
            { messages: msgs4 }
          );
        }


        case 'stratify': {
          const { file, name, skeleton, portfolio, cases_from, write, attempt_timeout_ms, admit_hash } = args as {
            file: string; name: string; skeleton: string; portfolio: string[];
            cases_from?: string; write?: boolean; attempt_timeout_ms?: number;
            admit_hash?: string;
          };
          currentProof.set(file, name);
          const attemptTimeout = attempt_timeout_ms ?? 10_000;
          let skel = skeleton.trim();
          if (skel.length > 0 && !skel.endsWith('.')) skel += '.';
          const entries = (portfolio || []).map(p => { let s = p.trim(); while (s.endsWith('.')) s = s.slice(0, -1).trim(); return s; }).filter(s => s.length > 0);
          if (entries.length === 0) throw new Error('stratify: portfolio is empty');

          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');
          const bounds = proofBounds(docLines, name);
          if (!bounds) throw new Error(`Proof not found or unterminated: "${name}"`);
          // Nested mode: locate the surviving admit by hash and stratify inside it.
          let targetAdmitLine = -1;
          if (admit_hash) {
            const admits = await queryAdmitHashes(doc, docLines, bounds);
            const match = admits.find(a => a.hash === admit_hash);
            if (!match) {
              const known = admits.map(a => a.hash).join(', ');
              return err(`stratify ${name}: no admit found with hash "${admit_hash}" (known: ${known || 'none'})`);
            }
            targetAdmitLine = match.line - 1; // queryAdmitHashes lines are 1-based
          }
          // Use admitSnapPosition — snaps just before the target admit (nested
          // mode) or just before Admitted. (whole-proof mode), inside proof mode.
          const { snapLine, snapChar } = admitSnapPosition(
            docLines, admit_hash ? targetAdmitLine : bounds.endLine, bounds.proofLine);
          const pos = { line: snapLine, character: snapChar };
          const uri = doc.uri;

          const baseState = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri, position: pos, opts: { memo: true, hash: true },
            })
          );
          const baseSt = await runPendingImports(uri, baseState.st);
          let skelRun: RunResult<number>;
          try { skelRun = await lspClient.sendRequest<RunResult<number>>('petanque/run', { st: baseSt, tac: skel, opts: { memo: true, hash: true } }); }
          catch (e: any) {
            const rawMsg: string = e?.message ?? String(e);
            // Check for variable name conflicts in the skeleton
            if (rawMsg.includes('already used') || rawMsg.includes('already exists')) {
              const clash = rawMsg.match(/['"]?(\w+)['"]?\s+is already used/i)?.[1]
                || rawMsg.match(/identifier\s+['"]?(\w+)['"]?/i)?.[1];
              const hint = clash
                ? `\n  The skeleton introduces "${clash}" which clashes with a name in the lemma statement. Rename this variable in your skeleton (e.g. use "${clash}0" instead).`
                : '\n  A variable name in the skeleton clashes with the lemma statement. Rename the conflicting variable.';
              return err(`stratify ${name}: skeleton failed: ${rawMsg}${hint}`);
            }
            return err(`stratify ${name}: skeleton failed: ${rawMsg}`);
          }
          const skelGoals = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', { st: skelRun.st, opts: { compact: true } });
          const goals = skelGoals.goals || [];
          const nGoals = goals.length;

          // Compute goal hashes — same MD5 as queryAdmitHashes.
          // Embedded in { (* Name:hash *) admit. } so consumers can
          // identify which admits correspond to which re-runnable goals.
          const { createHash } = await import('crypto');
          const goalHashes = goals.map(g => {
            const ty = ((g as any)?.ty || '').replace(/\s+/g, ' ');
            return createHash('md5').update(ty).digest('hex').slice(0, 8);
          });

          // Constructor names for labels (best-effort)
          let caseNames: string[] = [];
          if (cases_from) {
            try {
              const pr = await lspClient.sendRequest<RunResult<number>>('petanque/run', { st: baseSt, tac: `Print ${cases_from}.`, opts: { memo: true, hash: false } });
              const text = (pr.feedback || []).map(([, m]: any) => m).join('\n');
              const idx = text.indexOf(':=');
              if (idx >= 0) {
                const body = text.slice(idx + 2);
                const first = body.match(/^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:/);
                if (first) caseNames.push(first[1]);
                const re = /\n\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)\s*:/g;
                let m: RegExpExecArray | null;
                while ((m = re.exec(body)) !== null) caseNames.push(m[1]);
              }
            } catch {}
          }
          const labelled = caseNames.length === nGoals;
          const nameOf = (i: number) => labelled ? caseNames[i] : `case_${i + 1}`;

          // Portfolio: each subgoal independently, via goal selectors
          const wins: Array<number | null> = [];
          for (let i = 0; i < nGoals; i++) {
            let win: number | null = null;
            for (let k = 0; k < entries.length; k++) {
              const sel = `${i + 1}: solve [ ${entries[k]} ].`;
              try {
                await lspClient.sendRequest<RunResult<number>>('petanque/run', { st: skelRun.st, tac: sel, opts: { memo: true, hash: true } }, attemptTimeout);
                win = k; break;
              } catch {}
            }
            wins.push(win);
          }

          // Materialize
          const survivors: number[] = [];
          const bodyLines: string[] = [];
          let editRange: { start: Position; end: Position };
          if (admit_hash) {
            // Nested mode: replace the single "{ (* Label:hash *) admit. }" line
            // with the skeleton followed by one nested block per subgoal.
            const lineText = docLines[targetAdmitLine] || '';
            const m = lineText.match(/^(\s*)(.*?)\badmit\.\s*(\})?\s*$/);
            const indent = m ? m[1] : '';
            const pre = m ? m[2] : '';
            const hasClose = !!(m && m[3]);
            const sub = indent + '  ';
            bodyLines.push(`${indent}${pre}${skel}`);
            for (let i = 0; i < nGoals; i++) {
              if (wins[i] !== null) bodyLines.push(`${sub}{ (* ${nameOf(i)}:${goalHashes[i]} *) solve [ ${entries[wins[i]!]} ]. }`);
              else { survivors.push(i); bodyLines.push(`${sub}{ (* ${nameOf(i)}:${goalHashes[i]} *) admit. }`); }
            }
            if (hasClose) bodyLines.push(`${indent}}`);
            editRange = {
              start: { line: targetAdmitLine, character: 0 },
              end: { line: targetAdmitLine + 1, character: 0 },
            };
          } else {
            // Whole-proof mode: replace the body from after Proof. to Admitted.
            bodyLines.push('  ' + skel);
            for (let i = 0; i < nGoals; i++) {
              if (wins[i] !== null) bodyLines.push(`  { (* ${nameOf(i)}:${goalHashes[i]} *) solve [ ${entries[wins[i]!]} ]. }`);
              else { survivors.push(i); bodyLines.push(`  { (* ${nameOf(i)}:${goalHashes[i]} *) admit. }`); }
            }
            editRange = {
              start: { line: bounds.proofLine + 1, character: 0 },
              end: { line: bounds.endLine, character: 0 },
            };
          }

          let written = false;
          if (write !== false) {
            pushFileHistory(file, doc.text, currentProof.get(file));
            const newText = docManager.applyEdits(doc.text, [{
              range: editRange,
              newText: bodyLines.join('\n') + '\n',
            }]);
            await docManager.updateDocument(file, newText);
            await docManager.saveDocument(file);
            written = true;
            if (survivors.length === 0) {
              try {
                const cd = docManager.getDocument(file)!;
                const { text: qt, applied } = applyAutoQed(cd.text, name);
                if (applied) { await docManager.updateDocument(file, qt); await docManager.saveDocument(file); }
              } catch {}
            }
            // Force LSP re-sync after writing — close and reopen so subsequent
            // queries (e.g. insert_tactics with admit_hash) see the new state.
            try {
              await docManager.closeDocument(file);
              const reopened = await ensureDocumentOpened(file);
              await retryDocumentNotReady(() =>
                lspClient.sendRequest('coq/getDocument', {
                  textDocument: {
                    uri: reopened.uri,
                    version: reopened.version,
                  },
                })
              );
            } catch (e) {
              console.error('[stratify] re-sync failed:', e);
            }
          }

          const nSolved = nGoals - survivors.length;
          const parts: string[] = [];
          const scope = admit_hash ? ` (nested in ${admit_hash})` : '';
          parts.push(`stratify ${name}${scope}: skeleton → ${nGoals} goal(s)${cases_from ? ` (cases from ${cases_from})` : ''}, solved ${nSolved}/${nGoals}`);
          for (let j = 0; j < survivors.length; j++) {
            const i = survivors[j];
            const ty = ((goals[i] as any)?.ty || '').replace(/\s+/g, ' ').slice(0, 200);
            parts.push(`  survivor: ${nameOf(i)}:${goalHashes[i]} ⊢ ${ty}`);
          }
          if (survivors.length === 0 && written) {
            const cd = docManager.getDocument(file);
            const closed = cd ? findTacticAdmitLines(cd.text.split('\n'), bounds.proofLine, proofBounds(cd.text.split('\n'), name)?.endLine ?? bounds.endLine).length === 0 : false;
            parts.push(closed ? 'all cases closed — Qed applied' : 'all nested cases closed — other admits remain in proof');
          }
          else if (survivors.length > 0) parts.push('next: use close_admits to batch-close survivors, or stratify admit_hash=<hash> for nested case-elimination, or insert_tactics admit_hash=<hash> per survivor');
          return reply(parts.join('\n'), { written, solved: nSolved, total: nGoals, survivors: survivors.map(i => ({ name: nameOf(i), hash: goalHashes[i] })) });
        }

        case 'close_admits': {
          const { file, name, portfolio } = args as {
            file: string; name: string;
            portfolio: Array<{ hashes: string | string[]; tactic: string }>;
          };
          currentProof.set(file, name);
          if (!portfolio || portfolio.length === 0) {
            throw new Error('close_admits: portfolio is empty');
          }

          const processed = new Set<string>();
          const results: { closed: string[]; not_closed: Array<{ hash: string; error: string }> } = { closed: [], not_closed: [] };

          // Resolve hashes to a flat list; "*" expands to all currently-unclosed
          async function resolveHashes(
            hashes: string | string[],
            docLines: string[],
            bounds: { proofLine: number; endLine: number },
          ): Promise<string[]> {
            if (hashes === '*') {
              const doc = docManager.getDocument(file);
              if (!doc) return [];
              const admits = await queryAdmitHashes(doc, docLines, bounds);
              return [...new Set(admits.map(a => a.hash).filter(h => !processed.has(h)))];
            }
            if (Array.isArray(hashes)) return [...new Set(hashes.filter(h => !processed.has(h)))];
            if (processed.has(hashes)) return [];
            return [hashes];
          }

          // Process one hash: dry-run speculatively, commit on success
          async function processOne(
            hash: string,
            tactic: string,
            currentDocLines: string[],
            currentBounds: { proofLine: number; endLine: number },
            tacticIdx: number,
          ): Promise<{ closed: boolean; error?: string }> {
            // Find the admit line for this hash
            const admitLines = findAdmitLines(currentDocLines, currentBounds.proofLine, currentBounds.endLine);
            let targetLine = -1;
            for (const line of admitLines) {
              try {
                const { snapLine, snapChar } = admitSnapPosition(currentDocLines, line, currentBounds.proofLine);
                const freshDoc = docManager.getDocument(file)!;
                const stateR = await retryDocumentNotReady(() =>
                  lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                    uri: freshDoc.uri,
                    position: { line: snapLine, character: snapChar },
                    opts: { memo: false },
                  })
                );
                const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                  st: stateR.st, opts: { compact: true },
                });
                const goalText = (goalsR.goals || []).map((g: any) => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
                const h = createHash('md5').update(goalText).digest('hex').slice(0, 8);
                if (h === hash) { targetLine = line; break; }
              } catch {}
            }
            if (targetLine < 0) return { closed: false, error: `admit not found for hash "${hash}"` };

            // Speculative dry-run: try the tactic via Pétanque before editing
            {
              const { snapLine, snapChar } = admitSnapPosition(
                currentDocLines, targetLine, currentBounds.proofLine
              );
              try {
                const freshDoc = docManager.getDocument(file)!;
                const stateR = await retryDocumentNotReady(() =>
                  lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                    uri: freshDoc.uri,
                    position: { line: snapLine, character: snapChar },
                    opts: { memo: false },
                  })
                );
                await lspClient.sendRequest<RunResult<number>>('petanque/run', {
                  st: stateR.st, tac: tactic, opts: { memo: false },
                });
              } catch (e: any) {
                const msg = e?.message || String(e);
                return { closed: false, error: msg };
              }
            }

            // Commit: apply replaceAllMatchingAdmits
            const freshDoc = docManager.getDocument(file)!;
            const preEditText = freshDoc.text;
            pushFileHistory(file, preEditText, null);
            try {
              const { text: finalText, count: replaced } = await replaceAllMatchingAdmits(
                freshDoc.text, name, tactic, hash,
                async (line, currentText) => {
                  try {
                    await docManager.updateDocument(file, currentText);
                    const curLines = currentText.split('\n');
                    const curBounds = proofBounds(curLines, name);
                    const { snapLine: sl, snapChar: sc } = admitSnapPosition(
                      curLines, line, curBounds?.proofLine ?? 0
                    );
                    const tempDoc = docManager.getDocument(file)!;
                    const stateR = await retryDocumentNotReady(() =>
                      lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                        uri: tempDoc.uri,
                        position: { line: sl, character: sc },
                        opts: { memo: false },
                      })
                    );
                    const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                      st: stateR.st, opts: { compact: true },
                    });
                    return (goalsR.goals || []).map(g => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
                  } catch { return null; }
                }
              );

              if (replaced === 0) return { closed: false, error: 'no matching admit found during commit phase' };

              await docManager.updateDocument(file, finalText);
              await docManager.saveDocument(file);

              // Re-sync
              try {
                await docManager.closeDocument(file);
                await ensureDocumentOpened(file);
              } catch {}

              // Re-seal open goals after tactic
              try {
                const sealedDoc = docManager.getDocument(file)!;
                const sealedLines = sealedDoc.text.split('\n');
                const sealedBounds = proofBounds(sealedLines, name);
                if (sealedBounds) {
                  const parentBulletLine = sealedLines[targetLine] || '';
                  const tacticLines = (tactic.match(/\n/g) || []).length + 1;
                  const tacticEndLine = targetLine + tacticLines - 1;
                  const tacticEndChar = (sealedLines[tacticEndLine] || '').length;
                  const goalsR = await retryDocumentNotReady(() =>
                    lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                      textDocument: { uri: sealedDoc.uri, version: sealedDoc.version },
                      position: { line: tacticEndLine, character: tacticEndChar },
                      pp_format: 'Str', mode: 'After',
                    })
                  );
                  const tacticErrors = (goalsR?.messages || []).filter((m: any) => m.level === 1);
                  if (tacticErrors.length > 0) {
                    // Rollback on error
                    await docManager.updateDocument(file, preEditText);
                    await docManager.saveDocument(file);
                    await docManager.closeDocument(file);
                    await ensureDocumentOpened(file);
                    const errMsg = tacticErrors.map((m: any) => m.text || m.message).join('; ');
                    return { closed: false, error: `tactic error: ${errMsg}` };
                  }
                  const nFocused = goalsR?.goals?.goals?.length ?? 0;
                  if (nFocused > 0) {
                    const goals = goalsR?.goals?.goals || [];
                    const sealHashes = goals.map((g: any) => {
                      const gt = (g.ty || '').replace(/\s+/g, ' ');
                      return createHash('md5').update(gt).digest('hex').slice(0, 8);
                    });
                    const { text: sealed, sealMsg } = sealOpenGoals(
                      finalText, tacticEndLine, nFocused, parentBulletLine, sealHashes
                    );
                    await docManager.updateDocument(file, sealed);
                    await docManager.saveDocument(file);
                  }
                }
              } catch {}

              return { closed: true };
            } catch (e: any) {
              // Rollback on failure
              try {
                await docManager.updateDocument(file, preEditText);
                await docManager.saveDocument(file);
                await docManager.closeDocument(file);
                await ensureDocumentOpened(file);
              } catch {}
              return { closed: false, error: `commit failed: ${e?.message || String(e)}` };
            }
          }

          // Main loop: process each portfolio entry sequentially
          for (let pi = 0; pi < portfolio.length; pi++) {
            const entry = portfolio[pi];
            let tactic = entry.tactic?.trim();
            if (!tactic) throw new Error('close_admits: tactic is empty');
            // Ensure tactic ends with "." (required by petanque/run)
            if (!tactic.endsWith('.')) tactic += '.';

            // Refresh document
            const doc = await ensureDocumentOpened(file);
            const docLines = doc.text.split('\n');
            const bounds = proofBounds(docLines, name);
            if (!bounds) throw new Error(`Proof not found: "${name}"`);

            const hashes = await resolveHashes(entry.hashes, docLines, bounds);
            if (hashes.length === 0) continue;

            // Process hashes in order, re-reading state after each commit
            for (const hash of hashes) {
              // Mark as processed BEFORE attempting (even if it fails)
              processed.add(hash);

              // Re-fetch document state for line numbers
              const curDoc = docManager.getDocument(file) || doc;
              const curLines = curDoc.text.split('\n');
              const curBounds = proofBounds(curLines, name);
              if (!curBounds) {
                results.not_closed.push({ hash, error: 'proof bounds lost after previous edit' });
                continue;
              }
              const outcome = await processOne(hash, tactic, curLines, curBounds, pi);
              if (outcome.closed) {
                results.closed.push(hash);
              } else {
                results.not_closed.push({ hash, error: outcome.error || 'unknown' });
              }
            }
          }

          // Build reply
          const parts: string[] = [`close_admits ${name}: processed ${processed.size} hash(es)`];
          if (results.closed.length > 0) {
            parts.push(`  closed ${results.closed.length}: ${results.closed.join(', ')}`);
          }
          if (results.not_closed.length > 0) {
            parts.push(`  not closed ${results.not_closed.length}:`);
            for (const n of results.not_closed) {
              parts.push(`    ${n.hash}: ${n.error}`);
            }
          } else {
            parts.push('  all closed');
          }

          // Auto-Qed (once, after all portfolio entries)
          try {
            const qedDoc = docManager.getDocument(file);
            if (qedDoc) {
              const qedLines = qedDoc.text.split('\n');
              const qedBounds = proofBounds(qedLines, name);
              if (qedBounds) {
                const admittedLine = qedBounds.endLine;
                let hasFocusedGoals = false;
                if (qedLines[admittedLine]?.trim() === 'Admitted.') {
                  try {
                    const { snapLine: sl, snapChar: sc } = admitSnapPosition(qedLines, admittedLine, qedBounds.proofLine);
                    const sR = await retryDocumentNotReady(() =>
                      lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                        uri: qedDoc.uri, position: { line: sl, character: sc }, opts: { memo: false },
                      })
                    );
                    const gR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                      st: sR.st, opts: { compact: true },
                    });
                    hasFocusedGoals = (gR.goals?.length ?? 0) > 0 || ((gR.stack || []).length ?? 0) > 0;
                  } catch {}
                }
                if (!hasFocusedGoals) {
                  const { text: qt, applied } = applyAutoQed(qedDoc.text, name);
                  if (applied) {
                    await docManager.updateDocument(file, qt);
                    await docManager.saveDocument(file);
                    await docManager.closeDocument(file);
                    await ensureDocumentOpened(file);
                  }
                }
              }
            }
          } catch {}

          // Show remaining admits
          try {
            const finalDoc = docManager.getDocument(file);
            if (finalDoc) {
              const finalLines = finalDoc.text.split('\n');
              const finalBounds = proofBounds(finalLines, name);
              if (finalBounds) {
                const admitLines = findAdmitLines(finalLines, finalBounds.proofLine, finalBounds.endLine);
                if (admitLines.length > 0) {
                  const remaining: string[] = [];
                  for (const line of admitLines) {
                    try {
                      const { snapLine, snapChar } = admitSnapPosition(finalLines, line, finalBounds.proofLine);
                      const stateR = await retryDocumentNotReady(() =>
                        lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                          uri: finalDoc.uri,
                          position: { line: snapLine, character: snapChar },
                          opts: { memo: false },
                        })
                      );
                      const goalsR = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
                        st: stateR.st, opts: { compact: true },
                      });
                      const goals = goalsR.goals || [];
                      const goalText = goals.map((g: any) => (g.ty || '').replace(/\s+/g, ' ')).join(' | ');
                      const h = createHash('md5').update(goalText).digest('hex').slice(0, 8);
                      remaining.push(`${h}  L${line + 1}: ${goalText || '(no goals)'}`);
                    } catch { remaining.push(`error  L${line + 1}`); }
                  }
                  if (remaining.length > 0) {
                    parts.push(`\n${remaining.length} admit(s) remaining:\n${remaining.join('\n')}`);
                  }
                }
              }
            }
          } catch {}

          return reply(parts.join('\n'), {
            processed: processed.size,
            closed: results.closed.length,
            not_closed: results.not_closed.length,
            closed_hashes: results.closed,
            not_closed_details: results.not_closed,
          });
        }

        case 'require_lib': {
          const { file, lib } = args as {
            file: string;
            lib: string;
          };

          const doc = await ensureDocumentOpened(file);

          const docInfo = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc.uri, version: doc.version },
              ast: false,
            })
          );

          const targetPos: Position =
            (docInfo.spans && docInfo.spans.length > 0)
              ? docInfo.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc.uri,
              position: targetPos,
              opts: { memo: true, hash: true },
            })
          );

          const runResult = await lspClient.sendRequest<RunResult<number>>(
            'petanque/run',
            { st: stateResult.st, tac: `Require Import ${lib}.`, opts: { memo: false, hash: false } }
          );

          const msgs = (runResult.feedback || []).map(([level, msg]: [number, string]) => ({ level, message: msg }));
          const ok = !msgs.some(m => m.level === 1);
          if (ok) {
            // Register persistent speculative import
            const uri = docManager.pathToUri(file);
            const existing = speculativeImports.get(uri) || [];
            if (!existing.includes(lib)) {
              existing.push(lib);
              speculativeImports.set(uri, existing);
            }
          }
          return reply(
            ok
              ? `Imported ${lib} — available for subsequent queries on ${file}`
              : `Error importing ${lib}: ${msgs.map(m => m.message).join('; ')}`,
            { ok, messages: msgs }
          );
        }

        case 'locate_term': {
          const { file, thing } = args as {
            file: string;
            thing: string;
          };

          const doc = await ensureDocumentOpened(file);

          const docInfo = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc.uri, version: doc.version },
              ast: false,
            })
          );

          const targetPos: Position =
            (docInfo.spans && docInfo.spans.length > 0)
              ? docInfo.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc.uri,
              position: targetPos,
              opts: { memo: true, hash: true },
            })
          );

          const locateSt = await runPendingImports(doc.uri, stateResult.st);

          const runResult = await lspClient.sendRequest<RunResult<number>>(
            'petanque/run',
            { st: locateSt, tac: `Locate ${thing}.`, opts: { memo: false, hash: false } }
          );

          const msgs = (runResult.feedback || []).map(([level, msg]: [number, string]) => ({ level, message: msg }));
          const results = msgs.length > 0
            ? msgs.map(m => m.message).join('\n')
            : '(not found)';
          return reply(
            `Locate "${thing}" → ${msgs.length} result(s)\n${results}`,
            { messages: msgs }
          );
        }

        case 'reset_proof': {
          const { file, name } = args as {
            file: string;
            name: string;
          };

          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');
          const proofLine = findProofLine(docLines, name);
          if (proofLine < 0) throw new Error(`Proof not found: "${name}"`);

          let foundClosing = false;
          let endLine = proofLine + 1;
          while (endLine < docLines.length) {
            const l = (docLines[endLine] || '').trim();
            if (l === 'Qed.' || l === 'Admitted.' || l === 'Defined.') { foundClosing = true; break; }
            if (isTopLevelLine(docLines[endLine] || '')) break;
            endLine++;
          }

          const end = foundClosing
            ? { line: endLine + 1, character: 0 }
            : (endLine < docLines.length
                ? { line: endLine, character: 0 }
                : { line: endLine, character: (docLines[endLine - 1] || '').length });

          const newText = docManager.applyEdits(doc.text, [{
            range: {
              start: { line: proofLine + 1, character: 0 },
              end,
            },
            newText: 'Admitted.\n',
          }]);

          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          // Find the proof name
          let nameLine = proofLine - 1;
          let proofName = 'unknown';
          while (nameLine >= 0) {
            const nl = (docLines[nameLine] || '').trim();
            if (isTopLevelLine(docLines[nameLine] || '')) {
              proofName = nl.split(':')[0].trim();
              break;
            }
            nameLine--;
          }

          return reply(
            `${fileLine(file, proofLine)} — reset "${proofName}" to Admitted.`,
            { applied: true, proof: proofName }
          );
        }

        case 'add_lemma': {
          const { file, name, statement, before } = args as {
            file: string;
            name: string;
            statement: string;
            before?: string;
          };

          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');

          // Check if lemma already exists
          for (let i = 0; i < docLines.length; i++) {
            const l = docLines[i].trim();
            const kw = l.split(/\s+/)[0];
            if ((kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' || kw === 'Example') &&
                l.includes(name + ' :') && (l.includes(name + ' :') || l.includes(name + ':'))) {
              const existingStmt = l.split(':').slice(1).join(':').trim().replace(/\.$/, '');
              if (existingStmt === statement.trim()) {
            return reply(
                    `${fileLine(file, i)} — Lemma ${name} already exists with same statement (no-op)`,
                  { exists: true, identical: true, line: i, proof: name, statement: existingStmt }
                );
              }
              return reply(
                `${fileLine(file, i)} — Lemma ${name} already exists with different statement`,
                { exists: true, identical: false, line: i, proof: name, existing_statement: existingStmt, requested_statement: statement }
              );
            }
          }

          // Resolve insertion line via before parameter
          let targetLine: number;
          if (before) {
            const pLine = findProofLine(docLines, before);
            if (pLine < 0) throw new Error(`"${before}" not found`);
            for (let i = pLine - 1; i >= 0; i--) {
              const kw = (docLines[i] || '').trim().split(/\s+/)[0];
              if (kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' ||
                  kw === 'Definition' || kw === 'Fixpoint' || kw === 'Inductive' ||
                  kw === 'Example' || kw === 'Axiom') {
                targetLine = i;
                break;
              }
            }
            targetLine = targetLine!;
          } else {
            throw new Error('"before" parameter is required — specify which proof to insert above');
          }

          const block = `\nLemma ${name} : ${statement}.\nProof.\nAdmitted.\n\n`;
          pushFileHistory(file, doc.text, null);
          const newText = docManager.applyEdits(doc.text, [{
            range: { start: { line: targetLine, character: 0 }, end: { line: targetLine, character: 0 } },
            newText: block,
          }]);

          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);
          currentProof.set(file, name);

          // Lint: check the inserted range for errors
          try {
            const checkResult = await lspClient.sendRequest<{
              diagnostics: Array<{ range: Range; severity: number; message: string }>;
            }>('coq/check', { textDocument: { uri: doc.uri, version: docManager.getDocument(file)!.version } });
            const diags = (checkResult.diagnostics || []).filter((d: any) => d.range.start.line >= targetLine && d.range.start.line < targetLine + 6 && d.severity === 1);
            if (diags.length > 0) {
              const old = docManager.applyEdits(newText, [{
                range: { start: { line: targetLine, character: 0 }, end: { line: targetLine + block.split('\n').length, character: 0 } },
                newText: '',
              }]);
              await docManager.updateDocument(file, old);
              await docManager.saveDocument(file);
              throw new Error(`Lemma type error: ${diags[0].message}`);
            }
          } catch (e: any) {
            if (e.message && e.message.startsWith('Lemma type error')) throw e;
          }

          return reply(
            `${fileLine(file, targetLine)} — added Lemma ${name}`,
            { applied: true }
          );
        }

        case 'delete_lemma': {
          const { file, name } = args as {
            file: string;
            name: string | string[];
          };

          const names = Array.isArray(name) ? name : [name];
          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');
          let currentText = doc.text;
          let totalDeleted = 0;

          for (const lemmaName of names) {
            // Find the Lemma/Theorem line
            const s = lemmaName.trim();
            let kwLine = -1;
            for (let i = 0; i < docLines.length; i++) {
              const l = docLines[i].trim();
              const kw = l.split(/\s+/)[0];
              if ((kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' || kw === 'Example') &&
                  l.includes(s + ' :')) {
                kwLine = i;
                break;
              }
            }
            if (kwLine < 0) {
              if (names.length === 1) throw new Error(`Lemma not found: "${s}"`);
              continue;
            }

            // Find the Qed./Admitted. that closes it
            let endLine = kwLine;
            for (let j = kwLine + 1; j < docLines.length; j++) {
              const l = docLines[j].trim();
              if (l === 'Qed.' || l === 'Admitted.' || l === 'Defined.') {
                endLine = j;
                break;
              }
              if (isTopLevelLine(docLines[j] || '')) break;
            }

            // Remove the block including surrounding blank lines
            let startDel = kwLine;
            while (startDel > 0 && (docLines[startDel - 1] || '').trim() === '') startDel--;
            let endDel = endLine + 1;
            while (endDel < docLines.length && (docLines[endDel] || '').trim() === '') endDel++;

            pushFileHistory(file, currentText, null);
            currentText = docManager.applyEdits(currentText, [{
              range: { start: { line: startDel, character: 0 }, end: { line: endDel, character: 0 } },
              newText: '',
            }]);

            totalDeleted++;
          }

          if (totalDeleted === 0) throw new Error('No lemma found to delete');

          await docManager.updateDocument(file, currentText);
          await docManager.saveDocument(file);

          // Force LSP re-sync
          try {
            await docManager.closeDocument(file);
            await ensureDocumentOpened(file);
            const freshDoc = docManager.getDocument(file)!;
            const lastLine = Math.max(0, freshDoc.text.split('\n').length - 1);
            await retryDocumentNotReady(() =>
              lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                uri: freshDoc.uri,
                position: { line: lastLine, character: 0 },
                opts: { memo: false, hash: false },
              })
            );
          } catch (e) {
            console.error('[delete_lemma] re-sync failed:', e);
          }

          const namesStr = names.length === 1 ? `"${names[0]}"` : `${names.length} lemmas`;
          return reply(
            `${fileLine(file, 0)} — deleted ${namesStr}`,
            { applied: true, deleted: totalDeleted, names }
          );
        }



        default:
          throw new Error(`Unknown tool: ${name}`);
      }
    } catch (error) {
      const e = error as Error & { data?: unknown };
      crash(`handler error in "${name}": ${e.stack || e.message}`);
      return err(
        `${name}: ${e.message}`,
        String(e.data ?? e.message)
      );
    }
  });

  // Connect stdio transport
  const transport = new StdioServerTransport();
  await server.connect(transport);

  // Handle shutdown
  process.on('SIGINT', async () => {
    await lspClient.shutdown();
    process.exit(0);
  });

  process.on('SIGTERM', async () => {
    await lspClient.shutdown();
    process.exit(0);
  });
}

main().catch((error) => {
  console.error('Fatal error:', error);
  process.exit(1);
});
