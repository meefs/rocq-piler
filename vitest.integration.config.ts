import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    include: ['tests/integration/**/*.test.ts'],
    testTimeout: 120_000,
    hookTimeout: 120_000,
    // Run integration tests serially — one coq-lsp process, sequential operations
    pool: 'forks',
  },
});
