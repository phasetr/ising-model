# Rev22 static-audit synchronization

- Canonical #4519 checkpoint posted: https://github.com/phasetr/ising-model/issues/4519#issuecomment-4979750222
- #4506 tracker backlink posted: https://github.com/phasetr/ising-model/issues/4506#issuecomment-4979751432
- Append-only local synchronization completed in `.self-local/issues/4519.md`,
  `.self-local/issues/4506.md`, and `.self-local/issues/INDEX.md`.
- Recorded terminal status: Rev22 `STATIC_AUDIT_FAIL / RETIRED`; root
  `20260715T113000Z-rev22-static`; gist commit
  `806537ed4023f09b9d64b8536bdc9db6ede5aa5e`; raw SHA-256
  `fa73feafa2e6eb55744958c21bd1fe5b41ca7884427e607157fc8faa060de681`; actual suite
  `2 PASS / 1 ERROR` caused by twice executing `self.chain`, with the second state creation
  raising `FileExistsError`.
- Rev22 is immutable: no repair, reanchor, retry, resume, correction, or reuse. A separately
  authorized fresh Rev23 is required. No documentation or Lake action was taken.
