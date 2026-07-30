## Purpose

State the bounded purpose. Do not claim completion before evidence exists.

## Scope

List the files or behavior intentionally changed.

## Exclusions

List adjacent work that this pull request does not perform.

## Test plan

List exact commands and distinguish planned runs from completed runs.

## Review focus

Identify deterministic checks and separate human semantic review.

## Human semantic evidence

Follow the full [semantic evidence and closure protocol][human-protocol].

[human-protocol]: https://github.com/phasetr/ising-model/blob/main/docs/completion-claims.md#human-semantic-evidence-and-closure-protocol

- Inventory every in-scope semantic unit with a stable ID, role, locator,
  bounded claim, positive and negative evidence, disposition, any required
  reopen condition, and current reviewer finding.
- For theorem/API, source, and history units, record the exact contract,
  primary-source locator, or commit/content comparison required by the
  protocol.
- Recheck the whole stable documentation block in the PR #4800 row 20
  regression shape, not only the original line or hunk.
- Link separate exact-head source-review and issue-audit records, with reviewer
  identity, independence, commands, evidence, findings, and verdict.
- Require a clean round on the current head. Candidate content or material
  evidence changes reset the affected record as defined by the protocol.
- Keep the pull request in draft until the inventory and both review records
  are current. Record parent, child, canary, and post-merge synchronization
  separately.

## Completion-claim evidence

Replace every placeholder before requesting ready review. Draft pull requests
may leave `PENDING` in documented evidence fields and will remain incomplete.
Replace `ISSUE` with an issue number allowed by the offline context.
Do not use any GitHub issue-completion directive token in this body; the nine
forbidden words and conservative whole-body policy are listed in
`docs/completion-claims.md`.
Do not use a less-than character, raw HTML, or an angle autolink anywhere in
this body. Write comparisons in words and use ordinary Markdown links.
Under active ruleset `14892885`, `build` and `completion-claim/live` from
integration ID `15368` are mechanically required for pull requests targeting
`main`, with strict latest-base policy and no bypass actors. Integration
binding does not authenticate a particular workflow file, trigger, or matrix
producer. A successful `completion-claim/live` status binds mechanical
evidence to the exact head but remains semantically non-authoritative. It does
not replace source review, issue audit, semantic review, or
reviewer-independence review.
Pull-request events, main backfill, and default-branch replay share one
per-pull-request matrix cancellation domain. Cancellation is not an atomic
guard for a status request already in flight, so status residue remains
operational evidence requiring human review under #4801.
The live adapter writes exact-head pending after minimal routing identity and
before validating body size, structured references, changed files, issues, or
history. At most 16 structured references are allowed; exact strings and issue
numbers must be unique. Workflow UTF-8 text must exactly equal the embedded
canonical value, including its final line feed. Flow YAML, anchors, aliases,
extra keys, jobs, steps, comments, whitespace, and CRLF are rejected before
secondary structure, permission, expression, and digest checks.

```completion-claims-v1
{
  "schema_version": 1,
  "candidate": {
    "base_sha": "PENDING",
    "head_sha": "PENDING",
    "changed_file_count": "PENDING",
    "sorted_path_digest": "PENDING"
  },
  "claim_levels": [
    "exact_candidate_diff"
  ],
  "review_records": [
    {
      "kind": "source_review",
      "head_sha": "PENDING",
      "url": "PENDING"
    },
    {
      "kind": "issue_resolution_audit",
      "head_sha": "PENDING",
      "url": "PENDING"
    }
  ],
  "references": {
    "non_closing": [
      "Refs #ISSUE"
    ],
    "closing": []
  },
  "history_claims": [],
  "semantic_claims": []
}
```

See `docs/completion-claims.md` for the schema, digest algorithm, exit statuses,
and the boundary between mechanical validation and required human review.
