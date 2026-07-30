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

## Completion-claim evidence

Replace every placeholder before requesting ready review. Draft pull requests
may leave `PENDING` in documented evidence fields and will remain incomplete.
Replace `ISSUE` with an issue number allowed by the offline context.
Do not use any GitHub issue-completion directive token in this body; the nine
forbidden words and conservative whole-body policy are listed in
`docs/completion-claims.md`.
Do not use a less-than character, raw HTML, or an angle autolink anywhere in
this body. Write comparisons in words and use ordinary Markdown links.
The advisory `completion-claim/live` status binds mechanical evidence to the
exact head. It does not replace source review, issue audit, semantic review,
or reviewer-independence review.
Pull-request events, main backfill, and default-branch replay share one
per-pull-request matrix cancellation domain. Cancellation is not an atomic
guard for a status request already in flight, so status residue remains
advisory and requires human review.
The live adapter writes exact-head pending after minimal routing identity and
before validating body size, structured references, changed files, issues, or
history. At most 16 structured references are allowed; exact strings and issue
numbers must be unique. Workflow actions and one-line commands are
byte-canonical, and extra steps or command suffixes are rejected.

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
