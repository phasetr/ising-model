# Completion-claim evidence gate

The phase-1 gate validates a pull request's declared evidence against a small,
trusted, offline context snapshot. It does not query GitHub, inspect the local
repository, run commands, read credentials, or decide whether a mathematical or
historical statement is true.

`PASS` means only that the structured fields agree with the supplied context.
It is not a semantic completion verdict. Every semantic claim and every
semantic claim level is reported as `HUMAN_REVIEW_REQUIRED`.

## Trusted live adapter

Phase 2 wraps the offline calculation in
`scripts/completion_claim_live.py`. The live adapter publishes the advisory
commit-status context `completion-claim/live` on the exact pull-request head.
Only offline exit 0 with a well-formed `PASS` report can publish `success`.
Draft-incomplete, deterministic rejection, unexpected checker output, API or
timeout errors, bounded-input violations, snapshot races, and status-write
errors all fail shut. This status is advisory during #4801; repository
required-check policy remains in #4802.

The isolated `.github/workflows/completion_claim_live.yml` workflow runs for
the exact `pull_request_target` actions `opened`, `reopened`, `synchronize`,
`edited`, `ready_for_review`, and `converted_to_draft`. A `main` push performs
a bounded open-pull-request backfill. A default-branch-only
`repository_dispatch` event of type `completion_claim_replay` accepts one
positive integer in `client_payload.pr_number`; branch-selectable
`workflow_dispatch` is intentionally absent. Actor identity never bypasses
evaluation.

The discovery job has only `contents: read` and `pull-requests: read`.
It emits a bounded JSON array of pull-request numbers and cannot write a
status. The matrix evaluation job adds only `issues: read` and
`statuses: write`. Workflow-level permissions are empty.
The workflow validator first parses each job's `steps` block by indentation.
It enumerates named and unnamed list-item forms plus every nested or top-level
`uses` and `run`, then requires the exact job ownership, four records, names,
field order, checkout `with` fields, two full-SHA checkout actions, and two
one-line Python commands. Extra actions, commands, block scalars, command
suffixes, step fields, and misplaced list items are rejected structurally.
Permission and expression contracts run next. The byte-canonical SHA-256
digest runs last as defense-in-depth, so coordinating an attacker workflow
with a new digest cannot mask structural rejection. Uncoordinated whitespace
changes remain digest failures.

It checks out only `${{ github.workflow_sha }}` with a full-SHA-pinned checkout
action, one-commit depth, and credential persistence disabled. It never checks
out or executes the pull-request head, merge revision, fork content, artifact,
cache, dependency installer, or candidate-supplied action. Concurrency is
keyed only by repository ID and matrix pull-request number. Pull-request
events, main backfill, and replay therefore use the same cancellation domain.
The adapter selection phase never writes status and each matrix process
evaluates exactly one pull request.

### Live snapshot and bounds

The adapter first reads fresh pull-request metadata and validates only the
minimum status identity: open state, pull-request number, target repository,
main base, and exact base and head SHAs. It immediately writes `pending` to
that head. A failed pending write stops the process without a second status
attempt. Body type and size, draft flag, changed-file count, head metadata,
managed JSON, and every primary fact are validated only after pending.
Therefore a same-head body edit cannot leave an older success untouched merely
by making the new body oversized or malformed.

After pending, the adapter records P1 from fresh REST responses: repository and
pull-request identity, state, draft flag, exact base and head SHAs, complete
body bytes and digest, changed-file count, sorted paths and digest, structural
issue facts, and bounded primary history facts. It invokes the existing
offline evaluator with the derived context, then reads P2. State, draft flag,
base SHA, head SHA, body digest, changed-file count, and path digest must remain
exactly equal. A mismatch attempts `failure` on the P1 head; a newer event owns
the newer body or head.

Changed files use fixed 100-entry pages. Metadata, page sizes, unique paths,
and the collected count must agree exactly. The adapter always requests the
next fixed sentinel page after the expected entries, including metadata counts
0, 100, and 3,000, and requires that page to be empty. At most 30 data pages
and 3,000 paths are accepted; 3,001 paths, underreported metadata, a missing or
extra entry, a duplicate, an incomplete page, or a partial digest is rejected.
The body and derived context are each limited to one MiB, each API response to
two MiB, structural issue ancestry to 64 issues and depth 8, history to 128
facts, each cited commit to three 100-file data pages plus an empty sentinel,
push backfill to 100 pull requests, diagnostics to 8,192 bytes, and HTTP
attempts to one request plus two bounded retries. Oversize and truncation
never produce partial acceptance.

Issue authority begins only with `Refs` entries in the managed JSON. Each seed
issue and every formal parent must be an open, same-repository issue rather
than a pull request. The chain is read through structural issue-parent
endpoints; unrestricted prose cannot widen the allowlist. At most 16 total
structured references are accepted. Every exact reference string and every
issue number must be unique, and at least one `Refs` child seed is required.
These checks run before changed-file, issue, or history endpoint reads. Issue
objects and parent results are memoized across shared chains, bounding the
issue graph to at most 16 seed issue reads plus 64 parent reads.

Structured history is derived from bounded commit-file pages, the requested
commit, its sole parent, ancestry comparison, and exact repository blob
identities. The cited path must have matching `added`, `modified`, or `removed`
commit-file status. Modified content must exist on both sides with distinct
blob SHAs; added and removed content must have the matching existence
transition and blob identity. Unchanged, unrelated, renamed, copied, unknown,
merge, and unreachable history is rejected. Matching those facts does not
certify natural-language relevance, which remains human review.

The same-head body-edit interval before `pending` and production commit-status
behavior for a fork-owned head remain documented canary questions for #4802.
Per-PR concurrency prevents independent active jobs from intentionally writing
in different event-specific groups, but it is not an atomic compare-and-set
for an HTTP status request already issued when cancellation begins. Such
cancelled-run residue remains a residual race and never becomes semantic or
merge authority. Mocked tests exercise these shapes but cannot turn production
behavior into a proven fact. #4801 remains open after the code merge until
bounded backfill and real same-repository and fork observations are recorded.
If the pull-request metadata HTTP response itself is unavailable, malformed,
truncated, or oversized before a valid head SHA can be obtained, no exact head
exists on which the adapter can publish pending. That pre-identity condition
is fail-shut in the workflow result but cannot clear an older commit status;
it remains a documented operational canary.

## Inputs

Invoke the checker with two explicit UTF-8 files:

```text
python3 scripts/completion_claim_gate.py --context context.json --body body.md
```

The context has this exact schema:

```json
{
  "schema_version": 1,
  "is_draft": true,
  "delivery": "pull_request",
  "base_sha": "0000000000000000000000000000000000000000",
  "head_sha": "1111111111111111111111111111111111111111",
  "changed_paths": ["repo/relative/path"],
  "allowed_issue_refs": [4796, 4801],
  "history_facts": [
    {
      "commit_sha": "2222222222222222222222222222222222222222",
      "path": "repo/relative/path",
      "action": "modified"
    }
  ]
}
```

The caller is responsible for constructing that trusted snapshot. Phase 1 has
no live workflow, API client, ruleset integration, authentication, or mirror
gate.

## Managed block

The body must contain exactly one canonical top-level JSON block copied from
the pull-request template. Its opener is exactly
```` ```completion-claims-v1 ```` at column zero and its closer is exactly three
backticks at column zero. Tildes, longer runs, indentation, trailing info,
blockquote/list containers, and cross-container openers or closers are not
accepted. Any `completion-claims-v1` marker outside the sole recognized
canonical opener is `AMBIGUOUS_MANAGED_BLOCK`. Marker counting uses the same
HTML-entity decoding, Unicode NFKC normalization, and format-control removal as
the directive scan, so disguised markers count too. The marker remains
case-sensitive, while raw canonical parsing still accepts only the literal
template opener. An unclosed canonical block is `MALFORMED_MANAGED_BLOCK`.
Unknown or missing keys, duplicate JSON keys, malformed types, and unsupported
schema versions also fail closed.

```completion-claims-v1
{
  "schema_version": 1,
  "candidate": {
    "base_sha": "0000000000000000000000000000000000000000",
    "head_sha": "1111111111111111111111111111111111111111",
    "changed_file_count": 1,
    "sorted_path_digest": "sha256:2678a1efde492cf52d850f50bfa0e980fc4c718e9c67bd22779c714358fa63d6"
  },
  "claim_levels": ["exact_candidate_diff"],
  "review_records": [
    {
      "kind": "source_review",
      "head_sha": "1111111111111111111111111111111111111111",
      "url": "https://github.com/example/project/issues/4801#issuecomment-1"
    },
    {
      "kind": "issue_resolution_audit",
      "head_sha": "1111111111111111111111111111111111111111",
      "url": "https://github.com/example/project/issues/4801#issuecomment-2"
    }
  ],
  "references": {
    "non_closing": ["Refs #4801", "Part of #4796"],
    "closing": []
  },
  "history_claims": [
    {
      "commit_sha": "2222222222222222222222222222222222222222",
      "path": "repo/relative/path",
      "action": "modified"
    }
  ],
  "semantic_claims": [
    {
      "id": "stable-local-id",
      "kind": "source",
      "statement": "The cited source supports the stated role.",
      "evidence_urls": ["https://example.test/source"]
    }
  ]
}
```

### Candidate identity

Both SHAs must be full lowercase 40-character hexadecimal values. The base SHA,
head SHA, changed-file count, and path digest must agree exactly with the
context. Review records of both kinds are required and must record that same
head SHA.

Changed paths are nonempty, unique, repository-relative UTF-8 strings. Empty
paths, absolute paths, parent traversal, newlines, NULs, backslashes, and
duplicates are rejected. There are no path exemptions, including for
`.self-local/reports/*.lean`.

To compute `sorted_path_digest`, encode every path as UTF-8, sort by those bytes,
and hash each path in sequence as:

```text
<decimal byte length>:<path bytes>
```

The result is written as `sha256:` followed by 64 lowercase hexadecimal
characters. Length framing prevents concatenation ambiguity.

### Claim and review boundary

Allowed claim levels are:

- `build_health`
- `source_axiom_health`
- `exact_candidate_diff`
- `bounded_tracker_completion`
- `theorem_api_contract`
- `repository_wide_completion`

The list must be nonempty and duplicate-free. The checker validates the enum;
it does not certify that a selected level is honest. Only
`exact_candidate_diff` is fully bound to context fields. Every other level
emits `HUMAN_REVIEW_REQUIRED`; this includes the explicitly semantic
`bounded_tracker_completion`, `theorem_api_contract`, and
`repository_wide_completion` levels.

Review records must contain exactly the `source_review` and
`issue_resolution_audit` kinds, durable HTTPS URL syntax, and the exact
candidate head. These checks prove only record syntax and head binding. Each
record itself emits `HUMAN_REVIEW_REQUIRED`: URL relevance, reviewer
independence, authorship, source role, theorem meaning, and historical or
provenance prose remain human decisions.

Semantic claim kinds are `source`, `theorem`, and `provenance`. Every semantic
claim emits `HUMAN_REVIEW_REQUIRED`; a semantic result is never reported as
`PASS`.

All nonempty prose outside the managed block is conservatively charged as
`HUMAN_REVIEW_REQUIRED`. Issue mentions and future-plan language receive
additional human-review records. Thus an unmanaged claim cannot silently
inherit the machine `PASS` status.

### Structured history

`context.history_facts` and payload `history_claims` contain exact ordered
tuples with only `commit_sha`, `path`, and `action`. The SHA is full lowercase
hex, the path follows the same repository-relative normalization rules as a
changed path, and the action is one of `added`, `modified`, or `deleted`.
Counts and every tuple component must match exactly. A structured match says
only that the payload repeats the caller-supplied primary fact; interpretation
of unrestricted historical prose remains human-reviewed.

### Body syntax restriction

After HTML-entity decoding, Unicode NFKC normalization, and format-control
removal, the body must contain no less-than character (`<`). This check runs
before managed-block extraction and reports `RAW_HTML_FORBIDDEN`. The checker
does not parse HTML and has no tag-length cutoff: comments, block containers,
tags, closing or self-closing tags, quoted or multiline attributes, angle
autolinks, entity-encoded delimiters, and fullwidth delimiters are all rejected
by the same character test. Comparisons must be written in words, and links
must use ordinary Markdown link syntax.

### Issue references

`references.closing` is mandatory and must be empty. The body is also rejected
if it contains any standalone, case-insensitive official GitHub closing
directive token
(`close`, `closes`, `closed`, `fix`, `fixes`, `fixed`, `resolve`, `resolves`,
or `resolved`) anywhere in the pull-request body. No issue reference is needed
for rejection. The conservative policy intentionally does not interpret
Markdown: prose, emphasis, inline and reference-style links, link
destinations, code, HTML, and comments are treated alike. HTML entities and
Unicode NFKC forms are normalized first, and format controls cannot split a
token. The bounded one-direction token scanner is linear in the body size.
Authors must avoid these nine words until the post-merge issue action.

The only structured non-closing forms are `Refs #NUMBER` and
`Part of #NUMBER`, and their numbers must be in `allowed_issue_refs`. The same
allowlist is applied to raw `Refs` or `Part of` directives elsewhere in the
body, so copied evidence cannot hide a wrong issue number outside the managed
block.

## Draft and ready behavior

Draft bodies may use the literal string `PENDING` for candidate fields, review
record SHAs or URLs, and semantic evidence URLs. Missing review kinds are also
allowed in a draft. With no deterministic contradiction, these produce
`DRAFT_INCOMPLETE` and exit 2.

A deterministic contradiction produces `FAIL` and exit 1 in both draft and
ready states. A ready body rejects every `PENDING` value and requires both
exact-head review records. When all deterministic checks succeed, the machine
status is `PASS` and the process exits 0; any accompanying semantic records
still say `HUMAN_REVIEW_REQUIRED`.

All JSON strings and keys pass through one Unicode validator. Lone high or low
surrogates, NUL, U+0085, and other C0/C1 controls fail as `INVALID_UNICODE`
instead of escaping as an encoding or URL-parser exception. Tab, LF, and CR
remain valid text controls and retain their normal JSON/Markdown meaning.

## Self-test

Run:

```text
python3 scripts/test_completion_claim_gate.py
python3 scripts/test_completion_claim_live.py
```

The suite includes baseline and incident-derived fixtures for #4709, #4718,
and PR #4800. It mutates SHAs, paths, counts, digests, references, review heads,
structured history commits/paths/actions, delivery, fences, keys, and ready
placeholders. It probes normalized completion-directive forms, separators longer
than the former cutoff, emphasized and reference-link directive tokens, long
links and HTML tags, exact canonical fences, and rejected blockquote/list or
cross-container variants. Entity, NFKC, and format-control marker disguises,
mixed duplicate disguises, and normalized marker-count mutants are pinned.
Hidden HTML block containers, tags, comments, autolinks, normalized less-than
delimiters, comparison prose, and weakened raw-HTML guards are also pinned.
Directive, marker, and body-syntax scans beyond one MiB remain bounded. The
suite also covers malformed URLs, lone surrogates, invalid controls,
boolean-as-integer inputs, and unmanaged prose; kills representative weakened
checker mutants; pins `.self-local` path coverage; and verifies that the
checker imports no process, network, or dynamic-execution facility.

The live-adapter suite is hermetic and performs no network requests. Its
injected transport covers pull-request actions, draft and ready transitions,
dispatch and backfill, same-repository, fork, and Dependabot-shaped metadata,
fixed-page boundaries through 3,000 paths, structural issue ancestry, primary
history actions, P1/P2 races, checker exit mapping, status payloads, API and
size errors, and workflow security mutations.
