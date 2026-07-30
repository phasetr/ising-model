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
The validator first requires the supplied UTF-8 workflow text to equal the
single `canonical_workflow_text` value, including its final line feed. Any
difference fails before all secondary diagnostics. This includes flow-style
YAML, anchors, aliases, extra top-level keys, jobs or steps, comments,
whitespace, and CRLF line endings; semantically equivalent YAML is not
accepted. Only the exact canonical text reaches the secondary indentation
record check, permission and expression checks, and SHA-256 digest check.
Those checks provide independent consistency evidence; the indentation check
is deliberately not presented as a general YAML parser. Coordinating a
changed digest therefore cannot authorize changed workflow text.

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

## Human semantic evidence and closure protocol

The mechanical gate cannot establish semantic completion. A pull request that
makes a semantic completion claim must follow this human protocol in addition
to satisfying the managed block. The
[authoritative bounded design for #4803][design-4803] governs this protocol.

[design-4803]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5129563555

### Semantic-unit inventory

Decompose every claim into stable review units. Each inventory row must record
all of the following:

- a stable local unit ID;
- an artifact role: module, declaration, theorem/API contract, documentation
  block, tracker row, source claim, or history/provenance claim;
- a stable locator: repository path plus declaration name, heading or block
  identity, tracker row key, or another justified content identity;
- the exact claim and bounded scope, including the observable, parameters,
  volume, quantifiers, and source role where applicable;
- positive evidence showing what exists;
- negative evidence showing the scope searched and what does not exist;
- one disposition: `implemented`, `partial`, `unresolved`, `contradicted`,
  `not_applicable`, `accepted_scoped_endpoint`, or `deferred`;
- a reopen condition for every `accepted_scoped_endpoint` or `deferred` unit;
  and
- the reviewer finding and status for the current exact candidate.

Line numbers and diff hunks are navigation aids, not stable unit identities or
proof of inventory completeness. A module-wide claim requires an inventory of
the whole module. A theorem/API claim requires the named declaration and its
actual contract. A documentation claim requires review of the complete
semantic block, not a selected sentence.

The inventory itself is durable evidence. Give it a version or stable scope
identity, and link that identity from both exact-head review records. A claim
whose in-scope units are not fully inventoried remains incomplete even when
builds and deterministic checks pass.

### Theorem/API, source, and history evidence

For each theorem/API unit, record:

- the exact repository path and declaration name;
- the candidate-head signature or statement;
- all relevant hypotheses and the result;
- parameter, observable, quantifier, and volume scope; and
- the commands or source inspection used to rule out a stronger absent
  declaration.

Build success and axiom health are separate evidence. They do not establish
that a declaration has the claimed meaning or scope.

For each source unit, identify the primary source and a durable locator such
as chapter, section, theorem, or page. State the role actually supported, plus
every mismatch or project-local extension. Repository prose copied from that
source is not primary-source evidence.

For each history/provenance unit, cite the exact commit, path, change kind,
parent or content comparison, and a natural-language relevance judgment. A
mechanically valid commit/path tuple establishes only the primary history
fact, not the truth of prose about its significance.

PR #4800 row 20 is the mandatory regression example for documentation review.
A selected line anchor appeared corrected while the same
`AntidiagonalTupleCard.lean` documentation block retained an unsupported
attribution. Review must therefore reset to the stable documentation block
and inspect positive and negative evidence beyond the original hunk or anchor.

### Two independent exact-head records

Every exact candidate requires two durable review records. Both records bind
to the full 40-character candidate-head SHA, use separate URLs, and represent
separate review passes.

The source-review record must state:

- reviewer identity and independence from implementation authorship;
- the exact candidate-head SHA and inventory version or scope;
- commands, repository content, primary sources, and history inspected;
- findings for every declared semantic unit and the whole in-scope diff;
- review of positive and negative evidence, theorem/API contracts,
  source roles, history relevance, scope, and exclusions; and
- whether the current round is clean.

The issue-resolution-audit record must state:

- reviewer identity and independence from implementation authorship;
- the exact candidate-head SHA;
- a mapping from every issue acceptance criterion and every attached child
  disposition to exact evidence;
- one classification per criterion or child: `resolved`, `partial`,
  `unresolved`, `contradicted`, or `not_applicable`;
- evidence URLs, lifecycle and hierarchy checks, and the resulting issue
  verdict.

Neither record substitutes for the other. If one independent reviewer performs
both roles, disclose that fact and use fresh, separately prompted and
separately recorded review passes. Self-review, a checkbox, prior issue state,
or green CI is not either record.

### Clean round, invalidation, and draft boundary

A clean round is the latest complete review of the current exact candidate
with zero open findings. Correcting one finding does not create a clean round.
All in-scope units and the full diff must be reviewed again on the new head.

Any candidate-content change invalidates both exact-head records. A material
PR-body or evidence change on the same head invalidates the affected semantic
review or audit until it is explicitly rechecked. A change to scope,
acceptance criteria, issue hierarchy, or disposition resets the issue audit.
Old findings may remain as history, but an older verdict cannot be promoted to
the new round.

Keep the pull request in draft while inventory or review evidence is
incomplete. Ready review requires current source-review and issue-audit URLs,
the exact head in both records, a clean round, honest exclusions, and no
blocking criterion hidden by prose.

### Child, parent, and post-merge source of truth

The child issue owns its acceptance criteria and evidence-backed disposition.
A parent summarizes child state but cannot turn a partial child into a
completed child. Link durable design, source-review, issue-audit, merge, and
canary records from the child first, then synchronize the summary upward to
its parents.

After merge, verify all of the following:

- the reviewed candidate against the merged tree or exact two-file content;
- the squash or main SHA, final CI, and changed paths;
- branch removal and the issue hierarchy; and
- synchronized GitHub issue bodies and ignored `.self-local/issues/` mirrors.

Issue closure is a separate action. Perform it only after the child has its
own supported disposition and every parent summary agrees. Candidate CI or a
merged pull request alone never changes issue lifecycle state.

### Honest partial demonstration

The current #4786 and #4790 hierarchy demonstrates the classification method;
it is not completion evidence:

- **#4786 repository-wide claim.** Build, audit, and bounded prevention work
  are positive evidence. Multiple mathematical and governance children remain
  open. The disposition is `partial`.
- **#4790 finite-volume field derivative.**
  `hasDerivAt_correlation_h_uniform_bound` gives the recorded finite-volume
  bound. It is not an infinite-volume derivative contract. The disposition is
  `implemented` only at the finite-volume scope.
- **#4790 high-temperature field CE.** A holomorphic locally uniform limit and
  real-axis identification exist under stated hypotheses. No declared real
  `HasDerivAt correlationInfinite ...` theorem matches the historical claim.
  The disposition is `partial`.
- **#4790 primary infinite-volume contract.** No positive declaration evidence
  exists. Repository inspection records the absent named or
  contract-equivalent theorem. The disposition is `unresolved`, unless a
  narrower endpoint is accepted with a reopen condition.

Accordingly #4786, #4790, #4796, and #4803 remain open. This record does not
satisfy an exact-candidate source review, a full hierarchy audit, or issue
closure criteria.

### Same-repository canary record

The implementation pull request for this protocol remains a same-repository
draft until its evidence is complete. Record each observation with the event,
run URL, exact head, status sequence, and cancelled-run or status residue:

The pre-observation design expectation was that a draft body with `PENDING`
review fields would produce `DRAFT_INCOMPLETE`. The actual opened canary
superseded that expectation because it used an empty kickoff candidate. Its
exact head received pending and then failure with `INVALID_CHANGED_PATH`;
empty-path validation occurred before review-field evaluation. That
observation is fail-shut evidence, but it is not an observed
`DRAFT_INCOMPLETE` result.

The exact two-file candidate was then synchronized with both review records
still `PENDING`. Its exact head received pending and then failure with the
generic live description `OFFLINE_CHECK_FAILED`. A separate offline evaluation
of the same exact candidate and body returned `DRAFT_INCOMPLETE` with exactly
two `PENDING_REVIEW` diagnostics, one for each required record. The generic
live description does not expose those offline diagnostics and is not an
exact-head success.

The superseding issue record will carry the observed run URLs, exact heads,
status sequences, timestamps, offline report, and any cancelled-run or status
residue. The remaining lifecycle must occur in this order. These are required
future observations, not current outcomes:

1. Bind a valid body to the current exact head, changed-file count, and path
   digest. Supply separate durable exact-head source-review and issue-audit
   URLs. Trigger evaluation on that same head, require pending followed by
   success, and record the actual result before any invalidation.
2. Only after that success, change one allowed review-record value to the
   canonical `PENDING` string on the unchanged head. Trigger evaluation,
   require pending followed by failure, and record the actual result.
3. Restore the exact durable URL for that record on the unchanged head.
   Trigger evaluation, require pending followed by success, and record the
   actual result.
4. Convert the unchanged draft to ready. Require another pending transition
   followed by exact-head success and record the actual result before merge.
5. After merge, record candidate-to-squash tree or exact-content identity,
   main CI, hierarchy, issue-body and mirror synchronization, and an honest
   issue disposition.

The live status remains mechanical and advisory. It does not certify semantic
inventory completeness or reviewer independence. Fork-head and
replay/backfill ownership belong to #4801; required-status and ruleset policy
belong to #4802.

The acceptance boundary for #4803 is this two-file documentation and template
change, a clean exact-candidate source review, a separate issue-resolution
audit, the same-repository lifecycle canary, post-merge verification, and the
honest #4786/#4790 demonstration. Full #4786 completion, the absent #4790
theorem or acceptance of a narrower endpoint, fork behavior, replay/backfill,
and ruleset enforcement remain dependencies or adjacent work.

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
