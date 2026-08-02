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
`scripts/completion_claim_live.py`. The live adapter publishes the
commit-status context `completion-claim/live` on the exact pull-request head.
Under active ruleset `14892885`, the only mechanically required status for a
pull request targeting `main` is `build` from integration ID `15368`, with
strict latest-base policy and no bypass actors. `completion-claim/live` is
published and observable on the exact head but is not currently a required
check, so its result does not by itself block or authorize a merge. Integration
binding does not authenticate a particular workflow file, trigger, or matrix
producer. Only
offline exit 0 with a well-formed `PASS` report can publish `success`.
Draft-incomplete, deterministic rejection, unexpected checker output, API or
timeout errors, bounded-input violations, snapshot races, and status-write
errors all fail shut. A successful status remains semantically
non-authoritative: it does not certify theorem meaning, parameter or volume
scope, source or citation validity, semantic-unit completeness, issue
resolution, or reviewer independence, and it does not replace exact-head
source review or issue-resolution audit.

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

Issue authority begins only with the anchored references the body declares: the
managed JSON's `Refs` entries, or, for a prose body, its `Refs`, `Part of`, and
`Closes` directives. `Refs` and `Closes` seed the walk; a `Part of` target must
prove itself a true ancestor of a seed. Each fetched issue must be a
same-repository issue, and every formal parent must be an issue rather than a
pull request; a `Refs` target may be a pull request, in which case its chain is
not walked. A missing issue is `ISSUE_NOT_FOUND`. Individual references may be
closed, but at least one seed must resolve to an open issue, otherwise
`MISSING_OPEN_ISSUE_REFERENCE`. The chain is read through structural
issue-parent endpoints; unanchored prose mentions cannot widen the allowlist.
At most 16 total references are accepted. Every exact reference string and
every issue number must be unique, and the managed form additionally requires
at least one `Refs` child seed. These checks run before changed-file, issue, or
history endpoint reads. Issue objects and parent results are memoized across
shared chains, bounding the issue graph to at most 16 seed issue reads plus 64
parent reads.

Structured history is derived from bounded commit-file pages, the requested
commit, its sole parent, ancestry comparison, and exact repository blob
identities. The cited path must have matching `added`, `modified`, or `removed`
commit-file status. Modified content must exist on both sides with distinct
blob SHAs; added and removed content must have the matching existence
transition and blob identity. Unchanged, unrelated, renamed, copied, unknown,
merge, and unreachable history is rejected. Matching those facts does not
certify natural-language relevance, which remains human review.

The production same-head body-edit invalidation and recovery sequence is
completed in the #4803 A–J canary record below. Non-empty push backfill and
fork-owned-head behavior remain production observations for #4801; the
default-branch replay incident and corrective lifecycle are recorded below and
governed by [the authoritative incident record][replay-4801-incident]. Per-PR
concurrency prevents independent active jobs from intentionally writing in
different event-specific groups, but it is not an atomic compare-and-set for
an HTTP status request already issued when cancellation begins. Such
cancelled-run residue remains a residual race and never becomes semantic or
merge authority. Mocked tests exercise these shapes but cannot turn production
behavior into a proven fact. If the pull-request metadata HTTP response itself
is unavailable, malformed, truncated, or oversized before a valid head SHA can
be obtained, no exact head exists on which the adapter can publish pending.
That pre-identity condition is fail-shut in the workflow result but cannot
clear an older commit status. Honest final operational dispositions for
cancellation-window residue, pre-identity failure, and fork limitations remain
under #4801; unsafe fault injection is excluded.

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

### Prose contract (default)

The body mode is decided by the normalized `completion-claims-v1` marker count.
Zero markers select the prose contract below; one or more select the managed
contract in the next section. A body that carries a marker but no single valid
canonical block still fails as `AMBIGUOUS_MANAGED_BLOCK` or
`MALFORMED_MANAGED_BLOCK`: a broken managed block is never an easier way to
pass than a correct one. The report records the selected mode as `body_mode`.

The prose contract is what an ordinary pull-request body must satisfy:

1. Size and Unicode limits are the same in both modes.
2. Raw HTML is rejected by tag shape rather than by every less-than character
   (see the body-syntax section below), so comparison prose is allowed. An
   angle-delimited run that contains `@` and no whitespace is rejected as an
   email autolink even when it is not tag-shaped.
3. A closing keyword that GitHub would act on must appear as a standalone
   canonical trailer line, exactly `Closes #N`, `Fixes #N`, or `Resolves #N`
   with nothing else on the line, inside a paragraph that holds nothing but
   trailer lines. Every closing reference the keyword scanner finds must
   correspond to such a line; otherwise the body is
   `AMBIGUOUS_CLOSING_DIRECTIVE`. This keeps the #4725 shape
   ("This does not Closes #4801.") rejected, together with entity-obscured,
   emphasis-wrapped, lower-case, and trailing-text variants, and the same
   shape split over two lines.
   "Standalone" is a claim about the rendered document, so both halves of that
   comparison read a masked view of the body in which fenced code blocks and
   inline code spans are masked out, and both require the trailer line's
   paragraph — the maximal run of non-blank lines around it — to contain only
   trailer lines. A line-by-line scan cannot see either fact on its own: it
   reads a bare `Refs #4801` inside a fence, inside a code span that crosses a
   line ending, or in the middle of a negating paragraph as if it were the
   line GitHub renders as a citation. The masked view is the coarser one, so
   nothing it hides can be anchored, and a blank line is CommonMark's — spaces
   and tabs only, never a no-break or zero-width space. A masked container is
   never blank-line shaped either, so no masking can invent the paragraph break
   a standalone trailer needs. Details are in the body-syntax section below.
4. Close vocabulary that carries no `#N` reference is ordinary prose and is
   allowed, because GitHub does nothing with it.
5. Non-closing references are the anchored forms `Refs #N` and `Part of #N`,
   under the same standalone-trailer rule: every pairing the keyword scanner
   finds must also be a line that is exactly `Refs #N` or `Part of #N`, and the
   two are compared as multisets of kind and number; otherwise the body is
   `AMBIGUOUS_NON_CLOSING_DIRECTIVE`. One such line may list several references
   after the keyword, separated by single spaces (`Refs #4850 #4851 #4830`, a
   shape this repository already writes), and each number counts on its own.
   The closing keywords keep the one-per-line rule instead: several numbers on
   a line GitHub acts on is a real auto-close ambiguity, while a non-closing
   line closes nothing. Any wider separator — a comma, a second space, a
   no-break space, or trailing text — is not a run, so the scan and the trailer
   grammar disagree and the body is refused, and a line too long to be any
   trailer is not one either. These numbers widen issue authority — they seed
   the live hierarchy walk — so a negated, quoted, fenced, code-spanned,
   emphasized, line-split, trailing-text, or link-labelled `Refs #N` is refused
   or ignored rather than honoured for a reference the body does not really
   carry. Only a bare same-repository `#N` is supported; an `owner/repo#N` or
   URL form is `UNSUPPORTED_ISSUE_REF_FORM`, since another repository's number
   space cannot be verified here.
6. At least one anchored reference (`Refs`, `Part of`, or `Closes`) is
   required, otherwise `MISSING_ISSUE_REFERENCE`. At most 16 anchored
   references, 8 closing trailers, and 64 distinct bare mentions are accepted;
   exceeding any of those is `TOO_MANY_ISSUE_REFERENCES`. Each cap is applied
   while the references are read, so a body that lists far more than the cap
   allows is refused without being parsed in full. Repeating one issue number
   across anchored references is `DUPLICATE_ISSUE_REF`.
7. Every non-closing anchored number must be in `allowed_issue_refs`,
   otherwise `UNMANAGED_ISSUE_REF`.
8. A bare `#N` with no directive in front of it is an informational mention.
   It is neither verified nor allowed to widen issue authority; it is recorded
   as an `unverified_issue_mention` human-review entry. GitHub's `GH-N`
   shorthand is recorded the same way, so it stays visible rather than being
   dropped from the report; it is never an anchored form.
9. The four claim families a prose body cannot express — candidate diff
   self-report, review records, semantic claims, and history claims — are not
   machine-checked in this mode. Each one is recorded as an
   `unverified_claim_family` human review so the reduction stays visible in the
   report rather than silent. Draft state is recorded the same way; prose mode
   has no `PENDING` placeholder mechanism and therefore never returns
   `DRAFT_INCOMPLETE`.
10. This is an honest reduction in strength. Everything in point 9 is
    recoverable by opting back into the managed block, which is unchanged.

Snapshot consistency (body digest, base and head SHA, path digest, changed-file
count) and every API-boundary bound are format-independent and apply in both
modes.

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
  real-axis identification exist under stated hypotheses. The downstream
  `correlationInfinite_latticeGraph_general_hasDerivAt_field_high_temp`
  declaration now converts that limit into a real derivative for a nonempty
  general observable, normalized `⟨a,b,1⟩`, small `a`, and
  `0 < b < r < π/2`. The disposition is `implemented` at that limited scope.
- **#4790 residual infinite-volume contract.** Positive declaration evidence
  now exists only for the normalized reduced-field window above. The endpoint
  `b = 0`, arbitrary physical-parameter rescaling, the full nonperturbative
  range, and a U3/series derivative identity, sign, or uniform bound remain
  outside that theorem. At the post-merge checkpoint for PR #4810, this
  declaration upgraded the broader mathematical disposition from `unresolved`
  to `partial`. The current durable GitHub acceptance records for #4790 govern
  its issue lifecycle separately; this tracked demonstration does not.

The [final #4803 closure audit][audit-4803-final] records the completed
semantic-evidence protocol and A–J lifecycle without upgrading #4786, #4790,
or #4796. This partial demonstration does not satisfy those issues' own
closure criteria.

### Same-repository canary record

The same-repository lifecycle completed under #4803. Each durable observation
records its event, run URL, exact head, status sequence, and cancelled-run or
status residue.

The [superseding canary design correction][design-4803-canary] replaces the
original opened-event expectation and canary ordering. The original bounded
design continues to govern every other scope, evidence, review, reset, and
lifecycle requirement.

[design-4803-canary]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5130003919

The [durable A/B/C observation record][canary-4803-abc] carries the run URLs,
exact heads, status sequences, timestamps, offline report, trusted-checkout
evidence, and status residue:

[canary-4803-abc]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5130004142

1. **A, opened.** The empty kickoff head received `PENDING` and then `FAILURE`
   with `INVALID_CHANGED_PATH`. This supersedes the pre-observation
   `DRAFT_INCOMPLETE` expectation because empty-path validation occurred
   before review-field evaluation.
2. **B, edited.** A body edit on the unchanged empty kickoff head again
   received `PENDING` and then `FAILURE` with `INVALID_CHANGED_PATH`.
3. **C, synchronize.** The exact two-file candidate with both review records
   still `PENDING` received live `PENDING` and then `FAILURE` with the generic
   description `OFFLINE_CHECK_FAILED`. A separate offline evaluation of the
   same exact candidate and body returned `DRAFT_INCOMPLETE` with exactly two
   `PENDING_REVIEW` diagnostics, one for each required record.

The A and B results are fail-shut evidence, but neither is an observed
`DRAFT_INCOMPLETE` result. The generic C live description does not expose the
offline diagnostics and is not an exact-head success. The later durable
records complete the lifecycle:

4. **D/E/F, synchronize corrections.** The first correction and the pre-sync
   body edit plus second correction are recorded with old/new-head status and
   trusted-checkout evidence in [D][canary-4803-d] and
   [E/F][canary-4803-ef].
5. **G, reviewed exact-body success.** Both exact-head review records were
   bound and the unchanged candidate reached pending followed by success in
   [G][canary-4803-g].
6. **H, same-head invalidation.** One review field returned to canonical
   `PENDING`; the unchanged head received pending followed by failure in
   [H][canary-4803-h].
7. **I, same-head recovery.** Restoring the durable review URL on the
   unchanged head produced pending followed by success in
   [I][canary-4803-i].
8. **J, unchanged-head ready.** The ready transition produced another
   pending-to-success evaluation in [J][canary-4803-j].
9. **Post-merge and disposition.** Candidate/squash identity, merged-main CI,
   hierarchy and source-of-truth synchronization, the non-recursive INDEX
   correction, and the completed #4803 disposition are recorded in the
   [final audit][audit-4803-final].

[canary-4803-d]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5130018031
[canary-4803-ef]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5130070443
[canary-4803-g]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5130152008
[canary-4803-h]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5130197969
[canary-4803-i]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5130243470
[canary-4803-j]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5130290648
[audit-4803-final]: https://github.com/phasetr/ising-model/issues/4803#issuecomment-5131139086

The [independent #4802 audit][review-4802-enforcement] and
[final #4802 closure audit][audit-4802-final] record the active enforcement:
ruleset `14892885`, history version `44903447`, an empty bypass list, strict
latest-base policy, and the integration-bound contexts `build` and
`completion-claim/live`. Those contexts were mechanically required for a pull
request targeting `main` at that time; the ruleset's current required-check
list contains only `build`, so that audit's `completion-claim/live` requirement
is no longer active. Their integration IDs do not authenticate a
particular workflow file, trigger, or matrix producer. A successful live
status remains semantically non-authoritative and does not replace exact-head
source review or issue-resolution audit. Fork-head and replay/backfill
ownership remain with #4801.

The final audit records #4803's bounded two-file protocol, separate reviews,
same-repository A–J lifecycle, post-merge verification, and honest
#4786/#4790 demonstration as completed. Required-context enforcement does not
make the live status semantic authority. It does not certify theorem meaning,
source or citation validity, semantic completeness, issue resolution, or
reviewer independence. Non-empty push backfill, fork-owned-head behavior, and
final operational dispositions for cancellation-window residue, pre-identity
failure, and fork limitations remain human judgments under #4801. Replay
lifecycle and disposition are owned by the authoritative incident record
below.

[review-4802-enforcement]: https://github.com/phasetr/ising-model/issues/4802#issuecomment-5133601140
[audit-4802-final]: https://github.com/phasetr/ising-model/issues/4802#issuecomment-5133631946

### Default-branch replay incident record

The [authoritative replay incident][replay-4801-incident] records that the
first exact-one procedure failed: two `completion_claim_replay` dispatches
were sent for the fully bound PR #4809 head
`df96820621ef72a4d94dd8ab11461a6f13949a87`.

1. [Run 30546819296][replay-4801-cancelled] used event
   `repository_dispatch` and trusted default-branch workflow SHA
   `31a01b6b0fa91dd2c7babf03f56181b5b2dd844a`. Discovery selected PR #4809,
   then the overlapping evaluation was cancelled. The run conclusion was
   `CANCELLED`.
2. [Run 30546834736][replay-4801-success] used the same event and trusted
   workflow SHA, selected exactly PR #4809, and completed evaluation. The
   exact candidate head received `PENDING` at `2026-07-30T13:25:41Z`, then
   `SUCCESS` at `2026-07-30T13:25:45Z`.

Both runs checked out only the trusted default-branch workflow revision;
neither checked out or executed the candidate head. The observations establish
replay routing, shared per-PR cancellation, and one complete replay evaluation,
but they do not satisfy the requirement to send exactly one dispatch. No
status write was attributed to the cancelled first evaluation, which does not
prove that cancellation can never leave residue after a request is issued.

At this incident checkpoint, exactly one corrective replay was required after
the corrected exact head had current CI, independent reviews, bound-body
currency, and normal live success. Any later run and disposition are carried
by [the authoritative incident record][replay-4801-incident], updated in place.
This historical paragraph does not assert the replay lifecycle's current
state. Non-empty push backfill, fork-owned-head production behavior, and final
operational dispositions for cancellation-window residue, pre-identity
failure, and fork limitations remain unresolved under #4801.

[replay-4801-incident]: https://github.com/phasetr/ising-model/issues/4801#issuecomment-5131434810
[replay-4801-cancelled]: https://github.com/phasetr/ising-model/actions/runs/30546819296
[replay-4801-success]: https://github.com/phasetr/ising-model/actions/runs/30546834736

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
removal, the body is scanned for markup delimiters. A managed body must contain
no less-than character (`<`) at all. A prose body must contain no `<`
immediately followed by a letter, `!`, `/`, or `?`, and no angle-delimited run
that contains `@` and no whitespace; a comparison such as `value < bound` is
therefore accepted in prose mode and rejected in managed mode, while
`a < b@c > d` stays accepted because whitespace breaks that run. All these
checks run before managed-block extraction and report `RAW_HTML_FORBIDDEN`. The
checker does not parse HTML and has no tag-length cutoff: comments, block
containers, tags, closing or self-closing tags, quoted or multiline attributes,
URI autolinks, entity-encoded delimiters, and fullwidth delimiters all
normalize to a tag-shaped delimiter. An email autolink is the one angle form
that need not be tag-shaped, because its local part may start with a digit or a
symbol (`<1@example.test>`), so the autolink shape catches it instead. Every
form above is rejected in both modes, and links must use ordinary Markdown link
syntax.

### Issue references

In a managed body, `references.closing` is mandatory and must be empty, and the
body is rejected if it contains any standalone, case-insensitive official
GitHub closing directive token
(`close`, `closes`, `closed`, `fix`, `fixes`, `fixed`, `resolve`, `resolves`,
or `resolved`) anywhere in the pull-request body. No issue reference is needed
for rejection. The conservative policy intentionally does not interpret
Markdown: prose, emphasis, inline and reference-style links, link
destinations, code, HTML, and comments are treated alike. HTML entities and
Unicode NFKC forms are normalized first, and format controls cannot split a
token. The bounded one-direction token scanner is linear in the body size.
Managed-body authors must avoid these nine words until the post-merge issue
action.

A prose body uses the same scanner but a narrower rule: a closing keyword only
matters when an issue reference follows it, and every such pairing must also be
a standalone canonical `Closes #N`, `Fixes #N`, or `Resolves #N` trailer line.
The two sets are compared as multisets of issue numbers, so an obscured,
emphasized, lower-case, negated, or comment-suffixed pairing is
`AMBIGUOUS_CLOSING_DIRECTIVE`, while close vocabulary with no attached
reference is ordinary prose.

The only anchored non-closing forms are `Refs #NUMBER` and `Part of #NUMBER`,
and their numbers must be in `allowed_issue_refs`. One line may carry a
single-space-separated run of them (`Refs #4850 #4851`), and the allowlist is
applied to every number in the run. That allowlist is applied to raw `Refs` or
`Part of` directives everywhere in the body, so copied evidence cannot hide a
wrong issue number outside the managed block. The managed block's own
`references.non_closing` entries stay one number per string. Cross-repository
`owner/repo#N` and issue-URL forms are not accepted as references.

A prose body holds the non-closing directives to the standalone-trailer rule as
well, and by the same multiset comparison. The asymmetry with the closing forms
would otherwise be a fail-open in the other direction: a closing keyword is
dangerous because GitHub acts on it, while a non-closing keyword is dangerous
because this gate acts on it — `Refs` seeds the live issue hierarchy, so an
unanchored one could satisfy both `MISSING_ISSUE_REFERENCE` and
`MISSING_OPEN_ISSUE_REFERENCE` with a number the body never really cited. The
`GH-N` shorthand is not an anchored form in either mode; it is reported as an
unverified mention so that it cannot pass unseen.

### What "standalone trailer line" means exactly

Both scans a prose body's anchoring rests on — the raw line scan and the
normalized keyword scan — read a masked view of the body, and both apply a
paragraph rule. Neither scan can otherwise tell a rendered citation from text
that merely looks like one on its own line.

Every one of them takes its lines from a single splitter, and that splitter uses
CommonMark's line-ending grammar: a line ends at a carriage return, at a line
feed, or at a carriage return followed by a line feed, and the pair is one
ending rather than two. Nothing else ends a line. `str.splitlines` would also
break at a form feed, at `U+2028`, and at other separators, and a scan that
broke there would read lines GitHub does not.

Both halves of that rule are load-bearing. The scans once split on line feeds
and stripped a trailing carriage return, so a lone carriage return was an
ordinary character here and a line break on GitHub: a body whose first line is a
triple backtick, a lone carriage return, and one word, followed by a blank line
and a `Refs #N` line, opened a code block this checker never saw. GitHub's
`/markdown` renders that trailer inside the block; the checker anchored it.
Counting the pair twice would fail in the opposite direction, inventing an empty
line inside every CRLF body and isolating a trailer its own paragraph negates.

CRLF bodies — the spelling GitHub's own web editor delivers — were mishandled in
the other direction as well. The blank line that bounds an inline code span was
matched as a line feed, optional spaces, and a second line feed, which a CRLF
body never contains, so a span could run past the paragraph GitHub ends it in
and mask a reference GitHub resolves. That was a withdrawal rather than a
fail-open, and it is fixed by the same splitter. The last forty merged
pull-request bodies contain no lone carriage return and no CRLF at all; neither
their verdicts nor their masked views change.

Masking replaces every fenced code block, including its delimiters and an
unclosed fence's run to the end of the body, and every inline code span, where
a run of N backticks is closed by the next run of exactly N backticks within
the same paragraph. Fences are masked first, so a backtick inside a fence
cannot open a span. Masked characters keep their position and every line ending
survives, so the two scans still describe the same body and can be compared.

One filler serves every container, and it is neither alphanumeric, nor a
Markdown separator, nor whitespace. It is not a separator because a blank
filler would let a directive scan step across the removed words onto a later
reference and read a pairing the body does not contain. It is not whitespace
because a masked region that crosses a line ending would otherwise leave an
apparently empty line, faking the paragraph break that makes a trailer
standalone.

Fences once masked to spaces for the line scan, on the argument that a fenced
block really is a block boundary and a trailer directly under one is
standalone. That reading made this checker's fence bookkeeping load-bearing,
and the bookkeeping is not CommonMark's: CommonMark measures a fence's
indentation against its enclosing container and closes that container's fences
when the container ends, while this scan matches columns against the document
alone. A fence opened inside a list item and closed at column 0 split the two
readings, and the space filler then turned that disagreement into a
manufactured paragraph break, so a `Refs #N` line GitHub renders inside a code
block was anchored as a trailer. A container-complete fence tracker is not the
fix here; removing the blank-line-shaped filler is, because it makes any such
disagreement mask the wrong characters instead of inventing a paragraph
boundary. The cost is that a trailer directly below a fence now needs the
blank line every other trailer needs.

Removing the filler bounds the damage a fence disagreement can do, but it does
not remove the disagreement, because a blank line the *author* wrote survives
masking. A body shaped "bullet, indented opener, column-0 closer, blank line,
`Refs #N`" therefore still isolated a trailer that GitHub renders as code text.

The fence scan now handles that shape at its source. Any line inside a fence
that stands shallower than the opener admits two readings and this scan cannot
choose between them. Either the line belongs to the fence — its content stands
at whatever column it likes, and CommonMark lets a closer sit at any column up
to three whatever its opener did — or the container holding the fence ended
there, in which case CommonMark force-closes the fence with no delimiter of its
own and offers the same line to the block starts again at the outer level, where
a bare delimiter run opens a new fence.

Whichever line is too shallow ends the container, closer-shaped or not. That is
the whole rule, and it took two rounds to reach: reading the closer's column
alone left the same boundary open through every other line, so a body whose
*content* line reached column 0 still anchored a trailer GitHub renders as code.
GitHub's `/markdown` gives one reading for each of these three, which is why
none of them may be assumed:

````text
(a) a closer too shallow  (b) content too shallow       (c) parity decides it
- Verified with:          - Verified with:               ```
  ```                       ```                         ```
  lake build              lake build                    ```
```                         ```                         Refs #4801

Refs #4801                Refs #4801
````

GitHub renders (a) as two code blocks with the trailer inside the second. It
renders (b) as an empty code block, a `lake build` paragraph, and a second,
unclosed code block holding the blank line and the trailer — the item's fence
was force-closed by a line that carries no delimiter at all. In (c) the first
delimiter opens, the second closes, and the third opens an unclosed block that
swallows the trailer.

A blank line is not a shallow line, however wide it is: it ends no list item —
it only makes the list loose — so a fence that holds one is still open below it.
A tab is not a shallow line either, because CommonMark measures a container's
continuation in columns and a tab advances to the next multiple of four.

The two readings disagree about the parity of every delimiter below, so each
one's code is the other's prose and their union is the whole tail. The scan
masks that tail. This is not a blunt over-approximation but exactly the union,
and it is the only sound choice: committing to "the fence closed" is the
original bug, and committing to "the container ended" is wrong in the other
direction — in the third body above it would read the second delimiter as a
closer and leave a trailer GitHub renders inside an unclosed block in the open.

The cost is over-masking, and it is charged in one direction only. Where the
indentation was decorative rather than a container, the tail masking is wider
than GitHub's code, so a reference GitHub would resolve is withdrawn: it is not
anchored, it is reported as an unverified mention, and a body whose only
reference is withdrawn is rejected. One consequence is worth stating plainly: a
disallowed non-closing reference inside an over-masked tail stops raising
`UNMANAGED_ISSUE_REF` and is downgraded to an unverified mention, so the
allowlist is enforced on fewer references for such a body.

That cost is real and it is measured. Enumerating a fence inside every container
shape with every combination of opener, content, and closer indentation gives
1,494 bodies the generalized rule withdraws that the closer-only rule anchored;
a sample of 250 of them, rendered by `/markdown`, splits 39 references GitHub
resolves nothing of — the fail-open the rule exists to close — against 211
GitHub does resolve. The synthetic ratio is not the operational one: of the 300
most recently merged pull-request bodies in this repository, three carry an
indented fence opener at all, none carries a line inside a fence shallower than
its opener, and no verdict and no masked view changes for any of the 300.

Two rounds closed this family, and what makes it closed is not the count of
shapes tested but where an anchored trailer can stand. A trailer line matches
only at column 0: the grammar admits no indentation, no blockquote marker, and
no other prefix, so every reference this checker can anchor lies on a line that
begins at column 0. Of CommonMark's blocks only three render their text
literally — an indented code block, which needs four columns and so contains no
column-0 line; an HTML block, which the raw-HTML guard rejects outright; and a
fenced code block. A fence holding a column-0 line cannot live in a container
that indents its content, because that line would end the container and force
the fence closed, so its opener stands at column three or less and the opener
pattern sees it. What is left is parity — whether a delimiter this scan matched
is the delimiter GitHub matched — and parity is exactly what the tail rule gives
up on wherever a container may have intervened. It gives up on more than
CommonMark needs, never less: a line shallower than the opener is shallower than
the container's own content column, since the opener itself stands in that
container.

The paragraph rule is that a trailer line counts only inside a paragraph — the
maximal run of non-blank lines containing it — that holds trailer lines and
nothing else. A blank line is CommonMark's: spaces and tabs only, and only one
the author wrote, since masking produces none. This is what rejects prose
bleeding in from the line above or below, including a blockquote's lazy
continuation (`> Quoted evidence:` then an unquoted `Refs #4801`) and a
negation split over two lines. Several trailer lines may share one paragraph,
and a trailer that ends the body needs nothing after it, which is the shape this
repository writes.

Masking and the paragraph rule are deliberately coarser than a Markdown parser,
so they refuse in both directions rather than resolve ambiguity. A reference in
a container is not anchored and is reported as an unverified mention; a trailer
line glued to a heading, a list item, a table row, a link reference definition,
or any other block reports `AMBIGUOUS_CLOSING_DIRECTIVE` or
`AMBIGUOUS_NON_CLOSING_DIRECTIVE` even where GitHub would render it as its own
paragraph. Regex-based container detection cannot be complete; the contract is
that an unrecognized container costs a rejection, never an anchored reference.

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
A separate prose-mode class pins the default contract: a realistic prose body
passes and reports its four `unverified_claim_family` entries, a missing
anchored reference fails, negated and decorated closing forms fail while a
standalone trailer and bare close vocabulary pass, the same disguises of
`Refs`/`Part of` (negated, padded, blockquoted, line-split, link-labelled,
multi-line link-labelled, lazily continued from a blockquote, negated across
two lines, trailing-text, lower-case, emphasized, entity-obscured) fail while
standalone non-closing trailers pass, a single trailer line listing
several references anchors each of them while its malformed spellings
(comma-separated, double-spaced, no-break-spaced, hash-less, glued, quoted,
URL-suffixed) fail and a multi-number closing trailer stays ambiguous, a `GH-N`
shorthand surfaces as an unverified mention, every raw-HTML variant still
fails — including digit-leading, underscore-leading, and dot-leading email
autolinks — while `value < bound` and `a < b@c > d` pass, a malformed managed
marker never falls through to prose, cross-repository and URL reference forms
fail, and the reference and mention caps hold. The container rules have their
own cases: a bare, padded, multi-number, tilde-fenced, or `Closes` trailer
inside a fence and a multi-line or single-line code span anchor nothing and
surface as unverified mentions, neither a code span crossing a line ending nor
a fence can fake the blank line that isolates a trailer, every masked container
keeps its lines non-blank, seven shapes of a fence opened inside a bullet,
ordered-list, or blockquote container and closed at column 0 anchor nothing
with the trailer glued below them, only a spaces-and-tabs blank line
separates paragraphs, and the
accepted trailer shapes (blank-separated, last line with no newline, several
trailer lines together, a blank line below a fence) are pinned beside the
rejected glued ones, which now include a trailer directly below a fence.
The line-ending grammar has its own cases: a fence opener, a fence info string,
and an outdented closer each hidden behind a lone carriage return are refused,
a carriage return closing a fence, a pair of them separating a paragraph, and a
blank line spelled either with carriage returns or with CRLF ending a code span
are honoured, a CRLF pair stays one ending inside a negated paragraph, the
managed block reads the same in all three spellings, and the splitter is pinned
to break at those three endings and at no other separator.
Weakened anchored-reference, closing-trailer, non-closing-trailer,
container-masking, trailer-isolation, mask-filler, blank-container-filler,
line-feed-only splitting, carriage-return-splitting, and
autolink guards are killed as mutants, the
autolink scan is timed past one MiB, container masking is timed on fence and
backtick storms, and a reference run far past every cap is pinned to fail in
seconds and under 8 MiB instead of being parsed in full first.
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
size errors, and workflow security mutations. Prose bodies are covered end to
end: identical authority from prose and managed bodies, preserved offline
diagnostic codes, cross-repository and pull-request-parent rejection, a passing
closed non-seed reference, all-closed seeds, a missing issue, an unreachable
`Part of`, closing versus referencing a pull request, exact-head success, a
one-line `Refs` run whose every number seeds the walk, thirteen disguised
`Refs` shapes that fail shut without ever fetching the issue they name, a
fenced-only reference that reaches neither the issue endpoint nor its parent,
and mutants for the open-seed guard and for a prose fallback that would bypass
a managed block.
