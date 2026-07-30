# Completion-claim evidence gate

The phase-1 gate validates a pull request's declared evidence against a small,
trusted, offline context snapshot. It does not query GitHub, inspect the local
repository, run commands, read credentials, or decide whether a mathematical or
historical statement is true.

`PASS` means only that the structured fields agree with the supplied context.
It is not a semantic completion verdict. Every semantic claim and every
semantic claim level is reported as `HUMAN_REVIEW_REQUIRED`.

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
canonical opener is `AMBIGUOUS_MANAGED_BLOCK`; an unclosed canonical block is
`MALFORMED_MANAGED_BLOCK`. Unknown or missing keys, duplicate JSON keys,
malformed types, and unsupported schema versions also fail closed.

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
```

The suite includes baseline and incident-derived fixtures for #4709, #4718,
and PR #4800. It mutates SHAs, paths, counts, digests, references, review heads,
structured history commits/paths/actions, delivery, fences, keys, and ready
placeholders. It probes normalized completion-directive forms, separators longer
than the former cutoff, emphasized and reference-link directive tokens, long
links and HTML tags, exact canonical fences, and rejected blockquote/list or
cross-container variants. Directive scans beyond one MiB remain bounded. The
suite also covers malformed URLs, lone surrogates, invalid controls,
boolean-as-integer inputs, and unmanaged prose; kills representative weakened
checker mutants; pins `.self-local` path coverage; and verifies that the
checker imports no process, network, or dynamic-execution facility.
