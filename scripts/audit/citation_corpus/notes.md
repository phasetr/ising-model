# Frozen extractor corpus, Markdown half

Read only by `scripts/test_citation_audit.py`, never by the audit itself. Editing
this file is editing the expectation, and `expected.tsv` must move with it in the
same commit.

The proof lives in `Corpus/Resolved.lean` and is complete.

The old `Corpus/Gone.lean` was deleted in a refactor.

A basename such as `Alone.lean` is a name, and `Twin.lean` is ambiguous.

Wildcards such as `*.lean`, and the bare `.lean` extension, are not citations.

Everything now lives in `Corpus/Moved.lean`,
and it is re-exported for backward compatibility by
the legacy `Moved.lean` shim.
