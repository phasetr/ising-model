#!/usr/bin/env python3
"""Hermetic tests for the offline completion-claim evidence gate."""

from __future__ import annotations

import ast
import copy
import json
import sys
import time
import types
import unittest
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
FIXTURE_DIR = SCRIPT_DIR / "testdata" / "completion_claim_gate"
GATE_PATH = SCRIPT_DIR / "completion_claim_gate.py"
REPO_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

import completion_claim_gate as gate  # noqa: E402


def managed_body(
    payload: dict[str, Any],
    prefix: str = "",
    opening: str = gate.BLOCK_FENCE,
    closing: str = "```",
) -> str:
    encoded = json.dumps(payload, indent=2, sort_keys=True)
    return f"{prefix}{opening}\n{encoded}\n{closing}\n"


def fixture(name: str) -> dict[str, Any]:
    return json.loads((FIXTURE_DIR / name).read_text(encoding="utf-8"))


def set_field(value: dict[str, Any], dotted: str, replacement: Any) -> None:
    target: Any = value
    parts = dotted.split(".")
    for part in parts[:-1]:
        target = target[int(part)] if isinstance(target, list) else target[part]
    final = parts[-1]
    if isinstance(target, list):
        target[int(final)] = replacement
    else:
        target[final] = replacement


def fullwidth_ascii(text: str) -> str:
    return "".join(chr(ord(char) + 0xFEE0) for char in text)


class GateHarness:
    @classmethod
    def setUpClass(cls) -> None:
        source = fixture("issue_4709.json")["control"]
        cls.context = source["context"]
        cls.payload = source["payload"]

    def run_gate(
        self,
        *,
        context: dict[str, Any] | None = None,
        payload: dict[str, Any] | None = None,
        prefix: str = "",
        body: str | None = None,
        module: types.ModuleType = gate,
    ) -> tuple[int, dict[str, Any]]:
        selected_context = copy.deepcopy(context if context is not None else self.context)
        selected_payload = copy.deepcopy(payload if payload is not None else self.payload)
        selected_body = body if body is not None else managed_body(selected_payload, prefix)
        return module.evaluate(selected_context, selected_body)

    def assert_code(
        self,
        expected: str,
        *,
        context: dict[str, Any] | None = None,
        payload: dict[str, Any] | None = None,
        prefix: str = "",
        body: str | None = None,
        module: types.ModuleType = gate,
    ) -> dict[str, Any]:
        code, report = self.run_gate(
            context=context,
            payload=payload,
            prefix=prefix,
            body=body,
            module=module,
        )
        self.assertEqual(code, gate.EXIT_FAIL, report)
        self.assertEqual(report["machine_status"], gate.FAIL)
        codes = [entry["code"] for entry in report["diagnostics"]]
        self.assertIn(expected, codes, report)
        return report

    def mutated_payload(self, field: str, value: Any) -> dict[str, Any]:
        payload = copy.deepcopy(self.payload)
        set_field(payload, field, value)
        return payload


class GateTest(GateHarness, unittest.TestCase):
    def test_ready_control_passes_nonvacuously(self) -> None:
        code, report = self.run_gate()
        self.assertEqual(code, gate.EXIT_PASS, report)
        self.assertEqual(report["machine_status"], gate.PASS)
        self.assertEqual(len(self.context["changed_paths"]), 2)
        self.assertNotEqual(self.payload["candidate"]["sorted_path_digest"], "sha256:" + "0" * 64)
        review_items = [
            item for item in report["human_reviews"] if item["kind"] == "review_record"
        ]
        self.assertEqual(len(review_items), 2)
        self.assertTrue(
            all(item["status"] == gate.HUMAN_REVIEW_REQUIRED for item in review_items)
        )

    def test_sha_nibble_mutation_fails(self) -> None:
        self.assert_code(
            "HEAD_SHA_MISMATCH",
            payload=self.mutated_payload("candidate.head_sha", "b" * 39 + "c"),
        )

    def test_add_path_fails_count_and_digest(self) -> None:
        context = copy.deepcopy(self.context)
        context["changed_paths"].append("docs/completion-claims.md")
        _, report = self.run_gate(context=context)
        codes = {entry["code"] for entry in report["diagnostics"]}
        self.assertEqual(report["machine_status"], gate.FAIL)
        self.assertTrue({"FILE_COUNT_MISMATCH", "PATH_DIGEST_MISMATCH"} <= codes)

    def test_remove_path_fails_count_and_digest(self) -> None:
        context = copy.deepcopy(self.context)
        context["changed_paths"].pop()
        _, report = self.run_gate(context=context)
        codes = {entry["code"] for entry in report["diagnostics"]}
        self.assertEqual(report["machine_status"], gate.FAIL)
        self.assertTrue({"FILE_COUNT_MISMATCH", "PATH_DIGEST_MISMATCH"} <= codes)

    def test_count_mutation_fails(self) -> None:
        self.assert_code(
            "FILE_COUNT_MISMATCH",
            payload=self.mutated_payload("candidate.changed_file_count", 1),
        )

    def test_digest_nibble_mutation_fails(self) -> None:
        old = self.payload["candidate"]["sorted_path_digest"]
        replacement = old[:-1] + ("a" if old[-1] != "a" else "b")
        self.assert_code(
            "PATH_DIGEST_MISMATCH",
            payload=self.mutated_payload("candidate.sorted_path_digest", replacement),
        )

    def test_duplicate_block_fails(self) -> None:
        block = managed_body(self.payload)
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=block + block)

    def test_duplicate_json_key_fails(self) -> None:
        raw = '{"schema_version":1,"schema_version":1}'
        self.assert_code(
            "DUPLICATE_JSON_KEY",
            body=f"{gate.BLOCK_FENCE}\n{raw}\n```\n",
        )

    def test_duplicate_path_fails(self) -> None:
        context = copy.deepcopy(self.context)
        context["changed_paths"].append(context["changed_paths"][0])
        self.assert_code("DUPLICATE_PATH", context=context)

    def test_unknown_payload_key_fails(self) -> None:
        payload = copy.deepcopy(self.payload)
        payload["surprise"] = True
        self.assert_code("UNKNOWN_KEY", payload=payload)

    def test_unknown_claim_level_fails(self) -> None:
        payload = copy.deepcopy(self.payload)
        payload["claim_levels"] = ["trust_me"]
        self.assert_code("UNKNOWN_CLAIM_LEVEL", payload=payload)

    def test_review_sha_mutation_fails(self) -> None:
        self.assert_code(
            "REVIEW_HEAD_MISMATCH",
            payload=self.mutated_payload("review_records.0.head_sha", "c" * 40),
        )

    def test_wrong_issue_ref_fails(self) -> None:
        self.assert_code(
            "INVALID_ISSUE_REF",
            payload=self.mutated_payload("references.non_closing.0", "Refs #4709"),
        )

    def test_nonempty_closing_refs_fail(self) -> None:
        payload = copy.deepcopy(self.payload)
        payload["references"]["closing"] = ["Refs #4801"]
        self.assert_code("CLOSING_REFERENCES_NOT_EMPTY", payload=payload)

    def test_negated_directive_in_prose_fails(self) -> None:
        self.assert_code(
            "DIRECTIVE_KEYWORD_FORBIDDEN",
            prefix="This does not Closes #4801.\n",
        )

    def test_all_official_directive_tokens_are_forbidden_without_a_reference(self) -> None:
        for keyword in gate.OFFICIAL_CLOSE_KEYWORDS:
            prefix = f"Ordinary prose says **{keyword.upper()}** without an issue number.\n"
            with self.subTest(prefix=prefix):
                self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)

    def test_nfkc_entity_and_markdown_wrappers_cannot_hide_directives(self) -> None:
        variants = [
            "\uff26\uff49\uff58\uff45\uff53\n",
            "[Resolves](https://example.test/reason)\n",
            "[Fixes][reason]\n",
            "`Close`\n",
            "Fi&#120;es\n",
            "Fi\u200bxes\n",
        ]
        for prefix in variants:
            with self.subTest(prefix=prefix):
                self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)

    def test_underscore_emphasis_cannot_hide_keyword(self) -> None:
        for prefix in ["_Fixes_ #4801\n", "__Fixes__ #4801\n", "***Fixes*** #4801\n"]:
            with self.subTest(prefix=prefix):
                self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)

    def test_directives_anywhere_in_long_link_text_fail(self) -> None:
        prefix = "[label](https://example.test/" + "x" * 513 + "/Fixes)\n"
        self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)

    def test_directive_tokens_with_arbitrary_following_text_fail(self) -> None:
        variants = [
            "Closes" + " " * 65 + "ordinary\n",
            "Fixes" + "\n" * 100 + "ordinary\n",
            "Resolved" + "*_~`-:;,.()[]" * 20 + "ordinary\n",
        ]
        for prefix in variants:
            with self.subTest(length=len(prefix)):
                self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)

    def test_code_comment_and_fence_directive_policy_is_pinned(self) -> None:
        variants = [
            "`Fixes`\n",
            "~~~text\nResolved\n~~~\n",
        ]
        for prefix in variants:
            with self.subTest(prefix=prefix[:20]):
                self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)

    def test_raw_html_block_tag_and_autolink_forms_are_forbidden(self) -> None:
        variants = [
            "<!-- hidden block -->\n",
            "<details>\n",
            "<div>\n",
            "<script>\n",
            "<template>\n",
            "<style>\n",
            "<textarea>\n",
            "</div>\n",
            "<br />\n",
            '<div data-note="quoted > value">\n',
            "<div\nclass=\"multiline\">\n",
            "<https://example.test/evidence>\n",
            "<reviewer@example.test>\n",
        ]
        for prefix in variants:
            with self.subTest(prefix=prefix[:30]):
                self.assert_code("RAW_HTML_FORBIDDEN", prefix=prefix)

    def test_hidden_html_containers_cannot_wrap_the_control_payload(self) -> None:
        containers = [
            ("<details>", "</details>"),
            ("<div>", "</div>"),
            ("<script>", "</script>"),
            ("<template>", "</template>"),
            ("<style>", "</style>"),
            ("<textarea>", "</textarea>"),
        ]
        for opening, closing in containers:
            body = f"{opening}\n{managed_body(self.payload)}{closing}\n"
            with self.subTest(opening=opening):
                self.assert_code("RAW_HTML_FORBIDDEN", body=body)

    def test_encoded_and_fullwidth_less_than_normalize_to_forbidden(self) -> None:
        fullwidth_less_than = chr(ord("<") + 0xFEE0)
        variants = [
            "&lt;details>\n",
            "&#60;div>\n",
            "&#x3c;script>\n",
            fullwidth_less_than + "template>\n",
            "<\u200bstyle>\n",
        ]
        for prefix in variants:
            with self.subTest(prefix=prefix):
                self.assert_code("RAW_HTML_FORBIDDEN", prefix=prefix)

    def test_raw_html_diagnostic_precedes_directive_diagnostic(self) -> None:
        self.assert_code("RAW_HTML_FORBIDDEN", prefix="<!-- Fixes -->\n")

    def test_comparison_prose_must_avoid_less_than(self) -> None:
        self.assert_code("RAW_HTML_FORBIDDEN", prefix="Measured value < bound.\n")
        code, report = self.run_gate(prefix="Measured value is below the bound.\n")
        self.assertEqual(code, gate.EXIT_PASS, report)

    def test_raw_html_guard_is_linearish_past_one_mibibyte(self) -> None:
        source = "ordinary text " * 85_000 + "&lt;details>"
        self.assertGreater(len(source), 1_048_576)
        started = time.monotonic()
        normalized = gate._normalized_body_text(source)
        with self.assertRaises(gate.GateInputError) as raised:
            gate._reject_raw_html(normalized)
        elapsed = time.monotonic() - started
        self.assertEqual(raised.exception.code, "RAW_HTML_FORBIDDEN")
        self.assertLess(elapsed, 5.0)

    def test_directive_ban_precedes_other_body_diagnostics(self) -> None:
        body = "[Fixes][reason]\n> ```completion-claims-v1\n> {}\n> ```\n"
        report = self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", body=body)
        self.assertEqual(len(report["diagnostics"]), 1)

    def test_raw_wrong_nonclosing_ref_outside_block_fails(self) -> None:
        self.assert_code(
            "UNMANAGED_ISSUE_REF",
            prefix="Copied evidence says Refs #4709.\n",
        )

    def test_raw_wrong_ref_after_long_separator_fails(self) -> None:
        self.assert_code(
            "UNMANAGED_ISSUE_REF",
            prefix="Refs" + "\n" * 100 + "#4709\n",
        )

    def test_push_delivery_fails(self) -> None:
        context = copy.deepcopy(self.context)
        context["delivery"] = "push"
        self.assert_code("INVALID_DELIVERY", context=context)

    def test_ready_placeholder_fails(self) -> None:
        self.assert_code(
            "READY_PLACEHOLDER",
            payload=self.mutated_payload("review_records.0.url", gate.PENDING),
        )

    def test_draft_placeholder_is_incomplete(self) -> None:
        context = copy.deepcopy(self.context)
        context["is_draft"] = True
        payload = self.mutated_payload("review_records.0.url", gate.PENDING)
        code, report = self.run_gate(context=context, payload=payload)
        self.assertEqual(code, gate.EXIT_DRAFT_INCOMPLETE, report)
        self.assertEqual(report["machine_status"], gate.DRAFT_INCOMPLETE)

    def test_draft_deterministic_mismatch_still_fails(self) -> None:
        context = copy.deepcopy(self.context)
        context["is_draft"] = True
        payload = self.mutated_payload("candidate.head_sha", "c" * 40)
        self.assert_code("HEAD_SHA_MISMATCH", context=context, payload=payload)

    def test_all_semantic_kinds_are_human_only(self) -> None:
        payload = copy.deepcopy(self.payload)
        payload["semantic_claims"] = [
            {
                "id": f"semantic-{kind}",
                "kind": kind,
                "statement": f"{kind} evidence requires review.",
                "evidence_urls": [f"https://example.test/{kind}"],
            }
            for kind in sorted(gate.SEMANTIC_KINDS)
        ]
        code, report = self.run_gate(payload=payload)
        self.assertEqual(code, gate.EXIT_PASS, report)
        statuses = [
            entry["status"]
            for entry in report["human_reviews"]
            if entry["kind"] in gate.SEMANTIC_KINDS
        ]
        self.assertEqual(statuses, [gate.HUMAN_REVIEW_REQUIRED] * 3)
        self.assertNotIn(gate.PASS, statuses)

    def test_semantic_claim_levels_are_human_only(self) -> None:
        payload = copy.deepcopy(self.payload)
        payload["claim_levels"] = sorted(gate.SEMANTIC_CLAIM_LEVELS)
        code, report = self.run_gate(payload=payload)
        self.assertEqual(code, gate.EXIT_PASS, report)
        statuses = [
            entry["status"]
            for entry in report["human_reviews"]
            if entry["kind"] == "claim_level"
        ]
        self.assertEqual(
            statuses,
            [gate.HUMAN_REVIEW_REQUIRED] * len(gate.SEMANTIC_CLAIM_LEVELS),
        )

    def test_unmanaged_claims_are_charged_to_human_review(self) -> None:
        prefix = "Future phase work will prove the source claim for issue #4800.\n"
        code, report = self.run_gate(prefix=prefix)
        self.assertEqual(code, gate.EXIT_PASS, report)
        kinds = {entry["kind"] for entry in report["human_reviews"]}
        self.assertTrue(
            {"unmanaged_prose", "unmanaged_issue_reference", "future_plan"} <= kinds
        )
        self.assertNotIn(gate.PASS, {entry["status"] for entry in report["human_reviews"]})

    def test_malformed_url_is_structured_fail_not_traceback(self) -> None:
        payload = self.mutated_payload("review_records.0.url", "https://[::1")
        self.assert_code("INVALID_URL", payload=payload)

    def test_bool_schema_versions_and_integer_fields_fail(self) -> None:
        context = copy.deepcopy(self.context)
        context["schema_version"] = True
        self.assert_code("INVALID_TYPE", context=context)
        payload = copy.deepcopy(self.payload)
        payload["schema_version"] = True
        self.assert_code("INVALID_TYPE", payload=payload)
        payload = self.mutated_payload("candidate.changed_file_count", True)
        self.assert_code("INVALID_TYPE", payload=payload)
        context = copy.deepcopy(self.context)
        context["allowed_issue_refs"] = [True, 4801]
        self.assert_code("INVALID_ISSUE_REF", context=context)

    def test_reusing_context_is_deterministic_and_does_not_mutate_input(self) -> None:
        context = copy.deepcopy(self.context)
        before = copy.deepcopy(context)
        first = gate.evaluate(context, managed_body(self.payload))
        second = gate.evaluate(context, managed_body(self.payload))
        self.assertEqual(first, second)
        self.assertEqual(context, before)

    def test_lone_surrogates_are_structured_unicode_failures(self) -> None:
        for value in ["\ud800", "\udfff"]:
            with self.subTest(codepoint=hex(ord(value))):
                payload = copy.deepcopy(self.payload)
                payload["semantic_claims"] = [
                    {
                        "id": "invalid-unicode",
                        "kind": "source",
                        "statement": value,
                        "evidence_urls": ["https://example.test/evidence"],
                    }
                ]
                self.assert_code("INVALID_UNICODE", payload=payload)

    def test_surrogates_in_path_url_and_key_never_traceback(self) -> None:
        context = copy.deepcopy(self.context)
        context["changed_paths"][0] += "\ud800"
        self.assert_code("INVALID_UNICODE", context=context)
        payload = self.mutated_payload(
            "review_records.0.url",
            "https://example.test/\udfff",
        )
        self.assert_code("INVALID_UNICODE", payload=payload)
        payload = copy.deepcopy(self.payload)
        payload["\ud800"] = "invalid-key"
        self.assert_code("INVALID_UNICODE", payload=payload)

    def test_invalid_controls_fail_but_json_whitespace_controls_are_allowed(self) -> None:
        for value in ["\x00", "\u0085"]:
            with self.subTest(codepoint=hex(ord(value))):
                payload = copy.deepcopy(self.payload)
                payload["semantic_claims"] = [
                    {
                        "id": "invalid-control",
                        "kind": "provenance",
                        "statement": value,
                        "evidence_urls": ["https://example.test/evidence"],
                    }
                ]
                self.assert_code("INVALID_UNICODE", payload=payload)
        payload = copy.deepcopy(self.payload)
        payload["semantic_claims"] = [
            {
                "id": "valid-whitespace-controls",
                "kind": "source",
                "statement": "line one\n\tline two\r",
                "evidence_urls": ["https://example.test/evidence"],
            }
        ]
        code, report = self.run_gate(payload=payload)
        self.assertEqual(code, gate.EXIT_PASS, report)

    def test_invalid_control_in_unmanaged_body_fails(self) -> None:
        self.assert_code("INVALID_UNICODE", prefix="prose\u0085claim\n")

    def test_directive_scanner_is_linearish_on_large_clean_input(self) -> None:
        normalized = ("disclosed prefixes ordinary\n" * 40_000) + "still clean"
        started = time.monotonic()
        spans = gate._keyword_spans(normalized, gate.CLOSE_KEYWORDS)
        elapsed = time.monotonic() - started
        self.assertEqual(spans, [])
        self.assertLess(elapsed, 5.0)

    def test_normalized_directive_scan_is_linearish_past_one_mibibyte(self) -> None:
        cases = [
            "[label](" + "x" * 1_100_000 + "/Fixes)",
            '<span data-long="' + "x" * 1_100_000 + ' Resolved">ordinary</span>',
        ]
        for source in cases:
            with self.subTest(prefix=source[:10]):
                started = time.monotonic()
                normalized = gate._normalized_body_text(source)
                spans = gate._keyword_spans(normalized, gate.CLOSE_KEYWORDS)
                elapsed = time.monotonic() - started
                self.assertTrue(spans)
                self.assertEqual(len(normalized), len(source))
                self.assertLess(elapsed, 5.0)


class DigestTest(unittest.TestCase):
    def test_utf8_byte_order_and_length_framing_are_pinned(self) -> None:
        paths = ["z", "a/b", "\u03b1.lean"]
        expected = "sha256:cb5187a15b084966d9ee2784f53758a1b1f6f263f2b1a2e8d62f9d33a25bce31"
        self.assertEqual(gate.sorted_path_digest(paths), expected)
        self.assertEqual(gate.sorted_path_digest(list(reversed(paths))), expected)

    def test_self_local_lean_has_no_exemption(self) -> None:
        included = gate.sorted_path_digest(
            [".self-local/reports/incident.lean", "scripts/completion_claim_gate.py"]
        )
        excluded = gate.sorted_path_digest(["scripts/completion_claim_gate.py"])
        self.assertEqual(
            included,
            "sha256:c563c95c14b6f005f8c5676a52cbb8be20d8c42003feb49142fe204d4725bcab",
        )
        self.assertNotEqual(included, excluded)

    def test_rejects_absolute_parent_newline_nul_and_backslash(self) -> None:
        invalid = ["/tmp/a", ".", "./a", "a/./b", "../a", "a/../b", "a\nb", "a\x00b", "a\\b"]
        for path in invalid:
            with self.subTest(path=repr(path)):
                with self.assertRaises(gate.GateInputError):
                    gate.sorted_path_digest([path])


class ManagedFenceTest(GateHarness, unittest.TestCase):
    def test_exact_top_level_template_fence_passes(self) -> None:
        code, report = self.run_gate(body=managed_body(self.payload))
        self.assertEqual(code, gate.EXIT_PASS, report)

    def test_noncanonical_managed_openers_are_ambiguous(self) -> None:
        variants = [
            "~~~~completion-claims-v1",
            "   ```completion-claims-v1",
            "````completion-claims-v1",
            "```completion-claims-v1   ",
            "```completion-claims-v1 extra",
        ]
        for opening in variants:
            with self.subTest(opening=opening):
                body = managed_body(self.payload, opening=opening)
                self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)

    def test_canonical_spelling_nested_in_other_fence_is_ambiguous(self) -> None:
        body = "````text\n" + managed_body(self.payload) + "````\n"
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)

    def test_duplicate_canonical_blocks_are_ambiguous(self) -> None:
        block = managed_body(self.payload)
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=block + block)

    def test_unclosed_and_noncanonical_closing_fences_fail(self) -> None:
        encoded = json.dumps(self.payload)
        bodies = [
            f"```completion-claims-v1\n{encoded}\n",
            f"````completion-claims-v1\n{encoded}\n```\n",
            f"```completion-claims-v1\n{encoded}\n````\n",
            f"```completion-claims-v1\n{encoded}\n~~~\n",
            f"```completion-claims-v1\n{encoded}\n   ```\n",
        ]
        for body in bodies:
            with self.subTest(body=body[-20:]):
                expected = (
                    "AMBIGUOUS_MANAGED_BLOCK"
                    if body.startswith("````")
                    else "MALFORMED_MANAGED_BLOCK"
                )
                self.assert_code(expected, body=body)

    def test_wrapped_or_list_managed_attempts_are_ambiguous(self) -> None:
        encoded = json.dumps(self.payload, indent=2)
        for prefix in ["> ", "> > ", " > > ", "- ", "    "]:
            body = "\n".join(
                [prefix + gate.BLOCK_FENCE]
                + [prefix + line for line in encoded.splitlines()]
                + [prefix + "```", ""]
            )
            with self.subTest(prefix=prefix):
                self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)

    def test_marker_outside_the_canonical_opener_is_ambiguous(self) -> None:
        suffix = "> ```completion-claims-v1\n> {}\n> ```\n"
        self.assert_code(
            "AMBIGUOUS_MANAGED_BLOCK",
            body=managed_body(self.payload) + suffix,
        )

    def test_five_normalized_marker_disguises_are_ambiguous(self) -> None:
        variants = [
            "completion&#45;claims-v1",
            fullwidth_ascii(gate.BLOCK_INFO),
            "completion\u200b-claims-v1",
            "completion-claims-v&#49;",
            "&#99;ompletion-claims-v1",
        ]
        for disguised in variants:
            with self.subTest(disguised=disguised):
                body = managed_body(self.payload) + f"Prose marker: {disguised}\n"
                self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)

    def test_mixed_and_multiple_disguised_markers_are_ambiguous(self) -> None:
        suffix = (
            "completion&#45;claims-v1 and completion\u200b-claims-v1 "
            f"and {fullwidth_ascii(gate.BLOCK_INFO)}\n"
        )
        self.assertEqual(gate._normalized_marker_count(suffix), 3)
        self.assert_code(
            "AMBIGUOUS_MANAGED_BLOCK",
            body=managed_body(self.payload) + suffix,
        )

    def test_disguised_opener_is_not_a_raw_canonical_opener(self) -> None:
        body = managed_body(
            self.payload,
            opening="```completion&#45;claims-v1",
        )
        self.assertEqual(gate._normalized_marker_count(body), 1)
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)

    def test_marker_contract_is_case_sensitive(self) -> None:
        body = managed_body(self.payload) + "COMPLETION-CLAIMS-V1\n"
        self.assertEqual(gate._normalized_marker_count(body), 1)
        code, report = self.run_gate(body=body)
        self.assertEqual(code, gate.EXIT_PASS, report)

    def test_normalized_marker_count_is_linearish_past_one_mibibyte(self) -> None:
        source = (
            managed_body(self.payload)
            + "ordinary text " * 85_000
            + "completion&#45;claims-v1"
        )
        self.assertGreater(len(source), 1_048_576)
        started = time.monotonic()
        count = gate._normalized_marker_count(source)
        elapsed = time.monotonic() - started
        self.assertEqual(count, 2)
        self.assertLess(elapsed, 5.0)

    def test_top_open_with_blockquote_close_is_malformed(self) -> None:
        encoded = json.dumps(self.payload, indent=2)
        body = "\n".join(
            [gate.BLOCK_FENCE]
            + encoded.splitlines()
            + ["> ```", ""]
        )
        self.assert_code("MALFORMED_MANAGED_BLOCK", body=body)

    def test_blockquote_open_with_top_close_is_ambiguous(self) -> None:
        encoded = json.dumps(self.payload, indent=2)
        body = "\n".join(
            ["> " + gate.BLOCK_FENCE]
            + ["> " + line for line in encoded.splitlines()]
            + ["```", ""]
        )
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)

    def test_blockquote_depth_mismatch_is_ambiguous(self) -> None:
        body = (
            "> ```completion-claims-v1\n"
            "> > {}\n"
            "> > ```\n"
        )
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)


class IncidentFixtureTest(GateHarness, unittest.TestCase):
    def test_baseline_cases(self) -> None:
        data = fixture("baseline.json")
        self.assertEqual(data["incident"], "baseline")
        self.assertEqual(len(data["cases"]), 3)
        for case in data["cases"]:
            with self.subTest(case=case["id"]):
                code, report = self.run_gate(
                    context=case["context"],
                    payload=case["payload"],
                    prefix=case["body_prefix"],
                )
                self.assertEqual(code, case["expected_exit"], report)
                self.assertEqual(report["machine_status"], case["expected_status"])
                if case["expected_code"] is not None:
                    codes = [entry["code"] for entry in report["diagnostics"]]
                    self.assertIn(case["expected_code"], codes)

    def test_issue_4709_mutations_and_human_boundary(self) -> None:
        data = fixture("issue_4709.json")
        self.assertEqual(data["incident"], "4709")
        control = data["control"]
        for case in data["cases"]:
            with self.subTest(case=case["id"]):
                if "mutation" in case:
                    payload = copy.deepcopy(control["payload"])
                    mutation = case["mutation"]
                    self.assertEqual(
                        self._field(payload, mutation["field"]),
                        mutation["from"],
                    )
                    set_field(payload, mutation["field"], mutation["to"])
                    self.assert_code(
                        case["expected_code"],
                        context=control["context"],
                        payload=payload,
                    )
                else:
                    payload = copy.deepcopy(control["payload"])
                    payload["semantic_claims"] = [
                        {
                            "id": f"incident-4709-{kind}",
                            "kind": kind,
                            "statement": "Historical prose needs independent review.",
                            "evidence_urls": [f"https://example.test/4709/{kind}"],
                        }
                        for kind in case["semantic_kinds"]
                    ]
                    _, report = self.run_gate(
                        context=control["context"],
                        payload=payload,
                    )
                    self.assertTrue(
                        all(
                            item["status"] == case["expected_status"]
                            for item in report["human_reviews"]
                        )
                    )

    def test_issue_4718_delivery_and_self_local_coverage(self) -> None:
        data = fixture("issue_4718.json")
        self.assertEqual(data["incident"], "4718")
        control = data["control"]
        delivery = data["cases"][0]
        context = copy.deepcopy(control["context"])
        mutation = delivery["context_mutation"]
        self.assertEqual(context[mutation["field"]], mutation["from"])
        context[mutation["field"]] = mutation["to"]
        self.assert_code(
            delivery["expected_code"],
            context=context,
            payload=control["payload"],
        )
        coverage = data["cases"][1]
        self.assertIn(coverage["required_path"], control["context"]["changed_paths"])
        self.assertEqual(
            control["payload"]["candidate"]["changed_file_count"],
            coverage["expected_count"],
        )
        self.assertEqual(
            gate.sorted_path_digest(control["context"]["changed_paths"]),
            coverage["expected_digest"],
        )
        code, _ = self.run_gate(context=control["context"], payload=control["payload"])
        self.assertEqual(code, gate.EXIT_PASS)

    def test_pr_4800_stale_negated_and_human_cases(self) -> None:
        data = fixture("pr_4800.json")
        self.assertEqual(data["incident"], "4800")
        control = data["control"]
        for case in data["cases"]:
            with self.subTest(case=case["id"]):
                if "mutation" in case:
                    payload = copy.deepcopy(control["payload"])
                    set_field(payload, case["mutation"]["field"], case["mutation"]["to"])
                    self.assert_code(
                        case["expected_code"],
                        context=control["context"],
                        payload=payload,
                    )
                elif "expected_code" in case:
                    self.assert_code(
                        case["expected_code"],
                        context=control["context"],
                        payload=control["payload"],
                        prefix=case["body_prefix"],
                    )
                else:
                    code, report = self.run_gate(
                        context=control["context"],
                        payload=control["payload"],
                        prefix=case["body_prefix"],
                    )
                    self.assertEqual(code, gate.EXIT_PASS)
                    matching = [
                        item
                        for item in report["human_reviews"]
                        if item["kind"] == case["expected_human_kind"]
                    ]
                    self.assertTrue(matching, report)
                    self.assertTrue(
                        all(item["status"] == case["expected_status"] for item in matching)
                    )

    @staticmethod
    def _field(value: dict[str, Any], dotted: str) -> Any:
        target: Any = value
        for part in dotted.split("."):
            target = target[int(part)] if isinstance(target, list) else target[part]
        return target


class MutationTest(GateHarness, unittest.TestCase):
    @staticmethod
    def mutant(old: str, new: str) -> types.ModuleType:
        source = GATE_PATH.read_text(encoding="utf-8")
        if source.count(old) != 1:
            raise AssertionError(f"mutation target count is {source.count(old)}")
        module = types.ModuleType("completion_claim_gate_mutant")
        module.__file__ = str(GATE_PATH)
        exec(compile(source.replace(old, new), str(GATE_PATH), "exec"), module.__dict__)
        return module

    def test_candidate_comparison_mutant_is_killed(self) -> None:
        mutant = self.mutant("elif actual != expected:", "elif False:")
        payload = self.mutated_payload("candidate.head_sha", "c" * 40)
        self.assert_code("HEAD_SHA_MISMATCH", payload=payload)
        code, _ = self.run_gate(payload=payload, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS)

    def test_directive_ban_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if _keyword_spans(normalized, CLOSE_KEYWORDS):",
            "if False:",
        )
        prefix = "[Resolves][reason]\n"
        self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)
        code, _ = self.run_gate(prefix=prefix, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS)

    def test_directive_boundary_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "return char.isascii() and char.isalnum()",
            'return char.isascii() and (char.isalnum() or char == "_")',
        )
        prefix = "__Fixes__\n"
        self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)
        code, _ = self.run_gate(prefix=prefix, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS)

    def test_directive_normalization_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            'normalized = unicodedata.normalize("NFKC", html.unescape(body))',
            "normalized = body",
        )
        prefix = "[F&#105;xes][reason]\n"
        self.assert_code("DIRECTIVE_KEYWORD_FORBIDDEN", prefix=prefix)
        code, _ = self.run_gate(prefix=prefix, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS)

    def test_raw_html_guard_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            'if "<" in normalized:',
            "if False:",
        )
        body = "<details>\n" + managed_body(self.payload) + "</details>\n"
        self.assert_code("RAW_HTML_FORBIDDEN", body=body)
        code, report = self.run_gate(body=body, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS, report)

    def test_raw_html_normalization_stage_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "_reject_raw_html(normalized_body)",
            "_reject_raw_html(body)",
        )
        prefix = "&lt;details&gt;\n"
        self.assert_code("RAW_HTML_FORBIDDEN", prefix=prefix)
        code, report = self.run_gate(prefix=prefix, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS, report)

    def test_canonical_top_level_guard_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if ordinary_fence is not None:",
            "if False:",
        )
        body = "````text\n" + managed_body(self.payload) + "````\n"
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)
        code, _ = self.run_gate(body=body, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS)

    def test_managed_marker_sweep_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if normalized_marker_count != 1:",
            "if False:",
        )
        suffix = "- ```completion-claims-v1\n{}\n- ```\n"
        self.assert_code(
            "AMBIGUOUS_MANAGED_BLOCK",
            body=managed_body(self.payload) + suffix,
        )
        code, _ = self.run_gate(
            body=managed_body(self.payload) + suffix,
            module=mutant,
        )
        self.assertEqual(code, gate.EXIT_PASS)

    def test_normalized_marker_count_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "return _normalized_body_text(body).count(BLOCK_INFO)",
            "return body.count(BLOCK_INFO)",
        )
        suffix = "Prose marker: completion&#45;claims-v1\n"
        body = managed_body(self.payload) + suffix
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)
        code, report = self.run_gate(body=body, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS, report)

    def test_unicode_validation_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            'if category == "Cs" or category == "Cc" and char not in "\\t\\n\\r":',
            "if False:",
        )
        payload = copy.deepcopy(self.payload)
        payload["semantic_claims"] = [
            {
                "id": "control-mutation",
                "kind": "source",
                "statement": "\u0085",
                "evidence_urls": ["https://example.test/evidence"],
            }
        ]
        self.assert_code("INVALID_UNICODE", payload=payload)
        code, _ = self.run_gate(payload=payload, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS)

    def test_path_exemption_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "encoded_paths = [\n"
            "        _path_bytes(path, f\"changed_paths[{index}]\")\n"
            "        for index, path in enumerate(paths)\n"
            "    ]",
            "encoded_paths = [\n"
            "        _path_bytes(path, f\"changed_paths[{index}]\")\n"
            "        for index, path in enumerate(paths)\n"
            "        if not path.startswith('.self-local/')\n"
            "    ]",
        )
        paths = [".self-local/reports/incident.lean", "scripts/completion_claim_gate.py"]
        self.assertNotEqual(mutant.sorted_path_digest(paths), gate.sorted_path_digest(paths))

    def test_history_action_comparison_mutant_is_killed(self) -> None:
        mutant = self.mutant("if claim[2] != fact[2]:", "if False:")
        payload = self.mutated_payload("history_claims.0.action", "deleted")
        self.assert_code("HISTORY_ACTION_MISMATCH", payload=payload)
        code, _ = self.run_gate(payload=payload, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS)

    def test_unmanaged_prose_charging_mutant_is_killed(self) -> None:
        mutant = self.mutant("if not unmanaged.strip():", "if True:")
        prefix = "Future source work will be handled in issue #4800.\n"
        _, real = self.run_gate(prefix=prefix)
        _, weakened = self.run_gate(prefix=prefix, module=mutant)
        self.assertIn(
            "unmanaged_prose",
            {item["kind"] for item in real["human_reviews"]},
        )
        self.assertNotIn(
            "unmanaged_prose",
            {item["kind"] for item in weakened["human_reviews"]},
        )

    def test_canonical_opener_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            'if line.removesuffix("\\r") == BLOCK_FENCE:',
            'if line.removesuffix("\\r").lstrip() == BLOCK_FENCE:',
        )
        body = managed_body(self.payload, opening="   " + gate.BLOCK_FENCE)
        self.assert_code("AMBIGUOUS_MANAGED_BLOCK", body=body)
        code, report = self.run_gate(body=body, module=mutant)
        self.assertEqual(code, gate.EXIT_PASS, report)


class SecurityAndWiringTest(unittest.TestCase):
    def test_checker_has_no_process_network_or_dynamic_execution(self) -> None:
        source = GATE_PATH.read_text(encoding="utf-8")
        tree = ast.parse(source)
        forbidden_imports = {
            "http.client",
            "requests",
            "socket",
            "subprocess",
            "urllib.request",
        }
        forbidden_calls = {"eval", "exec", "__import__", "compile"}
        imported: set[str] = set()
        called: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module is not None:
                imported.add(node.module)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                called.add(node.func.id)
        self.assertFalse(imported & forbidden_imports)
        self.assertFalse(called & forbidden_calls)
        self.assertNotIn("{0,64}", source)
        self.assertNotIn("{0,512}", source)

    def test_fixture_set_is_exact_and_nonempty(self) -> None:
        names = sorted(path.name for path in FIXTURE_DIR.glob("*.json"))
        self.assertEqual(
            names,
            ["baseline.json", "issue_4709.json", "issue_4718.json", "pr_4800.json"],
        )
        for name in names:
            data = fixture(name)
            self.assertTrue(data["cases"], name)

    def test_existing_build_job_runs_the_self_test(self) -> None:
        workflow = (REPO_ROOT / ".github/workflows/lean_action_ci.yml").read_text(
            encoding="utf-8"
        )
        command = "python3 scripts/test_completion_claim_gate.py"
        self.assertEqual(workflow.count(command), 1)
        self.assertIn("jobs:\n  build:", workflow)

    def test_no_separate_completion_claim_workflow_exists(self) -> None:
        workflows = REPO_ROOT / ".github" / "workflows"
        names = {path.name for path in workflows.iterdir()}
        self.assertFalse(
            {"completion_claim_gate.yml", "completion-claim-gate.yml"} & names
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
