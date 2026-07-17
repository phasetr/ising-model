# Session Handoff — Refactor Campaign 2026-07-17 (cycles 1-7)

Session closed by user request. Canonical durable records:
`.self-local/issues/INDEX.md` (tracked on main since PR #4534) + closed GitHub
issues #4535/#4538/#4541/#4544/#4547/#4550/#4553 + `docs/index.md`.

## Final state

- **main = `f3f1e899`** (session start `f3ed9ea9`; 24 PRs merged).
- **Open issues: 0. Open PRs: 0** (session-end cleanup on user instruction:
  PR #4520 closed as superseded + branch deleted; issue #4533 closed
  not-planned with reopen condition = explicit item-specific user
  authorization for M0 execution).
- Build: `lake build IsingModel` zero warnings; `lake exe GKSTest` green;
  `python3 scripts/audit_gate.py --full` (V1-V3) PASS, wired into CI
  (`.github/workflows/lean_action_ci.yml`, post-build step).
- `scripts/noshake.json`: 49 umbrella modules ignoreAll + 4 mathlib FP
  ignoreImport. `lake exe shake IsingModel` residual ~330 blocks
  (~270 coupled cascade = documented unviable; rest FP/non-target).
- Working tree caveat: local `main` ref is stale (a separate worktree at
  `../ising-model-4523-4526-tex` holds main). Start new work from
  `git fetch origin && git checkout -b <branch> origin/main`.
- Stashes may exist (`wip-4533-index-protocol-entries` etc.) — audit-trail
  only, safe to ignore.

## What was done (7 cycles, all issue-manager-governed, all gates passed)

| Cycle | Issue/PR | Content | main after |
|---|---|---|---|
| 1 | #4535 / #4536 | 97 ref-0 decoration theorems deleted; 1 umbrella import removed | `1793e549` |
| 2 | #4538 / #4539 | MayerMontroll → umbrella+3 children; LayerPerronExistence → umbrella+5 children (decl multiset preserved; 0 importer churn) | `4a44ad71` |
| 3 | #4541 / #4542 | audit_gate.py V1-V3 + capstones.txt (13) + CI wiring; 9 import removals; fail-open holes fixed (`e4532253`) | `2b6b1c22` |
| 4 | #4544 / #4545 | mathlib-only import downgrades: 9 applied / 4 FP reverted | `77cb0103` |
| 5 | #4547 / #4548 | umbrella→child Phase A: 626 files, -1584/+759 imports; Phase B closed unviable (non-converging cascade) | `ba0be416` |
| 6 | #4550 / #4551 | Phase-B-lite: 143 edits (69 TranslationInvariance dead imports + 35 pure + 39 downgrades) + MayerMontroll root wire; 27-file umbrella-drop class reverted wholesale | `816381d8` |
| 7 | #4553 / #4554 | 66/68 detached DONE modules wired into root umbrella; 2 reverted on genuine duplicate declaration | `7447d9e1` |

Clerical mirror PRs: #4534/#4537/#4540/#4543/#4546/#4549/#4552/#4555.

## Standing governance rulings (do not relitigate without user input)

- **User umbrella-convention ruling** (issue #4547, comment 4998637197):
  repo-internal consumers MAY import children directly; umbrella files KEPT.
- **Phase B (coupled shake chains, ~270): unviable-as-designed**, closed with
  evidence; any retry needs fresh baseline + new issue + new design + new
  item-specific user authorization.
- **shake output is candidate-only; the full build is the arbiter.** Known FP
  classes: tactic/deriving/simp/re-export transitive reliance.
- **PERMANENT BAN LIST** unchanged (OZ / SL-D2 / field-CE / Dobrushin
  extremal — see INDEX.md).
- Precedent chain (4 /goal issuances): generic re-issuance authorizes only the
  safest identified converging subset; item-specific naming required for
  non-recommended or user-gated items.

## Open user-decision items (nothing else remains in refactor scope)

1. **Duplicate-theorem dedup**: `mayerExpansionTerm_eq_zero_of_no_polymers`
   exists in detached `ClusterExpansion/MayerCore/Truncations.lean:84`
   (n>=1, weaker) AND reachable
   `ClusterExpansion/StrictPositivity/CycleSeven.lean:47` (general,
   supersedes). Options: (a) delete the MayerCore twin and wire the survivors
   (`MayerCore.{Truncations,MayerTermThreeEval}`, currently detached), or
   (b) leave detached. See INDEX.md D-candidate row.
2. **#4533 reopen** (M0 bottleneck measurement) — only on explicit
   item-specific user authorization.
3. **P-class detached modules**: `PseudoMass.FromParams*` (11 modules,
   #2965 parked) stay detached; `TestGenerators.lean` detached-by-design.
4. **H2 local git hook**: effectively superseded by the CI gate; only if the
   user additionally wants a local pre-push hook (per-case approval).

## Resume procedure (next session)

1. `docs/index.md` progress table + `git log origin/main` (single source of
   truth per CLAUDE.local.md).
2. `.self-local/issues/INDEX.md` header + cycle rows + open-question rows.
3. `gh issue list --state open` / `gh pr list --state open` (both empty at
   handoff).
4. New refactor work requires fresh user authorization; GJ book work follows
   docs/index.md「次に何をやるか」.

## Session ops notes

- gh/git inside the sandbox hit TLS trust errors and SSH-push blocks; per
  user instruction those specific commands were retried outside the sandbox.
- CI runtime varies 2-42 min (mathlib cache dependent); superseded CI runs
  were cancelled before watching head runs.
