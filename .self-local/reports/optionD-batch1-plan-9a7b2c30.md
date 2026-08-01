# Option-D reference-0 cleanup — CONSERVATIVE first-batch plan (main 9a7b2c30)

Independent design pass over the 824 delete-eligible pool
(`.self-local/reports/option-D-refzero-verified-9a7b2c30.md`) + #4559 items,
applying the frozen keep-criteria (`optionD-refzero-tracking-2026-07-24.md` §2)
and the task's deliverable-exclusion filter. No code changed; nothing deleted.

## Bottom line (honest)
After excluding every deliverable-suspect cluster the task named, the 824 residual is
**dominated by deliverables** (AlongExhaustion / Infinite / analytic / continuous /
susceptibilityΛ|magnetizationΛ regularity / Λ-latticeGraph API / Regularity/*). The
only two non-excluded ≥5 clusters are `ClusterExpansion/Basic.lean` (deliverable-adjacent
§18.4 polymer API — pulled to KEEP) and `BetaDerivative/Continuity.lean` (excluded by
the continuous/differentiable pattern). **There is NO large safe decl-deletion batch.**
Even the most-vetted #4559 detached Mayer subtree turns out to be doc-cited in
docs/index.md §18.4 as an explicit accomplished order-3 result. A defensible first batch
is therefore ~4 decls (doc-sync-gated) + 1 pure import-hygiene line — not hundreds.

## First batch (proposed)

### Item B — SAFEST, recommended to ship first (pure hygiene, 0 decls, 0 docs)
- **`IsingModel/ClusterExpansion/StrictPositivity/IffCharacterisations.lean:1`** — remove
  the unused import `import IsingModel.ClusterExpansion.StrictPositivity.CycleSeven`.
  - #4559 item 3 (item-specifically authorized). Verified: IffCharacterisations references
    NEITHER of CycleSeven's two live decls (`mayerExpansionTerm_two_filter_connected_eq_incompat`,
    `mayerExpansionTerm_eq_zero_of_no_polymers`); CycleSeven stays live via
    `AmbientLattice/AnalyticityLambdaCapstones.lean:179`.
  - RISK: this is IffCharacterisations's *sole* import, so it is almost certainly load-bearing
    *transitively* (TanhBounds → core defs). dev-implement MUST replace it with the direct
    module IffCharacterisations actually needs and confirm `lake build` (not a blind line-delete).
  - Confidence: HIGH that the import is decl-unused; MEDIUM that removal is clean (transitive).

### Item A — decl deletion, CONDITIONAL on a docs-ledger edit + explicit user OK
- **Delete whole file** `IsingModel/ClusterExpansion/MayerCore/Truncations.lean`
  (2 decls: `mayerExpansionTerm_three` :45, `mayerPartialSum_three` :82).
- **Delete whole file** `IsingModel/ClusterExpansion/MayerCore/MayerTermThreeEval.lean`
  (2 decls: `mayerExpansionTerm_three_eq` :47, `mayerPartialSum_three_eq` :75).
  - #4559 item 1 (item-authorized). Structural facts verified at 9a7b2c30:
    - Detached subtree: only importer of Truncations is MayerTermThreeEval; MayerTermThreeEval
      has ZERO importers; neither is in the `IsingModel.lean` umbrella. Disconnected component.
    - The general recurrence they specialize (`mayerPartialSum_succ`, `mayerPartialSum_two`,
      `mayerExpansionTerm_two`) lives in PolymerBounds/PolymerFreeEnergy/Terms and stays live —
      deletion removes ONLY the dead order-3 specializations.
    - `mayerExpansionTerm_three_eq_of_pairwise_disjoint` (IndependentMayerTerm.lean) is the live
      general independent-term form; the `_three_eq` explicit form is superseded.
  - **BLOCKER — why this is CONDITIONAL, not clean scaffold:** docs/index.md line 2128 (§18.4
    cluster-expansion cell, Issue #1499) documents these as an accomplished result — "the
    explicit `n=3` term as an ordered-triple sum `mayerExpansionTerm_three`", `mayerExpansionTerm_three_eq`
    "evaluates the third (first interacting) Mayer term in closed form", `mayerPartialSum_three_eq`
    "the fully explicit Mayer truncation through order 3". Keep-criterion (f) (doc-cited → KEEP)
    fires. The docs itself flags them as *re-derivations of the canonical PolymerBounds/PolymerFreeEnergy
    versions*, so a retraction is reasonable — but deleting them REQUIRES editing the §18.4 ledger
    narrative in the SAME PR (protocol §3.4) and is a substantive ledger change, not hygiene.
  - Confidence: HIGH they are structurally dead / detached; but MEDIUM-LOW that they are
    "safe to delete" under keep-criteria without user sign-off on retracting the docs §18.4
    order-3 narrative. Recommend: ask the user to confirm the docs retraction before shipping,
    or hold Item A and ship only Item B.

### Item C — #4559 item 2: NO ACTION (already resolved)
- `alternatingConnectedSubgraphSum_cycleGraph_seven` no longer exists anywhere in the repo
  (removed by the earlier cycleGraph cleanup, cf. #4636). Just record #4559 item 2 as done.

## Count
- Defensible decl deletions this batch: **4** (Item A, doc-sync-gated) across **2 whole files**.
- Pure hygiene: **1** import line (Item B, build-gated).
- #4559-linked: ALL of the above (item 1 = Item A, item 3 = Item B, item 2 = resolved).

## Pulled from the mechanical 824 as deliverable leakage (learn the filter)
- `ClusterExpansion/Basic.lean` cluster (5): `isEvenSubgraph_iff`:79, `isEdgeConnected_singleton`:217,
  `polymerSupport_union`:269, `isPolymerCompatible_symm`:521, `not_isPolymerCompatible_self_of_nonempty`:529.
  These are the ONLY non-excluded ≥5 cluster, BUT they are foundational §18.4 cluster-expansion API:
  docs/index.md:2128 names the underlying concepts (`polymerSupport`, `IsEvenSubgraph`,
  `IsPolymer`) as deliverable API, and `isEvenSubgraph_iff` is a documented "bridging lemma" to
  the named FV (3.45) result. Classic L6/L9 blind-spot territory (prose cites the concept, not the
  exact lemma name). → KEEP; at most a FUTURE batch after per-lemma docs-prose spot-check.
- The task's own suspects confirmed as deliverables/parked (all excluded, correctly):
  `susceptibilityΛ_*`/`magnetizationΛ_*` regularity, `*AlongExhaustion*`,
  `correlationAlongExhaustion_latticeGraph_analyticAt_joint`,
  `BddAbove_freeEnergyAlongExhaustion_*`, all `AnalyticityLambda*`, `Regularity/*`,
  `PartitionFunction*Analyticity*`, `MayerVdBounds` (sumAlongExhaustion), `truncated*_continuous/differentiable`.

## Filter-leakage lesson
The mechanical 824 excludes doc-cited items, so it did NOT contain the #4559 Mayer pair — yet
those (from #4559's older finding) ARE doc-cited. Conversely the 824 DID surface Basic.lean's
polymer API, which is doc-concept-cited but not exact-name-cited (the L6/L9 gap). Net: name/path
filters cannot distinguish "dead helper of a live documented concept" from "true scaffold"; every
candidate needs the docs-prose read done here.

## Recommended PR shape
- Smallest safe PR = **Item B only** (import hygiene), its own tiny issue, closes #4559 item 3.
- If user authorizes the §18.4 docs retraction → add **Item A** (delete 2 files + edit docs/index.md
  §18.4 cell to point order-3 narrative at the canonical PolymerBounds/PolymerFreeEnergy versions),
  closing #4559 item 1. Bundle Item B+A in one #4559-closing PR only if the docs edit is authorized;
  otherwise ship B, keep A parked.
