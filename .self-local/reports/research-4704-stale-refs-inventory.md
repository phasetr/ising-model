# Issue #4704 — docs/index.md + tex/proof-guide.tex stale-reference inventory (research pass)

main = `99ed7f68` at scan time (repo advanced to `4d23d7cc` by report-write time; no relevant
`docs/`/`tex/` edits landed in between per `git log --oneline -- docs/index.md tex/proof-guide.tex`
over that range).

Scan scope strictly: `docs/index.md`, `tex/proof-guide.tex`, `IsingModel/` (source of truth).
`.self-local/`, `.lake/`, `.git/` excluded from all greps as instructed.

## Methodology (and why raw counts are unreliable)

1. Extracted every backtick-quoted (`` `...` ``) span in `docs/index.md` and every backtick +
   `\texttt{}` span in `tex/proof-guide.tex`, line-scoped (multi-line backtick spans are not
   joined — a known limitation, see "Not done" below).
2. Split each span into (a) `.lean`-suffixed file-path tokens, (b) bare identifier-looking tokens
   (Unicode-aware regex covering Greek/subscript ranges, `\_`-unescaped for TeX).
3. Built the *real* declaration/file corpus by scanning `IsingModel/**/*.lean` for
   `theorem|lemma|def|structure|instance|abbrev|class` headers, **including the case where the
   keyword sits alone on its own line and the name is on the next line** (a common style in this
   repo's newer files, e.g. `AmbientComplexAnalyticity/BranchLocallyBoundedPatches/ConstNormBounded.lean:50-51`
   — a naive same-line-only regex misses these and was the single largest source of false "stale"
   hits before this fix: it turned ~360 false positives into confirmed matches).
4. Path tokens checked by path-suffix match against real files; identifier tokens checked against
   real declaration names (bare and last-dot-component, to tolerate `Namespace.foo` written forms).
5. **Second filter pass (new, not in the original ask, but necessary):** cross-checked remaining
   "stale" identifier tokens against Mathlib + Lean4-core declaration names (same extraction
   script run over `.lake/packages/mathlib/Mathlib/**/*.lean`, `.lake/packages/batteries/**/*.lean`,
   and the active toolchain's `src/lean/Init/**/*.lean`, ~403k declarations). This removed 867 of
   2064 unique surviving tokens (42%) — these are legitimate references to Mathlib/core API
   (`Finset.sum_image`, `HasSum`, `if_pos`, `Real.artanh_tanh`, `Combinatorics.SetFamily.FourFunctions`,
   `Mathlib.Analysis.SpecialFunctions.Complex.Analytic`, etc.), not stale project references.

## Raw counts at each filter stage

| stage | docs/index.md | tex/proof-guide.tex |
|---|---|---|
| all backtick/texttt file-path tokens | 2513 | 959 |
| all backtick/texttt identifier tokens | 10693 | 9342 |
| file tokens NOT suffix-matching a real file | 15 (+5 dotted-module-form) | 85 (+4) |
| identifier tokens NOT matching a real decl (after multi-line-header fix) | 2963 | 3195 |
| … of which start with a bare `_` (doc shorthand, see below) | 563 | 340 |
| … of which match Mathlib/core (false positive) | included above | included above |
| unique surviving candidate tokens across both files, after Mathlib/core filter | **1218** (before deep manual triage) |

**These 1218 unique tokens (≈2500 mention-instances, ≈1600 distinct source lines) are NOT a
reliable stale-reference count.** Manual inspection of samples shows the dominant remaining noise
sources are systematic *doc-writing conventions* in this repo, not actual broken references:

- **Common-prefix shorthand.** The docs/tex habitually write families of related lemma names as
  `foo_bar_baz`/`_qux`/`_quux` (shared stem elided) or `A/B/C/D.lean` (shared filename-prefix
  elided, slash used as a separator between *suffixes*, not a path). Example verified real:
  `docs/index.md:1915-1916` reads "`_core` refactors of
  `MassContinuityFiniteVolumeIncidentEdge/IncidentSum/DerivCombine/DerivSharp/BindingPairDeriv.lean`"
  — this is **not one broken path**; it denotes 5 real files
  (`IsingModel/Concrete/LatticeGraphCorrelation/Lemma_17_5_2/MassContinuityFiniteVolume{IncidentEdge,IncidentSum,DerivCombine,DerivSharp,BindingPairDeriv}.lean`,
  all confirmed to exist). A tokenizer that doesn't understand this convention flags it as one
  broken file. This convention alone plausibly accounts for a large fraction of the remaining
  ~1200 candidates; a token-level tool cannot safely auto-resolve it (would need per-line
  semantic parsing).
- **Ellipsis abbreviation** (`abs_correlationΛ_..._le_one`, `AlongExhaustion_..._apply`) — prose
  shorthand, not literal identifiers.
- **Dotted-projection artifacts** (`abs_le.mp`, `dt.fst`, `A.equivFin.symm`) — legitimate
  Mathlib/Lean dot-notation projections on values, not declaration references.
- Repeated **self-disclosed archival notes** citing old identifiers/paths by design, e.g.
  `docs/index.md:866` ("**FV §3.7.2 — *archived***... `RayExitAnchorVerticalStrictBridgeNonStripTurnStep.lean`
  ... **replaced** by...") and `docs/index.md:2048` (LatticeSystemBridge "**Removed**" row, PR
  #4703, already correctly retracted). These intentionally name dead things while stating they are
  dead — correctly documented, not a stale/false claim.

## Concrete verified cases (spot-checked with git log / grep, not exhaustive)

### A. Rename/move (content survives, path/name is stale) — verified examples
- `docs/index.md:1973,1974,1976,1979,1982,1983` cite `AmbientLattice/SpecialCases/Legacy.lean` and
  `Concrete/LatticeGraphCorrelation/Legacy.lean`. Both files were deleted in
  **PR #2561 / #2562** ("retire … Legacy shim", commits `2559040c`/`bb21e4b1`), but every
  declaration named on those lines (e.g. `freeEnergyAlongExhaustion_continuous_beta`,
  `magnetizationAlongExhaustion_continuous_beta`) **still exists**, moved to
  `AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityFE.lean` /
  `.../Magnetization.lean` and `Concrete/LatticeGraphCorrelation/PartitionFreeEnergyRegularityAlongExFreeEnergy.lean` /
  `.../MagnetizationRegularityBeta.lean` respectively. → mechanical path-citation fix, no
  progress-claim change.
- `docs/index.md:2010,2012,2019` cite `HLSConsolidatedSummary.lean`, `HLSSusceptibilityBridge.lean`,
  `HLSBridgeSummary.lean` — none exist under those names, but the cited declarations
  (`substantive_hls_full_consolidated`, `hls_and_susceptibility_bound_of_ferromagnetic_high_temp`,
  `simonLiebTrichotomyBridgeRate`) all exist, consolidated into
  `Concrete/LatticeGraphCorrelation/Lemma_17_5_2/HLSLatticeMassBridge.lean` and
  `.../HLSBridgeFromSimonLiebCanonical.lean`. → same pattern, mechanical fix.
- `docs/index.md:1729-1732` write fully-qualified `IsingModel.Ambient.Current.foo`; the actual
  declared names are `Current.foo` (no `IsingModel.Ambient.` namespace prefix) in
  `RandomCurrent/Switching/{GlobalSwitching,GlobalSwitchingLimit}.lean` and
  `Inequalities/{SourcefreeConnectionUnconditional,CurrentConnectivityRepresentation}.lean` — the
  declarations exist; the docs' qualification is simply wrong/stale-style, not a broken reference
  to nonexistent content. (These rows are the OZ-infrastructure bricks already flagged
  parked/reserved in memory; **no keep-criterion(f) issue** — content is real and current.)

### B. Genuinely deleted, and the surrounding text is candid about it (no hidden false claim found)
- `docs/index.md:866` — ray-exit scaffolding, disclosed "*archived*"/"**replaced**".
- `docs/index.md:2048` — LatticeSystemBridge, disclosed "**Removed**" (PR #4703, already merged).
- `docs/index.md:1667` (Dobrushin §17.1 row) — the paragraph explicitly opens with "_(scaffolding
  removed in PR-B1 … archived at git tag `archive/transfermatrix-spectral-gap-scaffolding`)_" (tag
  confirmed to exist) but then continues for ~15 more identifier-heavy sentences in present tense
  ("Proved via…", "Supporting: …") describing the removed scaffolding as if current. This is
  **not a hidden false claim** (removal is stated up front) but the wording is confusing/misleading
  on a close read and is a likely candidate for a docs-clarity pass (rewrite past-tense / trim the
  15-identifier restatement) — separate from a "stale reference" bug per se.

**No case was found in this spot-check where a docs/index.md progress-table row asserts "Done" for
content that has been silently deleted without any disclosure.** All B-type hits found are
self-disclosed. This does not rule out an undiscovered case in the ~1200 unclassified tokens, but
none surfaced in sampling across ~50 tokens plus all of the file-path stale list.

### C. False positives (majority, by far)
- 867/2064 (42%) of surviving identifier tokens = Mathlib/core API references (measured).
- The `_`-prefix shorthand-continuation tokens (563 in docs, 340 in tex — 27%/11% of the raw stale
  identifier counts) are not real identifiers at all.
- The slash-separated multi-file shorthand (`A/B/C/D.lean`) inflates the stale file-path counts;
  every sampled instance in docs (`MassContinuityFiniteVolume{IncidentEdge,IncidentSum,DerivCombine,
  DerivSharp,BindingPairDeriv}.lean`) resolved to real files.
- Self-disclosed archival notes (ray-exit, LatticeSystemBridge, Mayer-order-3 already retracted in
  PR #4702) are technically "reference to nonexistent decl" hits but are not documentation bugs.

Net effect: **the true "silently broken, undisclosed" reference count is almost certainly a small
single/low-double-digit number, an order of magnitude below the raw ~2500-6000 mechanical counts**,
concentrated in the A-type (rename/move) `Legacy.lean` and `HLS*Summary/Bridge.lean` clusters
identified above (9 docs rows confirmed A so far) plus whatever fraction of the unclassified ~1200
tokens are not shorthand/Mathlib/self-disclosed (not fully triaged this pass — see below).

## D. Not done in this pass (recommend as explicit follow-up scope)
- Full manual/line-by-line triage of the remaining ~1200 unique post-filter identifier tokens
  (~1600 distinct source lines) to separate genuine A/B/C with certainty. This requires either (i)
  a semantic (LLM-assisted) per-line read rather than token regex, because of the shorthand
  conventions documented above, or (ii) extending the extraction script to understand the
  `stem`/`_suffix` and `prefix{a,b,c}.lean` shorthand mechanically (parseable but nontrivial: the
  shared-stem boundary is not always the same delimiter).
- `tex/proof-guide.tex` file-path stale list (85 raw, not yet spot-checked the way docs' 15 were —
  same shorthand conventions almost certainly apply given tex mirrors docs prose style).
- Multi-line backtick/texttt spans (span crossing a newline) are not joined by the extractor; any
  reference broken across a line wrap is invisible to this pass (likely rare, `.md`/`.tex` tables
  are usually single-line-per-cell in this repo, but not verified).

## Implementation-unit recommendation
- The **A-type Legacy.lean / HLS-summary path citations (9 docs rows confirmed, tex likely has a
  parallel set)** are safe, mechanical, low-risk path/name corrections — no progress-claim
  retraction, no keep-criterion(f) exposure. These can be one small PR.
- The **§17.1 Dobrushin paragraph (docs:1667)** clarity issue (self-disclosed removal but present-
  tense wall-of-identifiers) is a separate, higher-judgment editorial fix — recommend its own PR
  or explicit user sign-off since it touches a "Done" row's narrative, even though no keep-
  criterion(f) fact is being retracted (the row was already honest about removal).
- **Do not attempt a single PR "fix everything flagged by the mechanical scan"** — the false-
  positive rate is too high (>50%, likely closer to 90%+ once shorthand-notation semantics are
  accounted for); a follow-up semantic triage pass (dev-research continuation or dev-docs-sync
  with line-by-line human/LLM read) is needed before any bulk edit, especially for
  `tex/proof-guide.tex`'s 85 file-path + ~3195 identifier raw hits which were not spot-checked to
  the same depth as docs/index.md in this pass.

## keep-criterion (f) status
**No confirmed trigger.** All identified B-type (content actually gone) cases are rows that
already self-disclose the removal (ray-exit archive, LatticeSystemBridge removed, Mayer-order-3
already retracted pre-#4702). All identified stale-but-content-survives cases are A-type
(Legacy.lean / HLS-summary renames), which do not require retracting any "Done" claim — the
underlying theorems are real and current, only the file citation is outdated.
