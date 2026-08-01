# Research: stale docs/tex references left by PR #4702 (Mayer order-3 removal)

Base commit inspected: `4d23d7cc` (current main). All reads via `git show 4d23d7cc:<path>`,
not the working tree (which may be on a different branch).

## 1. Declarations/files actually deleted by 4d23d7cc

From `git show 4d23d7cc` diff (`IsingModel.lean`, 2 deleted files, 190 deleted lines total):

Deleted declarations (all in namespace `IsingModel`):
- `mayerExpansionTerm_three` (was in `MayerCore/Truncations.lean`)
- `mayerPartialSum_three` (was in `MayerCore/Truncations.lean`)
- `mayerExpansionTerm_three_eq` (was in `MayerCore/MayerTermThreeEval.lean`)
- `mayerPartialSum_three_eq` (was in `MayerCore/MayerTermThreeEval.lean`)

Deleted files:
- `IsingModel/ClusterExpansion/MayerCore/Truncations.lean`
- `IsingModel/ClusterExpansion/MayerCore/MayerTermThreeEval.lean`

Deleted import line: `import IsingModel.ClusterExpansion.MayerCore.MayerTermThreeEval` from `IsingModel.lean`.

Preserved (do NOT retract mentions of these): `UrsellFinThree`, `ursellCoefficient_fin_three_eq`
(`UrsellFinThree.lean`, still present), `mayerPartialSum_two`, `mayerPartialSum_succ`,
general recurrence `mayerExpansionTerm`, general-`t` Mayer–Montroll identity
(`mayer_identity_general_t`, `MayerCore/MayerMontroll.lean`), and
`mayerExpansionTerm_{one,two,three}_eq_of_pairwise_disjoint` (non-interacting specialisation
family, a *different* theorem from the deleted `mayerExpansionTerm_three(_eq)`, unaffected).

## 2. `docs/index.md` (main @ 4d23d7cc) — stale references

All occurrences live inside the single large §18.4/18.5 table cell at **docs/index.md:2128**
(one very long markdown line, multiple `**bold sub-headers**` inside it). Two sub-clauses need
retraction; a third mentions `mayerExpansionTerm_three_eq_of_pairwise_disjoint` and must be KEPT
(different, still-live theorem).

### 2a. `docs/index.md:2128`, clause "Mayer truncation structure"
> **Mayer truncation structure** (`MayerCore/Truncations.lean`, reusing the canonical recurrence
> `mayerPartialSum_succ` from `PolymerBounds.lean`): the explicit `n = 3` term as an ordered-triple
> sum `mayerExpansionTerm_three` (`= ∑_{(P,Q,R)} ϕ^T(![P,Q,R])·t^|P|t^|Q|t^|R|`, reindexing
> `piFinset (Fin 3)` via `ω ↦ (ω 0, ω 1, ω 2)` and collapsing the activity by
> `Fin.prod_univ_three`); and the explicit truncation `mayerPartialSum_three`.

References only deleted file + deleted decls → **delete this whole clause entirely**.

### 2b. `docs/index.md:2128`, clause "Unified n=3 Ursell classification + third Mayer term"
> **Unified n=3 Ursell classification + third Mayer term** (`UrsellFinThree.lean`,
> `MayerCore/MayerTermThreeEval.lean`): `ursellCoefficient_fin_three_eq` packages all eight
> per-pattern lemmas into one statement — `ϕ^T(ω)` as a nested `if` on the three
> pair-incompatibility flags (`1/3` triangle, `1/6` path, `0` otherwise); `mayerExpansionTerm_three_eq`
> then evaluates the third (first *interacting*) Mayer term in closed form,
> `mayerExpansionTerm G 3 t = ∑_{(P,Q,R)} (pattern-value of (P,Q,R))·t^|P|t^|Q|t^|R|`, by rewriting
> each `ϕ^T(![P,Q,R])` in `mayerExpansionTerm_three` via the unified classification. (This PR also
> deduplicated `mayerPartialSum_succ`/`mayerPartialSum_two`, which `Truncations.lean` had re-derived,
> against the canonical `PolymerBounds.lean`/`PolymerFreeEnergy.lean` versions.)
> `mayerPartialSum_three_eq` then gives the fully explicit Mayer truncation through order 3:
> `mayerPartialSum G 3 t = (∑_P t^|P| − ½·∑_{(P,Q) incompatible} t^|P|t^|Q|) + ∑_{(P,Q,R)} (pattern
> value)·t^|P|t^|Q|t^|R|`, composing the canonical `mayerPartialSum_two` with
> `mayerExpansionTerm_three_eq`.

Mixed: the *first sentence fragment* — "`ursellCoefficient_fin_three_eq` packages all eight
per-pattern lemmas into one statement — ϕ^T(ω) as a nested if …" — describes a still-live
declaration in `UrsellFinThree.lean` and should be KEPT (retitle header, drop the
`MayerCore/MayerTermThreeEval.lean` file citation from the parenthetical, drop everything from
"`mayerExpansionTerm_three_eq` then evaluates …" onward through the end of the clause).

Retraction plan: keep "`ursellCoefficient_fin_three_eq` (`UrsellFinThree.lean`) packages all eight
per-pattern lemmas into one statement — `ϕ^T(ω)` as a nested `if` on the three pair-incompatibility
flags (`1/3` triangle, `1/6` path, `0` otherwise)." as its own clause (retitled, e.g. "**Unified
n=3 Ursell classification**"); delete the rest of clause 2b verbatim.

### 2c. Elsewhere in :2128 (KEEP, not stale)
> `mayerExpansionTerm_{one,two,three}_eq_of_pairwise_disjoint` give the first Mayer coefficients
> `∑_P t^|P|`, `-½∑_P (t^|P|)²`, `⅓∑_P (t^|P|)³` (the `n = 3` value `1/3` matches the triangle
> Ursell value, the non-interacting analogue of `ursellCoefficient_fin_three_*`).

This is the *preserved* `mayerExpansionTerm_three_eq_of_pairwise_disjoint` family (background
confirms this is not deleted) — leave untouched.

No other docs/index.md line matches the deleted names or file paths (single-match grep across
the whole 2332-line file for `mayerExpansionTerm_three`, `mayerPartialSum_three`,
`MayerTermThreeEval`, `MayerCore/Truncations`, `Truncations.lean`).

## 3. `tex/proof-guide.tex` (main @ 4d23d7cc) — stale references

Two `\paragraph{...}` blocks, both entirely retractable (matches the user's cited line ranges).

### 3a. lines 19367–19382, `\paragraph{Mayer truncation structure (\S18.4).}`
Full paragraph text (19368–19382) cites `MayerCore/Truncations.lean`, `mayerExpansionTerm_three`,
and `mayerPartialSum_three` throughout; it also cites the still-live `mayerPartialSum_succ` and
`mayerPartialSum_two`, but those are covered elsewhere in the doc (e.g. the "Independent polymer
free energy" / other paragraphs), so the whole paragraph can be deleted without losing unique
content. **Delete the entire paragraph, lines 19368–19382** (keep the blank line / paragraph
break structure; the paragraph title line 19367 goes too).

### 3b. lines 21076–21098, `\paragraph{Unified $n = 3$ classification and the third Mayer term (\S18.4).}`
- Lines 21077–21080 ("The eight per-pattern lemmas above are packaged into a single statement
  `ursellCoefficient_fin_three_eq` (`UrsellFinThree.lean`): ϕ^T(ω) as a nested if … proved by case
  analysis dispatching to the per-pattern lemmas.") — describes the still-live
  `ursellCoefficient_fin_three_eq` — **KEEP**, but retitle the paragraph (drop "and the third
  Mayer term" from the title since that part is retracted) and drop the trailing
  `\S18.4, pp.~378--386` reference line only if it was solely supporting the retracted content
  (check — likely fine to keep as it also supports the kept sentence).
- Lines 21081–21098 (from "Rewriting each `ϕ^T(![P,Q,R])` in the ordered-triple form
  `mayerExpansionTerm_three` …" through the `mayerPartialSum_three_eq` display and its
  `\[ ... \]` block, ending at "Reference: Glimm–Jaffe, 2nd ed., \S18.4, pp.~378--386.") —
  entirely about deleted decls — **delete**.

Minimal retraction: keep 21076 (retitled) + 21077–21080 + a closing reference line; delete
21081–21098 (or renumber/merge as appropriate when editing).

No other tex line matches (`grep -c` for the four deleted names / two deleted file paths across
all 36141 lines = 2, both accounted for above).

## 4. Suggested minimal retraction wording (English only)

For docs/index.md clause 2a: simply remove the clause (no replacement needed — the general
recurrence coverage already exists via `mayerPartialSum_succ`/`mayerExpansionTerm` mentioned
elsewhere in the same cell).

For docs/index.md clause 2b, replacement clause:
> **Unified n=3 Ursell classification** (`UrsellFinThree.lean`): `ursellCoefficient_fin_three_eq`
> packages all eight per-pattern lemmas into one statement — `ϕ^T(ω)` as a nested `if` on the
> three pair-incompatibility flags (`1/3` triangle, `1/6` path, `0` otherwise).

For tex 3a: delete paragraph outright (no replacement text needed).

For tex 3b: replacement paragraph:
> \paragraph{Unified $n = 3$ Ursell classification (\S18.4).} The eight per-pattern lemmas above
> are packaged into a single statement \texttt{ursellCoefficient\_fin\_three\_eq}
> (\texttt{UrsellFinThree.lean}): $\phi^T(\omega)$ as a nested \texttt{if} on the three
> pair-incompatibility flags ($1/3$ for the triangle, $1/6$ for a path, $0$ otherwise), proved by
> case analysis dispatching to the per-pattern lemmas. Reference: Glimm–Jaffe, 2nd ed., \S18.4,
> pp.~378--386.

## 5. Broader stale-reference scan (all `.lean` path mentions in docs/index.md + tex/proof-guide.tex)

Method: extracted every `[A-Za-z0-9_/]+\.lean` substring from both files (1617 raw mentions,
many duplicated/partial due to nested-path prose), then checked whether each is a path-suffix of
some real file in `git ls-tree -r 4d23d7cc -- IsingModel` (2016 real files). Raw non-matching
count: **269** substrings.

This is a noisy signal (regex captures partial nested-directory fragments from prose, and some
"mismatches" are self-documenting retirement notes, e.g. docs/index.md:2019 explicitly says "the
former standalone `HLSBridgeSummary.lean` wrapper module is retired" — not stale, it's narrating
history). Spot-checks confirm at least one **genuine** unrelated stale reference predating this
PR:

- `tex/proof-guide.tex:2603`: `\paragraph{... (\texttt{Peierls/SingleOrbitBase.lean})}` — no file
  `.../Peierls/SingleOrbitBase.lean` exists in the current tree (confirmed via
  `git ls-tree -r 4d23d7cc -- IsingModel`).

A large cluster of the 269 raw hits (`RangeAscoliPatches/...`, `SubseqCompactOpen/...`,
`Peierls/SingleOrbit*`, `Branches/...`, `BranchAscoliCompactOpen/...`, `MayerCore/Truncations.lean`
+ `MayerCore/MayerTermThreeEval.lean` [= this PR's items, already covered above]) look like
genuine candidates for a **separate, dedicated stale-doc-reference audit** — they are unrelated
to PR #4702 and pre-date it (likely left behind by earlier module-reorganisation refactors, e.g.
the AmbientComplexAnalyticity / Vitali branch-data restructuring and the Peierls single-orbit
walk work). Given the volume and the false-positive rate of the naive regex scan, this needs a
dedicated pass (ideally per-declaration, not just per-file-path) rather than blind deletion; not
attempted here beyond flagging it as a recurrence-prevention candidate for a future
"post-deletion-PR docs closing checklist" (grep all `\texttt{.*\.lean}` / `` `...lean` `` path
mentions against `git ls-tree`, then re-verify each declaration name in the corresponding
`\texttt{...}` backtick group against `grep -rn` in `IsingModel/`).

Raw candidate list saved at (session scratchpad, not committed):
`/private/tmp/claude-501/.../scratchpad/missing_lean_paths.txt` (269 lines).
