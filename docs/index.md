---
layout: default
title: Home
---

## ising-model

Lean 4 + mathlib formalization of Ising model theorems, with particular
emphasis on Glimm–Jaffe, *Quantum Physics: A Functional Integral Point of
View* (2nd ed., 1987).

The intended direction of the library's import graph is documented in the
[import-DAG layer contract](architecture-import-layers.html) (#4833), checked by
`scripts/import_dag_contract.py`.

The historical build-speed and simplification baseline for the completed #4506 campaign is
recorded in the [archived refactoring execution plan for #4506](plans/4506-refactoring-replan.html).
Follow-up decisions and measurements formerly tracked by #4793 and #4794 are no longer live:
both issue numbers have been deleted on GitHub, and current tracking is described on the
[current-status page](status.html).

## Documentation

- [Current status](status.html) defines delivery terms and formalization regimes, records the
  infinite-volume ledger, and states the axiom policy.
- [Library map](library-map.html) points Lean contributors to focused public modules and the import
  architecture.
- [References](references.html) lists the primary and supplementary literature.
- [Theorem catalogue](theorems/index.html) organizes formalized results by mathematical and API
  responsibility.
- [Book coverage](coverage/index.html) organizes the Glimm--Jaffe inventory by chapter and keeps
  its scope qualifications with their canonical chapter owners.

> **Notice:** automatic publication of the doc-gen4 API reference to
> `/docs/` on GitHub Pages is **currently paused**. Every main-push
> run of the `docs` job in the CI workflow was taking ~1 hour and
> queuing up behind each merge, so the `docs` job in
> `.github/workflows/lean_action_ci.yml` has been commented out. The
> Lean build and tests (`build` job) continue to run on every push
> and pull request. To build the API reference locally, run
> `lake -R -Kenv=dev build IsingModel:docs` and open
> `.lake/build/doc/index.html`.

## Formalized theorems

Use the [theorem catalogue](theorems/index.html) for the topic-oriented view, organized by
mathematical responsibility. Use the [book-coverage index](coverage/index.html) for the
Glimm--Jaffe chapter order. Status vocabulary and the delivery ledger remain owned by the
[current-status page](status.html).
