---
layout: default
title: Publication policy
---

## Publication roles

Tracked Markdown is the canonical, always-current documentation and is intended to work directly
in GitHub's source browser. The public GitHub Pages site is a low-frequency derived snapshot of the
handwritten documentation. It is published manually and for Lean release tags, so it may lag behind
the default branch.

The Pages workflow is the sole publisher. Each deployment has one writer, one complete artifact,
and one deploy operation. Per-commit publication from the default branch, a generated publication
branch, a second publisher, and a separately deployed API artifact are outside this policy.

Generated doc-gen4 API documentation is not currently published. The live Pages artifact contains
the handwritten site only.

## Verified handwritten publication

The single-writer path was exercised at source revision
`8907607815735384244790863ce74df565e9d94c`. The
[artifact-only run](https://github.com/phasetr/ising-model/actions/runs/31746203963) built and checked
20 pages, 96 local edges, and 25 files before upload without deploying. The separate
[deployment run](https://github.com/phasetr/ising-model/actions/runs/31746327507) rebuilt the same
revision, checked the same inventory, deployed one artifact, and passed the live provenance and
route crawl. Generated API output was absent by design in both runs.

## Generated-API No-Go

The available measurements use the current Lean and Mathlib release, `v4.29.0`:

| Measurement | Source revision | Docs-job duration | Completeness |
| --- | --- | ---: | --- |
| [Cold cache miss](https://github.com/phasetr/ising-model/actions/runs/24449104668) | `2fb5faa91e341602b4b39e12f44e0db1ed4e4131` | 98m54s | Project API present |
| [Cache hit](https://github.com/phasetr/ising-model/actions/runs/24453784477) | `b761d5e27c8b533d17f0c2bf261149d188f93ee5` | 67m28s | `IsingModel.html` and `IsingModel/**` module pages absent |

The warm-cache target is 15 minutes and its hard ceiling is 30 minutes. There is no cold-cache time
cutoff. The measured cache-hit path independently exceeds the hard ceiling and fails project-API
completeness, either of which requires a No-Go decision.

The historical-to-current tracked-library census, including the umbrella `IsingModel.lean` module,
is `18 modules / 5,660 lines -> 1,915 modules / 274,012 lines`. This comparison is not a duration
estimate; it prevents the incomplete historical cache hit from being treated as evidence for
current-project completeness.
No new build design or optimization was authorized that could change either failed criterion, so
another hour-scale run was not performed.

## Reopen criteria

Generated API publication may be reconsidered only after a separately authorized proposal provides:

- a reproducible build and cache design bound to exact toolchain, manifest, procedure, and source
  identities;
- a complete current-module inventory and identical required project-API routes on cache miss and
  cache hit, with project output regenerated rather than silently omitted by cache replay;
- a credible route below the 30-minute warm hard ceiling, with 15 minutes remaining the target;
- an artifact-only pilot that proves the handwritten site and complete API can be assembled,
  inventoried, and crawled as one artifact before any deployment.

A No-Go decision may not introduce a default-branch push trigger, generated branch, second writer, or
partial API deployment. If a future combined publication must be rolled back, publication returns
to one complete handwritten-only artifact; tracked Markdown remains the canonical documentation.
