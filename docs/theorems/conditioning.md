---
layout: default
title: Conditioning theorems
---
[Theorem catalogue](index.md) · [Documentation home](../index.md) · [Current status](../status.md)

## Chapter 10 (Conditioning inequalities)

| Result | Statement | File |
|---|---|---|
| `partitionFunction_monotone_beta` (Cor 10.2.3) | `Z` monotone in `β` | `Conditioning/Bounds.lean` |
| `hamiltonian_abs_le` (Cor 10.3.2) | `|H| ≤ \|J\|·\|E\| + \|h\|·\|ι\|` | `Conditioning/Bounds.lean` |
| `partitionFunction_upper/lower` | `Z` bounds | `Conditioning/Bounds.lean` |
| `ReflectionPositive` (§10.4) | definition + `discriminant_nonneg` | `Conditioning.lean` |
| `ReflectionPositive` cone closure (§10.4) | The reflection-positive bilinear forms are a convex cone stable under reparametrization and finite sums, which is what lets a concrete RP witness be assembled from simpler pieces rather than checked directly: `ReflectionPositive.zero`, `ReflectionPositive.const`, `ReflectionPositive.of_diag_nonneg` (a form depending on its first argument alone, with nonnegative values), `ReflectionPositive.add`, `ReflectionPositive.smul_nonneg`, `ReflectionPositive.comp` (pullback along any map), `ReflectionPositive.sum` and `ReflectionPositive.weighted_sum` (nonnegative-weighted finite sums). `ReflectionPositive.of_diag_eq` is the transfer lemma making the property depend on diagonal values alone, so it moves between two forms agreeing on the diagonal. These supply the `ReflectionPositive` hypothesis of the §10.6 non-symmetric Schwarz bounds, and only that hypothesis: `ReflectionPositive` is a predicate on an arbitrary `α → α → ℝ` (`∀ x, 0 ≤ b x x`), `schwarz_of_reflection_positive` takes bilinearity as four further explicit hypotheses, and the closure lemmas do not preserve it (`comp` pulls back along an arbitrary map, `const` and `of_diag_nonneg` need no module structure at all), so a form assembled here still owes Schwarz its own bilinearity proof | `IsingModel/Conditioning/Reflection/RPClosure.lean`, `IsingModel/Conditioning/Reflection/Predicates.lean` |
| `iterated_schwarz_sq` (§10.5) | iterated Schwarz bound | `Conditioning.lean` |
| `highTempParam` (§18.1) | `\|tanh(βJ)\| < 1` | `Conditioning.lean` |
