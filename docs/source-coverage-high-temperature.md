# High-Temperature Source Coverage

## Authority and classifications

This audit compares the current Lean declarations directly with Friedli--Velenik,
*Statistical Mechanics of Lattice Systems* (2017), Section 3.7.3, pp. 116--119, and
Glimm--Jaffe, *Quantum Physics*, 2nd edition, Theorem 17.6.1, p. 313, and Chapter 18,
pp. 321--342. Project progress prose is not evidence for mathematical coverage.

The classifications below have the following meanings:

- **Exact**: the source and Lean statements have the same mathematical content after the stated
  notational or parameter specialization.
- **Derived corollary**: the Lean statement follows from the source-route algebra and proved Lean
  results but is not stated in the cited source.
- **Analogy**: the proof architecture is related, but the model, parameter, boundary condition, or
  observable differs.
- **Not covered**: no current Lean declaration formalizes the literal source statement.

## FV (3.41)--(3.46) source-to-owner matrix

| Source | Literal source contract | Weakest reusable Lean owner and specialization | Classification |
|---|---|---|---|
| FV (3.41), p. 116 | The single-edge identity `exp(beta * sigma_i * sigma_j) = cosh(beta) * (1 + tanh(beta) * sigma_i * sigma_j)`. | `IsingModel.exp_edgeSpin_decomp` in `IsingModel/Inequalities/NonnegCorrelations.lean`, with `alpha = beta * J`; `boltzmannWeight_h_zero_prod` uses its normalized product form. | Exact after `alpha = beta * J`. |
| FV (3.42), p. 116 | The zero-field plus-boundary Boltzmann weight on `Lambda` factors over the boundary-edge set. | `boltzmannWeight_h_zero_prod`; `boltzmannWeightBC_h_zero_prod_of_agrees` in `IsingModel/Conditioning/PlusHighTempRepresentation.lean` supplies the boundary specialization. | Exact after uniform-coupling and plus-boundary specialization. |
| FV (3.43), p. 116 | A finite product of `1 + f(e)` expands as a sum over edge subsets. | Mathlib's `Finset.prod_one_add`, used directly by the project proofs. | Exact library identity; no project wrapper is needed. |
| FV (3.44), p. 117 | Summing a spin raised to its incidence count gives `2` for even incidence and `0` for odd incidence at each interior vertex. | `sum_indicator_agreesOff_plus_prod_pow` in `IsingModel/Conditioning/PlusHighTempRepresentation.lean`; the single-spin identity is a private implementation detail. | Exact pinned-boundary parity collapse. |
| FV (3.45), p. 117 | The plus-boundary partition function is an even-interior-incidence edge-subset sum. | `partitionFunctionBC_plus_h_zero_closed` in `IsingModel/Conditioning/PlusHighTempRepresentation.lean`. | Exact graph/general-coupling realization after choosing the source edge graph. |
| FV (3.46), p. 117 | The plus-boundary singleton expectation at site `0` is the ratio of the odd-at-`0`, even-elsewhere sum to the even-interior-incidence sum. | `gibbsExpectationBC_plus_spinProduct_h_zero_ratio` is the general owner and `gibbsExpectationBC_plus_singleSpin_h_zero_ratio` in `IsingModel/Conditioning/PlusOnePointRepresentation.lean` is the exact singleton surface. | Exact source contract at the singleton specialization. |

## FV singleton and pair consequences

FV (3.46) is a plus-boundary one-point ratio. It is not the free-boundary identity
`correlation_high_temp_expansion_h_zero_closed`. The latter is an arbitrary-observable
free-boundary analogue obtained from the same parity expansion.

The free-boundary theorem `correlation_high_temp_h_zero_at_singleton` vanishes for all real `J`
and `beta` by odd-observable cancellation. Fixed plus-boundary edges prevent that cancellation in
FV (3.46), whose singleton expectation is generally nonzero at finite volume. The two statements
therefore require distinct owners.

FV Exercises 3.23--3.25, p. 119, give the relevant two-point context: analogous plus- and
free-boundary representations, high-temperature exponential upper decay, and a lower comparison
by a power of `tanh(beta)`. The project theorem
`correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges` instead selects one adjacent edge
in the free-boundary numerator and applies a coarse denominator estimate. It is a derived
corollary, not FV (3.46) and not the lower bound stated in Exercise 3.25.

## GJ 17.6.1 and Chapter 18 matrix

| Source | Literal source contract | Closest current Lean relation | Classification |
|---|---|---|---|
| GJ Theorem 17.6.1, p. 313 | In the continuum `lambda phi^4 + sigma phi^2` model, the derivatives of infinite-volume Schwinger functions with respect to `sigma` exist for `sigma_c < sigma`. | The Ising beta and field differentiability theorems concern different models, parameters, and high-temperature domains. | Not covered. |
| GJ Corollary 18.1.4, p. 324 | Continuum `P(phi)_2` Schwinger functions are analytic in the interaction coupling `lambda` in the stated small right-half-plane sector. | `correlationInfinite_latticeGraph_general_analytic_high_temp` uses a related locally uniform convergence and Vitali argument for lattice Ising beta. | Analogy only. |
| GJ Theorem 18.3.1, p. 330 | A volume-uniform tail estimate controls the continuum `P(phi)_2` cluster expansion. | The project Kotecky--Preiss and volume-uniform Ising correlation bounds play an analogous architectural role. | Analogy only. |

In particular, the current Ising beta result is not literally GJ Theorem 17.6.1. It proves
analyticity and real differentiability only on a small Ising high-temperature interval and in a
different parameter direction.

## Surviving canonical-owner invariants

The source coverage is preserved by the following weakest canonical owners:

| Mathematical content | Surviving canonical owner | Coverage role |
|---|---|---|
| Plus-boundary arbitrary-observable parity ratio | `gibbsExpectationBC_plus_spinProduct_h_zero_ratio` | General boundary-conditioned owner for the algebra behind FV (3.46). |
| Plus-boundary singleton ratio | `gibbsExpectationBC_plus_singleSpin_h_zero_ratio` | Exact specialization of FV (3.46). |
| Free-boundary singleton cancellation along an exhaustion | `Ambient.correlationAlongExhaustion_high_temp_h_zero_at_singleton` | Preserves the project consequence without unnecessary sign assumptions. |
| Free-boundary adjacent-edge lower bound along an exhaustion | `Ambient.correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges` | Preserves the project-derived bound under the weakest product hypothesis. |
| Concrete lattice adjacent-edge lower bound | `correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges` | Surviving lattice specialization of the project-derived pair result. |
| Infinite-volume lattice Ising beta analyticity | `Ambient.correlationInfinite_latticeGraph_general_analytic_high_temp` | General-observable owner for the Ising result and its finite-observable specializations. |

Stronger-hypothesis wrappers and duplicate proof surfaces add no source coverage. The exact FV
plus-boundary singleton row remains owned by the boundary-conditioned declarations above, while
the general-observable analyticity owner remains an analogy to the GJ Chapter 18 method rather than
literal GJ coverage.

## Audit provenance

The FV rows were checked against `.self-local/refs/Friedli.Velenik.txt`, lines 8661--8920, and the
corresponding local PDF pages 116--119. GJ Theorem 17.6.1 was checked against
`.self-local/refs/Glimm.Jaffe.Quantum_Physics.txt`, lines 15209--15247, and PDF page 324 because the
displayed derivative formula is absent from the extracted text. The Chapter 18 rows were checked
against the same extracted text, lines 15556--16118, and the corresponding PDF pages. Current Lean
owners were checked under `IsingModel/Conditioning`, `IsingModel/AmbientLattice`, and
`IsingModel/ClusterExpansion`. No issue, pull-request history, or project progress document was
used as mathematical authority.
