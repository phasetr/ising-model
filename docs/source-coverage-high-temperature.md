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

| Source | Boundary/model | Observable | Parameter domain | Volume quantifiers | Literal conclusion | Surviving Lean owner | Exact specialization or relation | Classification |
|---|---|---|---|---|---|---|---|---|
| FV (3.41), p. 116 | One nearest-neighbour Ising bond; the identity has no boundary condition. | Bond spin product `sigma_i sigma_j`. | Source inverse temperature `beta >= 0`; the algebraic identity holds for every real `beta`. | Local identity with no volume limit. | `exp(beta * sigma_i * sigma_j) = cosh(beta) + sigma_i * sigma_j * sinh(beta) = cosh(beta) * (1 + tanh(beta) * sigma_i * sigma_j)`. | `IsingModel.exp_edgeSpin_decomp`. | Take `e = s(i,j)` and Lean `alpha = beta_source` for literal unit coupling, or `alpha = beta_Lean * J` for the project's uniform scalar-coupling rescaling. | Exact algebraic identity. |
| FV (3.42), p. 116 | Finite `Lambda` in `Z^d`, plus boundary, boundary-edge set `E^b_Lambda`, zero field, and unit nearest-neighbour coupling. | Boltzmann weight of each `omega` in `Omega^+_Lambda`. | Physical `beta >= 0`. | Every finite `Lambda` and configuration; no infinite-volume limit. | The weight is cosh(beta) raised to the cardinality of `E^b_Lambda`, times the product of `1 + tanh(beta) * omega_i * omega_j` over boundary edges. | `boltzmannWeightBC_h_zero_prod_of_agrees`, with algebraic owner `boltzmannWeight_h_zero_prod`. | Choose a finite ambient vertex type containing `Lambda` and all endpoints of `E^b_Lambda`, set `G.edgeFinset = E^b_Lambda`, `eta = plusConfig`, `h = 0`, and `J = 1`; equivalently use `beta_source = beta_Lean * J`. | Exact after the explicit plus-boundary and uniform-coupling specialization. |
| FV (3.43), p. 116 | No Ising boundary or model; an arbitrary nonempty finite set `E`. | Arbitrary scalar function `f` on `E`. | No Ising parameter. | Finite combinatorial identity; the Lean theorem also covers `E = empty`. | The product of `1 + f(e)` equals the sum over all subsets of the corresponding products. | Mathlib `Finset.prod_one_add`. | Instantiate the finset with `E^b_Lambda` and `f(e) = tanh(beta_source) * sigma_i * sigma_j`, or with the uniform `beta_Lean * J` rescaling, for the FV application. | Exact library identity. |
| FV (3.44), p. 117 | The same finite plus-boundary volume; exterior spins are pinned and only `i` in `Lambda` is summed. | Local incidence monomial `omega_i ^ I(i,E)` for a fixed edge subset `E`. | No parameter beyond the selected `E`. | Each interior vertex of every finite `Lambda`; no infinite-volume limit. | The two-spin sum is `2` for even incidence and `0` for odd incidence. | `sum_indicator_agreesOff_plus_prod_pow`. | Choose the finite ambient support of `E^b_Lambda`, `eta = plusConfig`, and `k(v) = I(v,E)`. The owner packages the product of these exact local collapses and leaves exterior factors at `1`. | Exact pinned aggregate specialization. |
| FV (3.45), p. 117 | Finite `Lambda` in `Z^d`, plus boundary, `E^b_Lambda`, zero field, and uniform unit coupling. | Plus-boundary partition function. | Physical `beta >= 0`. | Every finite `Lambda`; no infinite-volume limit. | 2 raised to the cardinality of Lambda, times cosh(beta) raised to the cardinality of `E^b_Lambda`, times the sum over edge subsets having even incidence at every interior vertex. | `partitionFunctionBC_plus_h_zero_closed`. | Choose an arbitrary finite `SimpleGraph G` with `G.edgeFinset = E^b_Lambda`, the interior finset `Lambda`, and the plus configuration. Set the uniform scalar `J = 1` for literal FV notation, or identify `beta_source = beta_Lean * J`. The owner permits arbitrary finite graph geometry but not edge-dependent coupling. | Exact after the stated graph and uniform-scalar-coupling specialization. |
| FV (3.46), p. 117 | The same finite plus-boundary volume and boundary-edge graph, zero field, and uniform unit coupling. | Singleton spin at source site `0`, with `0` in `Lambda`. | Physical `beta >= 0`. | Every finite `Lambda` containing `0`; no infinite-volume limit. | Ratio of the edge-subset sum odd at `0` and even at other interior sites to the even-interior-incidence sum. | General owner `gibbsExpectationBC_plus_spinProduct_h_zero_ratio` and exact singleton surface `gibbsExpectationBC_plus_singleSpin_h_zero_ratio`. | Set `G.edgeFinset = E^b_Lambda`, use the plus configuration, take `A = {0}`, and set `J = 1`, or use the same exact `beta_source = beta_Lean * J` rescaling. | Exact at the singleton specialization. |

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

| Source | Boundary/model | Observable | Parameter domain | Volume quantifiers | Literal conclusion | Surviving Lean owner or relation | Exact specialization or relation | Classification |
|---|---|---|---|---|---|---|---|---|
| GJ Theorem 17.6.1, p. 313 | Infinite-volume continuum `lambda phi^4 + sigma phi^2` theory with the weak-coupling boundary construction from the preceding text, not a lattice Ising boundary condition. | Each infinite-volume `n`-point Schwinger function `S_n(x)`; the following remark extends to truncated Schwinger and vertex functions. | Fixed interaction data and `sigma_c < sigma`. | Already infinite-volume. | Existence of `partial S_n(x) / partial sigma`. | Nearest Ising relation: `Ambient.correlationInfinite_latticeGraph_general_differentiableAt_beta_high_temp`. | None: the model, parameter, domain, and observable differ; the Lean theorem is only a beta-direction Ising analogy. | Not covered. |
| GJ Corollary 18.1.4, p. 324 | Continuum infinite-volume `P(phi)_2`; preceding finite-volume bounds are uniform and the infinite-volume expectations are boundary-condition independent. | Schwinger functions. | Complex coupling `lambda` whose absolute value is positive and less than epsilon and whose argument lies between `-pi/2` and `pi/2`, with `epsilon / m_0^2` small. | Infinite-volume analyticity obtained from finite-volume analyticity, convergence, and Vitali. | Analytic dependence on `lambda` in the stated sector. | `Ambient.correlationInfinite_latticeGraph_general_analytic_high_temp`. | None: Lean concerns lattice Ising at zero field with `J >= 0`, arbitrary finite spin observable `A`, and complexified `beta` in a ball whose real identification is on `0 < beta < r`. | Analogy only through the locally uniform/Vitali architecture. |
| GJ Theorem 18.3.1, p. 330 | Continuum `P(phi)_2` cluster expansion with a finite interaction cutoff, uniformly controlled as the cutoff grows. | Test-function pairing terms `<w,T>` in the cluster-expansion tail. | Any `K > 0`, sufficiently large `m_0`, sufficiently small `epsilon` depending on `K`, and `lambda` in the closure of sector (18.1.6). | Uniform in `lambda`, `m_0`, tail threshold `D`, and the finite-volume cutoff; used to obtain infinite-volume results. | The tail over clusters X whose cardinality is at least D is bounded by the norm used for w times `exp(-K * (D - n))`. | `Ambient.correlationComplexAlongExhaustion_general_norm_le_uniform`. | None: Lean bounds finite-stage lattice Ising correlations for arbitrary finite `A` and complex `beta` in a high-temperature ball by `generalRatioBoundFun`, not continuum cluster terms. | Architectural analogy only. |

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
`IsingModel/ClusterExpansion`. In particular, the surviving declarations cited in the matrices
were checked in `IsingModel/Inequalities/NonnegCorrelations.lean`,
`IsingModel/Conditioning/PlusHighTempRepresentation.lean`,
`IsingModel/Conditioning/PlusOnePointRepresentation.lean`,
`IsingModel/ClusterExpansion/TwoPointCorrelationInfiniteBetaDeriv.lean`, and
`IsingModel/ClusterExpansion/TwoPointCorrelationInfiniteAnalytic.lean`. No issue, pull-request
history, or project progress document was used as mathematical authority.
