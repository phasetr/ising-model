# Refactoring rollback ledger

## Purpose and authority

This document is the durable, tracked record for refactoring work that was merged and then
deliberately rolled back at the user's explicit instruction. It replaces the rollback evidence
that ceased to be durable when PR [#4910](https://github.com/phasetr/ising-model/pull/4910)
untracked `.self-local`.

The inventories below are historical evidence, not a backlog and not implementation
authorization. They preserve literal names and paths so that future scans find this ledger before
turning the same material into another proposal.

## History topology

The three squash merges formed one linear lane after
`f23fa1e732d6985a59d305c85e018f06d62b2f88`, in this order:

1. PR [#4824](https://github.com/phasetr/ising-model/pull/4824), merge commit
   `e5b7675cf4e63190d75874fe83109a84060c00e6`;
2. PR [#4821](https://github.com/phasetr/ising-model/pull/4821), merge commit
   `4bfe4aebdec575435d7731d613abd0f6df7696fb`;
3. PR [#4820](https://github.com/phasetr/ising-model/pull/4820), merge commit
   `167ff124814bf90e31d96d2e3ed2fd6a2ad63b91`.

The current `main` is not a descendant of any of these three commits. It continues from their
common parent instead, so there is no later revert commit whose presence can stand in for this
record. The commits remain valid historical objects and their diffs are the source of the exact
inventories below.

## PR #4820: nine-path module-cost lane

PR #4820 changed exactly these nine tracked paths:

- `.github/workflows/lean_action_ci.yml`
- `.self-local/issues/INDEX.md`
- `.self-local/reports/design-4794-module-cost-protocol.md`
- `.self-local/reports/handoff-4792-post4819-2026-07-31.md`
- `.self-local/reports/measure-module-cost-pfer-family-20260731T122216Z.json`
- `.self-local/reports/perf-4724-fixed-cost-reconciliation.md`
- `.self-local/reports/perf-isdefeq-cluster-artifacts/measure.sh`
- `scripts/measure_module_cost.py`
- `scripts/test_measure_module_cost.py`

This lane changed zero Lean declarations and zero `.lean` paths. Its raw sample named these eight
measured module candidates:

- `IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularity.lean`
- `IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityDifferentiable.lean`
- `IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityDifferentiableH.lean`
- `IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityFE.lean`
- `IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityFEDifferentiable.lean`
- `IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityFEDifferentiableJoint.lean`
- `IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityFEJoint.lean`
- `IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityH.lean`

These paths and measurements do not authorize restoration of the harness, raw samples, CI wiring,
or any refactoring of the measured modules.

## PR #4821: clusters C and D

PR #4821 changed exactly these 26 tracked paths:

- `IsingModel/AmbientLattice/AnalyticityLambdaPolymer.lean`
- `IsingModel/BallBoundarySimonLieb/ScaledGKS.lean`
- `IsingModel/Basic.lean`
- `IsingModel/BetaDerivative/CorrelationFormulas.lean`
- `IsingModel/ClusterExpansion/AnchoredPeel.lean`
- `IsingModel/ClusterExpansion/SourceGeneratingFunction.lean`
- `IsingModel/ClusterExpansion/StrictPositivity/MayerPartialFerro.lean`
- `IsingModel/ClusterExpansion/TwoPointNumeratorFactorization.lean`
- `IsingModel/ComplexAnalyticity/DomainGeometry.lean`
- `IsingModel/ComplexAnalyticity/FugacityCalculus.lean`
- `IsingModel/ComplexAnalyticity/RealAxis.lean`
- `IsingModel/Concrete/LatticeGraphCorrelation/ComplexIsingPoly.lean`
- `IsingModel/Concrete/LatticeGraphCorrelation/ComplexRestrictionsLeeYangIsOpen.lean`
- `IsingModel/Concrete/LatticeGraphCorrelation/Lemma_17_5_2/HLSBridgeFromCubicTanhCore.lean`
- `IsingModel/Concrete/LatticeGraphCorrelation/Lemma_17_5_2/HLSBridgeFromSimonLiebVariants.lean`
- `IsingModel/CouplingDerivative.lean`
- `IsingModel/Hamiltonian.lean`
- `IsingModel/Inequalities/FKG.lean`
- `IsingModel/Inequalities/FKGInhomogeneous.lean`
- `IsingModel/Inequalities/GKSBoundaryConditionII.lean`
- `IsingModel/Inequalities/MonotonicityField.lean`
- `IsingModel/JDerivative.lean`
- `IsingModel/ScaledBetaDerivative.lean`
- `docs/index.md`
- `scripts/test_dead_candidate_scan.py`
- `tex/proof-guide.tex`

The definition-site reconciliation was 16 deletions and 2 additions, for a net reduction of 14
declarations. Fifteen distinct names left the tree; `edgeSpin_spinMul` accounts for the sixteenth
deletion because it was relocated and re-added under the same name.

The two additions/owners were:

- new generic owner `Spin.sign_mul`;
- relocated owner `edgeSpin_spinMul`.

The following three declarations changed visibility from private to public without changing
their owner name:

- `spin_edge_supermodular`
- `edgeSpin_quot_eq_spinProduct`
- `subset_pair_of_even_card`

The fifteen retired names were:

- `bc_edgeSpin_spinMul`
- `bc_sign_spinMul`
- `sign_spinMul`
- `continuous_leeYangFugacity'`
- `edgeSpin_quot_eq_spinProduct'`
- `edgeSpin_quot_eq_spinProduct_J`
- `finset_subset_pair_of_even_card`
- `isOpen_logZ_slitPlane_locus`
- `latticeDistance_pair_eq_displacement`
- `leeYangFugacity_mapsTo_leeYangDomain`
- `mayerPartialSum_zero_eq_zero`
- `norm_partitionFunctionComplex_eq_partitionFunction_at_real`
- `partitionFunctionComplex_analyticOnNhd_univ_joint'`
- `spin_edge_supermodularJ`
- `spin_edge_supermodular_F`

The merge explicitly carried forward, rather than resolved, these candidates:

- private concrete twin `Spin.sign_mul_ℝ`;
- pair `norm_partitionFunctionComplex_eq_partitionFunction_at_real_latticeGraph` and
  `norm_partitionFunctionComplex_at_real_latticeGraph`.

They are recorded because later proposals named them, not because they remain authorized work.

## PR #4824: cluster B

PR #4824 changed exactly these eight tracked paths:

- `IsingModel/Concrete/LatticeGraphCorrelation/EnergyClosedForms.lean`
- `IsingModel/Concrete/LatticeGraphCorrelation/EnergyClosedFormsSpinProductAndBot.lean`
- `IsingModel/Concrete/LatticeGraphCorrelation/FiniteVolumeBasics.lean`
- `IsingModel/Concrete/LatticeGraphCorrelation/FiniteVolumeBasicsHamiltonian.lean`
- `IsingModel/Concrete/LatticeGraphCorrelation/FiniteVolumeEnergyBounds.lean`
- `docs/index.md`
- `scripts/test_dead_candidate_scan.py`
- `tex/proof-guide.tex`

It removed nine duplicate declarations. The retired name and surviving owner for each pair were:

- `hamiltonianΛ_latticeGraph_J_zero` -> `hamiltonian_J_zero_latticeGraph`
- `hamiltonianΛ_flip_eq_latticeGraph` -> `hamiltonian_flip_eq_latticeGraph`
- `hamiltonianΛ_neg_h_latticeGraph` -> `hamiltonian_neg_h_latticeGraph`
- `hamiltonianΛ_latticeGraph_zero_params` -> `hamiltonian_zero_params_latticeGraph`
- `hamiltonianΛ_latticeGraph_eq_bot_at_J_zero` ->
  `hamiltonian_eq_bot_at_J_zero_latticeGraph`
- `partitionFunction_eq_bot_at_J_zero_latticeGraph` ->
  `partitionFunctionΛ_eq_bot_at_J_zero_latticeGraph`
- `correlationΛ_eq_bot_at_J_zero_latticeGraph` ->
  `correlation_eq_bot_at_J_zero_latticeGraph`
- `boltzmannWeightΛ_latticeGraph_pos` -> `boltzmannWeight_pos_latticeGraph`
- `hamiltonianΛ_latticeGraph_abs_le` -> `hamiltonian_abs_le_latticeGraph`

The measured merge had zero import-line changes and zero redirected call sites. It did not
establish a measured build-time benefit, and this ledger makes no such claim.

## Rollback authorization evidence

The [#4823 close comment](https://github.com/phasetr/ising-model/issues/4823#issuecomment-5149817710)
states that the issue was created during a session whose work was being rolled back at the user's
instruction. The [#4826 rollback comment](https://github.com/phasetr/ising-model/pull/4826#issuecomment-5149817476)
states both that the work was rolled back at the user's instruction and that its `.self-local`
force-adds lacked authorization. These comments are the controlling authorization evidence for
the deliberate rollback of the lane described above.

## Rejected duplicate re-proposals

The following issues were closed because they duplicated explicitly rolled-back work. Their
closure is not a successful implementation and creates no authorization:

- [#4885](https://github.com/phasetr/ising-model/issues/4885) and its
  [rejection comment](https://github.com/phasetr/ising-model/issues/4885#issuecomment-5172323997)
  re-proposed the nine PR #4824 declaration pairs.
- [#4886](https://github.com/phasetr/ising-model/issues/4886) and its
  [rejection comment](https://github.com/phasetr/ising-model/issues/4886#issuecomment-5172324334)
  re-proposed `Spin.sign_mul`, `Spin.sign_mul_ℝ`, edge-spin ownership, and related foundational
  consolidation from PR #4821.
- [#4887](https://github.com/phasetr/ising-model/issues/4887) and its
  [rejection comment](https://github.com/phasetr/ising-model/issues/4887#issuecomment-5172324755)
  re-proposed the two concrete complex-wrapper pairs carried after PR #4821.

## Immutable authorization firewall

PRs #4820, #4821, and #4824 and rejected re-proposals #4885, #4886, and #4887 form an
immutable campaign blacklist. Future work must not reintroduce, delete, alias, re-home,
generalize, or otherwise repackage any blacklisted item merely because it appears attractive in a
new audit.

Duplication scans and name/path scans do not authorize revival. Build timings do not authorize
revival. Consumer counts do not authorize revival. Absence of the reverted merge commits or their
declarations from current `main` does not authorize revival. Only a new explicit user instruction
naming the blacklisted item can authorize revival.

## Current refactoring safeguards

These are current intentions for reading the live theorem inventories, not additions to the
historical rollback topology above and not a record of issue, date, or batch history.

- A [coverage-catalogue row](coverage/chapters-2-10.html) that enumerates declaration ownership is
  the authority for that enumeration;
  preserve its distinction between generic APIs and a specialized owner rather than treating a
  shared suffix as proof that every declaration has the same domain.
- A candidate list or deletion scan is evidence for scoped investigation, never implementation
  authorization. Routine deletion requires a fresh, explicit work item and verification against
  the current tree.
- The [Chapter 17 coverage catalogue](coverage/chapter-17.html) and
  [Chapter 18 coverage catalogue](coverage/chapter-18.html) own their current scope qualifications.
  Rows labelled conditional, analogy, parked, off-book, or out of scope must not be promoted by a
  refactoring proposal.
- Clustering/analyticity and polymer/Mayer material require separate, scoped investigation because
  their catalogue rows distinguish finite, infinite-volume, conditional, and analogy-only results.
  Their presence in a scan grants no implementation authorization.
