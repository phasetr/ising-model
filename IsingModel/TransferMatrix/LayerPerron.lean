import IsingModel.TransferMatrix.LayerPerron.EigenpairComparison
import IsingModel.TransferMatrix.LayerPerron.FlipEvenInvolution
import IsingModel.TransferMatrix.LayerPerron.PositiveColumn
import IsingModel.TransferMatrix.LayerPerron.BalancedLayerColumn
import IsingModel.TransferMatrix.LayerPerron.FlipSpinConstructors

/-!
# Positive/simple Perron-facing bridge for finite layer transfer matrices

This file records finite-dimensional consequences that are useful after a
Perron--Frobenius analysis has supplied a positive dominant eigenvector and a
one-dimensional dominant eigenspace.  It deliberately does not prove existence
of that eigenvector, spectral-radius maximality, a strict spectral gap,
thermodynamic limits, or open-slab estimates.

The main use for the layer route is to replace the direct `flip-even` dominant
column hypothesis from the spin-observable cancellation constructors by the
more natural inputs that the dominant column is positive and spans its
eigenspace.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.

## Contents

The declarations live in five child modules, re-exported by this declaration-free facade:

* `TransferMatrix.LayerPerron.EigenpairComparison` — the Collatz--Wielandt comparison of an
  arbitrary real eigenvector against a strictly positive one: the optimal attained relative
  scale in absolute value and one-sided, the one-dimensionality of the eigenspace of a
  strictly positive eigenpair of an entrywise positive matrix, and the resulting weak and
  strict absolute bounds on all real eigenvalues.
* `TransferMatrix.LayerPerron.PositiveColumn` — the column theory of explicit real
  orthogonal spectral data: a column is a right eigenvector for the corresponding
  spectral-data eigenvalue, columns are nonzero and pairwise non-proportional, and a
  strictly positive top column of an entrywise positive matrix has a positive eigenvalue,
  dominates all spectral-data eigenvalues in absolute value, spans its eigenspace,
  dominates strictly off the top, and admits some finite subdominant ratio `theta < 1`.
* `TransferMatrix.LayerPerron.FlipEvenInvolution` — the involution block: a strictly
  positive vector proportional to its pullback by an involution is invariant under it,
  hence a positive eigenvector spanning a simple eigenspace of a commuting matrix is even,
  together with the layer-state global spin flip as an involution and its balanced
  transfer-matrix instance.
* `TransferMatrix.LayerPerron.BalancedLayerColumn` — the balanced layer transfer-matrix
  restatements of the positive-column conclusions (absolute eigenvalue bound, eigenspace
  simplicity, strict bound off the top column, finite subdominant ratio) and the two
  general-`Ω` certificate constructors that fix the transfer scale to the positive top
  column's eigenvalue.
* `TransferMatrix.LayerPerron.FlipSpinConstructors` — the eight spin-observable certificate
  constructors replacing the direct flip-evenness hypothesis by dominant-column positivity:
  the `positiveSimpleFlipSpin` family, where the caller supplies eigenspace simplicity, and
  the `positiveColumnFlipSpin` family, where simplicity is derived from entrywise
  positivity, each in orthogonal and Hermitian variants with a free or scale-fixed transfer
  scale.
-/
