import IsingModel.TransferMatrix.LayerPerronExistence.QuadraticForm
import IsingModel.TransferMatrix.LayerPerronExistence.OrthogonalSpectralData
import IsingModel.TransferMatrix.LayerPerronExistence.LayerWrappers
import IsingModel.TransferMatrix.LayerPerronExistence.SpinObservableCertificates
import IsingModel.TransferMatrix.LayerPerronExistence.MaximalColumnCertificates

/-!
# Signed positive dominant columns for finite layer transfer matrices

This file is an umbrella re-exporting the sign-invariant interface and the finite
maximal-column construction needed for the Perron-facing layer route, split for
build modularity into the child modules under
`IsingModel.TransferMatrix.LayerPerronExistence`.  A real orthogonal spectral
column is only determined up to sign, so the useful statement is that a chosen
column is positive after multiplication by a scalar sign with square one.

The content is organized as:

* `LayerPerronExistence.QuadraticForm` — squared-norm and quadratic-form helpers
  and the sign-orientation lemma;
* `LayerPerronExistence.OrthogonalSpectralData` — the `RealOrthogonalSpectralData`
  signed-positive column construction and its spectral consequences;
* `LayerPerronExistence.LayerWrappers` — balanced layer transfer matrix
  specialisations;
* `LayerPerronExistence.SpinObservableCertificates` — flip-even signed-positive
  spin-observable certificate constructors;
* `LayerPerronExistence.MaximalColumnCertificates` — maximal-column certificate
  constructors and their finite-prefactor discharges.

Importing this module re-exports every declaration of the split, so existing
downstream imports of `IsingModel.TransferMatrix.LayerPerronExistence` are
unaffected.  The split still does not discharge the finite-cardinality prefactor
condition in the certificates, open-slab geometry, thermodynamic limits, or
final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/
