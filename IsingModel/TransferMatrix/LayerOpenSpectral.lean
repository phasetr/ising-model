import IsingModel.TransferMatrix.LayerOpenSpectral.PathGlue
import IsingModel.TransferMatrix.LayerOpenSpectral.NumeratorIdentities
import IsingModel.TransferMatrix.LayerOpenSpectral.SpectralForm
import IsingModel.TransferMatrix.LayerOpenSpectral.PartitionAndCertificates

/-!
# Open-boundary layer spectral bridges

This file is the finite open-boundary counterpart of the cyclic spectral
certificate constructors.  It rewrites the open layer partition as a
boundary-vector matrix-power sum and packages explicit open-path bounds into
the existing open min-gap certificate.

The results are finite and conditional.  They do not prove a physical
interacting spectral window, a Perron--Frobenius theorem, a thermodynamic limit,
or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/
