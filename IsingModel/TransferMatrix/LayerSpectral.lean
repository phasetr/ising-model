import IsingModel.TransferMatrix.LayerSpectral.Positivity
import IsingModel.TransferMatrix.LayerSpectral.Conjugation
import IsingModel.TransferMatrix.LayerSpectral.BalancedMatrix
import IsingModel.TransferMatrix.LayerSpectral.HermitianBridge
import IsingModel.TransferMatrix.LayerSpectral.FlipParity
import IsingModel.TransferMatrix.LayerSpectral.SpectralGap
import IsingModel.TransferMatrix.LayerSpectral.BalancedSpectralGap

/-!
# Finite layer spectral scaffold (GJ §17.1)

This file is an umbrella re-exporting the finite cyclic layer transfer matrix
spectral scaffold, split for build modularity into the child modules under
`IsingModel.TransferMatrix.LayerSpectral`.  For a positive one-layer weight
`u`, the generally non-symmetric transfer matrix `T a b = u b * k a b` is
diagonally similar to the balanced matrix

`S a b = sqrt (u a) * k a b * sqrt (u b)`.

When the transition kernel `k` is symmetric, `S` is a symmetric real matrix.
The scaffold records the diagonal similarity and the induced invariance of the
partition trace and the two-insertion marked trace.  It deliberately does not
prove a Perron--Frobenius theorem, a spectral gap, thermodynamic limits, or
exponential decay.

The content is organized as:

* `LayerSpectral.Positivity` — entrywise positivity vocabulary;
* `LayerSpectral.Conjugation` — matrix conjugation and trace helpers;
* `LayerSpectral.BalancedMatrix` — the balanced layer transfer matrix;
* `LayerSpectral.HermitianBridge` — finite Hermitian spectral bridge;
* `LayerSpectral.FlipParity` — flip-parity selection rules;
* `LayerSpectral.SpectralGap` — spectral-gap certificates;
* `LayerSpectral.BalancedSpectralGap` — balanced spectral-gap certificates.

Importing this module re-exports every declaration of the scaffold, so existing
downstream imports of `IsingModel.TransferMatrix.LayerSpectral` are unaffected.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/
