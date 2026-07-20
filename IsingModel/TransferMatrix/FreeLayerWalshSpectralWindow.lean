import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow.WalshBasisOrthogonality
import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow.WalshDiagonalization
import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow.PhysicalBridgeSpectralWindow
import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow.FlipParityMinGapCertificates

/-!
# Finite free-layer Walsh spectral window

This file extends the one-site and two-site free-layer spectral-window bridges
to an arbitrary finite transverse layer with no transverse edges, zero external
field, and identity longitudinal transition pairs.  The balanced transfer
matrix factors into independent one-dimensional transfer matrices, and the
finite Walsh characters give an explicit orthogonal spectral basis.

The final certificate uses the honest finite prefactor threshold
`tanh (p.β * p.J) < (2 ^ Fintype.card S - 1)⁻¹`.  This deliberately does not
claim an interacting transverse-layer spectral window or make `theta < 1`
sufficient in a larger state space.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.

## Contents

The declarations live in four child modules, re-exported by this declaration-free facade:

* `TransferMatrix.FreeLayerWalshSpectralWindow.WalshBasisOrthogonality` — the Walsh
  coordinates on a finite transverse layer (down-spin set of a layer state and its
  equivalence with `Finset S`, the all-up Walsh index, the normalized Walsh columns and
  the Walsh matrix, the free-layer product transfer matrix and its Walsh eigenvalues),
  together with the character orthogonality `∑_ω σ_A(ω) σ_B(ω) = 0` for `A ≠ B` and the
  two-sided orthogonality of the Walsh matrix.
* `TransferMatrix.FreeLayerWalshSpectralWindow.WalshDiagonalization` — the factorization
  of layer-state sums into independent one-site spin sums, the one-site signed and
  unsigned transfer row sums giving the top and bottom `1D` eigenvalues, the eigenvector
  property of each (normalized) Walsh character, the column identity `T · W = W · diag(λ)`
  and the full diagonalization `T = W · diag(λ) · Wᵀ`.
* `TransferMatrix.FreeLayerWalshSpectralWindow.PhysicalBridgeSpectralWindow` — the bridge
  to the physical zero-field free layer (identity transition weight as a product of
  one-dimensional transfer entries, trivial internal weight at `h = 0`, balanced layer
  transfer matrix equal to the free product transfer matrix), the spectral-window
  consequences (`|λ_χ| = tanh a ^ |A_χ| · λ_top^{|S|}` and the subdominant bound with
  `theta = tanh a`), and the free-layer `RealOrthogonalSpectralData`.
* `TransferMatrix.FreeLayerWalshSpectralWindow.FlipParityMinGapCertificates` — the
  behaviour of the Walsh basis under the global layer spin flip (parity sign of the index,
  flip-even / flip-odd columns, flip-even and signed-positive top column), the physical
  zero-field spectral data with its flip-parity adaptation, and the conditional and
  unconditional finite free-layer balanced min-gap certificates.
-/
