import IsingModel.TransferMatrix.LayerSpectral.FlipParitySelectionRules
import IsingModel.TransferMatrix.LayerSpectral.FlipParitySpectralSum
import IsingModel.TransferMatrix.LayerSpectral.FlipParityPartitionBounds
import IsingModel.TransferMatrix.LayerSpectral.FlipParityLayerSymmetric

/-!
# Flip-parity selection rules (GJ §17.1)

Parity (flip-even / flip-odd) selection rules for the real orthogonal spectral
data, the induced marked-matrix and boundary vanishing, the spectral-sum
expansions of marked traces, and the resulting partition lower bounds and
marked-sum spectral-prefactor upper bounds.  Also records the balanced
transfer eigenvalue/eigenvector data.  Part of the `LayerSpectral` scaffold.

This is an umbrella module: the content lives in the child modules
`FlipParitySelectionRules`, `FlipParitySpectralSum`, `FlipParityPartitionBounds`,
and `FlipParityLayerSymmetric`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/
