import IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay.Spectral
import IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay.Numerator
import IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay.Certificate

/-!
# Finite open layer-slab two-marked spectral decay (GJ Section 17.1)

This file generalises the single-mark open-slab spectral decay to *two distinct
marks* `f`, `g` at the two observable cut points.  The single-mark chain inserts
the same observable `f` at the left (`i`--`j`) and right (`j`--`l`) spectral cut;
here the left cut carries `f` and the right cut carries `g`.  This is exactly the
shape needed to bound cross-transverse-site correlations
`⟨σ_(left,x) · σ_(left+sep,y)⟩` with `x ≠ y`, where the first mark is
`layerSpinAt x` and the second mark is `layerSpinAt y`.

The bulk of the single-mark glue is mark-agnostic (the path-glue combinatorics
and the denominator/partition infrastructure carry over verbatim), so only the
genuinely two-mark numerator pieces are twinned here.  The central-channel
cancellation still only needs the *left* mark to kill the dominant marked
diagonal; the right mark is a passive spectator.

The statements remain finite and conditional.  They do not prove an open
Perron--Frobenius input, a physical interacting spectral window,
thermodynamic-limit decay, or final hyperplane exponential decay.

This module is an umbrella that re-exports the split children:

* `LayerOpenTwoMarkedSpectralDecay.Spectral` — the `RealOrthogonalSpectralData`
  two-marked spectral prefactor, central-channel cancellation, boundary product
  and spectral-sum bound.
* `LayerOpenTwoMarkedSpectralDecay.Numerator` — the open two-marked numerator
  chain down to the numerator spectral-prefactor absolute bound.
* `LayerOpenTwoMarkedSpectralDecay.Certificate` — the open two-marked min-gap
  certificate, its normalised decay bound and the project-level
  cross-transverse-site correlation equate lemma and decay theorem.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/
