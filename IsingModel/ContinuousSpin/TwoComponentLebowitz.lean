import IsingModel.ContinuousSpin.TwoComponentLebowitz.RotatedProductsDiff
import IsingModel.ContinuousSpin.TwoComponentLebowitz.GibbsIntegrability

/-!
# The second/third inequalities of GJ Theorem 4.7.1 (Lebowitz for two-component spins)

The difference-observable non-negative-coefficient expansion completing the
duplicate-variable proof of the second/third inequalities of GJ Theorem 4.7.1
(4.7.6)–(4.7.8), pp. 70–71.

In the §4.7 block rotation, the single-copy spins are recovered from the rotated
coordinates by `tᵢ = (αᵢ + βᵢ)/√2`, `tᵢ' = (αᵢ − βᵢ)/√2`, `qᵢ = (γᵢ − δᵢ)/√2`,
`qᵢ' = (γᵢ + δᵢ)/√2`.  Hence the difference of a `t`- (resp. `q`-) monomial across
the duplicate is `(√2/2)^{|A|}` times the difference of the `±` products of the
rotated coordinates, which expands (`plusProd − minusProd`) with **non-negative
coefficients** (mutual induction `nncoeffs_evenSum_oddDiff`).  Feeding the product
of two such differences to `doubled_integral_nonneg` and combining with the GKS-II
doubling consequence gives the headline inequalities
`⟨t^A t^B⟩ ≥ ⟨t^A⟩⟨t^B⟩` (4.7.6), `⟨q^A q^B⟩ ≥ ⟨q^A⟩⟨q^B⟩` (4.7.7), and
`⟨t^A q^B⟩ ≤ ⟨t^A⟩⟨q^B⟩` (4.7.8), and Corollary 4.7.2.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, Cor 4.7.2, pp. 70–71
-/
