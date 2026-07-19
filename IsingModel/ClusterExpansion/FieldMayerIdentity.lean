import IsingModel.ClusterExpansion.FieldMayerIdentity.Capstone

/-!
# Field-dependent Mayer–Montroll identity `log Ξ_{a,b} = ∑ₙ fieldMayerExpansionTerm`
(GJ §17.6.1, brick 4)

Brick 4 of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(`∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window).  This file supplies the **algebraic
Mayer–Montroll identity** for the field-dependent hard-core polymer gas: the
field polymer free energy (the log of the field polymer partition function)
equals the field Mayer series,
`fieldPolymerFreeEnergy G a b = ∑' n, fieldMayerExpansionTerm G n a b`.

This is the field generalisation of the already-formalised `h = 0` identity
`mayer_identity_general_t` (`MayerCore/MayerMontroll.lean`, PR #3998), obtained by
carrying the multiplicative field weight
`w_{a,b}(P) = tanh(a)^|P|·tanh(b)^{#odd(P)}` (`fieldPolymerWeight`,
`Families/FieldConnectedPolymers.lean`) through the identical colour-degree /
log-Taylor / Fubini tower over the *connected* species `allConnectedPolymers G`.
The combinatorial coefficients (`ursellCoefficient`, `properSurjectiveColorings`
counts, the incompatibility graph) are weight-agnostic and reused *verbatim* from
`MayerMontroll.lean`; the genuinely new content is re-running the weight-carrying
`Finset` regroupings with `w_{a,b}` in place of the monomial `t^|P|`, and
supplying the analytic `log(1 + ε)` side over the field `ε`.  Convergence is
imported from brick 3 (`summable_fieldMayerExpansionTerm`, the
domination `|fieldClusterSeqActivity a b ω| ≤ clusterSeqActivity |tanh a| ω`).

Real `h` only; complex `h` (where `|tanh b|` need not be `≤ 1`) is deferred to the
later non-vanishing brick.  Regression at `b = 0`: `tanh 0 = 0`, so
`fieldPolymerWeight a 0 P = tanh(a)^|P|·0^{#odd(P)}` collapses to `tanh(a)^|P|` on
even polymers and vanishes otherwise, so `fieldPolymerZ G a 0` reduces to the
even-species reduced partition sum and the identity lands on the `h = 0`
`mayer_identity_general_t` up to the species relabelling `allPolymers ⤳
allConnectedPolymers`.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.5, pp. 378–386
  (lattice cluster expansion, field version).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.3
  (Mayer–Montroll) and §3.7.3, eqs. (3.48)–(3.49) (magnetic-field expansion).
-/
