import IsingModel.ClusterExpansion.RegularityHZero.PolymerSumContinuityDifferentiability
import IsingModel.ClusterExpansion.RegularityHZero.RealAnalyticityCapstone
import IsingModel.ClusterExpansion.RegularityHZero.ComplexAnalyticityCore
import IsingModel.ClusterExpansion.RegularityHZero.ComplexZeroFreeBalls

/-!
# Cluster expansion zero-field regularity

Regularity of the zero-field (`h = 0`) Ising partition function and free energy obtained
from the polymer (cluster) expansion of Glimm–Jaffe §18.6: writing
`Z(J, 0, β) = 2^|ι| · cosh(β·J)^|E| · ∑_Γ ∏_{P ∈ Γ} tanh(β·J)^|P|`
(the vertex-disjoint polymer-family identity of §18.4), each factor is as regular as the
elementary functions occurring in it, so the partition function and the free energy
`f = (1/|ι|) · log Z` inherit continuity, differentiability and real analyticity in `β`
and in `J`.

The same polynomial polymer-family sum is then taken over `ℂ` (Issue #3054): it is
complex-analytic in the activity variable and, through `Complex.tanh (β·J)`, in `β` and
`J` wherever `Complex.cosh (β·J) ≠ 0`.  Since its value at zero activity is `1`, it stays
non-zero on a ball around the origin, with a uniform lower bound `ε > 0` on a closed
sub-ball — the per-fixed-volume precursor of the volume-uniform `Z_ℂ` lower bound wanted
by the Lemma 17.5.2 `hZ` provider (Issue #3044).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §18.6.

## Contents

The declarations live in four child modules, re-exported by this declaration-free facade:

* `ClusterExpansion.RegularityHZero.PolymerSumContinuityDifferentiability` — the lattice
  Ising polymer partition function `latticeIsingPolymerPartition` with its non-negativity
  and `1 ≤ ·` bounds, the polymer activity simp lemmas, the continuity and
  differentiability of the vertex-disjoint polymer-family sum in the activity variable and
  in `β` / `J` through the `tanh(β·J)` substitution, and the resulting continuity and
  differentiability of the partition function at `h = 0`.
* `ClusterExpansion.RegularityHZero.RealAnalyticityCapstone` — the monomial-product helper
  `analyticAt_prod_pow`, the `AnalyticAt ℝ` polymer-family sum statements, and the
  `AnalyticAt ℝ` / `AnalyticOnNhd ℝ _ Set.univ` statements for the partition function and
  the free energy at `h = 0` (the §18.6 capstone).
* `ClusterExpansion.RegularityHZero.ComplexAnalyticityCore` — the complex counterparts
  (Issue #3054): continuity and `Differentiable ℂ` in the activity variable, the helper
  `analyticAt_prod_pow_complex`, the `AnalyticAt ℂ` polymer-family sum, the project-local
  `analyticAt_complex_tanh`, and the `tanh`-substituted `AnalyticAt ℂ` statements in `β`
  and `J`.
* `ClusterExpansion.RegularityHZero.ComplexZeroFreeBalls` — the value `1` of the complex
  polymer-family sum at zero activity and at `β = 0` / `J = 0`, the `Eventually` and
  open-ball non-vanishing statements around the origin, and the compactness upgrade to a
  uniform norm lower bound `ε > 0` on a closed ball, in both the `β` and the `J`
  direction.
-/
