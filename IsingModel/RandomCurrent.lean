import IsingModel.RandomCurrent.Core
import IsingModel.RandomCurrent.ClusterConditioning
import IsingModel.RandomCurrent.BoundedExpansion
import IsingModel.RandomCurrent.Switching
import IsingModel.RandomCurrent.Peeling
import IsingModel.RandomCurrent.Switching.GlobalSwitchingLimit
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Random current representation for the Ising model (FV §3.7)

Umbrella file importing all random-current sub-modules:

* `RandomCurrent.Core` — `Current` type, parity, sources, weight, `weightSum`.
* `RandomCurrent.ClusterConditioning` — edge-partition weight factorization
  (GJ §17.5 Lemma 5.1 ingredient SL-A).
* `RandomCurrent.BoundedExpansion` — `CurrentBounded`, Taylor expansion,
  N → ∞ convergence capstone.
* `RandomCurrent.Switching` — Aizenman switching lemma infrastructure
  (subFinset, pairFinset, jointFactor, source algebra, connectivity).
* `RandomCurrent.Peeling` — edge peeling + `weightSum_pair_le_edge_sum`
  (Simon 1980; Lieb 1980).
* `RandomCurrent.Switching.GlobalSwitchingLimit` — the `tsum`/`iSup` lift of
  the bounded global switching identity to `weightSum` (GJ §17.5 brick 2).

Reference: Friedli–Velenik §3.7. For the `Peeling` bound:
B. Simon, *Correlation inequalities and the decay of correlations in
ferromagnets*, Comm. Math. Phys. 77 (1980), 111–126; E. H. Lieb, *A refinement
of Simon's correlation inequality*, Comm. Math. Phys. 77 (1980), 127–135. -/

namespace IsingModel
namespace Ambient
end Ambient
end IsingModel
