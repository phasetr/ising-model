import IsingModel.RandomCurrent.Core
import IsingModel.RandomCurrent.BoundedExpansion
import IsingModel.RandomCurrent.Switching
import IsingModel.RandomCurrent.Peeling
import IsingModel.AmbientLattice
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Random current representation for the Ising model (GJ §5.1 / FV §3.7)

Umbrella file importing all random-current sub-modules:

* `RandomCurrent.Core` — `Current` type, parity, sources, weight, `weightSum`.
* `RandomCurrent.BoundedExpansion` — `CurrentBounded`, Taylor expansion,
  N → ∞ convergence capstone.
* `RandomCurrent.Switching` — Aizenman switching lemma infrastructure
  (subFinset, pairFinset, jointFactor, source algebra, connectivity).
* `RandomCurrent.Peeling` — edge peeling + `weightSum_pair_le_edge_sum`
  (GJ §5.1 / FV Prop 9.31 p. 428).

References: Glimm–Jaffe §5.1 pp. 76–79; Friedli–Velenik §3.7, Prop 9.31. -/

namespace IsingModel
namespace Ambient
end Ambient
end IsingModel
