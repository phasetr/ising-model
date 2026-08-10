import IsingModel.AmbientLattice.Defs
import IsingModel.ClusterExpansion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep
import IsingModel.AmbientLattice.AnalyticityLambdaPerDirection
import IsingModel.AmbientLattice.AnalyticityLambdaPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaSandwich
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds
import IsingModel.AmbientLattice.AnalyticityLambdaMayer
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff
import IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening
import IsingModel.AmbientLattice.AnalyticityLambdaSection186
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Λ-restricted analyticity: aggregation point

This module declares nothing — no definition, no theorem, no instance — so its imports
serve re-export alone, and importing this path is what brings the whole Λ-layer analyticity
development into scope at once. Every name reachable through it is declared in one of its
imports: the ambient-lattice definitions, the base-layer cluster expansion, and the
`AnalyticityLambda*` modules.

What those imports develop is the Glimm-Jaffe §18.4-§18.6 cluster expansion, and the
regularity that accompanies it, transported from a graph on a finite vertex type to the
induced subgraph `inducedGraph G Λ` of an ambient `G : SimpleGraph V` on a finite volume
`Λ : Finset V`. Two kinds of subject occur there. `partitionFunctionΛ`, `freeEnergyΛ`,
`correlationΛ`, `magnetizationΛ` and `susceptibilityΛ` are Λ-layer definitions, each
unfolding to its base-layer counterpart at `inducedGraph G Λ`. `polymerFreeEnergy`,
`mayerPartialSum`, `mayerExpansionTerm`, `allPolymers` and `vdCompatiblePolymerFamilies`
have no Λ-layer definition of their own and are applied to `inducedGraph G Λ` directly;
there it is only the theorem names that carry a `_Λ` marker.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

end Ambient
end IsingModel
