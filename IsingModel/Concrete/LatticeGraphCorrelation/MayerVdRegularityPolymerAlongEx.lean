import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymer

/-!
# ℤ^d regularity of the polymer activity sum in the activity

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the regularity in the activity of the activity sum over the vertex-disjoint
compatible polymer families of the stage-`n` induced subgraph: it is `Continuous` and
`Differentiable ℝ`, and it `HasDerivAt` the termwise derivative
`∑_Γ ∑_{Q ∈ Γ} (∏_{P ∈ Γ.erase Q} t ^ |P|) * (|Q| * t ^ (|Q| - 1))`. No condition on the
activity is imposed.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d along-ex: vdPolymerFamilies_sum Continuous in t**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_continuous
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_continuous
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum Differentiable ℝ in t**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_differentiable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_differentiable
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum HasDerivAt**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_hasDerivAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_hasDerivAt
    (IsingModel.latticeGraph d) Λ n t

end Ambient

end IsingModel
