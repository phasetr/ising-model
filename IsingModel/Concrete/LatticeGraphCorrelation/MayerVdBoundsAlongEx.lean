import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdBounds

/-!
# ℤ^d bounds on the polymer activity sum at the `tanh` activity

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the bounds on the activity sum over the vertex-disjoint compatible polymer
families of the stage-`n` induced subgraph at the activity `tanh (β * J)`: it is at least `1`,
at most `(1 + tanh (β * J)) ^ |E_n|`, and at most `2 ^ |E_n|`. Every statement assumes
`0 ≤ β * J`, and none assumes a sign for `β` or `J` separately.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: vdSum_tanh ≤ 2^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_le_two_pow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_le_two_pow
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: vdSum_tanh ≤ (1+tanh)^|E|** under `0 ≤ β·J`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_le_one_plus_tanh_pow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_le_one_plus_tanh_pow
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: 1 ≤ vdSum_tanh** under `0 ≤ β·J`. -/
theorem one_le_vdPolymerFamilies_sumAlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  Ambient.one_le_vdPolymerFamilies_sumAlongExhaustion
    (IsingModel.latticeGraph d) Λ hβJ n

end Ambient
end IsingModel
