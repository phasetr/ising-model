import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.LocalCoverPatch.Vitali

/-!
# Open-cover local patch wrappers

This module contains the open-cover patching wrapper split from
`PerStageComplex.Branches.LocalCoverPatch.OpenPatch`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d open-cover branch-family patching handoff on `leeYangDomain`**:
if a Lee-Yang open cover carries compatible local branch-family limits, then
the limits patch to one differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_openCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {α : Type*} {U : α → Set ℂ}
    {F : α → ℕ → ℂ → ℂ} {f : α → ℂ → ℂ}
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : IsingModel.leeYangDomain ⊆ ⋃ i, U i)
    (hbranch : ∀ i n,
      AnalyticOnNhd ℂ (F i n) (U i)
        ∧ (∀ z ∈ U i,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F i n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n))
    (hconv : ∀ i, TendstoLocallyUniformlyOn (F i) (f i) Filter.atTop (U i))
    (hcompat : ∀ i j, Set.EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (f i) (U i)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_openCover_patch
    (IsingModel.latticeGraph d) Λ J β hUopen hcover hbranch hconv hcompat

end Ambient

end IsingModel
