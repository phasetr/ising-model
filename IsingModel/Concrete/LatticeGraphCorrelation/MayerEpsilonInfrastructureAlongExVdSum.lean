import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructureVdSum

/-!
# Concrete along-ex vdPolymerFamilies_sumAlongExhaustion ε(t) wrappers

Narrow child module for 3 ℤ^d along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_*_minus_one_*` ε(t) wrappers
extracted from `MayerEpsilonInfrastructureAlongEx.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_at_zero`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_continuous`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_lt_one_eventually`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerEpsilonInfrastructureAlongEx` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: ε(0) = 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_at_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: ε(t) is `Continuous`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_continuous
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_continuous
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: ε(t) < 1 eventually as t → 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_lt_one_eventually
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
