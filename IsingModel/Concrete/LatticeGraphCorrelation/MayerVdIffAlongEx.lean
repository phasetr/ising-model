import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdIff

/-!
# ℤ^d threshold characterisations of the polymer activity sum, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the characterisations of when the activity sum over the vertex-disjoint
compatible polymer families of the stage-`n` induced subgraph sits at `1` and of when it
exceeds `1`: it equals `1` exactly when the sum over the families other than the empty one
vanishes, it exceeds `1` exactly when that sum is strictly positive, and at the activity
`tanh (β * J)` these unfold to the activity being `0`, respectively strictly positive,
together with that subgraph having no polymer, respectively at least one. The comparison at
equality holds at an arbitrary activity; its strict counterpart assumes `0 ≤ t`, and the
`tanh` statements assume `0 ≤ β * J`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: vdSum = 1 ↔ ε = 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_eq_one_iff_eps_eq_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_eq_one_iff_eps_eq_zero
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: vdSum > 1 ↔ ε > 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_gt_one_iff_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_gt_one_iff_eps_pos
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_gt_one_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_eq_one_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff
    (IsingModel.latticeGraph d) Λ hβJ n

end Ambient
end IsingModel
