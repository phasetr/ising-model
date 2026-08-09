import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIff

/-!
# ℤ^d ferromagnetic thresholds and strict bounds, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, at the activity `tanh (β * J)`, the ferromagnetic thresholds for the activity sum
over the vertex-disjoint compatible polymer families of the stage-`n` induced subgraph — it
exceeds `1` exactly when the activity is strictly positive and that subgraph has at least one
polymer, and it equals `1` exactly when the activity is `0` or that subgraph has none —
together with strict upper bounds on `polymerFreeEnergy`, by `(1 + tanh (β * J)) ^ |E_n| - 1`
and by the activity sum over the families other than the empty one. Every statement assumes
`0 ≤ β` and `0 ≤ J` separately; the strict upper bounds assume in addition that the latter sum
is strictly positive.
-/

namespace IsingModel
namespace Ambient

/-- **Z^d along-ex: 1 < vdSum(tanh) iff 0 < tanh and allPolymers nonempty**
(ferro). -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_gt_one_iff_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: vdSum(tanh) = 1 iff tanh = 0 or allPolymers empty**
(ferro). -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_eq_one_iff_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: pFE(tanh) < (1+tanh)^|E| - 1** under
eps(tanh) > 0 (ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n h_eps_pos

/-- **Z^d along-ex: pFE(tanh) < eps(tanh)** under eps(tanh) > 0
(ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_eps_of_eps_pos_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n h_eps_pos

end Ambient
end IsingModel
