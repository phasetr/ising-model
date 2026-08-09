import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivity

/-!
# ℤ^d positivity and vanishing of the nonempty-family sum, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the characterisations of when the activity sum over the vertex-disjoint
compatible polymer families of the stage-`n` induced subgraph other than the empty one is
strictly positive and of when it vanishes: it is strictly positive exactly when the activity
is strictly positive and that subgraph has at least one polymer, and it vanishes exactly when
the activity is `0` or that subgraph has none. Each characterisation is given at a bare
activity under `0 ≤ t` and at the activity `tanh (β * J)` under `0 ≤ β * J`, with no sign
condition on `β` or `J` separately.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pos_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_pos_iff
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_eq_zero_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_eq_zero_iff
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tanh_pos_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_iff
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tanh_eq_zero_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_eq_zero_iff
    (IsingModel.latticeGraph d) Λ hβJ n

end Ambient
end IsingModel
