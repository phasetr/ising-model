import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsTanh

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy tanh-bound wrappers (§18.5)

Narrow child module for four ℤ^d
`polymerFreeEnergyAlongExhaustion_latticeGraph_*` tanh-bound wrappers:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_sandwich`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_log_two_of_le_one`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_log_two`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_double_bound`.

Each result is a thin pass-through of the ambient
`Ambient.polymerFreeEnergyAlongExhaustion_*` tanh-bound lemma at
`G := IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: polymerFreeEnergy tanh-form sandwich**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_sandwich
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: polymerFreeEnergy ≤ |E|·log 2 for 0 ≤ t ≤ 1**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_log_two_of_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card * Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_le_card_log_two_of_le_one
    (IsingModel.latticeGraph d) Λ ht ht1 n

/-- **ℤ^d along-ex: polymerFreeEnergy_tanh ≤ |E|·log 2 under
0 ≤ β·J**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_log_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card * Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: polymerFreeEnergy_tanh double bound**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_double_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card * Real.tanh (β * J) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card * Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_double_bound
    (IsingModel.latticeGraph d) Λ hβJ n

end Ambient

end IsingModel
