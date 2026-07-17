import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds
import IsingModel.Lattice

/-!
# Concrete ℤ^d polymerFreeEnergy tanh-bound wrappers (§18.5)

Narrow child module for the 8 ℤ^d polymerFreeEnergy tanh-bound
wrappers (`polymerFreeEnergy_Λ_latticeGraph_{tanh_sandwich,
le_card_log_two_of_le_one, tanh_le_card_log_two, tanh_double_bound}`
and `polymerFreeEnergyAlongExhaustion_latticeGraph_{tanh_sandwich,
le_card_log_two_of_le_one, tanh_le_card_log_two, tanh_double_bound}`)
extracted from `PolymerFreeEnergyBounds.lean` in PR #2060. Each is a
thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_*` / `polymerFreeEnergyAlongExhaustion_*`
tanh-bound lemma at `IsingModel.latticeGraph d`. The theorem names
are unchanged from the former `PolymerFreeEnergyBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 polymerFreeEnergy tanh-bound family ℤ^d wraps -/

/-- **ℤ^d Λ: polymerFreeEnergy tanh-form sandwich**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergy_Λ_tanh_sandwich
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: polymerFreeEnergy ≤ |E|·log 2 for 0 ≤ t ≤ 1**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_le_card_log_two_of_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_le_card_log_two_of_le_one
    (IsingModel.latticeGraph d) Λ ht ht1

/-- **ℤ^d Λ: polymerFreeEnergy_tanh ≤ |E|·log 2 under 0 ≤ β·J**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_log_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_card_log_two
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: polymerFreeEnergy_tanh double bound**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_double_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_tanh_double_bound
    (IsingModel.latticeGraph d) Λ hβJ

/-! ## Moved: AlongExhaustion polymerFreeEnergy tanh-bound wrappers

The four wrappers
`polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_sandwich`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_log_two_of_le_one`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_log_two`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_double_bound` now
live in `PolymerFreeEnergyBoundsTanhAlongEx.lean`. -/


end Ambient

end IsingModel
