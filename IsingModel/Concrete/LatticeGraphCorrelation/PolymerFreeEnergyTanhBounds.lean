import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBounds

/-!
# Concrete polymer free-energy tanh-bound wrappers

Narrow child module for concrete `ℤ^d` `polymerFreeEnergy` tanh bounds,
ferromagnetic bounds, the `log(1 + eps)` decomposition, and the `HasDerivAt`
wrapper. This keeps callers that only need these forwarders out of the
monolithic lattice-correlation legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 polymerFreeEnergy tanh-bound + ferro + hasDerivAt +
eq_log_one_add ℤ^d wraps -/

/-- **ℤ^d Λ: polymerFreeEnergy tanh ≤ |E| · tanh** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_mul
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_card_mul
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: ferro polymerFreeEnergy_tanh ≤ |E|·tanh**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_mul_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d Λ: ferro polymerFreeEnergy_tanh sandwich**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_sandwich_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d Λ: ferro polymerFreeEnergy_tanh ≤ |E|·log 2**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_log_two_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro
    (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d Λ: polymerFreeEnergy = log(1 + ε(t))** decomposition. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_log_one_add_eps
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.polymerFreeEnergy_Λ_eq_log_one_add_eps
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_hasDerivAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  Ambient.polymerFreeEnergy_Λ_hasDerivAt
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d along-ex: polymerFreeEnergy_tanh ≤ |E|·tanh** under
`0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_mul
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card * Real.tanh (β * J) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_card_mul
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: ferro polymerFreeEnergy_tanh ≤ |E|·tanh**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_mul_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card * Real.tanh (β * J) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro
    (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d along-ex: ferro polymerFreeEnergy_tanh sandwich**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_sandwich_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro
    (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d along-ex: ferro polymerFreeEnergy_tanh ≤ |E|·log 2**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_log_two_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card * Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro
    (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d along-ex: polymerFreeEnergy = log(1 + ε(t))**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_eq_log_one_add_eps
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_log_one_add_eps
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_hasDerivAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_hasDerivAt
    (IsingModel.latticeGraph d) Λ ht n

end Ambient
end IsingModel
