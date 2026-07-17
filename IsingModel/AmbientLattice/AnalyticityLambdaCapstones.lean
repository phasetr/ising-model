import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.CycleSeven

/-!
# AmbientLattice/Analyticity §18.4-§18.6 capstones + Mayer filter-connected wrappers

Narrow child module for 11 Λ-layer wrappers covering:

- §18.4-§18.6 capstones: `partitionFunctionΛ_high_temp_expansion_h_zero_polymer_family`
  (Z formula), `_closed_evenSubgraphs` (FV (3.45) form),
  `freeEnergyΛ_eq_polymerFreeEnergy` / `_ferromagnetic` (§18.6 decomposition),
  `freeEnergyΛ_eq_log_two_at_betaJ_zero`, `mayerPartialSum_Λ_one_at_one`.
- §18.5 Mayer filter-connected / ε^n / mayerPartialSum_analyticOnNhd:
  `mayerPartialSum_Λ_analyticOnNhd`,
  `vdPolymerFamilies_sum_Λ_minus_one_pow`,
  `mayerExpansionTerm_Λ_filter_connected_{zero, one}`,
  `mayerExpansionTerm_Λ_two_filter_connected_eq_incompat`.

The theorem names are unchanged from the former `Analyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.4-§18.6 capstones Λ-layer wraps -/

/-- **Λ-layer: §18.4 partitionFunction polymer-family form** capstone:
`Z_Λ(J, 0, β) = 2^|Λ| · cosh(β·J)^|E_Λ| · ∑_Γ ∏ tanh(β·J)^|P|`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_polymer_family
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    partitionFunctionΛ G Λ ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset V) *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card *
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_polymer_family
    (inducedGraph G Λ) J β

/-- **Λ-layer: §18.4 partitionFunction even-subgraph form** (FV (3.45))**:
`Z_Λ = 2^|Λ| · cosh(β·J)^|E_Λ| · ∑_X tanh(β·J)^|X|`. -/
theorem
partitionFunctionΛ_high_temp_expansion_h_zero_closed_evenSubgraphs
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    partitionFunctionΛ G Λ ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset V) *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card *
        ∑ X ∈ IsingModel.evenSubgraphs (inducedGraph G Λ),
          Real.tanh (β * J) ^ X.card := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_closed_evenSubgraphs
    (inducedGraph G Λ) J β

/-- **Λ-layer: §18.6 freeEnergy decomposition** under `0 ≤ β·J` and
`Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset V) :=
  IsingModel.freeEnergy_eq_polymerFreeEnergy
    (inducedGraph G Λ) J β hβJ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: §18.6 ferromagnetic freeEnergy decomposition** under
`0 ≤ J, 0 < β` and `Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset V) :=
  IsingModel.freeEnergy_eq_polymerFreeEnergy_ferromagnetic
    (inducedGraph G Λ) J β hJ hβ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: freeEnergy = log 2** at `β·J = 0`, under
`Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_log_two_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ = Real.log 2 :=
  IsingModel.freeEnergy_eq_log_two_at_betaJ_zero
    (inducedGraph G Λ) hβJ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: mayerPartialSum at N=1, t=1 = |allPolymers|**. -/
theorem mayerPartialSum_Λ_one_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 1 1 =
      (IsingModel.allPolymers (inducedGraph G Λ)).card :=
  IsingModel.mayerPartialSum_one_at_one (inducedGraph G Λ)

/-! ### §18.5 Mayer filter-connected + ε^n + mayerPartialSum
analyticOnNhd Λ-layer wraps -/

/-- **Λ-layer: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSum_Λ_analyticOnNhd
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph G Λ) N s) Set.univ :=
  IsingModel.mayerPartialSum_analyticOnNhd (inducedGraph G Λ) N

/-- **Λ-layer: ε(t)^n as multi-Γ piFinset sum**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ^ n =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n =>
                (IsingModel.vdCompatiblePolymerFamilies
                  (inducedGraph G Λ)).erase ∅),
        ∏ i : Fin n, ∏ P ∈ ω i, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pow
    (inducedGraph G Λ) t n

/-- **Λ-layer: mayerExpansionTerm filter-connected at n=0 = ∅**. -/
theorem mayerExpansionTerm_Λ_filter_connected_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (Fintype.piFinset
        (fun _ : Fin 0 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) = ∅ :=
  IsingModel.mayerExpansionTerm_filter_connected_zero
    (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm filter-connected at n=1 = full
piFinset**. -/
theorem mayerExpansionTerm_Λ_filter_connected_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers (inducedGraph G Λ)) :=
  IsingModel.mayerExpansionTerm_filter_connected_one (inducedGraph G Λ)

/-- **Λ-layer: filter-connected = filter-incompatible at n=2**. -/
theorem mayerExpansionTerm_Λ_two_filter_connected_eq_incompat
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (Fintype.piFinset
        (fun _ : Fin 2 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset
          (fun _ : Fin 2 =>
            IsingModel.allPolymers (inducedGraph G Λ))).filter
          (fun ω => IsingModel.PolymersIncompatible (ω 0) (ω 1)) :=
  IsingModel.mayerExpansionTerm_two_filter_connected_eq_incompat
    (inducedGraph G Λ)

end Ambient

end IsingModel
