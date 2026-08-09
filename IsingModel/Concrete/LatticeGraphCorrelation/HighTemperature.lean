import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSandwich

/-!
# ℤ^d polymer free energy inside the cluster-expansion convergence radius (§18.5)

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the
high-temperature control of `polymerFreeEnergy` in the regime where `(1 + t) ^ |E_Λ|` stays
below `2`: a chain placing the polymer free energy between `0` and the activity sum
`∑_Γ ∏_{P ∈ Γ} t ^ |P|` over the vertex-disjoint compatible polymer families other than the
empty one, placing that sum below `(1 + t) ^ |E_Λ| - 1`, that quantity below `1`, and hence
the polymer free energy below `log 2`; and, in the same regime, an alternating logarithmic
series in that activity sum which `HasSum`s to the polymer free energy. Each statement is
given at a bare activity `t` under `0 ≤ t` and at the activity `tanh (β * J)` under
`0 ≤ β * J`, and each carries the convergence hypothesis in its own activity.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ-direct: high-temperature sandwich for `polymerFreeEnergy`**
(§18.5 ℤ^d wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_high_temp_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 ∧
    (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t < Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_high_temp_sandwich
    (IsingModel.latticeGraph d) Λ ht h_pow

/-- **ℤ^d Λ-direct: log Taylor expansion for `polymerFreeEnergy`**
(§18.5 ℤ^d wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_hasSum_via_log_of_pow_lt_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t) :=
  Ambient.polymerFreeEnergy_Λ_hasSum_via_log_of_pow_lt_two
    (IsingModel.latticeGraph d) Λ ht h_pow

/-- **ℤ^d Λ-direct: high-temperature sandwich for `polymerFreeEnergy`
(tanh form)** (§18.5 ℤ^d wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_high_temp_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_tanh_high_temp_sandwich
    (IsingModel.latticeGraph d) Λ hβJ h_pow

/-- **ℤ^d Λ-direct: log Taylor expansion for `polymerFreeEnergy`
(tanh form)** (§18.5 ℤ^d wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_hasSum_via_log_of_pow_lt_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J))) :=
  Ambient.polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two
    (IsingModel.latticeGraph d) Λ hβJ h_pow

end Ambient
end IsingModel
