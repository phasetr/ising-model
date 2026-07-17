import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.MayerPartialFerro

/-!
# AmbientLattice/Analyticity polymerFreeEnergy_Λ basic wrappers

Narrow child module for the 16 §18.4 polymerFreeEnergy_Λ /
vdPolymerFamilies_sum_Λ / mayer*_Λ basic iff / strict-mono /
strict-pos / le-pow / hasSum filter-connected wrappers. The theorem
names are unchanged from the former `Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Λ-layer: `polymerFreeEnergy` strictly increasing under polymers
exist** (§18.4 strict-mono Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) s <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_lt_of_lt_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hs hst

/-- **Λ-layer: `polymerFreeEnergy_strictMonoOn (Set.Ici 0)` under
polymers exist** (§18.4 strict-mono Λ wrap). -/
theorem polymerFreeEnergy_Λ_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy (inducedGraph G Λ) t)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_strictMonoOn_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: `polymerFreeEnergy > 0 ↔ 0 < t ∧ polymers exist`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ↔
      0 < t ∧ (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_pos_iff (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy = 0 ↔ t = 0 ∨ no polymers`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 ↔
      t = 0 ∨ IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_eq_zero_iff (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy ≤ ε(t)` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_le_eps_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_le_eps_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy < ε(t)` when `ε(t) > 0`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_eps_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_eps_pos : 0 < ∑ Γ ∈
      (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_lt_eps_of_eps_pos (inducedGraph G Λ) h_eps_pos

/-- **Λ-layer: `polymerFreeEnergy ≤ (1+t)^|E| - 1` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_le_pow_sub_one_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_le_pow_sub_one_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy < log 2` under `(1+t)^|E| < 2` and
`0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_log_two_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t < Real.log 2 :=
  IsingModel.polymerFreeEnergy_lt_log_two_of_pow_lt_two (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: `vdSum > 1 ↔ ε > 0` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_gt_one_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_gt_one_iff_eps_pos (inducedGraph G Λ) ht

/-- **Λ-layer: `vdSum = 1 ↔ ε = 0`** (§18.4 Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_eq_one_iff_eps_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  IsingModel.vdPolymerFamilies_sum_eq_one_iff_eps_eq_zero (inducedGraph G Λ) t

/-! ### §18.4 mayerExpansionTerm / mayerPartialSum Λ-layer wrappers -/

/-- **Λ-layer: `mayerExpansionTerm = 0` for graphs with no polymers** (§18.4 Λ wrap). -/
theorem mayerExpansionTerm_Λ_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅) (n : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t = 0 :=
  IsingModel.mayerExpansionTerm_eq_zero_of_no_polymers (inducedGraph G Λ) h_no n t

/-- **Λ-layer: `mayerPartialSum G 0 t = 0`** (§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_zero_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerPartialSum_zero_eq_zero (inducedGraph G Λ) t

/-- **Λ-layer: `mayerPartialSum G 1 t > 0` under `0 < t` and polymers exist**
(§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t :=
  IsingModel.mayerPartialSum_one_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: `mayerPartialSum G 1 t ≥ 0` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t :=
  IsingModel.mayerPartialSum_one_nonneg_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `mayerExpansionTerm` filter to connected polymer
sequences** (§18.4 Λ wrap of PR #1521). -/
theorem mayerExpansionTerm_Λ_filter_connected
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t =
      ∑ ω ∈ (Fintype.piFinset
          (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω => (IsingModel.polymerSeqIncompatibilityGraph ω).Connected),
        IsingModel.ursellCoefficient ω * IsingModel.clusterSeqActivity t ω :=
  IsingModel.mayerExpansionTerm_filter_connected (inducedGraph G Λ) n t

/-- **Λ-layer: `mayerPartialSum` filter to connected polymer sequences**
(§18.4 Λ wrap of PR #1522). -/
theorem mayerPartialSum_Λ_filter_connected
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (N : ℕ) (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ω ∈ (Fintype.piFinset
            (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ))).filter
          (fun ω => (IsingModel.polymerSeqIncompatibilityGraph ω).Connected),
          IsingModel.ursellCoefficient ω * IsingModel.clusterSeqActivity t ω :=
  IsingModel.mayerPartialSum_filter_connected (inducedGraph G Λ) N t

end Ambient

end IsingModel
