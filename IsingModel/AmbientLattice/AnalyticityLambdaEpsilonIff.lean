import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.StrictMono

/-!
# When the excess polymer sum is positive, and when it is zero (§18.5)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`. Write `Ξ t` for the polymer sum
`∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ), ∏ P ∈ Γ, t ^ P.card` and `ε t` for
the same sum over `… .erase ∅`, so that `Ξ t = 1 + ε t` and
`polymerFreeEnergy (inducedGraph G Λ) t = Real.log (Ξ t)`. Neither sum has a definition of
its own; both are written out in each statement.

The characterisations are exact and their two cases are complementary. Under `0 ≤ t`:
`0 < ε t` precisely when `0 < t` and `(allPolymers (inducedGraph G Λ)).Nonempty`, and
`ε t = 0` precisely when `t = 0` or `allPolymers (inducedGraph G Λ) = ∅`. At the physical
activity `Real.tanh (β * J)` under `0 ≤ β * J` the same pair is stated for `ε` and again for
`polymerFreeEnergy`, with `0 < Real.tanh (β * J)` and `Real.tanh (β * J) = 0` in place of
the conditions on `t`. So the excess sum, the polymer sum's departure from `1`, and the
polymer free energy all vanish together and are all positive together.

The strict statements assume `(allPolymers (inducedGraph G Λ)).Nonempty` and are then
unconditional in the graph: `Ξ` is strictly larger at `t` than at `s` whenever `0 ≤ s < t`,
and `StrictMonoOn` over `Set.Ici 0`; both `polymerFreeEnergy` and `Ξ` are `StrictMonoOn`
over `Set.Ioi 0`. Under `0 < t` with that nonemptiness, `polymerFreeEnergy` is strictly
positive, `1 < Ξ t`, and `0 < ε t`; the same three are stated at `Real.tanh (β * J)` under
`0 < Real.tanh (β * J)` with that nonemptiness.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `0 ≤ t`, `0 ≤ β * J`, `0 < t`, `0 ≤ s`, `s < t`,
`0 < Real.tanh (β * J)` and `(allPolymers (inducedGraph G Λ)).Nonempty`; every statement
here carries at least one of them.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 ε(t) / polymerFreeEnergy positivity-iff Λ-layer wraps -/

/-- **Λ-layer: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pos_iff
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨ IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_minus_one_eq_zero_iff
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** under
`0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_pos_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_eq_zero_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 0 < polymerFreeEnergy(tanh) ↔ 0 < tanh ∧
allPolymers ≠ ∅** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff (inducedGraph G Λ) hβJ

/-- **Λ-layer: polymerFreeEnergy(tanh) = 0 ↔ tanh = 0 ∨
allPolymers = ∅** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff
    (inducedGraph G Λ) hβJ

/-! ### §18.5 strict-mono / strict-pos under polymers ≠ ∅
Λ-layer wraps -/

/-- **Λ-layer: vdSum(s) < vdSum(t) for `0 ≤ s < t`** under polymers
exist. -/
theorem vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hs hst

/-- **Λ-layer: vdSum is `StrictMonoOn (Set.Ici 0)`** under polymers
exist. -/
theorem vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  IsingModel.vdPolymerFamilies_sum_strictMonoOn_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: 0 < pFE under `0 < t` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_gt_one_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 0 < pFE(tanh) under `0 < tanh` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: 1 < vdSum(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: 0 < ε(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: pFE is `StrictMonoOn (Set.Ioi 0)`** under polymers
exist. -/
theorem polymerFreeEnergy_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) t) (Set.Ioi 0) :=
  IsingModel.polymerFreeEnergy_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: vdSum is `StrictMonoOn (Set.Ioi 0)`** under polymers
exist. -/
theorem
vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  IsingModel.vdPolymerFamilies_sum_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (inducedGraph G Λ) h_poly


end Ambient

end IsingModel
