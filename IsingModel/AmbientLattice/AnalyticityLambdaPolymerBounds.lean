import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.MayerCore.PolymerBounds

/-!
# AmbientLattice/Analyticity polymerFreeEnergy_Λ bounds wrappers

Narrow child module for 12 Λ-layer polymerFreeEnergy_Λ nonneg / bounds /
monotone / eq_zero / tanh sandwich / tanh double bound wrappers. The
theorem names are unchanged from the former `Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Λ-layer: `polymerFreeEnergy ≥ 0` under `t ≥ 0`** (§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_nonneg_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy ≤ |E| · log(1 + t)` under
`t ≥ 0`** (§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_le_card_log_one_plus_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log (1 + t) :=
  IsingModel.polymerFreeEnergy_le_card_log_one_plus_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy ≤ |E| · t` under `t ≥ 0`**
(§18.5 Λ wrap of Step 634). -/
theorem polymerFreeEnergy_Λ_le_card_mul_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * t :=
  IsingModel.polymerFreeEnergy_le_card_mul_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy` is `MonotoneOn (Set.Ici 0)`**
(§18.5 Λ wrap of Step 633). -/
theorem polymerFreeEnergy_Λ_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    MonotoneOn (fun t : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) t)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_monotoneOn_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: `polymerFreeEnergy = 0` for empty-polymer induced
graphs** (§18.5 Λ wrap of Step 621). -/
theorem polymerFreeEnergy_Λ_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (t : ℝ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 :=
  IsingModel.polymerFreeEnergy_eq_zero_of_no_polymers
    (inducedGraph G Λ) h_no t

/-- **Λ-layer: `polymerFreeEnergy = 0` for edgeless induced graphs**
(§18.5 Λ wrap of Step 623). -/
theorem polymerFreeEnergy_Λ_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 :=
  IsingModel.polymerFreeEnergy_eq_zero_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty t

/-- **Λ-layer: `polymerFreeEnergy` preserves order on `[0, ∞)`**
(§18.5 Λ wrap of Step 649). -/
theorem polymerFreeEnergy_Λ_le_of_le_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) s :=
  IsingModel.polymerFreeEnergy_le_of_le_of_nonneg
    (inducedGraph G Λ) ht hs hts

/-- **Λ-layer: `polymerFreeEnergy` strict-form order preservation**
(§18.5 Λ wrap of Step 650). -/
theorem polymerFreeEnergy_Λ_le_of_le_strict_form
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) s :=
  IsingModel.polymerFreeEnergy_le_of_le_strict_form
    (inducedGraph G Λ) ht hts

/-- **Λ-layer: `polymerFreeEnergy` tanh-form sandwich** (§18.5 Λ wrap
of Step 632). -/
theorem polymerFreeEnergy_Λ_tanh_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_sandwich (inducedGraph G Λ) hβJ

/-- **Λ-layer: `polymerFreeEnergy ≤ |E|·log 2` for `0 ≤ t ≤ 1`**
(§18.5 Λ wrap of Step 642). -/
theorem polymerFreeEnergy_Λ_le_card_log_two_of_le_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_le_card_log_two_of_le_one
    (inducedGraph G Λ) ht ht1

/-- **Λ-layer: `polymerFreeEnergy_tanh ≤ |E|·log 2` under `0 ≤ β·J`**
(§18.5 Λ wrap of Step 643). -/
theorem polymerFreeEnergy_Λ_tanh_le_card_log_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_le_card_log_two
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: `polymerFreeEnergy_tanh` double bound** (§18.5 Λ wrap
of Step 645). -/
theorem polymerFreeEnergy_Λ_tanh_double_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.tanh (β * J) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_double_bound
    (inducedGraph G Λ) hβJ


end Ambient

end IsingModel
