import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.MayerCore.PolymerBounds

/-!
# Nonnegativity, monotonicity and edge-count bounds for the polymer free energy

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`. Write `E` for `(inducedGraph G Λ).edgeFinset`;
`polymerFreeEnergy (inducedGraph G Λ) t` is by definition `Real.log` of
`∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ), ∏ P ∈ Γ, t ^ P.card`.

At a nonnegative activity the polymer free energy is nonnegative, and it is bounded above
by `E.card * Real.log (1 + t)`, by `E.card * t`, and — once `t ≤ 1` as well — by
`E.card * Real.log 2`. It is `MonotoneOn` over `Set.Ici 0` with no hypothesis at all, and
its comparison form requires only `0 ≤ t` and `t ≤ s`.

It vanishes identically in the activity in two degenerate situations, each stated for every
real `t`: when `allPolymers (inducedGraph G Λ) = ∅`, and when `E = ∅`.

At the physical activity `Real.tanh (β * J)` under `0 ≤ β * J` the same material appears as
a conjunction `0 ≤ polymerFreeEnergy ∧ polymerFreeEnergy ≤ E.card * Real.log (1 + tanh)`, as
the single bound `E.card * Real.log 2`, and as a two-fold conjunction pairing
`E.card * Real.tanh (β * J)` with `E.card * Real.log 2`.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `0 ≤ t`, `0 ≤ s`, `t ≤ s`, `t ≤ 1`, `0 ≤ β * J`,
`allPolymers (inducedGraph G Λ) = ∅` and `E = ∅`; the `MonotoneOn` statement carries none.
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

/-- At the Λ layer, polymer free energy preserves order when the smaller activity is
nonnegative. -/
theorem polymerFreeEnergy_Λ_le_of_le_of_nonneg_left
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) s :=
  IsingModel.polymerFreeEnergy_le_of_le_of_nonneg_left
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
