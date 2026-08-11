import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.MayerPartialFerro

/-!
# The positivity dichotomy at ferromagnetic parameters (§18.5)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`, all at the physical activity
`Real.tanh (β * J)`. Write `E` for `(inducedGraph G Λ).edgeFinset`, `Ξ t` for
`∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ), ∏ P ∈ Γ, t ^ P.card` and `ε t` for
the same sum over `… .erase ∅`; neither sum has a definition of its own, and
`polymerFreeEnergy (inducedGraph G Λ) t = Real.log (Ξ t)` by definition. The comments below,
declaration and section alike, write `vdSum` for `Ξ` and `pFE` for
`polymerFreeEnergy (inducedGraph G Λ)`, and parenthesise the activity: `vdSum(tanh)`,
`ε(tanh)` and `pFE(tanh)` are `Ξ`, `ε` and the polymer free energy at `Real.tanh (β * J)`.
All three are prose shorthands of this file, and only the last abbreviates something that is
a `def`.

The regime here is the ferromagnetic pair: `0 ≤ β` together with `0 ≤ J`, stated as two
separate hypotheses rather than as the single product condition `0 ≤ β * J`, which the pair
implies but which does not imply it.

Under that pair the polymer free energy at `Real.tanh (β * J)` is positive exactly when
`ε (tanh (β * J))` is, and is `0` exactly when `ε (tanh (β * J))` is `0`; it is strictly
below `ε (tanh (β * J))` exactly when the latter is positive. Resolving the excess sum into
the parameters, positivity holds exactly when `0 < Real.tanh (β * J)` and
`(allPolymers (inducedGraph G Λ)).Nonempty`, and vanishing exactly when
`Real.tanh (β * J) = 0` or `allPolymers (inducedGraph G Λ) = ∅` — two complementary
conditions, recorded both for the polymer free energy and, as `1 < Ξ` and `Ξ = 1`, for the
polymer sum.

Adding `0 < ε (tanh (β * J))` to the pair yields the two strict upper bounds
`polymerFreeEnergy < ε (tanh (β * J))` and
`polymerFreeEnergy < (1 + Real.tanh (β * J)) ^ E.card - 1`.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `0 ≤ β`, `0 ≤ J` and `0 < ε (tanh (β * J))`; the first two are carried by
every statement here, the third by the two strict bounds alone.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy/vdSum tanh ferromagnetic iff family
Λ-layer wraps (under `0 ≤ β, 0 ≤ J`) -/

/-- **Λ-layer: pFE(tanh) < ε(tanh) ↔ ε(tanh) > 0** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_iff_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ ε(tanh) = 0** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < ε(tanh)** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 1 < vdSum(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**
(ferro). -/
theorem vdPolymerFamilies_sum_Λ_tanh_gt_one_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: vdSum(tanh) = 1 ↔ tanh = 0 ∨ allPolymers = ∅**
(ferro). -/
theorem vdPolymerFamilies_sum_Λ_tanh_eq_one_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_tanh_eq_one_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) < (1 + tanh)^|E| - 1** under ε(tanh) > 0
(ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ h_eps_pos

/-- **Λ-layer: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_of_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ h_eps_pos


end Ambient

end IsingModel
