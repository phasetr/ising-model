import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.MayerCore.LogTaylor

/-!
# Second-order Mayer terms and the polymer free energy at low order (§18.5)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`. Write `E` for `(inducedGraph G Λ).edgeFinset`,
`Ξ t` for `∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ), ∏ P ∈ Γ, t ^ P.card` and
`ε t` for the same sum over `… .erase ∅`; neither has a definition of its own, and
`polymerFreeEnergy (inducedGraph G Λ) t = Real.log (Ξ t)` by definition.

At order `2` the Mayer expansion term is written out over
`allPolymers (inducedGraph G Λ) ×ˢ allPolymers (inducedGraph G Λ)`, once with the weight
`if PolymersIncompatible pq.1 pq.2 then -1/2 else 0` and once as `-1/2` times the sum over
the `PolymersIncompatible` filter of that product; the order-`2` partial sum is then the
order-`1` sum `∑ P ∈ allPolymers (inducedGraph G Λ), t ^ P.card` plus that term. Independent
of the order, the expansion term is bounded in absolute value by the sum of
`|ursellCoefficient ω| * |clusterSeqActivity t ω|` over all length-`n` polymer sequences,
and the partial sum vanishes at every order and activity when
`allPolymers (inducedGraph G Λ) = ∅` or when `E = ∅`.

For the polymer free energy: `polymerFreeEnergy … 0 = 0` and
`polymerFreeEnergy … 1 = Real.log (vdCompatiblePolymerFamilies (inducedGraph G Λ)).card` at
literal activities, and `polymerFreeEnergy … t = Real.log (1 + ε t)` for every real `t`,
which is the `Ξ t = 1 + ε t` decomposition read through the logarithm.

Its analytic statements name the region they hold on, and each lies in the nonnegative
activity: `AnalyticAt ℝ` at a point assumed to satisfy `0 ≤ t`, `AnalyticOnNhd ℝ` over
`Set.Ici 0`, and `HasDerivAt` at a point assumed to satisfy `0 ≤ t` with the derivative
named explicitly as the ratio of the termwise derivative of `Ξ` to `Ξ t`. Nothing here
treats a negative activity, in either direction. Under `0 ≤ t` the free energy is also
sandwiched between `0` and `E.card * Real.log (1 + t)`; at `Real.tanh (β * J)` it is bounded
by `E.card * Real.tanh (β * J)` under `0 ≤ β * J`, and, under the ferromagnetic pair
`0 ≤ J`, `0 < β`, by the same product, by `E.card * Real.log 2`, and by the sandwich with
`E.card * Real.log (1 + tanh (β * J))` on the right.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `0 ≤ t`, `0 ≤ β * J`, `0 ≤ J`, `0 < β`,
`allPolymers (inducedGraph G Λ) = ∅` and `E = ∅`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 Mayer expansion edge-cases + n=2 + abs_le Λ-layer -/

/-- **Λ-layer: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTerm_Λ_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
              (IsingModel.allPolymers (inducedGraph G Λ)),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerExpansionTerm_two (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTerm_Λ_two_filter
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
                (IsingModel.allPolymers (inducedGraph G Λ))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerExpansionTerm_two_filter (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSum_Λ_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 2 t =
      (∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
                  (IsingModel.allPolymers (inducedGraph G Λ))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerPartialSum_two (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum = 0 on no-polymer graphs**. -/
theorem mayerPartialSum_Λ_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t = 0 :=
  IsingModel.mayerPartialSum_eq_zero_of_no_polymers
    (inducedGraph G Λ) h_no t N

/-- **Λ-layer: mayerPartialSum = 0 on edgeless graphs**. -/
theorem mayerPartialSum_Λ_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t = 0 :=
  IsingModel.mayerPartialSum_eq_zero_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty t N

/-- **Λ-layer: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTerm_Λ_abs_le
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (t : ℝ) :
    |IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ)),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  IsingModel.mayerExpansionTerm_abs_le (inducedGraph G Λ) n t

/-! ### §18.5 polymerFreeEnergy at-zero/at-one + analytic + sandwich Λ -/

/-- **Λ-layer: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergy_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 0 = 0 :=
  IsingModel.polymerFreeEnergy_at_zero (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy at `t = 1`** =
`log |vdCompatiblePolymerFamilies|`. -/
theorem polymerFreeEnergy_Λ_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G Λ)).card :=
  IsingModel.polymerFreeEnergy_at_one (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G Λ) s) t :=
  IsingModel.polymerFreeEnergy_analyticAt (inducedGraph G Λ) ht

/-- **Λ-layer: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem polymerFreeEnergy_Λ_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G Λ) s) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_analyticOnNhd_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy sandwich for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log (1 + t) :=
  IsingModel.polymerFreeEnergy_sandwich_of_nonneg (inducedGraph G Λ) ht

/-! ### §18.5 polymerFreeEnergy tanh-bound + ferro + hasDerivAt +
eq_log_one_add Λ-layer wraps -/

/-- **Λ-layer: polymerFreeEnergy tanh ≤ |E| · tanh** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_mul
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.tanh (β * J) :=
  IsingModel.polymerFreeEnergy_tanh_le_card_mul (inducedGraph G Λ) hβJ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh_le_card_mul**. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.tanh (β * J) :=
  IsingModel.polymerFreeEnergy_tanh_le_card_mul_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh_sandwich**. -/
theorem polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh ≤ |E| · log 2**. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_le_card_log_two_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: polymerFreeEnergy = log(1 + ε(t))** decomposition. -/
theorem polymerFreeEnergy_Λ_eq_log_one_add_eps
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.polymerFreeEnergy_eq_log_one_add_eps (inducedGraph G Λ) t

/-- **Λ-layer: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_hasDerivAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  IsingModel.polymerFreeEnergy_hasDerivAt (inducedGraph G Λ) ht


end Ambient

end IsingModel
