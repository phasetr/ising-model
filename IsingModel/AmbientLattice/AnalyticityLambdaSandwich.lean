import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.PolymerBounds

/-!
# High-temperature sandwich and log series for the polymer free energy (§18.4-§18.5)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`. Write `E` for `(inducedGraph G Λ).edgeFinset`,
`Ξ t` for `∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ), ∏ P ∈ Γ, t ^ P.card` and
`ε t` for the same sum over `… .erase ∅`; neither sum has a definition of its own, so a
statement that mentions one carries the summation written out — the free-energy sandwich and
series statements carry `ε`, the polymer-sum bounds carry `Ξ`, and none carries both — and
`polymerFreeEnergy (inducedGraph G Λ) t` is by definition `Real.log (Ξ t)`.

The sandwich is stated as one five-fold conjunction:
`0 ≤ polymerFreeEnergy`, `polymerFreeEnergy ≤ ε t`, `ε t ≤ (1 + t) ^ E.card - 1`,
`(1 + t) ^ E.card - 1 < 1`, and `polymerFreeEnergy < Real.log 2`. Alongside it, and under the
same hypotheses, the alternating logarithm series
`fun n ↦ (-1) ^ n * (ε t) ^ (n + 1) / (n + 1)` `HasSum` to `polymerFreeEnergy`.

Both are stated at a bare activity `t` under `0 ≤ t`, and at the physical activity
`Real.tanh (β * J)` under `0 ≤ β * J` and again under the ferromagnetic pair `0 ≤ J`,
`0 < β`; in every case the high-temperature hypothesis `(1 + t) ^ E.card < 2`, with `t` the
activity in force, is also required; it is that hypothesis which forces `ε t < 1`, through
the third and fourth conjuncts of the sandwich, and so makes the series converge.

The polymer sum itself is sandwiched at the physical activity, `1 ≤ Ξ (tanh (β * J))` on the
left in every case and, on the right, either the crude `2 ^ E.card` or the sharp
`(1 + tanh (β * J)) ^ E.card`; each of those two right-hand bounds is stated once under
`0 ≤ β * J` and once under the ferromagnetic pair, with no high-temperature hypothesis.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `0 ≤ t`, `0 ≤ β * J`, `0 ≤ J`, `0 < β` and `(1 + t) ^ E.card < 2` in its
bare and `tanh` forms; every statement here carries at least one of them.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`** (§18.4 Λ wrap of PR #1526). -/
theorem polymerFreeEnergy_Λ_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t < Real.log 2 :=
  IsingModel.polymerFreeEnergy_high_temp_sandwich (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: explicit log Taylor expansion for `polymerFreeEnergy`**
(§18.4 Λ wrap of PR #1517). -/
theorem polymerFreeEnergy_Λ_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log_of_pow_lt_two
    (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`
(tanh form)** (§18.5 Λ wrap of the abstract tanh-form
`polymerFreeEnergy_tanh_high_temp_sandwich`). -/
theorem polymerFreeEnergy_Λ_tanh_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_high_temp_sandwich
    (inducedGraph G Λ) hβJ h_pow

/-- **Λ-layer: explicit log Taylor expansion for `polymerFreeEnergy`
(tanh form)** (§18.5 Λ wrap of the abstract tanh-form
`polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two`). -/
theorem polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J))) :=
  IsingModel.polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two
    (inducedGraph G Λ) hβJ h_pow

/-- **Λ-layer: VD polymer-family sum sandwich** (§18.5 Λ wrap of
`vdPolymerFamilies_sum_sandwich`). -/
theorem vdPolymerFamilies_sum_Λ_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich (inducedGraph G Λ) hβJ

/-- **Λ-layer: VD polymer-family sum sharp sandwich** (§18.5 Λ wrap
of `vdPolymerFamilies_sum_sandwich_sharp`). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_sharp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_sharp
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_high_temp_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_high_temp_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ h_pow

/-- **Λ-layer: log Taylor expansion for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic Λ wrap). -/
theorem
polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J))) :=
  IsingModel.polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    (inducedGraph G Λ) hJ hβ h_pow

/-- **Λ-layer: VD polymer-family sum sandwich (ferromagnetic)**
(§18.5 ferromagnetic Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: VD polymer-family sum sharp sandwich
(ferromagnetic)** (§18.5 ferromagnetic Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_sharp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_sharp_ferromagnetic
    (inducedGraph G Λ) hJ hβ


end Ambient

end IsingModel
