import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.IffCharacterisations

/-!
# Values, decomposition and elementary bounds of the polymer sum (§18.5)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`. Write `E` for `(inducedGraph G Λ).edgeFinset`,
`Ξ t` for `∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ), ∏ P ∈ Γ, t ^ P.card` and
`ε t` for the same sum over `… .erase ∅`. Neither sum has a definition of its own; both are
written out in every statement, and only the theorem names abbreviate them.

Special values are recorded at literal arguments substituted into the statement: `Ξ 0 = 1`,
`Ξ 1 = (vdCompatiblePolymerFamilies (inducedGraph G Λ)).card`,
`mayerPartialSum (inducedGraph G Λ) N 0 = 0` and
`mayerExpansionTerm (inducedGraph G Λ) n 0 = 0` at a literal activity `0`, and at low order
`mayerPartialSum … 0 t = 0`, `mayerExpansionTerm … 0 t = 0`, with both
`mayerPartialSum … 1 t` and `mayerExpansionTerm … 1 t` equal to
`∑ P ∈ allPolymers (inducedGraph G Λ), t ^ P.card`. The decomposition `Ξ t = 1 + ε t`, which
isolates the empty family, holds for every real `t` and needs no hypothesis.

At a nonnegative activity, `Ξ t` is strictly positive, at least `1`, and at most
`(1 + t) ^ E.card`. At the physical activity `Real.tanh (β * J)` under `0 ≤ β * J` the same
bounds appear as `1 ≤ Ξ (tanh (β * J))`, `Ξ (tanh (β * J)) ≤ (1 + tanh (β * J)) ^ E.card`
and the cruder `Ξ (tanh (β * J)) ≤ 2 ^ E.card`.

Where `Ξ` sits relative to `1` is settled exactly there, and the two cases are
complementary: `1 < Ξ (tanh (β * J))` precisely when `0 < Real.tanh (β * J)` and
`(allPolymers (inducedGraph G Λ)).Nonempty`, and `Ξ (tanh (β * J)) = 1` precisely when
`Real.tanh (β * J) = 0` or `allPolymers (inducedGraph G Λ) = ∅`.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `0 ≤ t` and `0 ≤ β * J`; the special values and the `1 + ε t` decomposition
carry neither.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 basic identities at_zero / at_one Λ wraps -/

/-- **Λ-layer: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sum_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  IsingModel.vdPolymerFamilies_sum_at_zero (inducedGraph G Λ)

/-- **Λ-layer: vdPolymerFamilies_sum at t = 1 = #vdCompatPoly families**. -/
theorem vdPolymerFamilies_sum_Λ_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).card :=
  IsingModel.vdPolymerFamilies_sum_at_one (inducedGraph G Λ)

/-- **Λ-layer: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSum_Λ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerPartialSum_zero (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at N = 1 = ∑_P t^|P|**. -/
theorem mayerPartialSum_Λ_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card :=
  IsingModel.mayerPartialSum_one (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSum_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 = 0 :=
  IsingModel.mayerPartialSum_at_zero (inducedGraph G Λ) N

/-- **Λ-layer: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerExpansionTerm_zero (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at n = 1 = ∑_P t^|P|**. -/
theorem mayerExpansionTerm_Λ_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card :=
  IsingModel.mayerExpansionTerm_one (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n 0 = 0 :=
  IsingModel.mayerExpansionTerm_at_zero (inducedGraph G Λ) n

/-! ### §18.5 vdPolymerFamilies_sum tanh iff characterizations Λ wraps -/

/-- **Λ-layer: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_gt_one_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_eq_one_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G Λ),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_tanh_eq_one_iff
    (inducedGraph G Λ) hβJ

/-! ### §18.5 vdPolymerFamilies_sum bound family Λ-layer wraps -/

/-- **Λ-layer: vdSum_tanh ≤ 2^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_le_two_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_two_pow (inducedGraph G Λ) hβJ

/-- **Λ-layer: vdSum_tanh ≤ (1+tanh)^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_le_one_plus_tanh_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_one_plus_tanh_pow
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 1 ≤ vdSum_tanh** under `0 ≤ β·J`. -/
theorem one_le_vdPolymerFamilies_sum_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  IsingModel.one_le_vdPolymerFamilies_sum (inducedGraph G Λ) hβJ

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds Λ-layer -/

/-- **Λ-layer: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_ge_one_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_ge_one_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_pos_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_pos_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sum_Λ_eq_one_add
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_eq_one_add (inducedGraph G Λ) t


end Ambient

end IsingModel
