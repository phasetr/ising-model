import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.MayerCore.PolymerFreeEnergy

/-!
# The Mayer identity where it holds unconditionally in the order (§18.5)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`. Write `Ξ t` for the polymer sum
`∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ), ∏ P ∈ Γ, t ^ P.card`, which has no
definition of its own, so the statements that name it carry the summation written out while
the rest are phrased through `polymerFreeEnergy`; by definition
`polymerFreeEnergy (inducedGraph G Λ) t = Real.log (Ξ t)`.

The Mayer identity equates `Real.log (Ξ t)` with `mayerPartialSum (inducedGraph G Λ) N t`
for an order `N : ℕ` that is universally quantified and otherwise unconstrained. In general
that equality needs the full series; what is recorded here are the situations where it holds
for every `N` at once, because both sides are `0`.

Two families of such situations occur. In the first the activity itself is `0`: at `t = 0`;
at `Real.tanh (β * J)` under the hypothesis `β * J = 0`; and at `Real.tanh (0 * J)` and
`Real.tanh (β * 0)`, where the vanishing parameter is a literal `0` substituted into the
statement rather than a hypothesis. Each is stated both with `Real.log (Ξ …)` written out
and in the `polymerFreeEnergy` form, and the doubly-substituted `Real.tanh (0 * 0)` case is
recorded as well. In the second family the graph carries no polymer: under
`allPolymers (inducedGraph G Λ) = ∅`, and under the stronger hypothesis
`(inducedGraph G Λ).edgeFinset = ∅`, which forces it, the identity holds at every activity,
in the bare and in the `Real.tanh (β * J)` form. The disjunctive statement straddles the two
families rather than joining either: under
`β * J = 0 ∨ allPolymers (inducedGraph G Λ) = ∅` the first disjunct kills the activity and
the second kills the polymers, and it is recorded at `Real.tanh (β * J)` alone, with no
bare-activity counterpart.

Away from those situations the statements weaken to an inequality: the order-`0` partial sum
is at most the polymer free energy, at a bare activity under `0 ≤ t` and at
`Real.tanh (β * J)` under `0 ≤ β * J` and again under the ferromagnetic pair `0 ≤ J`,
`0 < β`.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `β * J = 0`, `allPolymers (inducedGraph G Λ) = ∅`,
`(inducedGraph G Λ).edgeFinset = ∅`, the disjunction of the first two, `0 ≤ t`, `0 ≤ β * J`,
`0 ≤ J` and `0 < β`; the literal-substitution slices carry none.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 mayer_identity_at edge-case Λ wraps -/

/-- **Λ-layer: Mayer identity at `t = 0`** (Step 600). -/
theorem mayer_identity_at_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 :=
  IsingModel.mayer_identity_at_zero (inducedGraph G Λ) N

/-- **Λ-layer: Mayer identity at `β·J = 0`** (Step 609). -/
theorem mayer_identity_at_betaJ_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_at_betaJ_zero (inducedGraph G Λ) hβJ N

/-- **Λ-layer: Mayer identity at `β = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_beta_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.mayer_identity_at_beta_zero (inducedGraph G Λ) J N

/-- **Λ-layer: Mayer identity at `J = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_J_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_J_zero (inducedGraph G Λ) β N

/-! ### §18.5 polymerFreeEnergy_eq_mayerPartialSum_at edge-case Λ wraps -/

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at t = 0**
(Step 611). -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 0 =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_zero
    (inducedGraph G Λ) N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at β·J = 0**
(Step 617). -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero
    (inducedGraph G Λ) hβJ N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at β = 0**. -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_beta_zero
    (inducedGraph G Λ) J N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at J = 0**. -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_J_zero
    (inducedGraph G Λ) β N

/-! ### §18.5 mayer_identity polymer_free_energy variants Λ wraps -/

/-- **Λ-layer: Mayer identity at `J = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_J_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_J_zero_polymer_free_energy
    (inducedGraph G Λ) β N

/-- **Λ-layer: Mayer identity at `β = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_beta_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.mayer_identity_at_beta_zero_polymer_free_energy
    (inducedGraph G Λ) J N

/-- **Λ-layer: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_either_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_either_zero_polymer_free_energy
    (inducedGraph G Λ) N

/-! ### §18.5 mayerPartialSum_zero ≤ polymerFreeEnergy Λ wraps -/

/-- **Λ-layer: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_Λ_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.mayerPartialSum_zero_le_polymerFreeEnergy
    (inducedGraph G Λ) ht

/-- **Λ-layer: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) :=
  IsingModel.mayerPartialSum_zero_tanh_le_polymerFreeEnergy
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) :=
  IsingModel.mayerPartialSum_zero_tanh_le_polymerFreeEnergy_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-! ### §18.5 mayer_identity_of edge-case Λ wraps -/

/-- **Λ-layer: Mayer identity for empty-polymer graphs**. -/
theorem mayer_identity_of_no_polymers_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayer_identity_of_no_polymers (inducedGraph G Λ) h_no t N

/-- **Λ-layer: Mayer identity for empty-polymer graphs (tanh form)**. -/
theorem mayer_identity_of_no_polymers_tanh_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_no_polymers_tanh
    (inducedGraph G Λ) h_no β J N

/-- **Λ-layer: Mayer identity under disjunctive trivial conditions**. -/
theorem mayer_identity_of_trivial_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers (inducedGraph G Λ) = ∅) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_trivial (inducedGraph G Λ) h N

/-- **Λ-layer: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayer_identity_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty t N

/-- **Λ-layer: Mayer identity for edgeless induced graphs (tanh form)**. -/
theorem mayer_identity_of_edgeFinset_empty_tanh_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_edgeFinset_empty_tanh
    (inducedGraph G Λ) h_empty β J N

end Ambient

end IsingModel
