import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Order-zero comparison and the Mayer identity on trivial stage subgraphs

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

The Mayer partial sum of the stage subgraph at truncation order `0` is at most
`IsingModel.polymerFreeEnergy` of that subgraph: for an activity `t` with `0 ≤ t`; for the
activity `Real.tanh (β * J)` under `0 ≤ β * J`; and for that activity again under `0 ≤ J`
together with `0 < β`.

The identity `IsingModel.polymerFreeEnergy = IsingModel.mayerPartialSum`, at every
truncation order `N`, is recorded in these degenerate situations: on a subgraph with no
polymer and on one with an empty edge finset, each at a general activity `t` and again at
`Real.tanh (β * J)`; and, at that activity, under the disjunction `β * J = 0` or no polymer.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_AlongExhaustion_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0 t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t :=
  mayerPartialSum_zero_Λ_le_polymerFreeEnergy G (Λ.volume n) ht

/-- **Along-ex: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) :=
  mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy G (Λ.volume n) hβJ

/-- **Along-ex: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) :=
  mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    G (Λ.volume n) hJ hβ

/-- **Along-ex: Mayer identity for empty-polymer induced graphs**. -/
theorem mayer_identity_of_no_polymers_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N t :=
  mayer_identity_of_no_polymers_Λ G (Λ.volume n) h_no t N

/-- **Along-ex: Mayer identity for empty-polymer induced graphs
(tanh form)**. -/
theorem mayer_identity_of_no_polymers_tanh_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_no_polymers_tanh_Λ G (Λ.volume n) h_no β J N

/-- **Along-ex: Mayer identity under disjunctive trivial conditions**. -/
theorem mayer_identity_of_trivial_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers
        (inducedGraph G (Λ.volume n)) = ∅) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_trivial_Λ G (Λ.volume n) h N

/-- **Along-ex: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N t :=
  mayer_identity_of_edgeFinset_empty_Λ G (Λ.volume n) h_empty t N

/-- **Along-ex: Mayer identity for edgeless induced graphs (tanh
form)**. -/
theorem mayer_identity_of_edgeFinset_empty_tanh_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_edgeFinset_empty_tanh_Λ
    G (Λ.volume n) h_empty β J N

end Ambient
end IsingModel
