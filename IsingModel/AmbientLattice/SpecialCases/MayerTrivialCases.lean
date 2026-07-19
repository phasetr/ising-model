import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer trivial-case wrappers along an exhaustion

Narrow child module for along-exhaustion `mayerPartialSum 0 ≤ polymerFreeEnergy`
comparisons and Mayer identity wrappers for no-polymer, trivial, and edgeless
cases. This keeps callers that only need these forwarders out of the
monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 mayerPartialSum_zero ≤ polymerFreeEnergy along-ex wraps -/

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

/-! ### §18.5 mayer_identity_of edge-case along-ex wraps -/

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
