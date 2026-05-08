import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerTrivialCases

/-!
# Concrete Mayer trivial-case wrappers

Narrow child module for concrete `ℤ^d` `mayerPartialSum 0 ≤ polymerFreeEnergy`
comparisons and Mayer identity wrappers for no-polymer, trivial, and edgeless
cases. This keeps callers that only need these wrappers out of the monolithic
lattice-correlation legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 mayerPartialSum_zero ≤ polymerFreeEnergy ℤ^d wraps -/

/-- **ℤ^d Λ: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_Λ_latticeGraph_le_polymerFreeEnergy
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t :=
  Ambient.mayerPartialSum_zero_Λ_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_latticeGraph_tanh_le_polymerFreeEnergy
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_Λ_latticeGraph_tanh_le_polymerFreeEnergy_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d along-ex: mayerPartialSum 0 ≤ polymerFreeEnergy under
`t ≥ 0`**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_latticeGraph_le_polymerFreeEnergy
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t :=
  Ambient.mayerPartialSum_zero_AlongExhaustion_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_latticeGraph_tanh_le_polymerFreeEnergy
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_latticeGraph_tanh_le_polymerFreeEnergy_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ n

/-! ### §18.5 mayer_identity_of edge-case ℤ^d wraps -/

/-- **ℤ^d Λ: Mayer identity for empty-polymer induced graphs**. -/
theorem mayer_identity_of_no_polymers_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t :=
  Ambient.mayer_identity_of_no_polymers_Λ
    (IsingModel.latticeGraph d) Λ h_no t N

/-- **ℤ^d Λ: Mayer identity for empty-polymer induced graphs (tanh
form)**. -/
theorem mayer_identity_of_no_polymers_tanh_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_no_polymers_tanh_Λ
    (IsingModel.latticeGraph d) Λ h_no β J N

/-- **ℤ^d Λ: Mayer identity under disjunctive trivial conditions**. -/
theorem mayer_identity_of_trivial_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_trivial_Λ
    (IsingModel.latticeGraph d) Λ h N

/-- **ℤ^d Λ: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t :=
  Ambient.mayer_identity_of_edgeFinset_empty_Λ
    (IsingModel.latticeGraph d) Λ h_empty t N

/-- **ℤ^d Λ: Mayer identity for edgeless induced graphs (tanh form)**. -/
theorem mayer_identity_of_edgeFinset_empty_tanh_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_edgeFinset_empty_tanh_Λ
    (IsingModel.latticeGraph d) Λ h_empty β J N

/-- **ℤ^d along-ex: Mayer identity for empty-polymer induced graphs**. -/
theorem mayer_identity_of_no_polymers_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t :=
  Ambient.mayer_identity_of_no_polymers_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h_no t N

/-- **ℤ^d along-ex: Mayer identity for empty-polymer induced graphs
(tanh form)**. -/
theorem mayer_identity_of_no_polymers_tanh_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_no_polymers_tanh_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h_no β J N

/-- **ℤ^d along-ex: Mayer identity under disjunctive trivial
conditions**. -/
theorem mayer_identity_of_trivial_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅)
    (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_trivial_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h N

/-- **ℤ^d along-ex: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t :=
  Ambient.mayer_identity_of_edgeFinset_empty_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h_empty t N

/-- **ℤ^d along-ex: Mayer identity for edgeless induced graphs (tanh
form)**. -/
theorem
mayer_identity_of_edgeFinset_empty_tanh_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_edgeFinset_empty_tanh_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h_empty β J N


end Ambient
end IsingModel
