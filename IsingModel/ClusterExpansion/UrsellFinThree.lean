import IsingModel.ClusterExpansion.AlternatingFinThree
import IsingModel.ClusterExpansion.MayerRootComponent

/-!
# The n = 3 Ursell coefficient by incompatibility pattern (GJ §18.4)

The closed-form Ursell coefficient `ϕ^T(ω)` for a 3-element polymer sequence `ω`,
classified by its incompatibility pattern.  When exactly two of the three pairs are
incompatible (a path-shaped incompatibility graph), `ϕ^T(ω) = 1/6`; when all three
are incompatible (triangle), `ϕ^T(ω) = 1/3` (`ursellCoefficient_complete_eq`); when
the graph is disconnected (≤ 1 incompatible pair), `ϕ^T(ω) = 0`
(`ursellCoefficient_eq_zero_of_disconnected`).

The path values use the identity isomorphism `polymerSeqIncompatibilityGraph ω ≃g
fromEdgeSet {path edges}` together with `alternatingConnectedSubgraphSum_iso` and
the path value `alternatingConnectedSubgraphSum_fin_three_path_*` (#3949).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (Mayer expansion), pp. 378–386.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **n = 3 Ursell coefficient, path pattern `0–1–2`**: if exactly the pairs
`(ω 0, ω 1)` and `(ω 1, ω 2)` are incompatible (and `(ω 0, ω 2)` is compatible),
the incompatibility graph is the path `0–1–2`, so `ϕ^T(ω) = 1/6`. -/
theorem ursellCoefficient_fin_three_path_01_12 (ω : Fin 3 → Finset (Sym2 ι))
    (h01 : PolymersIncompatible (ω 0) (ω 1)) (h12 : PolymersIncompatible (ω 1) (ω 2))
    (h02 : ¬ PolymersIncompatible (ω 0) (ω 2)) :
    ursellCoefficient ω = 1 / 6 := by
  have e : polymerSeqIncompatibilityGraph ω ≃g
      SimpleGraph.fromEdgeSet
        (↑({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) :=
    { toEquiv := Equiv.refl (Fin 3)
      map_rel_iff' := by
        have h10 : PolymersIncompatible (ω 1) (ω 0) := h01.symm
        have h21 : PolymersIncompatible (ω 2) (ω 1) := h12.symm
        have h02' : ¬ PolymersIncompatible (ω 2) (ω 0) := fun h => h02 h.symm
        intro i j
        simp only [Equiv.refl_apply, polymerSeqIncompatibilityGraph_adj,
          SimpleGraph.fromEdgeSet_adj, Finset.coe_insert, Finset.coe_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        fin_cases i <;> fin_cases j <;> simp_all }
  rw [ursellCoefficient_eq_alternatingConnectedSubgraphSum_div,
    alternatingConnectedSubgraphSum_iso e,
    alternatingConnectedSubgraphSum_fin_three_path_01_12]
  norm_num

/-- **n = 3 Ursell coefficient, path pattern `1–0–2`**: exactly `(ω 0, ω 1)` and
`(ω 0, ω 2)` incompatible (and `(ω 1, ω 2)` compatible), `ϕ^T(ω) = 1/6`. -/
theorem ursellCoefficient_fin_three_path_01_02 (ω : Fin 3 → Finset (Sym2 ι))
    (h01 : PolymersIncompatible (ω 0) (ω 1)) (h02 : PolymersIncompatible (ω 0) (ω 2))
    (h12 : ¬ PolymersIncompatible (ω 1) (ω 2)) :
    ursellCoefficient ω = 1 / 6 := by
  have e : polymerSeqIncompatibilityGraph ω ≃g
      SimpleGraph.fromEdgeSet
        (↑({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) :=
    { toEquiv := Equiv.refl (Fin 3)
      map_rel_iff' := by
        have h10 : PolymersIncompatible (ω 1) (ω 0) := h01.symm
        have h20 : PolymersIncompatible (ω 2) (ω 0) := h02.symm
        have h12' : ¬ PolymersIncompatible (ω 2) (ω 1) := fun h => h12 h.symm
        intro i j
        simp only [Equiv.refl_apply, polymerSeqIncompatibilityGraph_adj,
          SimpleGraph.fromEdgeSet_adj, Finset.coe_insert, Finset.coe_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        fin_cases i <;> fin_cases j <;> simp_all }
  rw [ursellCoefficient_eq_alternatingConnectedSubgraphSum_div,
    alternatingConnectedSubgraphSum_iso e,
    alternatingConnectedSubgraphSum_fin_three_path_01_02]
  norm_num

/-- **n = 3 Ursell coefficient, path pattern `0–2–1`**: exactly `(ω 0, ω 2)` and
`(ω 1, ω 2)` incompatible (and `(ω 0, ω 1)` compatible), `ϕ^T(ω) = 1/6`. -/
theorem ursellCoefficient_fin_three_path_02_12 (ω : Fin 3 → Finset (Sym2 ι))
    (h02 : PolymersIncompatible (ω 0) (ω 2)) (h12 : PolymersIncompatible (ω 1) (ω 2))
    (h01 : ¬ PolymersIncompatible (ω 0) (ω 1)) :
    ursellCoefficient ω = 1 / 6 := by
  have e : polymerSeqIncompatibilityGraph ω ≃g
      SimpleGraph.fromEdgeSet
        (↑({s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) :=
    { toEquiv := Equiv.refl (Fin 3)
      map_rel_iff' := by
        have h20 : PolymersIncompatible (ω 2) (ω 0) := h02.symm
        have h21 : PolymersIncompatible (ω 2) (ω 1) := h12.symm
        have h01' : ¬ PolymersIncompatible (ω 1) (ω 0) := fun h => h01 h.symm
        intro i j
        simp only [Equiv.refl_apply, polymerSeqIncompatibilityGraph_adj,
          SimpleGraph.fromEdgeSet_adj, Finset.coe_insert, Finset.coe_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        fin_cases i <;> fin_cases j <;> simp_all }
  rw [ursellCoefficient_eq_alternatingConnectedSubgraphSum_div,
    alternatingConnectedSubgraphSum_iso e,
    alternatingConnectedSubgraphSum_fin_three_path_02_12]
  norm_num

end IsingModel
