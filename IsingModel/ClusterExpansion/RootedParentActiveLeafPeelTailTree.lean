import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelTailInduction
import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelTree

/-!
# The sharpened (tail) leaf-peel bound for the complete-graph tree code (GJ §18.5)

Specialising the tail leaf-peel induction bound
(`rootedParentActiveSum_le_pow_mul_childCount_bound`, #4129) to the full active set
`Finset.univ` (of cardinality `n`) and the complete-graph spanning-tree parent code gives
the tail tree bound

`rootedParentActiveSum G (parentCode T) univ _ (fun _ => 0) t ≤ (Δ²e|t|)^n·peelBound`.

* `rootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The sharpened (tail) leaf-peel bound for the complete-graph spanning-tree parent
code (gas form).**  For the full active set (cardinality `n`) and the parent code of a
spanning tree `T` of the complete graph on `Fin (n + 1)`, with `Δ²e|t| < 1`, a
support-cardinality bound `|supp P| ≤ c·|P|` for all `P ∈ 𝓟`, and `0 ≤ c`, the rooted-tree
active gas sum at exponent `0` is bounded by `(Δ²e|t|)^n` times the child-count gas peel
bound.  The leaf existence is discharged by `completeGraphTreeParentCode_exists_active_leaf`.
The even gas (`allPolymers G`) takes `c = 1` in
`rootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound`. -/
theorem rootedGasParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) (n : ℕ)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) {c : ℝ}
    (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) (hc : 0 ≤ c) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedGasParentActiveSum G 𝓟 (Penrose.completeGraphTreeParentCode n T)
        (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T))
        (fun _ => 0) t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * rootedGasParentActivePeelBound G 𝓟 c (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
  have h := rootedGasParentActiveSum_le_pow_mul_childCount_bound G hgas
    (fun hB => completeGraphTreeParentCode_exists_active_leaf hB T)
    (Finset.univ : Finset (Fin n))
    (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T)) (fun _ => 0)
    hsupp hc hkp
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- **The sharpened (tail) leaf-peel bound for the complete-graph spanning-tree parent
code.**  Even-gas (`allPolymers G`, `c = 1`) instance of
`rootedGasParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound`,
discharging the support bound via `polymerSupport_card_le_card_of_mem_allPolymers`. -/
theorem rootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (n : ℕ)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedParentActiveSum G (Penrose.completeGraphTreeParentCode n T)
        (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T))
        (fun _ => 0) t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
  have hsupp : ∀ P ∈ allPolymers G, ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    intro P hP; rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  exact rootedGasParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound G
    (evenPolymerGasData G) n T hsupp zero_le_one hkp

end IsingModel
