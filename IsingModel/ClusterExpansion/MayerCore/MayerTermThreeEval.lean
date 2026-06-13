import IsingModel.ClusterExpansion.MayerCore.Truncations
import IsingModel.ClusterExpansion.UrsellFinThree

/-!
# Closed-form evaluation of the third Mayer term (GJ §18.4)

The explicit value of the `n = 3` Mayer expansion term as a sum over ordered
triples of polymers, with each Ursell coefficient `ϕ^T(![P, Q, R])` replaced by
its closed value from the complete `n = 3` classification
(`ursellCoefficient_fin_three_eq`): `1/3` for a fully-incompatible triangle,
`1/6` for a path-shaped (exactly two incompatible pairs) cluster, and `0`
otherwise.  This is the first explicit *interacting* Mayer term, combining the
ordered-triple form `mayerExpansionTerm_three` (`MayerCore/Truncations.lean`)
with the per-`ω` Ursell classification (`UrsellFinThree.lean`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (Mayer expansion), pp. 378–386.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Closed form of the third Mayer term** (GJ §18.4): the `n = 3` Mayer
expansion term as a sum over ordered triples `(P, Q, R)` of polymers, with the
Ursell coefficient evaluated by incompatibility pattern — `1/3` for the
fully-incompatible triangle, `1/6` for a path (exactly two incompatible pairs),
`0` for the disconnected (`≤ 1` incompatible pair) cases.  Obtained from the
ordered-triple form `mayerExpansionTerm_three` by rewriting each
`ϕ^T(![P, Q, R])` with the unified classification
`ursellCoefficient_fin_three_eq`. -/
theorem mayerExpansionTerm_three_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 3 t =
      ∑ pqr ∈ (allPolymers G) ×ˢ ((allPolymers G) ×ˢ (allPolymers G)),
        (if PolymersIncompatible pqr.1 pqr.2.1 then
          (if PolymersIncompatible pqr.1 pqr.2.2 then
            (if PolymersIncompatible pqr.2.1 pqr.2.2 then 1 / 3 else 1 / 6)
          else
            (if PolymersIncompatible pqr.2.1 pqr.2.2 then 1 / 6 else 0))
        else
          (if PolymersIncompatible pqr.1 pqr.2.2 then
            (if PolymersIncompatible pqr.2.1 pqr.2.2 then 1 / 6 else 0)
          else
            (if PolymersIncompatible pqr.2.1 pqr.2.2 then 0 else 0)))
          * (t ^ pqr.1.card * t ^ pqr.2.1.card * t ^ pqr.2.2.card) := by
  rw [mayerExpansionTerm_three]
  refine Finset.sum_congr rfl (fun pqr _ => ?_)
  rw [ursellCoefficient_fin_three_eq ![pqr.1, pqr.2.1, pqr.2.2]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- **Explicit Mayer truncation through order 3** (GJ §18.4): the partial sum
`mayerPartialSum G 3 t` in fully explicit polymer-sum form — the total polymer
activity `∑_P t^|P|`, the `n = 2` incompatible-pair contribution
`-½·∑_{(P,Q) incompatible} t^|P| t^|Q|`, and the `n = 3` triple contribution
with each Ursell coefficient evaluated by incompatibility pattern.  Composes the
canonical `mayerPartialSum_two` (`PolymerFreeEnergy.lean`) with the evaluated
third term `mayerExpansionTerm_three_eq`. -/
theorem mayerPartialSum_three_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 3 t =
      ((∑ P ∈ allPolymers G, t ^ P.card) +
        (-1 / 2 : ℝ) *
          ∑ pq ∈ ((allPolymers G) ×ˢ (allPolymers G)).filter
              (fun pq => PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card))
      + ∑ pqr ∈ (allPolymers G) ×ˢ ((allPolymers G) ×ˢ (allPolymers G)),
          (if PolymersIncompatible pqr.1 pqr.2.1 then
            (if PolymersIncompatible pqr.1 pqr.2.2 then
              (if PolymersIncompatible pqr.2.1 pqr.2.2 then 1 / 3 else 1 / 6)
            else
              (if PolymersIncompatible pqr.2.1 pqr.2.2 then 1 / 6 else 0))
          else
            (if PolymersIncompatible pqr.1 pqr.2.2 then
              (if PolymersIncompatible pqr.2.1 pqr.2.2 then 1 / 6 else 0)
            else
              (if PolymersIncompatible pqr.2.1 pqr.2.2 then 0 else 0)))
            * (t ^ pqr.1.card * t ^ pqr.2.1.card * t ^ pqr.2.2.card) := by
  rw [mayerPartialSum_three, mayerPartialSum_two, ← mayerExpansionTerm_three,
    mayerExpansionTerm_three_eq]

end IsingModel
