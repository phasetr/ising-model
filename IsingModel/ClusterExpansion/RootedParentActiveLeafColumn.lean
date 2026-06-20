import IsingModel.ClusterExpansion.PolymerActivityKPMoment

/-!
# The leaf column sum and its Kotecky--Preiss bound (GJ §18.5)

After peeling the leaf coordinate out of `rootedParentActiveSum`, the leaf value `x`
ranges over `allPolymers G` subject to the single constraint `x ∼ P`, where `P` is the
remainder polymer assigned to the leaf's parent.  The resulting inner sum is the
*leaf column sum*

`leafColumnSum G P d t = ∑_{x ∈ allPolymers G, x ∼ P} |x|^d·(e|t|)^{|x|}`.

`leafColumnSum_le` bounds it by the incompatibility-neighbourhood moment estimate
(`incompatibilityActivity_cardPow_expWeighted_le`, #4102): for `P ∈ allPolymers G` and
`Δ²·e·|t| < 1`, `leafColumnSum G P d t ≤ |P|·d!/(1 − Δ²e|t|)^{d+1}`.  The factor `|P|` is exactly the
moment bump that the leaf-peel induction folds into the remainder weight at the
parent vertex.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The leaf column sum.**  The moment-weighted activity of the polymers `x` of `G`
incompatible with a fixed polymer `P`: `∑_{x ∼ P} |x|^d·(e|t|)^{|x|}`.  This is the
inner sum over the leaf value once the leaf coordinate has been peeled out of
`rootedParentActiveSum`. -/
noncomputable def leafColumnSum (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (P : Finset (Sym2 ι)) (d : ℕ) (t : ℝ) : ℝ :=
  ∑ x ∈ allPolymers G,
    if PolymersIncompatible x P then (x.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ x.card else 0

/-- **The leaf column sum equals the incompatibility-neighbourhood moment sum.**  The
constrained sum over `allPolymers G` is the unconstrained sum over the incompatibility
neighbourhood `incompatiblePolymers G P` (using that `PolymersIncompatible` is
symmetric). -/
theorem leafColumnSum_eq (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (P : Finset (Sym2 ι)) (d : ℕ) (t : ℝ) :
    leafColumnSum G P d t
      = ∑ x ∈ incompatiblePolymers G P, (x.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ x.card := by
  rw [leafColumnSum, ← Finset.sum_filter]
  congr 1
  rw [incompatiblePolymers]
  exact Finset.filter_congr fun x _ => ⟨fun h => h.symm, fun h => h.symm⟩

/-- **Kotecky--Preiss bound for the leaf column sum.**  For `P ∈ allPolymers G` and
`Δ²·e·|t| < 1` (`Δ = G.maxDegree`), the leaf column sum is bounded by the
incompatibility-neighbourhood moment estimate `incompatibilityActivity_cardPow_expWeighted_le`:
`leafColumnSum G P d t ≤ |P|·d!/(1 − Δ²e|t|)^{d+1}`.  The factor `|P|` is the moment
bump folded into the remainder weight at the parent vertex. -/
theorem leafColumnSum_le (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) (d : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    leafColumnSum G P d t
      ≤ (P.card : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
  rw [leafColumnSum_eq]
  exact incompatibilityActivity_cardPow_expWeighted_le G hP d hkp

end IsingModel
