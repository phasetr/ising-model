import IsingModel.ClusterExpansion.RootedParentActiveLeafColumn
import IsingModel.ClusterExpansion.PolymerActivityKPMomentTail

/-!
# Sharpened (tail) Kotecky--Preiss bound for the leaf column sum (GJ §18.5)

The leaf column sum bound (`leafColumnSum_le`, #4110) is
`leafColumnSum G P d t ≤ |P|·d!/(1−Δ²e|t|)^{d+1}`.  Using the tail-sharpened
incompatibility-neighbourhood moment bound (`incompatibilityActivity_cardPow_expWeighted_tail_le`,
#4122) instead carries an extra factor `Δ²e|t|`:

`leafColumnSum G P d t ≤ |P|·(Δ²e|t|)·d!/(1−Δ²e|t|)^{d+1}`.

* `leafColumnSum_tail_le`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Sharpened (tail) Kotecky--Preiss bound for the leaf column sum.**  For
`P ∈ allPolymers G` and `Δ²e|t| < 1`, the leaf column sum carries an extra factor
`Δ²e|t|` over `leafColumnSum_le`:
`leafColumnSum G P d t ≤ |P|·(Δ²e|t|)·d!/(1−Δ²e|t|)^{d+1}`.  This is `leafColumnSum_eq`
followed by the tail incompatibility-neighbourhood moment bound #4122. -/
theorem leafColumnSum_tail_le (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) (d : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    leafColumnSum G P d t
      ≤ (P.card : ℝ)
          * (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            * ((d.factorial : ℝ)
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1))) := by
  rw [leafColumnSum_eq]
  exact incompatibilityActivity_cardPow_expWeighted_tail_le G hP d hkp

end IsingModel
