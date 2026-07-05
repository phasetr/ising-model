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

/-- **Sharpened (tail) Kotecky--Preiss bound for the leaf column gas sum.**  For
`Δ²e|t| < 1`, a support-cardinality bound `|supp P| ≤ c·|P|`, and `0 ≤ c`, the leaf
column gas sum carries an extra factor `Δ²e|t|` over `leafGasColumnSum_le`:
`leafGasColumnSum 𝓟 P d t ≤ c·|P|·(Δ²e|t|)·d!/(1−Δ²e|t|)^{d+1}`.  This is
`leafGasColumnSum_eq` followed by the tail incompatibility-neighbourhood moment bound
`incompatibilityGasActivity_cardPow_expWeighted_tail_le` and the support bound; the even
gas takes `c = 1`. -/
theorem leafGasColumnSum_tail_le (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) (P : Finset (Sym2 ι)) (d : ℕ)
    {c : ℝ} (hsupp : ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    leafGasColumnSum 𝓟 P d t
      ≤ c * (P.card : ℝ)
          * (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            * ((d.factorial : ℝ)
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1))) := by
  rw [leafGasColumnSum_eq]
  refine (incompatibilityGasActivity_cardPow_expWeighted_tail_le G hgas P d hkp).trans ?_
  have hpos : (0 : ℝ) < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) := by linarith
  exact mul_le_mul_of_nonneg_right hsupp
    (mul_nonneg (by positivity)
      (div_nonneg (by positivity) (le_of_lt (pow_pos hpos (d + 1)))))

/-- **Sharpened (tail) Kotecky--Preiss bound for the leaf column sum.**  For
`P ∈ allPolymers G` and `Δ²e|t| < 1`, the leaf column sum carries an extra factor
`Δ²e|t|` over `leafColumnSum_le`:
`leafColumnSum G P d t ≤ |P|·(Δ²e|t|)·d!/(1−Δ²e|t|)^{d+1}`.  Even-gas (`c = 1`) instance
of `leafGasColumnSum_tail_le`. -/
theorem leafColumnSum_tail_le (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) (d : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    leafColumnSum G P d t
      ≤ (P.card : ℝ)
          * (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            * ((d.factorial : ℝ)
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1))) := by
  have hsupp : ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  simpa using leafGasColumnSum_tail_le G (evenPolymerGasData G) P d hsupp hkp

end IsingModel
