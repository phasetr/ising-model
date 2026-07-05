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
`Δ²·e·|t| < 1`, `leafColumnSum G P d t ≤ |P|·d!/(1 − Δ²e|t|)^{d+1}`.  The factor `|P|`
is exactly the moment bump that the leaf-peel induction folds into the remainder weight
at the parent vertex.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The leaf column gas sum.**  The moment-weighted activity of the polymers `x` of the
gas `𝓟` incompatible with a fixed polymer `P`: `∑_{x ∈ 𝓟, x ∼ P} |x|^d·(e|t|)^{|x|}`.
This is the inner sum over the leaf value once the leaf coordinate has been peeled out of
`rootedGasParentActiveSum`.  The even gas (`allPolymers G`) is recovered by
`leafColumnSum`. -/
noncomputable def leafGasColumnSum (𝓟 : Finset (Finset (Sym2 ι))) (P : Finset (Sym2 ι))
    (d : ℕ) (t : ℝ) : ℝ :=
  ∑ x ∈ 𝓟,
    if PolymersIncompatible x P then (x.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ x.card else 0

/-- **The leaf column sum.**  The even-gas (`allPolymers G`) instance of
`leafGasColumnSum`. -/
noncomputable def leafColumnSum (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (P : Finset (Sym2 ι)) (d : ℕ) (t : ℝ) : ℝ :=
  leafGasColumnSum (allPolymers G) P d t

/-- **The leaf column gas sum equals the incompatibility-neighbourhood moment sum.**  The
constrained sum over `𝓟` is the unconstrained sum over the incompatibility neighbourhood
`incompatibleGasPolymers 𝓟 P` (using that `PolymersIncompatible` is symmetric). -/
theorem leafGasColumnSum_eq (𝓟 : Finset (Finset (Sym2 ι))) (P : Finset (Sym2 ι)) (d : ℕ)
    (t : ℝ) :
    leafGasColumnSum 𝓟 P d t
      = ∑ x ∈ incompatibleGasPolymers 𝓟 P, (x.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ x.card := by
  rw [leafGasColumnSum, ← Finset.sum_filter]
  congr 1
  rw [incompatibleGasPolymers]
  exact Finset.filter_congr fun x _ => ⟨fun h => h.symm, fun h => h.symm⟩

/-- **The leaf column sum equals the incompatibility-neighbourhood moment sum.**  Even-gas
instance of `leafGasColumnSum_eq`. -/
theorem leafColumnSum_eq (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (P : Finset (Sym2 ι)) (d : ℕ) (t : ℝ) :
    leafColumnSum G P d t
      = ∑ x ∈ incompatiblePolymers G P, (x.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ x.card :=
  leafGasColumnSum_eq (allPolymers G) P d t

/-- **Kotecky--Preiss bound for the leaf column gas sum.**  For `Δ²·e·|t| < 1`
(`Δ = G.maxDegree`), a support-cardinality bound `|supp P| ≤ c·|P|` for the parent polymer
`P`, and `0 ≤ c`, the leaf column gas sum is bounded by the incompatibility-neighbourhood
moment estimate `incompatibilityGasActivity_cardPow_expWeighted_le` followed by the support
bound: `leafGasColumnSum 𝓟 P d t ≤ c·|P|·d!/(1 − Δ²e|t|)^{d+1}`.  The factor `c·|P|` is the
moment bump (in `.card` form) folded into the remainder weight at the parent vertex; the
even gas takes `c = 1`. -/
theorem leafGasColumnSum_le (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) (P : Finset (Sym2 ι)) (d : ℕ)
    {c : ℝ} (hsupp : ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    leafGasColumnSum 𝓟 P d t
      ≤ c * (P.card : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
  rw [leafGasColumnSum_eq]
  refine (incompatibilityGasActivity_cardPow_expWeighted_le G hgas P d hkp).trans ?_
  have hpos : (0 : ℝ) < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) := by linarith
  exact mul_le_mul_of_nonneg_right hsupp
    (div_nonneg (by positivity) (le_of_lt (pow_pos hpos (d + 1))))

/-- **Kotecky--Preiss bound for the leaf column sum.**  For `P ∈ allPolymers G` and
`Δ²·e·|t| < 1` (`Δ = G.maxDegree`), the leaf column sum is bounded by
`leafColumnSum G P d t ≤ |P|·d!/(1 − Δ²e|t|)^{d+1}`.  Even-gas (`c = 1`) instance of
`leafGasColumnSum_le`, discharging the support bound via
`polymerSupport_card_le_card_of_mem_allPolymers`. -/
theorem leafColumnSum_le (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) (d : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    leafColumnSum G P d t
      ≤ (P.card : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
  have hsupp : ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  simpa using leafGasColumnSum_le G (evenPolymerGasData G) P d hsupp hkp

end IsingModel
