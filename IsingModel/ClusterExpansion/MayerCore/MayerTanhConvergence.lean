import IsingModel.ClusterExpansion.MayerCore.UrsellMajorant
import IsingModel.ClusterExpansion.MayerCore.ZeroBounds
import Mathlib.Analysis.Complex.Trigonometric

/-!
# High-temperature convergence of the Ising cluster expansion (GJ §18.4-18.5)

The Mayer expansion of the Ising model has activity `t = tanh(β·J)`.  Specialising
the abstract absolute convergence `summable_mayerExpansionTerm_*`
(`UrsellMajorant.lean`) to `t = tanh(β·J)` gives the high-temperature convergence
of the Ising cluster expansion: since `tanh` is continuous with `tanh 0 = 0`, the
activity is small at high temperature (`β·J` near `0`), so the convergence
criterion `e · |allPolymers G| · |tanh(β·J)| < 1` holds.

The remaining M2 step (Issue #1499 Phase C) is the Mayer–Montroll identity
`log Ξ = ∑ₙ mayerExpansionTerm`; together with this convergence it expresses the
Ising free energy through its convergent cluster expansion.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (p. 332) – §18.5 (p. 335).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **High-temperature convergence of the Ising Mayer expansion**:
`Summable (fun n => mayerExpansionTerm G n (tanh(β·J)))` whenever
`e · |allPolymers G| · |tanh(β·J)| < 1`.  Since `|tanh| < 1`, the activity bound
`summable_mayerExpansionTerm_of_card_mul_lt` applies. -/
theorem summable_mayerExpansionTerm_tanh
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (h : Real.exp 1 * ((allPolymers G).card * |Real.tanh (β * J)|) < 1) :
    Summable (fun n : ℕ => mayerExpansionTerm G n (Real.tanh (β * J))) :=
  summable_mayerExpansionTerm_of_card_mul_lt G (Real.abs_tanh_lt_one _).le h

omit [Fintype ι] in
/-- **Polymer-activity sum at `tanh(β·J)` (ferromagnetic)**: for `0 ≤ β·J`,
`∑_{P ∈ allPolymers G} tanh(β·J)^{|P|} ≤ |allPolymers G| · tanh(β·J)`, since
`0 ≤ tanh(β·J) ≤ 1` and every polymer has `|P| ≥ 1`. -/
theorem tanh_activity_sum_le_card_mul_tanh
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card)
      ≤ (allPolymers G).card * Real.tanh (β * J) := by
  have habs : |Real.tanh (β * J)| = Real.tanh (β * J) := abs_of_nonneg (real_tanh_nonneg hβJ)
  have hkey := activity_sum_le_card_mul_abs (G := G) (Real.abs_tanh_lt_one (β * J)).le
  simpa [habs] using hkey

/-- **High-temperature convergence (ferromagnetic form)**:
for `0 ≤ β·J`, `Summable (fun n => mayerExpansionTerm G n (tanh(β·J)))` whenever
`e · |allPolymers G| · tanh(β·J) < 1`.  This is the high-temperature regime of the
ferromagnetic Ising model (`tanh(β·J) → 0` as `β·J → 0`). -/
theorem summable_mayerExpansionTerm_tanh_ferro
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h : Real.exp 1 * ((allPolymers G).card * Real.tanh (β * J)) < 1) :
    Summable (fun n : ℕ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  refine summable_mayerExpansionTerm_tanh G ?_
  rwa [abs_of_nonneg (real_tanh_nonneg hβJ)]

/-- **High-temperature convergence (activity-sum form)**:
`Summable (fun n => mayerExpansionTerm G n (tanh(β·J)))` whenever
`e · (∑_{P ∈ allPolymers G} |tanh(β·J)|^{|P|}) < 1`. -/
theorem summable_mayerExpansionTerm_tanh_of_activity
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (h : Real.exp 1 * (∑ P ∈ allPolymers G, |Real.tanh (β * J)| ^ P.card) < 1) :
    Summable (fun n : ℕ => mayerExpansionTerm G n (Real.tanh (β * J))) :=
  summable_mayerExpansionTerm_of_exp_one_mul_activity_lt_one G h

end IsingModel
