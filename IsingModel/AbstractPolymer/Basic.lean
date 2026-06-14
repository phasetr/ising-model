import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Abstract polymer models and the Kotecký–Preiss criterion (GJ §18.4–18.5)

A clean, Ising-independent abstraction for the cluster expansion of a finite
polymer gas (Issue #3954), replacing the earlier Ising-edge-set-coupled
scaffolding.  A *polymer model* is a finite type `P` of polymers with a
symmetric decidable *incompatibility* relation and a real *activity* `z`.

The **Kotecký–Preiss criterion** `KPAdmissible` — a weight `a : P → ℝ` with
`∑_{q ≁ p} |z q|·exp(a q) ≤ a p` for every polymer `p` — is the standard
sufficient condition for absolute convergence of the cluster expansion.  This
file fixes the abstraction and proves the criterion's elementary structural
consequences (`weight_nonneg`, `activity_le_weight`).  The all-order convergence
theorem (the per-polymer cluster-sum bound) is built on this foundation in
subsequent work; the Ising adapter (polymers as edge sets, support-disjoint
compatibility, `tanh(βJ)^|P|` activity) is added only after the theorem.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
* R. Kotecký, D. Preiss, *Cluster expansion for abstract polymer models*,
  Comm. Math. Phys. 103 (1986), 491–498.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
-/

namespace IsingModel.AbstractPolymer

open Finset

variable {P : Type*} [Fintype P]

/-- **Incompatible neighbourhood**: the polymers `q` incompatible with `p`
(under the incompatibility relation `Incompat`). -/
def incompatNbhd (Incompat : P → P → Prop) [DecidableRel Incompat] (p : P) : Finset P :=
  Finset.univ.filter (fun q => Incompat p q)

/-- Membership in the incompatible neighbourhood. -/
@[simp] theorem mem_incompatNbhd {Incompat : P → P → Prop} [DecidableRel Incompat]
    {p q : P} : q ∈ incompatNbhd Incompat p ↔ Incompat p q := by
  simp [incompatNbhd]

/-- **Kotecký–Preiss criterion**: a weight `a : P → ℝ` is *admissible* for the
activity `z` if, for every polymer `p`,
`∑_{q ≁ p} |z q| · exp(a q) ≤ a p` (the sum over polymers `q` incompatible with
`p`).  The standard sufficient condition for absolute convergence of the cluster
expansion of the polymer model `(Incompat, z)`. -/
def KPAdmissible (Incompat : P → P → Prop) [DecidableRel Incompat]
    (z a : P → ℝ) : Prop :=
  ∀ p : P, ∑ q ∈ incompatNbhd Incompat p, |z q| * Real.exp (a q) ≤ a p

variable {Incompat : P → P → Prop} [DecidableRel Incompat] {z a : P → ℝ}

/-- **KP weights are non-negative**: if `a` is KP-admissible then `0 ≤ a p` for
every polymer `p`, since `a p` dominates a sum of non-negative terms
`|z q|·exp(a q) ≥ 0`. -/
theorem KPAdmissible.weight_nonneg (h : KPAdmissible Incompat z a) (p : P) :
    0 ≤ a p := by
  refine le_trans (Finset.sum_nonneg (fun q _ => ?_)) (h p)
  positivity

/-- **KP dominates the activity**: if `a` is KP-admissible and every polymer is
self-incompatible (`hself : Incompat p p`), then `|z p| ≤ a p`.  Self-incompatibility
puts `p` itself into its KP sum, so `|z p|·exp(a p)` is one of the terms; with
`0 ≤ a p` (hence `1 ≤ exp(a p)`) this gives `|z p| ≤ |z p|·exp(a p) ≤ a p`. -/
theorem KPAdmissible.activity_le_weight (h : KPAdmissible Incompat z a)
    (hself : ∀ p, Incompat p p) (p : P) :
    |z p| ≤ a p := by
  have hpmem : p ∈ incompatNbhd Incompat p := mem_incompatNbhd.mpr (hself p)
  have hterm : |z p| * Real.exp (a p)
      ≤ ∑ q ∈ incompatNbhd Incompat p, |z q| * Real.exp (a q) :=
    Finset.single_le_sum (f := fun q => |z q| * Real.exp (a q))
      (fun q _ => by positivity) hpmem
  have hself' : |z p| ≤ |z p| * Real.exp (a p) := by
    have h1 : (1 : ℝ) ≤ Real.exp (a p) := by
      calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
        _ ≤ Real.exp (a p) := Real.exp_le_exp.mpr (h.weight_nonneg p)
    nlinarith [abs_nonneg (z p)]
  exact le_trans hself' (le_trans hterm (h p))

/-- **KP admissibility is monotone in the activity**: if `a` is KP-admissible for
`z` and `|z' q| ≤ |z q|` for every polymer `q`, then `a` is KP-admissible for
`z'`.  Lets one verify the criterion for a concrete activity by dominating it
with a simpler majorant. -/
theorem KPAdmissible.mono_activity (h : KPAdmissible Incompat z a)
    {z' : P → ℝ} (hz : ∀ q, |z' q| ≤ |z q|) :
    KPAdmissible Incompat z' a := by
  intro p
  refine le_trans (Finset.sum_le_sum (fun q _ => ?_)) (h p)
  exact mul_le_mul_of_nonneg_right (hz q) (Real.exp_nonneg _)

end IsingModel.AbstractPolymer
