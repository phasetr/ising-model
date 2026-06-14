import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Kotecký–Preiss criterion (GJ §18.4–18.5)

The convergence criterion for the polymer cluster expansion of Glimm–Jaffe
§18.4–18.5 (equivalently Friedli–Velenik §5.7).  For a finite polymer type `P`
with a decidable incompatibility relation `Incompat` and a real activity `z`, a
weight function `a : P → ℝ` is *Kotecký–Preiss admissible* when

`∀ p, ∑_{q ∼ p} |z q| · exp (a q) ≤ a p`,

where the sum runs over the incompatibility neighbourhood of `p`.  This file
records the criterion together with its **unconditional** structural
consequences — non-negativity of the weight, domination of the activity, and the
weighted-sum master inequality `weighted_le` that absorbs a per-polymer
quantity bounded by `exp ∘ a` into `a p`.  These are the algebraic ingredients of
the all-order convergence argument; everything here is proved without any
auxiliary hypothesis.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
* Kotecký–Preiss, *Cluster expansion for abstract polymer models*,
  Comm. Math. Phys. 103 (1986), 491–498.
-/

namespace IsingModel.ClusterExpansion

open Finset

variable {P : Type*} [Fintype P]

/-- **Incompatibility neighbourhood** of a polymer `p`: the polymers `q` that are
incompatible with `p`, as a `Finset`. -/
def incompatNbhd (Incompat : P → P → Prop) [DecidableRel Incompat] (p : P) : Finset P :=
  Finset.univ.filter (fun q => Incompat p q)

/-- **Membership in the incompatibility neighbourhood**: `q ∈ incompatNbhd p` iff
`Incompat p q`. -/
theorem mem_incompatNbhd {Incompat : P → P → Prop} [DecidableRel Incompat] {p q : P} :
    q ∈ incompatNbhd Incompat p ↔ Incompat p q := by
  simp [incompatNbhd]

/-- **Kotecký–Preiss admissibility**: the weight `a` controls the activity `z`
through `∀ p, ∑_{q ∼ p} |z q| · exp (a q) ≤ a p`. -/
def KPAdmissible (Incompat : P → P → Prop) [DecidableRel Incompat] (z a : P → ℝ) : Prop :=
  ∀ p : P, ∑ q ∈ incompatNbhd Incompat p, |z q| * Real.exp (a q) ≤ a p

variable {Incompat : P → P → Prop} [DecidableRel Incompat] {z a : P → ℝ}

/-- **KP weights are non-negative**: `0 ≤ a p`, since `a p` dominates a sum of
non-negative terms `|z q| · exp (a q)`. -/
theorem KPAdmissible.weight_nonneg (h : KPAdmissible Incompat z a) (p : P) :
    0 ≤ a p := by
  refine le_trans (Finset.sum_nonneg (fun q _ => ?_)) (h p)
  positivity

/-- **Weighted-sum master inequality**: for any `g` with `g q ≤ exp (a q)`
pointwise, `∑_{q ∼ p} |z q| · g q ≤ a p`.  This is the step that absorbs a
per-polymer quantity (later, the cluster sum rooted at `q`, bounded by `exp (a q)`)
into the weight `a p`. -/
theorem KPAdmissible.weighted_le (h : KPAdmissible Incompat z a) (p : P)
    {g : P → ℝ} (hg : ∀ q, g q ≤ Real.exp (a q)) :
    ∑ q ∈ incompatNbhd Incompat p, |z q| * g q ≤ a p := by
  refine le_trans (Finset.sum_le_sum (fun q _ => ?_)) (h p)
  exact mul_le_mul_of_nonneg_left (hg q) (abs_nonneg _)

/-- **KP dominates the activity**: if every polymer is self-incompatible
(`hself : ∀ p, Incompat p p`) then `|z p| ≤ a p`.  Self-incompatibility puts `p`
itself into its KP sum, and `1 ≤ exp (a p)` (from `0 ≤ a p`) finishes. -/
theorem KPAdmissible.activity_le_weight (h : KPAdmissible Incompat z a)
    (hself : ∀ p, Incompat p p) (p : P) :
    |z p| ≤ a p := by
  have hpmem : p ∈ incompatNbhd Incompat p := mem_incompatNbhd.mpr (hself p)
  have hterm : |z p| * Real.exp (a p)
      ≤ ∑ q ∈ incompatNbhd Incompat p, |z q| * Real.exp (a q) :=
    Finset.single_le_sum (f := fun q => |z q| * Real.exp (a q))
      (fun q _ => by positivity) hpmem
  have h1 : (1 : ℝ) ≤ Real.exp (a p) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (h.weight_nonneg p)
  have hself' : |z p| ≤ |z p| * Real.exp (a p) := by
    nlinarith [abs_nonneg (z p)]
  exact le_trans hself' (le_trans hterm (h p))

/-- **Monotonicity in the activity**: if `|z' q| ≤ |z q|` pointwise and `a` is
KP-admissible for `z`, then `a` is KP-admissible for `z'`. -/
theorem KPAdmissible.mono_activity (h : KPAdmissible Incompat z a) {z' : P → ℝ}
    (hz : ∀ q, |z' q| ≤ |z q|) : KPAdmissible Incompat z' a := by
  intro p
  refine le_trans (Finset.sum_le_sum (fun q _ => ?_)) (h p)
  exact mul_le_mul_of_nonneg_right (hz q) (Real.exp_nonneg _)

/-- **Activity sum bound** (`g = 1`): `∑_{q ∼ p} |z q| ≤ a p`. -/
theorem KPAdmissible.activity_sum_le (h : KPAdmissible Incompat z a) (p : P) :
    ∑ q ∈ incompatNbhd Incompat p, |z q| ≤ a p := by
  have hle := h.weighted_le p (g := fun _ => (1 : ℝ))
    (fun q => by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (h.weight_nonneg q))
  simpa using hle

/-- **Activity·weight sum bound** (`g = a`, using `a q ≤ exp (a q)`):
`∑_{q ∼ p} |z q| · a q ≤ a p`. -/
theorem KPAdmissible.activity_weight_sum_le (h : KPAdmissible Incompat z a) (p : P) :
    ∑ q ∈ incompatNbhd Incompat p, |z q| * a q ≤ a p :=
  h.weighted_le p (fun q => le_trans (le_add_of_nonneg_right zero_le_one)
    (Real.add_one_le_exp (a q)))

end IsingModel.ClusterExpansion
