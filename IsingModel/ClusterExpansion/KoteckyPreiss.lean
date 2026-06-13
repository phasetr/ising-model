import IsingModel.ClusterExpansion.MayerCore.Terms
import IsingModel.ClusterExpansion.Incompatibility

/-!
# The Kotecký–Preiss criterion (GJ §18.4–18.5)

Toward the convergence of the general (interacting) cluster expansion
(Issue #3954): the **Kotecký–Preiss criterion**.  A non-negative weight
function `a` on polymers is *KP-admissible* for an activity `z` if, for every
polymer `P`,
`∑_{Q ≁ P} |z Q| · exp(a Q) ≤ a P`,
the sum ranging over polymers `Q` incompatible with `P` (including `P` itself,
since a nonempty polymer is self-incompatible).  This single inequality is the
standard sufficient condition for the absolute convergence of the cluster
expansion (`log Ξ = ∑ cluster terms`), via the per-polymer cluster-sum bound
`∑_{Γ ∋ P} |ϕ^T(Γ)| ∏|z| ≤ a P`.

This file states the criterion and proves its elementary structural
consequences — `a` is automatically non-negative on polymers, and each
activity is dominated by its weight (`|z P| ≤ a P`).  The full convergence
theorem (the per-polymer cluster-sum bound, which consumes the tree-graph
inequality from `TreeGraphBound.lean`) remains for a later PR of #3954.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
* R. Kotecký, D. Preiss, *Cluster expansion for abstract polymer models*,
  Comm. Math. Phys. 103 (1986), 491–498.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Kotecký–Preiss criterion**: a weight `a : polymers → ℝ` is *admissible*
for the activity `z` on the graph `G` if, for every polymer `P` of `G`,
`∑_{Q ≁ P} |z Q| · exp(a Q) ≤ a P` (the sum over polymers `Q` of `G`
incompatible with `P`).  The standard sufficient condition for absolute
convergence of the cluster expansion. -/
def KPAdmissible (G : SimpleGraph ι) [Fintype G.edgeSet]
    (z a : Finset (Sym2 ι) → ℝ) : Prop :=
  ∀ P ∈ allPolymers G,
    ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
      |z Q| * Real.exp (a Q) ≤ a P

/-- **KP weights are non-negative on polymers**: if `a` is KP-admissible then
`0 ≤ a P` for every polymer `P`, since `a P` dominates a sum of non-negative
terms `|z Q| · exp(a Q) ≥ 0`. -/
theorem KPAdmissible.weight_nonneg
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    0 ≤ a P := by
  refine le_trans (Finset.sum_nonneg (fun Q _ => ?_)) (h P hP)
  positivity

/-- **KP dominates the activity**: if `a` is KP-admissible then `|z P| ≤ a P`
for every polymer `P`.  The self-incompatibility of a nonempty polymer
(`PolymersIncompatible.self_of_isPolymer`) puts `P` itself into the KP sum, so
`|z P| · exp(a P)` is one of its terms; with `0 ≤ a P` (hence `1 ≤ exp(a P)`)
this gives `|z P| ≤ |z P| · exp(a P) ≤ a P`. -/
theorem KPAdmissible.activity_le_weight
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    |z P| ≤ a P := by
  have hPmem : P ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q) := by
    rw [Finset.mem_filter]
    exact ⟨hP, PolymersIncompatible.self_of_isPolymer (mem_allPolymers.mp hP)⟩
  have hterm : |z P| * Real.exp (a P)
      ≤ ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
          |z Q| * Real.exp (a Q) :=
    Finset.single_le_sum (f := fun Q => |z Q| * Real.exp (a Q))
      (fun Q _ => by positivity) hPmem
  have hself : |z P| ≤ |z P| * Real.exp (a P) := by
    have h1 : (1 : ℝ) ≤ Real.exp (a P) := by
      calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
        _ ≤ Real.exp (a P) := Real.exp_le_exp.mpr (h.weight_nonneg hP)
    nlinarith [abs_nonneg (z P)]
  exact le_trans hself (le_trans hterm (h P hP))

/-- **KP admissibility is monotone in the activity**: if `a` is KP-admissible
for `z` and `|z' Q| ≤ |z Q|` for every polymer `Q`, then `a` is KP-admissible
for `z'` too.  Lets one verify the criterion for a concrete activity by
dominating it with a simpler one.  (Used to deduce KP for the Ising activity
`tanh(βJ)^{|P|}` from a clean majorant.) -/
theorem KPAdmissible.mono_activity
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z z' a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a)
    (hz : ∀ Q ∈ allPolymers G, |z' Q| ≤ |z Q|) :
    KPAdmissible G z' a := by
  intro P hP
  refine le_trans (Finset.sum_le_sum (fun Q hQ => ?_)) (h P hP)
  have hQmem : Q ∈ allPolymers G := (Finset.mem_filter.mp hQ).1
  exact mul_le_mul_of_nonneg_right (hz Q hQmem) (Real.exp_nonneg _)

/-- **KP bounds the bare activity sum**: if `a` is KP-admissible then, dropping
the exponential factors `exp(a Q) ≥ 1`, the bare incompatible-activity sum is
still bounded, `∑_{Q ≁ P} |z Q| ≤ a P`.  The summable form most directly used in
convergence estimates. -/
theorem KPAdmissible.activity_sum_le_weight
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q), |z Q| ≤ a P := by
  refine le_trans (Finset.sum_le_sum (fun Q hQ => ?_)) (h P hP)
  have hQmem : Q ∈ allPolymers G := (Finset.mem_filter.mp hQ).1
  have h1 : (1 : ℝ) ≤ Real.exp (a Q) := by
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (a Q) := Real.exp_le_exp.mpr (h.weight_nonneg hQmem)
  calc |z Q| = |z Q| * 1 := (mul_one _).symm
    _ ≤ |z Q| * Real.exp (a Q) := by gcongr

/-- **Order-2 cluster contribution bound** (KP, GJ §18.4): the order-2 part of
the cluster sum anchored at `P` — `∑_{Q ≁ P} |ϕ^T(![P,Q])| · |z P|·|z Q|` — is
bounded by `½ · |z P| · a P`.  Each connected `2`-cluster `{P, Q}` (with `P ≁ Q`)
has `ϕ^T = -1/2` (`ursellCoefficient_pair_incompatible`), so the sum factors as
`½·|z P|·∑_{Q ≁ P} |z Q|`, then `KPAdmissible.activity_sum_le_weight` bounds the
inner sum by `a P`.  A concrete instance of the per-polymer cluster-sum bound
that drives Kotecký–Preiss convergence (here at fixed order `n = 2`). -/
theorem KPAdmissible.order_two_cluster_bound
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
        |ursellCoefficient ![P, Q]| * (|z P| * |z Q|)
      ≤ (1 / 2) * (|z P| * a P) := by
  have hcongr : ∀ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
      |ursellCoefficient ![P, Q]| * (|z P| * |z Q|)
        = (1 / 2) * |z P| * |z Q| := by
    intro Q hQ
    have hPQ : PolymersIncompatible P Q := (Finset.mem_filter.mp hQ).2
    have hu : ursellCoefficient ![P, Q] = -1 / 2 :=
      ursellCoefficient_pair_incompatible (by simpa using hPQ)
    rw [hu]
    have habs : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [habs]; ring
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
  calc (1 / 2 * |z P|)
        * ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q), |z Q|
      ≤ (1 / 2 * |z P|) * a P :=
        mul_le_mul_of_nonneg_left (h.activity_sum_le_weight hP) (by positivity)
    _ = (1 / 2) * (|z P| * a P) := by ring

end IsingModel
