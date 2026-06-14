import IsingModel.ClusterExpansion.MayerCore.Terms
import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.UrsellFinThree

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

/-- **Order-3 triangle cluster contribution bound** (KP, GJ §18.4): the
order-3, fully-incompatible ("triangle") part of the cluster sum anchored at `P`
is bounded by `⅓ · |z P| · (a P)²`.  Each such 3-cluster `{P, Q, R}` with all
three pairs incompatible has `ϕ^T = 1/3` (`ursellCoefficient_fin_three_triangle`);
dropping the `Q ≁ R` constraint enlarges the index set to the product
`{Q ≁ P} × {R ≁ P}`, and `KPAdmissible.activity_sum_le_weight` bounds each factor
`∑_{Q ≁ P} |z Q|` by `a P`.  A second concrete instance (order 3, triangle case)
of the per-polymer cluster-sum bound underlying Kotecký–Preiss convergence. -/
theorem KPAdmissible.order_three_triangle_cluster_bound
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
        ∑ R ∈ ((allPolymers G).filter (fun Q => PolymersIncompatible P Q)).filter
            (fun R => PolymersIncompatible Q R),
          |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
      ≤ (1 / 3) * (|z P| * a P ^ 2) := by
  set A := (allPolymers G).filter (fun Q => PolymersIncompatible P Q) with hA
  have hzP : (0 : ℝ) ≤ |z P| := abs_nonneg _
  have haP : (0 : ℝ) ≤ a P := h.weight_nonneg hP
  calc ∑ Q ∈ A, ∑ R ∈ A.filter (fun R => PolymersIncompatible Q R),
          |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
      = ∑ Q ∈ A, ∑ R ∈ A.filter (fun R => PolymersIncompatible Q R),
          (1 / 3) * (|z P| * |z Q| * |z R|) := by
        refine Finset.sum_congr rfl (fun Q hQ => Finset.sum_congr rfl (fun R hR => ?_))
        have hPQ : PolymersIncompatible P Q := (Finset.mem_filter.mp hQ).2
        have hRA : R ∈ A := (Finset.mem_filter.mp hR).1
        have hPR : PolymersIncompatible P R := (Finset.mem_filter.mp hRA).2
        have hQR : PolymersIncompatible Q R := (Finset.mem_filter.mp hR).2
        have hu : ursellCoefficient ![P, Q, R] = 1 / 3 :=
          ursellCoefficient_fin_three_triangle ![P, Q, R]
            (by simpa using hPQ) (by simpa using hPR) (by simpa using hQR)
        rw [hu]
        rw [show |(1 / 3 : ℝ)| = 1 / 3 from by norm_num]
    _ ≤ ∑ Q ∈ A, ∑ R ∈ A, (1 / 3) * (|z P| * |z Q| * |z R|) := by
        refine Finset.sum_le_sum (fun Q _ => ?_)
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro R _ _; positivity
    _ = ∑ Q ∈ A, (1 / 3 * (|z P| * |z Q|)) * ∑ R ∈ A, |z R| := by
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun R _ => ?_)
        ring
    _ ≤ ∑ Q ∈ A, (1 / 3 * (|z P| * |z Q|)) * a P := by
        refine Finset.sum_le_sum (fun Q _ => ?_)
        exact mul_le_mul_of_nonneg_left (h.activity_sum_le_weight hP) (by positivity)
    _ = (1 / 3 * |z P| * a P) * ∑ Q ∈ A, |z Q| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        ring
    _ ≤ (1 / 3 * |z P| * a P) * a P := by
        refine mul_le_mul_of_nonneg_left (h.activity_sum_le_weight hP) ?_
        have : (0 : ℝ) ≤ 1 / 3 * |z P| := by positivity
        exact mul_nonneg this haP
    _ = (1 / 3) * (|z P| * a P ^ 2) := by ring

/-- **Unconditional `n = 3` Ursell bound**: `|ϕ^T(![P,Q,R])| ≤ 1/3` for any three
polymers.  By the unified classification `ursellCoefficient_fin_three_eq` the
value is always `0`, `1/6`, or `1/3`. -/
theorem abs_ursellCoefficient_fin_three_le_third
    (P Q R : Finset (Sym2 ι)) :
    |ursellCoefficient ![P, Q, R]| ≤ 1 / 3 := by
  rw [ursellCoefficient_fin_three_eq ![P, Q, R]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  split_ifs <;> norm_num

/-- **Master KP weighting lemma**: for *any* per-polymer weighting `g`
dominated by `exp ∘ a` on the incompatible polymers, the `g`-weighted activity
sum is bounded by `a P`, `∑_{Q ≁ P} |z Q| · g Q ≤ a P`.  Immediate from the KP
criterion (`∑ |z Q|·exp(a Q) ≤ a P`) by `|z Q|·g Q ≤ |z Q|·exp(a Q)`.  This is
the exact form consumed by the Kotecký–Preiss induction: with `g Q` the
per-polymer cluster sum at `Q` (which the induction shows is `≤ exp(a Q)`), it
absorbs the sub-cluster contributions into `a P`.  Specialises to
`activity_sum_le_weight` (`g = 1`) and `activity_weight_sum_le_weight`
(`g = a`). -/
theorem KPAdmissible.weighted_activity_sum_le_weight
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G)
    {g : Finset (Sym2 ι) → ℝ}
    (hg : ∀ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
      g Q ≤ Real.exp (a Q)) :
    ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q), |z Q| * g Q ≤ a P := by
  refine le_trans (Finset.sum_le_sum (fun Q hQ => ?_)) (h P hP)
  exact mul_le_mul_of_nonneg_left (hg Q hQ) (abs_nonneg _)

/-- **Exp-absorbing inductive lemma** (KP): the `a`-weighted incompatible-activity
sum is still bounded by the weight, `∑_{Q ≁ P} |z Q| · a Q ≤ a P`.  Since
`a Q ≤ exp(a Q)` (`Real.add_one_le_exp`), each term `|z Q|·a Q ≤ |z Q|·exp(a Q)`,
and the KP criterion bounds that sum by `a P`.  The `g = a` specialisation of
`weighted_activity_sum_le_weight`; the mechanism by which the Kotecký–Preiss
induction absorbs a sub-cluster's weight into the exponential. -/
theorem KPAdmissible.activity_weight_sum_le_weight
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q), |z Q| * a Q ≤ a P :=
  h.weighted_activity_sum_le_weight hP
    (fun Q _ => le_trans (by linarith) (Real.add_one_le_exp (a Q)))

/-- **Order-3 endpoint-path cluster contribution bound** (KP, GJ §18.4): the
order-3 contribution from clusters `{P, Q, R}` with `P ≁ Q` and `Q ≁ R` (a path
with `P` at an endpoint, plus triangles) is bounded by `⅓ · |z P| · a P` —
*linearly* in `a P`, because the inner sum over `R ≁ Q` is absorbed at `Q` (by
`activity_sum_le_weight`) and the resulting `a`-weighted outer sum over `Q ≁ P`
is absorbed by `activity_weight_sum_le_weight`.  Demonstrates the exponential
weight-absorption that powers the Kotecký–Preiss induction. -/
theorem KPAdmissible.order_three_endpoint_path_cluster_bound
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
        ∑ R ∈ (allPolymers G).filter (fun R => PolymersIncompatible Q R),
          |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
      ≤ (1 / 3) * (|z P| * a P) := by
  set A := (allPolymers G).filter (fun Q => PolymersIncompatible P Q) with hA
  calc ∑ Q ∈ A, ∑ R ∈ (allPolymers G).filter (fun R => PolymersIncompatible Q R),
          |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
      ≤ ∑ Q ∈ A, ∑ R ∈ (allPolymers G).filter (fun R => PolymersIncompatible Q R),
          (1 / 3) * (|z P| * |z Q| * |z R|) := by
        refine Finset.sum_le_sum (fun Q _ => Finset.sum_le_sum (fun R _ => ?_))
        exact mul_le_mul_of_nonneg_right
          (abs_ursellCoefficient_fin_three_le_third P Q R) (by positivity)
    _ = ∑ Q ∈ A, (1 / 3 * (|z P| * |z Q|))
          * ∑ R ∈ (allPolymers G).filter (fun R => PolymersIncompatible Q R), |z R| := by
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun R _ => ?_)
        ring
    _ ≤ ∑ Q ∈ A, (1 / 3 * (|z P| * |z Q|)) * a Q := by
        refine Finset.sum_le_sum (fun Q hQ => ?_)
        have hQmem : Q ∈ allPolymers G := (Finset.mem_filter.mp hQ).1
        exact mul_le_mul_of_nonneg_left (h.activity_sum_le_weight hQmem) (by positivity)
    _ = (1 / 3 * |z P|) * ∑ Q ∈ A, |z Q| * a Q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        ring
    _ ≤ (1 / 3 * |z P|) * a P := by
        exact mul_le_mul_of_nonneg_left (h.activity_weight_sum_le_weight hP) (by positivity)
    _ = (1 / 3) * (|z P| * a P) := by ring

/-- **Order-3 endpoint-path cluster contribution bound, mirror orientation**
(KP, GJ §18.4): the order-3 contribution from clusters `{P, Q, R}` with `P ≁ R`
and `R ≁ Q` (the `P`-endpoint path through `R`) is bounded by `⅓ · |z P| · a P`.
The mirror of `order_three_endpoint_path_cluster_bound` (roles of `Q` and `R`
swapped): the inner `Q ≁ R` sum is absorbed at `R` and the resulting
`a`-weighted outer `R ≁ P` sum by `activity_weight_sum_le_weight`.  Together with
the `P`-central and first endpoint bounds this covers every connected 3-cluster
shape anchored at `P`. -/
theorem KPAdmissible.order_three_endpoint_path_cluster_bound'
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    ∑ R ∈ (allPolymers G).filter (fun R => PolymersIncompatible P R),
        ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible R Q),
          |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
      ≤ (1 / 3) * (|z P| * a P) := by
  set A := (allPolymers G).filter (fun R => PolymersIncompatible P R) with hA
  calc ∑ R ∈ A, ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible R Q),
          |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
      ≤ ∑ R ∈ A, ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible R Q),
          (1 / 3) * (|z P| * |z R| * |z Q|) := by
        refine Finset.sum_le_sum (fun R _ => Finset.sum_le_sum (fun Q _ => ?_))
        calc |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
            ≤ (1 / 3) * (|z P| * |z Q| * |z R|) :=
              mul_le_mul_of_nonneg_right
                (abs_ursellCoefficient_fin_three_le_third P Q R) (by positivity)
          _ = (1 / 3) * (|z P| * |z R| * |z Q|) := by ring
    _ = ∑ R ∈ A, (1 / 3 * (|z P| * |z R|))
          * ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible R Q), |z Q| := by
        refine Finset.sum_congr rfl (fun R _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        ring
    _ ≤ ∑ R ∈ A, (1 / 3 * (|z P| * |z R|)) * a R := by
        refine Finset.sum_le_sum (fun R hR => ?_)
        have hRmem : R ∈ allPolymers G := (Finset.mem_filter.mp hR).1
        exact mul_le_mul_of_nonneg_left (h.activity_sum_le_weight hRmem) (by positivity)
    _ = (1 / 3 * |z P|) * ∑ R ∈ A, |z R| * a R := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun R _ => ?_)
        ring
    _ ≤ (1 / 3 * |z P|) * a P := by
        exact mul_le_mul_of_nonneg_left (h.activity_weight_sum_le_weight hP) (by positivity)
    _ = (1 / 3) * (|z P| * a P) := by ring

/-- **`n = 3` Ursell bound for a `P`-central cluster**: if `P` is incompatible
with both `Q` and `R`, then `|ϕ^T(![P,Q,R])| ≤ 1/3`, irrespective of the `Q`–`R`
relation.  By the unified classification `ursellCoefficient_fin_three_eq`: with
the first two flags true the value is `1/3` (triangle, `Q ≁ R`) or `1/6` (path,
`Q ~ R`), both `≤ 1/3`. -/
theorem abs_ursellCoefficient_fin_three_le_third_of_P_central
    {P Q R : Finset (Sym2 ι)}
    (hPQ : PolymersIncompatible P Q) (hPR : PolymersIncompatible P R) :
    |ursellCoefficient ![P, Q, R]| ≤ 1 / 3 := by
  rw [ursellCoefficient_fin_three_eq ![P, Q, R]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [if_pos hPQ, if_pos hPR]
  split_ifs <;> norm_num

/-- **Order-3 `P`-central cluster contribution bound** (KP, GJ §18.4): the total
order-3 contribution from clusters `{P, Q, R}` in which `P` is incompatible with
both `Q` and `R` (triangles and `P`-centred paths together) is bounded by
`⅓ · |z P| · (a P)²`.  On this product domain `{Q ≁ P} × {R ≁ P}` every Ursell
coefficient satisfies `|ϕ^T| ≤ 1/3`
(`abs_ursellCoefficient_fin_three_le_third_of_P_central`), and
`KPAdmissible.activity_sum_le_weight` bounds each activity factor by `a P`.  A
cleaner generalisation of `order_three_triangle_cluster_bound` covering both the
triangle and the `P`-centred path 3-clusters. -/
theorem KPAdmissible.order_three_P_central_cluster_bound
    {G : SimpleGraph ι} [Fintype G.edgeSet] {z a : Finset (Sym2 ι) → ℝ}
    (h : KPAdmissible G z a) {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    ∑ Q ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
        ∑ R ∈ (allPolymers G).filter (fun Q => PolymersIncompatible P Q),
          |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
      ≤ (1 / 3) * (|z P| * a P ^ 2) := by
  set A := (allPolymers G).filter (fun Q => PolymersIncompatible P Q) with hA
  have haP : (0 : ℝ) ≤ a P := h.weight_nonneg hP
  calc ∑ Q ∈ A, ∑ R ∈ A,
          |ursellCoefficient ![P, Q, R]| * (|z P| * |z Q| * |z R|)
      ≤ ∑ Q ∈ A, ∑ R ∈ A, (1 / 3) * (|z P| * |z Q| * |z R|) := by
        refine Finset.sum_le_sum (fun Q hQ => Finset.sum_le_sum (fun R hR => ?_))
        have hPQ : PolymersIncompatible P Q := (Finset.mem_filter.mp hQ).2
        have hPR : PolymersIncompatible P R := (Finset.mem_filter.mp hR).2
        exact mul_le_mul_of_nonneg_right
          (abs_ursellCoefficient_fin_three_le_third_of_P_central hPQ hPR) (by positivity)
    _ = ∑ Q ∈ A, (1 / 3 * (|z P| * |z Q|)) * ∑ R ∈ A, |z R| := by
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun R _ => ?_)
        ring
    _ ≤ ∑ Q ∈ A, (1 / 3 * (|z P| * |z Q|)) * a P := by
        refine Finset.sum_le_sum (fun Q _ => ?_)
        exact mul_le_mul_of_nonneg_left (h.activity_sum_le_weight hP) (by positivity)
    _ = (1 / 3 * |z P| * a P) * ∑ Q ∈ A, |z Q| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        ring
    _ ≤ (1 / 3 * |z P| * a P) * a P := by
        refine mul_le_mul_of_nonneg_left (h.activity_sum_le_weight hP) ?_
        have : (0 : ℝ) ≤ 1 / 3 * |z P| := by positivity
        exact mul_nonneg this haP
    _ = (1 / 3) * (|z P| * a P ^ 2) := by ring

end IsingModel
