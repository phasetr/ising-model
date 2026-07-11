import IsingModel.RandomCurrent.Core

/-!
# Cluster-conditioning weight factorization (GJ §17.5, ingredient SL-A)

Edge-partition factorization of the random-current weight `Current.weight`.

This module is ingredient **SL-A** of Lemma 5.1 (cluster-conditioning
factorisation), the weight-factorization engine used in step (ii) of that
proof. It is a **tracked ingredient** under the Group 1a authorisation, not an
isolated decoration: its capstone is Lemma 5.1 → P2-ii → `hLogLip` →
the lower-semicontinuity half of GJ Theorem 17.5.1 (§17.5). The successor
ingredients SL-B, …, SL-E build on it; SL-C and SL-D are new mathematics and
require a math-before-code pass before implementation.

## Definitions

The main statement `Current.weight_edge_partition_factor` splits the weight
product over the induced-graph edge set into a factor over an arbitrary
edge-subset `S` and a factor over its complement. The corollary
`Current.weight_dominant_edge_factor` specialises `S` to a single dominant edge
`e₀`, matching the cluster-conditioning factorisation displayed in
Glimm–Jaffe, pp. 311–312, eq. (17.5.1).

## References

* Glimm–Jaffe, *Quantum Physics*, §17.5, pp. 311–312, eq. (17.5.1).
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Edge-partition factorization of the random-current weight**
(GJ §17.5, ingredient SL-A). For any edge-subset `S` of the induced-graph edge
set, the weight `Current.weight` factors as the product of per-edge factors over
`S` times the product over the complement `Sᶜ`:
\[
  w(n) = \Bigl(\prod_{e \in S} (\beta J)^{n_e}/n_e!\Bigr)
    \cdot \prod_{e \notin S} (\beta J)^{n_e}/n_e!.
\]
This is the weight-factorization engine (step (ii)) of Lemma 5.1
(cluster-conditioning factorisation); it is a **tracked ingredient** whose
capstone is Lemma 5.1 → P2-ii → `hLogLip` → the lsc half of GJ Theorem 17.5.1
(§17.5). Successors SL-B, …, SL-E build on it (SL-C/SL-D are new mathematics
needing math-before-code). Holds for all `β, J ∈ ℝ`: it is the pure
combinatorial `Finset.prod_mul_prod_compl` split, requiring no positivity,
sign, or ordering hypothesis. -/
theorem Current.weight_edge_partition_factor (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) (n : Current G Λ)
    (S : Finset (inducedGraph G Λ).edgeSet) :
    n.weight G Λ β J
      = (∏ e ∈ S, (β * J) ^ (n e) / ((n e).factorial : ℝ))
        * ∏ e ∈ Sᶜ, (β * J) ^ (n e) / ((n e).factorial : ℝ) := by
  classical
  unfold Current.weight
  exact (Finset.prod_mul_prod_compl S
    (fun e => (β * J) ^ (n e) / ((n e).factorial : ℝ))).symm

/-- **Dominant-edge factorization of the random-current weight**
(GJ §17.5, ingredient SL-A). Specialising
`Current.weight_edge_partition_factor` to the singleton `{e₀}` gives the
cluster-conditioning factorisation of Glimm–Jaffe, pp. 311–312, eq. (17.5.1):
the weight separates into the factor of the dominant edge `e₀` and the product
over all remaining edges,
\[
  w(n) = \bigl((\beta J)^{n_{e_0}}/n_{e_0}!\bigr)
    \cdot \prod_{e \neq e_0} (\beta J)^{n_e}/n_e!.
\]
This is the step (ii) weight-factorization form used by Lemma 5.1
(cluster-conditioning): a **tracked ingredient** with capstone Lemma 5.1 →
P2-ii → `hLogLip` → the lsc half of GJ Theorem 17.5.1 (§17.5); SL-B, …, SL-E
succeed it (SL-C/SL-D are new mathematics). Holds for all `β, J ∈ ℝ`. -/
theorem Current.weight_dominant_edge_factor (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) (n : Current G Λ)
    (e₀ : (inducedGraph G Λ).edgeSet) :
    n.weight G Λ β J
      = ((β * J) ^ (n e₀) / ((n e₀).factorial : ℝ))
        * ∏ e ∈ ({e₀} : Finset (inducedGraph G Λ).edgeSet)ᶜ,
            (β * J) ^ (n e) / ((n e).factorial : ℝ) := by
  classical
  rw [Current.weight_edge_partition_factor G Λ β J n {e₀}, Finset.prod_singleton]

end Ambient

end IsingModel
