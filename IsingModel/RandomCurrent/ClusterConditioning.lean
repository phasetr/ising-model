import IsingModel.RandomCurrent.Core

/-!
# Cluster-conditioning weight factorization (ingredient SL-A)

Edge-partition factorization of the random-current weight `Current.weight`.
The weight `∏_e (βJ)^{n_e}/n_e!` is the random-current weight of
Friedli–Velenik, eq. (3.45) (§3.7); see `RandomCurrent/Core.lean`.

This module is ingredient **SL-A** intended to supply the (future) Lemma 5.1
(cluster-conditioning factorisation). It is a **tracked ingredient** under the
Group 1a authorisation, not an isolated decoration: it is planned to feed the
weight-factorization step of Lemma 5.1, which in turn is aimed at `hLogLip` →
the lower-semicontinuity half of GJ Theorem 17.5.1 (§17.5). That GJ §17.5
reference records the intended downstream position of this ingredient, not the
source of the weight itself (which is FV (3.45)). The successor ingredients
SL-B, …, SL-E are planned to build on it; SL-C and SL-D are new mathematics and
require a math-before-code pass before implementation.

## Definitions

The main statement `Current.weight_edge_partition_factor` splits the weight
product over the induced-graph edge set into a factor over an arbitrary
edge-subset `S` and a factor over its complement. The corollary
`Current.weight_dominant_edge_factor` specialises `S` to a single dominant edge
`e₀`, the algebraic form of the FV (3.45) weight used by the
cluster-conditioning factorisation.

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7,
  eq. (3.45) (random-current weight).
* Glimm–Jaffe, *Quantum Physics*, §17.5 (intended downstream position of this
  ingredient: cluster-conditioning → lsc half of Theorem 17.5.1).
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Edge-partition factorization of the random-current weight**
(ingredient SL-A). For any edge-subset `S` of the induced-graph edge set, the
FV (3.45) weight `Current.weight` factors as the product of per-edge factors
over `S` times the product over the complement `Sᶜ`:
\[
  w(n) = \Bigl(\prod_{e \in S} (\beta J)^{n_e}/n_e!\Bigr)
    \cdot \prod_{e \notin S} (\beta J)^{n_e}/n_e!.
\]
This is a **tracked ingredient** intended to supply the weight-factorization
step of the (future) Lemma 5.1 (cluster-conditioning factorisation), aimed
downstream at `hLogLip` → the lsc half of GJ Theorem 17.5.1 (§17.5). Successors
SL-B, …, SL-E are planned to build on it (SL-C/SL-D are new mathematics needing
math-before-code). Holds for all `β, J ∈ ℝ`: it is the pure combinatorial
`Finset.prod_mul_prod_compl` split, requiring no positivity, sign, or ordering
hypothesis. -/
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
(ingredient SL-A). Specialising `Current.weight_edge_partition_factor` to the
singleton `{e₀}` separates the FV (3.45) weight into the factor of the dominant
edge `e₀` and the product over all remaining edges,
\[
  w(n) = \bigl((\beta J)^{n_{e_0}}/n_{e_0}!\bigr)
    \cdot \prod_{e \neq e_0} (\beta J)^{n_e}/n_e!.
\]
This is the algebraic weight-factorization form intended to supply the (future)
Lemma 5.1 (cluster-conditioning): a **tracked ingredient** aimed downstream at
`hLogLip` → the lsc half of GJ Theorem 17.5.1 (§17.5); SL-B, …, SL-E are
planned to succeed it (SL-C/SL-D are new mathematics). Holds for all
`β, J ∈ ℝ`. -/
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
