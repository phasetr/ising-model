import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.EdgeFinsetParity

/-!
# Exchanging a vertex-indexed and an edge-indexed aggregate along a current

Rewriting an aggregate indexed by the vertices of `Λ`, weighted by the total incident degree
`Current.degreeAt G Λ n v` of a current `n` — the sum of the multiplicities `n e` over the
edges containing `v` — as the corresponding aggregate indexed by the edges of
`inducedGraph G Λ`, the subgraph of `G` that `Λ` induces, weighted by those multiplicities.
The graph `G : SimpleGraph V` and the finite volume `Λ : Finset V` are arbitrary.

In the additive form the target is an `AddCommMonoid M` and the data a function `f : ↥Λ → M`:
the sum over all vertices of `Current.degreeAt G Λ n v • f v` equals the sum over all edges
of `n e •` the sum of `f` over the endpoint `Finset` of `e`. In the multiplicative form the
target is a `CommMonoid M` and the data a function `g : ↥Λ → M`: the product over all
vertices of `g v` raised to `Current.degreeAt G Λ n v` equals the product over all edges of
the product of `g` over the endpoint `Finset` of `e`, raised to `n e`.

A spin specialization instantiates the multiplicative form at `M := ℝ` and at
`g := fun v => ((σ v).toSign : ℝ)` for a spin configuration `σ : ↥Λ → Spin`, so on the edge
side it carries the product of the spin signs over the endpoint `Finset` of each edge, raised
to the multiplicity of that edge.

Every statement here takes `[Fintype (inducedGraph G Λ).edgeSet]` together with
`[DecidableEq ↥Λ]`, the forms over a general target additionally take the monoid instance on
`M`, and none carries a hypothesis.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Edge → vertex sum identity (smul form)**: for any
`f : ↑Λ → M` (`M` an `AddCommMonoid`),
`∑_v degreeAt n v • f v = ∑_e n e • (e.toFinset.sum f)`. The
additive form of the central combinatorial step in the
random-current expansion of the Ising partition function
(FV §3.7); converts a vertex-side count weighted by edge
multiplicities into an edge-side count weighted by per-vertex
sums. -/
theorem Current.sum_degreeAt_smul {M : Type*} [AddCommMonoid M]
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (f : ↑Λ → M) :
    ∑ v ∈ (Finset.univ : Finset ↑Λ), n.degreeAt G Λ v • f v
      = ∑ e : (inducedGraph G Λ).edgeSet,
          n e • ((e : Sym2 ↑Λ).toFinset.sum f) := by
  classical
  -- LHS: expand degreeAt and pull smul through the sum
  simp only [Current.degreeAt, Finset.sum_smul]
  -- ∑ v, ∑ e, (if v ∈ e then n e else 0) • f v
  --   = ∑ v, ∑ e, if v ∈ e then n e • f v else 0   [push smul through if]
  have hpush : ∀ (v : ↑Λ) (e : (inducedGraph G Λ).edgeSet),
      (if v ∈ (e : Sym2 ↑Λ) then n e else 0) • f v
        = if v ∈ (e : Sym2 ↑Λ) then n e • f v else 0 := by
    intro v e
    by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [hv]
  simp_rw [hpush]
  -- swap summation order
  rw [Finset.sum_comm]
  -- ∑ e, ∑ v, if v ∈ e then n e • f v else 0
  --   = ∑ e, n e • ∑ v ∈ univ.filter (· ∈ e), f v
  --   = ∑ e, n e • e.toFinset.sum f
  congr 1
  ext e
  rw [← Finset.sum_filter, Finset.smul_sum]
  -- ∑ v ∈ univ.filter (· ∈ e), n e • f v = n e • ∑ v ∈ e.toFinset, f v
  congr 1
  ext v
  simp

omit [DecidableEq V] in
/-- **Edge → vertex product identity (pow form)**: for any
`g : ↑Λ → M` (`M` a `CommMonoid`),
`∏_v g v ^ degreeAt n v = ∏_e (e.toFinset.prod g) ^ n e`. The
multiplicative analogue of `sum_degreeAt_smul`; used to convert
the per-vertex spin product `∏_v σ_v^(degree)` into the per-edge
product `∏_e (σ_u σ_w)^(n e)` in the random-current expansion of
the Ising partition function (FV §3.7). -/
theorem Current.prod_pow_degreeAt {M : Type*} [CommMonoid M]
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (g : ↑Λ → M) :
    ∏ v ∈ (Finset.univ : Finset ↑Λ), g v ^ n.degreeAt G Λ v
      = ∏ e : (inducedGraph G Λ).edgeSet,
          ((e : Sym2 ↑Λ).toFinset.prod g) ^ n e := by
  classical
  simp only [Current.degreeAt]
  -- ∏ v, g v ^ (∑ e, if v ∈ e then n e else 0)
  --   = ∏ v, ∏ e, g v ^ (if v ∈ e then n e else 0)
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  -- push pow through if
  have hpush : ∀ (v : ↑Λ) (e : (inducedGraph G Λ).edgeSet),
      g v ^ (if v ∈ (e : Sym2 ↑Λ) then n e else 0)
        = if v ∈ (e : Sym2 ↑Λ) then g v ^ n e else 1 := by
    intro v e
    by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [hv]
  simp_rw [hpush]
  -- swap the two products
  rw [Finset.prod_comm]
  -- ∏ e, ∏ v, if v ∈ e then g v ^ n e else 1
  --   = ∏ e, ∏ v ∈ univ.filter (· ∈ e), g v ^ n e
  --   = ∏ e, (e.toFinset.prod g) ^ n e
  congr 1
  ext e
  rw [← Finset.prod_filter, ← Finset.prod_pow]
  congr 1
  ext v
  simp

omit [DecidableEq V] in
/-- **Spin-edge product = spin-vertex power (via degreeAt)**: for
any current `n` and spin configuration `σ : ↑Λ → Spin`,
`∏_v σ_v ^ degreeAt n v = ∏_e (e.toFinset.prod σ.toSign) ^ n e`.
The specialization of `prod_pow_degreeAt` to the spin-sign
function `(· : Spin).toSign : Spin → ℝ`. -/
theorem Config.prod_pow_spin_degreeAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (n : Current G Λ) :
    ∏ v ∈ (Finset.univ : Finset ↑Λ), ((σ v).toSign : ℝ) ^ n.degreeAt G Λ v
      = ∏ e : (inducedGraph G Λ).edgeSet,
          ((e : Sym2 ↑Λ).toFinset.prod
            (fun v => ((σ v).toSign : ℝ))) ^ n e :=
  Current.prod_pow_degreeAt (M := ℝ) G Λ n (fun v => ((σ v).toSign : ℝ))


end Ambient
end IsingModel
