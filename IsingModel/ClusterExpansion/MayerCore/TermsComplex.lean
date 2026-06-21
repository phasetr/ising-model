import IsingModel.ClusterExpansion.MayerCore.Terms
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Complexified Cluster Expansion Mayer Core Terms

Complex-variable versions of the real Mayer-expansion building blocks
`clusterSeqActivity` and `mayerExpansionTerm` from
`ClusterExpansion/{Incompatibility, MayerCore/Terms}.lean`.

The Ursell coefficient `ursellCoefficient ω` is `t`-independent, so the
`n`-th Mayer term `mayerExpansionTerm G n t` is a polynomial in `t`;
its complexification `mayerExpansionTermComplex G n z` is the same
polynomial evaluated at `z : ℂ`. This file records:

* the `_ofReal` bridges identifying the complexified terms with the
  `Complex.ofReal` image of the real terms, and
* per-term entirety: each `z ↦ mayerExpansionTermComplex G n z` is
  `Differentiable ℂ` (a finite sum of constant multiples of monomials),
  hence `AnalyticOnNhd ℂ _ Set.univ` and `DifferentiableOn ℂ _ U` on any
  set `U`.

This is PR-A of §18.6 (issue #4149): it makes the per-term holomorphy
available so the full Mayer series can later be shown holomorphic in `z`.
-/

namespace IsingModel

open Finset

/-- **Complexified cluster-sequence activity** (§18.6): the complex
monomial product `z(ω) = ∏ i, z ^ |ω i|` for `ω : Fin n → Finset (Sym2 ι)`
and a complex activity parameter `z : ℂ`. Complexification of
`clusterSeqActivity` (Step 581). -/
def clusterSeqActivityComplex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) : ℂ :=
  ∏ i : Fin n, z ^ (ω i).card

/-- **Complexified Mayer expansion `n`-th term** (§18.6): the
complexification of `mayerExpansionTerm` (Step 587),
`mayerExpansionTermComplex G n z = ∑_ω (ϕ^T(ω) : ℂ) · z(ω)`, where the
real Ursell coefficient `ursellCoefficient ω` is cast to `ℂ`. Since the
Ursell coefficient is `t`-independent, this is the polynomial
`mayerExpansionTerm G n ·` evaluated at `z : ℂ`. -/
noncomputable def mayerExpansionTermComplex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (z : ℂ) : ℂ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
    (ursellCoefficient ω : ℂ) * clusterSeqActivityComplex z ω

/-- **`clusterSeqActivityComplex` at a real point equals the cast of the
real activity** (§18.6): `clusterSeqActivityComplex (↑t) ω = ↑(clusterSeqActivity t ω)`.
The product/power commute with `Complex.ofReal` (`Complex.ofReal_prod`,
`Complex.ofReal_pow`). -/
theorem clusterSeqActivityComplex_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    clusterSeqActivityComplex (↑t) ω = ↑(clusterSeqActivity t ω) := by
  unfold clusterSeqActivityComplex clusterSeqActivity
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun i _ => (Complex.ofReal_pow t (ω i).card).symm)

/-- **`mayerExpansionTermComplex` at a real point equals the cast of the
real term** (§18.6): `mayerExpansionTermComplex G n (↑t) = ↑(mayerExpansionTerm G n t)`.
The sum/product/multiplication commute with `Complex.ofReal`
(`Complex.ofReal_sum`, `Complex.ofReal_mul`, `clusterSeqActivityComplex_ofReal`). -/
theorem mayerExpansionTermComplex_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    mayerExpansionTermComplex G n (↑t) = ↑(mayerExpansionTerm G n t) := by
  unfold mayerExpansionTermComplex mayerExpansionTerm
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Complex.ofReal_mul, clusterSeqActivityComplex_ofReal]

/-- **Complexified cluster-sequence activity is entire** (§18.6): the
finite product `z ↦ ∏ i, z ^ |ω i|` of monomials is `Differentiable ℂ`.
Uses `Differentiable.fun_finset_prod` and `Differentiable.pow differentiable_id`. -/
theorem clusterSeqActivityComplex_differentiable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    Differentiable ℂ (fun z : ℂ => clusterSeqActivityComplex z ω) := by
  unfold clusterSeqActivityComplex
  refine Differentiable.fun_finset_prod (fun i _ => ?_)
  exact (differentiable_id (𝕜 := ℂ)).pow _

/-- **Complexified Mayer expansion `n`-th term is entire** (§18.6): each
term is a polynomial in `z` (constant Ursell coefficients times monomial
activity factors), hence `Differentiable ℂ`. Uses `Differentiable.fun_sum`
and `Differentiable.const_mul` over `clusterSeqActivityComplex_differentiable`. -/
theorem mayerExpansionTermComplex_differentiable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => mayerExpansionTermComplex G n z) := by
  unfold mayerExpansionTermComplex
  refine Differentiable.fun_sum (fun ω _ => ?_)
  exact (clusterSeqActivityComplex_differentiable ω).const_mul _

/-- **Complexified Mayer expansion `n`-th term is analytic on `Set.univ`**
(§18.6): an entire function over `ℂ` is analytic. Derived from
`mayerExpansionTermComplex_differentiable` via
`DifferentiableOn.analyticOnNhd` on the open set `Set.univ`. -/
theorem mayerExpansionTermComplex_analyticOnNhd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ => mayerExpansionTermComplex G n z) Set.univ :=
  ((mayerExpansionTermComplex_differentiable G n).differentiableOn).analyticOnNhd isOpen_univ

/-- **Complexified Mayer expansion `n`-th term is differentiable on any
set** (§18.6): corollary of `mayerExpansionTermComplex_differentiable`,
restricting the entire function to an arbitrary set `U ⊆ ℂ`. -/
theorem mayerExpansionTermComplex_differentiableOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (U : Set ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => mayerExpansionTermComplex G n z) U :=
  (mayerExpansionTermComplex_differentiable G n).differentiableOn

end IsingModel
