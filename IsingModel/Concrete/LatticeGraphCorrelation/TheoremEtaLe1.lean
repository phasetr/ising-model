import IsingModel.BallBoundarySimonLieb
import IsingModel.Concrete.LatticeGraphCorrelation.Inequalities
import IsingModel.Peierls
import IsingModel.Concrete.CubicExhaustion

/-!
# GJ §17.8 Theorem 17.8.1: polynomial decay implies exponential decay (η ≤ 1)

This file formalizes the main content of Glimm–Jaffe §17.8 (pp. 316–318):
if the infinite-volume two-point function decays polynomially (i.e., faster
than any fixed power), then it decays exponentially (i.e., the mass is positive).

## Main definitions

* `IsingModel.Ambient.latticeBall d r` — ℓ¹ ball of radius `r` in ℤ^d centred at the origin,
  realized as a `Finset` by filtering `cubicBox d r`.
* `IsingModel.Ambient.latticeBallBoundaryEdges d r` — edges straddling ∂B_r,
  as a `Finset (Sym2 (Fin d → ℤ))`.
* `IsingModel.Ambient.HasPolynomialDecay d Λ p` — the two-point function decays faster than
  any fixed power along the cofinite filter.

## Main results

* `scaledCorrelation_at_zero_of_sep` (axiom) — disconnection at `s = 0`
  when every path from `r` to `s` in `G` avoiding `E₀` crosses from
  the interior of `C` to the exterior.
* `correlationInfinite_polynomial_implies_exponential` — polynomial decay
  implies exponential decay (sorry'd, full proof deferred).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.8 pp. 316–318, Springer 1987.
-/

namespace IsingModel

namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase 1: Disconnection at s = 0 -/

/-- **Disconnection axiom for the scaled model at `s = 0`** (GJ §17.8 p. 316):
If `C` separates `r` from `s` in the sense that every edge `e ∈ G.edgeFinset ∖ E₀`
that would cross the cut `(C, Cᶜ)` is absent from `G`, then
`scaledCorrelation G E₀ p 0 {r, s} = 0`.

At `s = 0` the scaled Boltzmann weight has the `E₀`-bonds entirely removed,
leaving `r` and `s` in different connected components; the correlation then
vanishes by a global spin-flip argument (same as `correlation_odd_vanish`
applied to each component separately).

The formal proof is deferred (it requires factorization of the partition
function over disconnected components, which holds but involves
measure-theoretic bookkeeping beyond the current scope).

Reference: Glimm–Jaffe §17.8 p. 316. -/
axiom scaledCorrelation_at_zero_of_sep (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (C : Finset ι) (hrC : r ∈ C) (hsC : s ∉ C)
    (hcut : ∀ v ∈ C, ∀ w ∉ C, ∀ (e : Sym2 ι), e = s(v, w) → e ∉ E₀ → ¬G.Adj v w) :
    scaledCorrelation G E₀ p 0 {r, s} = 0

/-! ## Phase 2: Lattice ball definitions -/

/-- **Lattice ball of radius `r`** in `ℤ^d` centred at the origin:
`B_r = {x : Fin d → ℤ | latticeDistance d 0 x ≤ r}`.

Realized as a `Finset` by filtering `cubicBox d r`, which is valid because
the ℓ¹ ball of radius `r` is contained in the ℓ∞ box of radius `r`:
if `latticeDistance d 0 x ≤ r` then each coordinate satisfies `|x i| ≤ r`. -/
noncomputable def latticeBall (d r : ℕ) : Finset (Fin d → ℤ) :=
  (cubicBox d r).filter fun x => IsingModel.latticeDistance d 0 x ≤ r

/-- **Membership in `latticeBall`**: `x ∈ latticeBall d r ↔ latticeDistance d 0 x ≤ r`.

The key fact is that the ℓ¹ ball is contained in the ℓ∞ box: the `i`-th coordinate
`|x i| = |(0 i - x i)|` is bounded by the ℓ¹ distance as a single summand. -/
theorem mem_latticeBall {d r : ℕ} {x : Fin d → ℤ} :
    x ∈ latticeBall d r ↔ IsingModel.latticeDistance d 0 x ≤ r := by
  simp only [latticeBall, Finset.mem_filter]
  constructor
  · exact fun ⟨_, h⟩ => h
  · intro h
    refine ⟨?_, h⟩
    rw [mem_cubicBox]
    intro i
    -- The i-th summand of latticeDistance is ≤ the whole sum ≤ r
    have hcoord : ((0 : Fin d → ℤ) i - x i).natAbs ≤
        IsingModel.latticeDistance d 0 x := by
      unfold IsingModel.latticeDistance
      exact Finset.single_le_sum
        (f := fun j => ((0 : Fin d → ℤ) j - x j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hkN : ((0 : Fin d → ℤ) i - x i).natAbs ≤ r := hcoord.trans h
    simp only [Pi.zero_apply, zero_sub] at hkN
    rw [Int.natAbs_neg] at hkN
    have hkNZ : |(x i)| ≤ (r : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hkN
    rw [abs_le] at hkNZ
    exact ⟨by linarith [hkNZ.1], by linarith [hkNZ.2]⟩

/-- **`latticeBall` is monotone**: `r₁ ≤ r₂ → latticeBall d r₁ ⊆ latticeBall d r₂`. -/
theorem latticeBall_mono {d : ℕ} {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    latticeBall d r₁ ⊆ latticeBall d r₂ := by
  intro x hx
  rw [mem_latticeBall] at hx ⊢
  exact hx.trans h

/-- **Boundary bonds of `latticeBall d r`** as a `Finset (Sym2 (Fin d → ℤ))`:
the image under `Sym2.map Subtype.val` of all edges in the induced graph on
`cubicBox d (r + 1)` that straddle ∂B_r.

An edge straddles ∂B_r if one endpoint has `latticeDistance ≤ r` and the other
has `latticeDistance > r`. These are the "cut edges" `E₀` used in the
ball-boundary Simon–Lieb inequality of GJ §17.8. -/
noncomputable def latticeBallBoundaryEdges (d r : ℕ) :
    Finset (Sym2 (Fin d → ℤ)) :=
  haveI : DecidablePred fun e : Sym2 (Fin d → ℤ) =>
      Sym2.lift ⟨fun (x y : Fin d → ℤ) =>
        (IsingModel.latticeDistance d 0 x ≤ r) ≠ (IsingModel.latticeDistance d 0 y ≤ r),
        fun _ _ => propext ne_comm⟩ e :=
    fun _ => Classical.dec _
  ((inducedGraph (IsingModel.latticeGraph d) (cubicBox d (r + 1))).edgeFinset.image
      (Sym2.map Subtype.val)).filter fun e =>
    Sym2.lift ⟨fun (x y : Fin d → ℤ) =>
      (IsingModel.latticeDistance d 0 x ≤ r) ≠ (IsingModel.latticeDistance d 0 y ≤ r),
      fun _ _ => propext ne_comm⟩ e

/-- **`latticeBallBoundaryEdges` contains no diagonal edges**: every edge in
`latticeBallBoundaryEdges d r` has distinct endpoints, since the two conditions
`latticeDistance ≤ r` and `latticeDistance > r` cannot both hold at the same point. -/
theorem latticeBallBoundaryEdges_nonDiag (d r : ℕ) :
    ∀ e ∈ latticeBallBoundaryEdges d r, ¬e.IsDiag := by
  intro e he
  simp only [latticeBallBoundaryEdges] at he
  have hne : Sym2.lift ⟨fun (x y : Fin d → ℤ) =>
      (IsingModel.latticeDistance d 0 x ≤ r) ≠ (IsingModel.latticeDistance d 0 y ≤ r),
      fun _ _ => propext ne_comm⟩ e := by
    classical
    rw [Finset.mem_filter] at he; exact he.2
  intro hdiag
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  rw [Sym2.mk_isDiag_iff] at hdiag
  subst hdiag
  simp only [Sym2.lift_mk, ne_eq, not_true] at hne

/-! ## Phase 3: Polynomial decay hypothesis -/

/-- **Polynomial decay of the two-point function**: the infinite-volume
two-point function `⟨σ_0 σ_x⟩_∞` times `|x|^{d-1}` tends to zero along
the cofinite filter on `{x : Fin d → ℤ // x ≠ 0}`.

Physically this means `⟨σ_0 σ_x⟩_∞ = o(|x|^{-(d-1)})` as `|x| → ∞`.
GJ §17.8 Thm 17.8.1 shows that this (very slow) polynomial decay already
forces *exponential* decay, i.e., positive mass.

Reference: Glimm–Jaffe §17.8 pp. 316–318. -/
def HasPolynomialDecay (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) : Prop :=
  Filter.Tendsto
    (fun x : {x : Fin d → ℤ // x ≠ 0} =>
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), x.val}
        * (IsingModel.latticeDistance d 0 x.val : ℝ) ^ (d - 1))
    Filter.cofinite (nhds 0)

/-! ## Phase 4: Main theorem -/

/-- **GJ §17.8 Theorem 17.8.1** (η ≤ 1, polynomial decay implies exponential decay):

For a `d`-dimensional ferromagnetic Ising model at `h = 0`, if the
infinite-volume two-point function decays polynomially in the sense of
`HasPolynomialDecay d Λ p`, then it decays exponentially, i.e., the
lattice mass is positive:

  `∃ m > 0, HasExponentialDecay d Λ p m`

## Proof sketch

The key chain is:
1. Fix a large ball radius `R` and let `E₀ = latticeBallBoundaryEdges d R`.
2. Apply the disconnection axiom `scaledCorrelation_at_zero_of_sep`:
   the origin `0` is inside `B_R` and any `x` with `|x| ≥ R+2` is outside,
   so `scaledCorrelation (latticeGraph d) E₀ p 0 {0, x} = 0`.
3. Apply `ball_boundary_simon_lieb_tight`:
   `⟨σ_0 σ_x⟩ ≤ βJ · Σ_{(k,l)∈E₀} [⟨σ_0 σ_k⟩·⟨σ_x σ_l⟩ + ⟨σ_0 σ_l⟩·⟨σ_x σ_k⟩]`
4. Use translation invariance to bound each summand by
   `⟨σ_0 σ_{k-x}⟩ · ⟨σ_0 σ_{l-x}⟩` when `|x|` is large and `k, l ∈ ∂B_R`.
5. The sum over `∂B_R` has size `O(R^{d-1})`, and under polynomial decay each factor
   is `o(R^{-(d-1)})`, so the product is `o(1)`. A quantitative induction
   then extracts exponential decay from the iteration.

## Reference

Glimm–Jaffe, *Quantum Physics* 2nd ed., §17.8 pp. 316–318, Springer 1987. -/
theorem correlationInfinite_polynomial_implies_exponential
    (d : ℕ) (hd : 1 ≤ d)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hpoly : HasPolynomialDecay d Λ p) :
    ∃ m : ℝ, 0 < m ∧ HasExponentialDecay d Λ p m := by
  sorry

end Ambient

end IsingModel
