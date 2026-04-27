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

* `scaledCorrelation_at_zero_of_sep` — disconnection at `s = 0`
  when every path from `r` to `s` in `G` avoiding `E₀` crosses from
  the interior of `C` to the exterior. Proved via the partial spin-flip
  `flipSet C` involution argument.
* `ball_boundary_tight_infinite` (axiom) — infinite-volume tight ball-boundary
  Simon–Lieb inequality for `h = 0` ferromagnetic Ising models.
* `polynomialDecay_contraction_factor_tendsto` (axiom, sub-step) — the contraction
  factor `α_r` tends to `0` under polynomial decay.
* `shellSup_contraction` (axiom, key inductive step) — one step of the iterated
  contraction argument for the shell supremum.
* `shellSup_iterated_bound` (axiom, inductive bound) — iterated contraction gives
  exponential bound on the shell supremum.
* `correlationInfinite_polynomial_implies_exponential` — polynomial decay
  implies exponential decay (GJ §17.8 Thm 17.8.1).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.8 pp. 316–318, Springer 1987.
-/

namespace IsingModel

namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase 1: Disconnection at s = 0 -/

omit [Fintype ι] in
/-- **edgeSpin invariance under flipSet for non-crossing edges** (auxiliary):
For an edge `e = s(u, v)` that does not cross the cut `(C, Cᶜ)` (i.e., both endpoints
are on the same side of `C`), the edge spin is unchanged under `flipSet C`.

If `u, v ∈ C`: both spins flip; the product of two negatives is unchanged.
If `u, v ∉ C`: neither spin flips; the product is unchanged. -/
private theorem edgeSpin_flipSet_of_not_crosses (C : Finset ι) (σ : Config ι)
    (u v : ι) (hnotcross : ¬(u ∈ C ∧ v ∉ C) ∧ ¬(u ∉ C ∧ v ∈ C)) :
    edgeSpin (K := ℝ) (Config.flipSet C σ) s(u, v) =
    edgeSpin (K := ℝ) σ s(u, v) := by
  simp only [edgeSpin, Sym2.lift_mk, Config.flipSet]
  push Not at hnotcross
  obtain ⟨h1, h2⟩ := hnotcross
  by_cases hu : u ∈ C
  · have hv : v ∈ C := h1 hu
    simp only [hu, hv, ite_true, Spin.sign_flip]; ring
  · have hv : v ∉ C := h2 hu
    simp only [hu, hv, ite_false]

/-- **scaledBoltzmannWeight at s=0 depends only on G\E₀ edges** (auxiliary):
At `s = 0` and `h = 0`, the scaled Boltzmann weight equals
`exp(β·J · Σ_{G\E₀} edgeSpin σ e)`.
This is the key identity showing that E₀ edges cancel out at `s = 0`. -/
private theorem scaledBoltzmannWeight_zero_sdiff (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hh : p.h = 0) (σ : Config ι) :
    scaledBoltzmannWeight G E₀ p 0 σ =
    Real.exp (p.β * p.J * ∑ e ∈ G.edgeFinset \ E₀, edgeSpin (K := ℝ) σ e) := by
  simp only [scaledBoltzmannWeight, boltzmannWeight, hamiltonian, interactionEnergy,
    externalFieldEnergy, hh, neg_zero, zero_mul, add_zero]
  rw [← Real.exp_add]
  congr 1
  rw [← Finset.sum_sdiff hE₀_sub]
  ring

/-- **scaledBoltzmannWeight invariance under flipSet at s=0** (auxiliary):
At `s = 0` and `h = 0`, when no edge in `G.edgeFinset \ E₀` crosses the cut `(C, Cᶜ)`,
the partial flip `flipSet C` preserves the scaled Boltzmann weight. -/
private theorem scaledBoltzmannWeight_flipSet_of_sep (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hh : p.h = 0)
    (C : Finset ι)
    (hcut : ∀ v ∈ C, ∀ w ∉ C, ∀ (e : Sym2 ι), e = s(v, w) → e ∉ E₀ → ¬G.Adj v w)
    (σ : Config ι) :
    scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) =
    scaledBoltzmannWeight G E₀ p 0 σ := by
  rw [scaledBoltzmannWeight_zero_sdiff G E₀ hE₀_sub p hh,
      scaledBoltzmannWeight_zero_sdiff G E₀ hE₀_sub p hh]
  -- Goal: exp(β*J*Σ_{G\E₀} edgeSpin (flipSet C σ) e) = exp(β*J*Σ_{G\E₀} edgeSpin σ e)
  congr 1; congr 1
  -- Goal: Σ_{G\E₀} edgeSpin (flipSet C σ) e = Σ_{G\E₀} edgeSpin σ e
  apply Finset.sum_congr rfl
  intro e he
  -- e ∈ G.edgeFinset \ E₀; write e = s(u, v) and show edgeSpin is preserved.
  obtain ⟨hemem, heE₀⟩ := Finset.mem_sdiff.mp he
  -- Induct on e as s(u,v); after induction, hemem and heE₀ are rewritten.
  induction e using Sym2.ind with
  | h u v =>
  apply edgeSpin_flipSet_of_not_crosses
  -- Show neither direction of crossing can occur.
  refine ⟨fun ⟨hu, hv⟩ => ?_, fun ⟨hu, hv⟩ => ?_⟩
  · -- ¬(u ∈ C ∧ v ∉ C): if u ∈ C and v ∉ C, then G.Adj u v by hemem, contradiction.
    have hnadj : ¬G.Adj u v := hcut u hu v hv s(u, v) rfl heE₀
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hemem
    exact hnadj hemem
  · -- ¬(u ∉ C ∧ v ∈ C): symmetric.
    have heE₀' : s(v, u) ∉ E₀ := by rwa [Sym2.eq_swap]
    have hnadj : ¬G.Adj v u := hcut v hv u hu s(v, u) rfl heE₀'
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hemem
    exact hnadj hemem.symm

set_option linter.unusedVariables false in
/-- **Disconnection theorem for the scaled model at `s = 0`** (GJ §17.8 p. 316):
If `C` separates `r` from `s` in the sense that every edge `e ∈ G.edgeFinset ∖ E₀`
that would cross the cut `(C, Cᶜ)` is absent from `G`, then
`scaledCorrelation G E₀ p 0 {r, s} = 0`.

At `s = 0` the scaled Boltzmann weight retains only edges in `G.edgeFinset ∖ E₀`.
Since no such edge crosses the cut `(C, Cᶜ)`, the partial flip `flipSet C` is a
measure-preserving involution that negates `spinProduct {r, s}` (because `r ∈ C`
and `s ∉ C`). A standard pairing argument then shows the numerator sum is zero.

## Proof sketch

1. **flipSet C preserves scaledBoltzmannWeight G E₀ p 0**: at `s = 0` and `h = 0`,
   `scaledBoltzmannWeight G E₀ p 0 σ = exp(β·J · Σ_{G\E₀} edgeSpin σ e)`.
   Each edge `e = ⟨u, v⟩ ∈ G\E₀` does not cross `(C, Cᶜ)` by `hcut`,
   so both endpoints are on the same side; `edgeSpin (flipSet C σ) e = edgeSpin σ e`.

2. **flipSet C negates spinProduct {r, s}**: `r ∈ C` is flipped, `s ∉ C` is not,
   so `sign((flipSet C σ) r) = -sign(σ r)` while `sign((flipSet C σ) s) = sign(σ s)`.

3. **Pairing argument**: `Σ f(σ) = Σ f(flipSet C σ) = -Σ f(σ)`, hence 0.

Note: the hypothesis `hf : Ferromagnetic p` is retained in the signature for
uniformity with the rest of the API, even though this particular proof does not
use it directly (the spin-flip argument at `h = 0` does not require ferromagneticity).

Reference: Glimm–Jaffe §17.8 p. 316. -/
theorem scaledCorrelation_at_zero_of_sep (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (C : Finset ι) (hrC : r ∈ C) (hsC : s ∉ C)
    (hcut : ∀ v ∈ C, ∀ w ∉ C, ∀ (e : Sym2 ι), e = s(v, w) → e ∉ E₀ → ¬G.Adj v w) :
    scaledCorrelation G E₀ p 0 {r, s} = 0 := by
  simp only [scaledCorrelation, scaledGibbsExpectation]
  -- Reduce to showing the numerator sum is zero.
  suffices hsum : ∑ σ : Config ι,
      spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ = 0 by
    rw [hsum, mul_zero]
  -- Step B: spinProduct {r,s} (flipSet C σ) = -spinProduct {r,s} σ
  -- since r ∈ C (so sign flips) and s ∉ C (so sign unchanged).
  have hsp : ∀ σ : Config ι,
      spinProduct {r, s} (Config.flipSet C σ) = -spinProduct {r, s} σ := by
    intro σ
    -- {r, s} has r ≠ s, so the two-element product expands.
    rw [spinProduct, spinProduct]
    simp only [Finset.prod_pair hrs, Config.flipSet]
    simp only [hrC, hsC, ite_true, ite_false, Spin.toSign_flip, Int.cast_neg]
    ring
  -- Step A: scaledBoltzmannWeight is invariant under flipSet C (by hcut and h=0).
  have hbw : ∀ σ : Config ι,
      scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) =
      scaledBoltzmannWeight G E₀ p 0 σ :=
    scaledBoltzmannWeight_flipSet_of_sep G E₀ hE₀_sub p hh C hcut
  -- Step C: combining, the summand negates under flipSet C.
  have hflip : ∀ σ : Config ι,
      spinProduct {r, s} (Config.flipSet C σ) *
        scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) =
      -(spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ) := by
    intro σ; rw [hsp, hbw]; ring
  -- Step D: pairing argument — Σ f(σ) = Σ f(flipSet C σ) = -Σ f(σ), so Σ f(σ) = 0.
  let flipSetEquiv : Equiv.Perm (Config ι) :=
    ⟨Config.flipSet C, Config.flipSet C,
      Config.flipSet_flipSet C, Config.flipSet_flipSet C⟩
  have hreindex : ∑ σ : Config ι,
        spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ =
      ∑ σ : Config ι,
        spinProduct {r, s} (Config.flipSet C σ) *
          scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) :=
    (Equiv.sum_comp flipSetEquiv _).symm
  have hneq : ∑ σ : Config ι,
        spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ =
      -(∑ σ : Config ι, spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ) :=
    calc ∑ σ : Config ι, spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ
        = ∑ σ : Config ι,
            spinProduct {r, s} (Config.flipSet C σ) *
              scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) := hreindex
      _ = ∑ σ : Config ι,
            -(spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ) :=
            Finset.sum_congr rfl (fun σ _ => hflip σ)
      _ = -(∑ σ : Config ι, spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ) := by
            rw [← Finset.sum_neg_distrib]
  linarith

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

/-! ## Phase 4: Infinite-volume ball-boundary inequality (axiom) -/

/-- **Infinite-volume tight ball-boundary Simon–Lieb inequality** (axiom, GJ §17.8 pp. 316–318):

For a ferromagnetic Ising model at `h = 0` on `latticeGraph d`, with `E₀ =
latticeBallBoundaryEdges d r` and a point `x : Fin d → ℤ` with
`latticeDistance d 0 x > r`, the infinite-volume two-point correlation satisfies:

  `correlationInfinite (latticeGraph d) Λ p {0, x} ≤`
  `  p.β * p.J * ∑ e ∈ E₀, Sym2.lift ⟨fun k l =>`
  `    correlationInfinite ... {0, k} * correlationInfinite ... {l, x}`
  `    + correlationInfinite ... {0, l} * correlationInfinite ... {k, x}, ...⟩ e`

**Proof sketch (deferred)**: Apply `ball_boundary_simon_lieb_tight` at each finite
volume stage (using `scaledCorrelation_at_zero_of_sep` for the disconnection
hypothesis at `x` outside `B_{r+1}`), then take the limit using
`correlationAlongExhaustion_le_correlationInfinite`.

Reference: Glimm–Jaffe §17.8 eq. (17.8.4)–(17.8.5), pp. 316–318. -/
axiom ball_boundary_tight_infinite (d : ℕ) (hd : 1 ≤ d)
    (r : ℕ)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (x : Fin d → ℤ) (hx : r < IsingModel.latticeDistance d 0 x) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), x}
      ≤ p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              * correlationInfinite (IsingModel.latticeGraph d) Λ p {l, x}
            + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l}
              * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, x},
          fun k l => by ring⟩ e

/-! ## Phase 5: Contraction factor -/

/-- **Contraction factor for radius `r`**: the weighted sum over boundary edges of the
sum of two-point correlations from the origin to each endpoint.

`contractionFactor d Λ p r := p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,`
`  Sym2.lift ⟨fun k l => corr∞{0, k} + corr∞{0, l}, ...⟩ e`

Under translation invariance (at `h = 0`), `corr∞{l, x} = corr∞{0, x - l}`, so the
ball-boundary inequality with `sup_{|x| ≥ n} corr∞{0, x}` bounded by
`contractionFactor * sup_{|y| ≥ n - r - 1} corr∞{0, y}` (see `shellSup_contraction`).

Key property: under `HasPolynomialDecay`, `contractionFactor d Λ p r → 0` as `r → ∞`,
so in particular `contractionFactor < 1` for large enough `r`. -/
noncomputable def contractionFactor (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (r : ℕ) : ℝ :=
  p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,
    Sym2.lift ⟨fun k l =>
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
        + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
    fun k l => by ring⟩ e

/-- **The contraction factor is non-negative**: `0 ≤ contractionFactor d Λ p r`.

Follows from `p.β * p.J ≥ 0` (ferromagnetic) and
`correlationInfinite ≥ 0` (ferromagnetic). -/
theorem contractionFactor_nonneg (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ) :
    0 ≤ contractionFactor d Λ p r := by
  unfold contractionFactor
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg
  intro e _
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  apply add_nonneg
  · exact correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
  · exact correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _

/-- **Polynomial decay implies contraction factor tends to zero** (axiom, sub-step of GJ §17.8):

Under `HasPolynomialDecay d Λ p`, `contractionFactor d Λ p r → 0` as `r → ∞`
along `Filter.atTop`.

**Proof sketch (deferred)**: The boundary `latticeBallBoundaryEdges d r` has
`O(r^{d-1})` edges. Each endpoint `k` (or `l`) at distance `∼ r` from the origin
satisfies `corr∞{0, k} ≤ c * r^{-(d-1)}` by the polynomial decay hypothesis.
The product `O(r^{d-1}) * O(r^{-(d-1)}) * β * J → 0` since the polynomial
decay gives the `o(1)` term: for any `ε > 0`, eventually all summands
`corr∞{0, k} * dist(0, k)^{d-1} ≤ ε`, so
`contractionFactor r ≤ β * J * |∂B_r| * ε * r^{-(d-1)} ≤ C * ε → 0`.

Reference: Glimm–Jaffe §17.8 pp. 317–318. -/
axiom polynomialDecay_contraction_factor_tendsto (d : ℕ) (hd : 1 ≤ d)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hpoly : HasPolynomialDecay d Λ p) :
    Filter.Tendsto (contractionFactor d Λ p) Filter.atTop (nhds 0)

/-! ## Phase 6: Shell-supremum contraction (axiom) -/

/-- **Shell supremum contraction** (axiom, key inductive step of GJ §17.8):

For `n > r + 1`, the supremum of `corr∞{0, y}` over the shell `{y : |y| ≥ n}` satisfies:

  `⨆ {|y| ≥ n} corr∞{0, y} ≤ contractionFactor d Λ p r * ⨆ {|y| ≥ n - r - 1} corr∞{0, y}`

**Proof sketch (deferred)**: For each `y` with `|y| ≥ n > r`, apply
`ball_boundary_tight_infinite` to get:
  `corr∞{0, y} ≤ β * J * Σ_{(k,l)∈Γ_r} [corr∞{0,k} * corr∞{l,y} + corr∞{0,l} * corr∞{k,y}]`
By translation invariance (`correlationInfinite_vaddFinset_of_translationInvariant`
with translation `t = -l`), `corr∞{l, y} = corr∞{0, y - l}`. Boundary edges satisfy
`|k|, |l| ≤ r + 1`, so `|y - l| ≥ |y| - r - 1 ≥ n - r - 1`. Thus
  `corr∞{0, y} ≤ contractionFactor * (⨆ {|z| ≥ n-r-1} corr∞{0, z})`
Taking the `iSup` over `y` gives the claimed inequality.

Reference: Glimm–Jaffe §17.8 proof of Thm 17.8.1, p. 317. -/
axiom shellSup_contraction (d : ℕ) (hd : 1 ≤ d)
    (r : ℕ)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (n : ℕ) (hn : r + 1 < n) :
    ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
      ≤ contractionFactor d Λ p r *
        ⨆ (y : {y : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}

/-! ## Phase 7: Iterated contraction bound (axiom) -/

/-- **Shell supremum iterated bound** (axiom, iterated application of `shellSup_contraction`):

Fix `r : ℕ` and `α = contractionFactor d Λ p r` with `α < 1`. Set step size `s = r + 2`.
For all `k : ℕ` and all `n ≥ k * s`:

  `⨆ {|y| ≥ n} corr∞{0, y} ≤ α^k`

**Proof sketch (deferred)**: By induction on `k`.
- Base `k = 0`: the sup is `≤ 1 = α^0` from `correlationInfinite_le_one`.
- Step: for `n ≥ (k+1) * s = k * s + r + 2 > r + 1`,
  apply `shellSup_contraction` at `n` to get
  `sup(n) ≤ α * sup(n - r - 1)`.
  Since `n - r - 1 ≥ k * s`, the inductive hypothesis gives `sup(n - r - 1) ≤ α^k`.
  Thus `sup(n) ≤ α * α^k = α^(k+1)`.

Reference: Glimm–Jaffe §17.8 proof of Thm 17.8.1, p. 317. -/
axiom shellSup_iterated_bound (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1)
    (k n : ℕ) (hn : k * (r + 2) ≤ n) :
    ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
      ≤ (contractionFactor d Λ p r) ^ k

/-! ## Phase 8: Auxiliary lemmas -/

/-- **Rewrite `p` using `hh`**: for any `p : IsingParams ℝ` with `hh : p.h = 0`,
`p = ⟨p.J, 0, p.β⟩`. Used to apply theorems stated for `⟨J, 0, β⟩`. -/
private theorem isingParams_h_zero (p : IsingParams ℝ) (hh : p.h = 0) :
    p = (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := by cases p; simp_all

/-- **BddAbove for the shell supremum**: the set of values
`{corr∞{0, y.val} : y : {y // n ≤ dist(0,y) ∧ y ≠ 0}}` is bounded above by `1`.

Used in `le_ciSup_of_le` calls to show the `iSup` is well-defined. -/
private theorem shellSup_bddAbove (d n : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    BddAbove (Set.range (fun (y :
        {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}) =>
      correlationInfinite (IsingModel.latticeGraph d) Λ p
        {(0 : Fin d → ℤ), y.val})) :=
  ⟨1, fun _x ↦ by
    rintro ⟨y, rfl⟩
    exact correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _⟩

/-- **Exponential contraction bound for `α^k`**: if `0 < α < 1`, `s > 0`, and `k = n / s`
(natural number floor division), then `α ^ k ≤ (1 / α) * Real.exp (Real.log α / s * n)`.

**Proof**: Set `k = n / s`. The key inequality is that `n / s` (real division) is strictly
less than `k + 1`, which follows from `n < (k + 1) * s` (a standard property of floor
division: `s * (n / s) + n % s = n` and `n % s < s`).  Since `log α < 0` and `n/s < k+1`,
multiplying by `log α` reverses the inequality:
`(k+1) * log α ≤ (n/s) * log α`.
Therefore `α^(k+1) = exp((k+1) * log α) ≤ exp(n/s * log α) = exp(log α / s * n)`.
Finally `α^k = (1/α) * α^(k+1) ≤ (1/α) * exp(log α / s * n)`. -/
private theorem pow_div_le_inv_mul_exp (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (s : ℕ) (hs_pos : 0 < s) (n : ℕ) :
    α ^ (n / s) ≤ (1 / α) * Real.exp (Real.log α / s * n) := by
  have hlog_neg : Real.log α < 0 := Real.log_neg hα_pos hα_lt_one
  -- n < (n / s + 1) * s  follows from n = s*(n/s) + n%s and n%s < s
  have hlt_nat : n < (n / s + 1) * s := by
    have h1 : s * (n / s) + n % s = n := Nat.div_add_mod n s
    have h2 : n % s < s := Nat.mod_lt n hs_pos
    nlinarith
  -- (n : ℝ) / (s : ℝ) < (n / s : ℕ) + 1
  have hlt_real : (n : ℝ) / (s : ℝ) < ((n / s : ℕ) : ℝ) + 1 := by
    have : ((n : ℕ) : ℝ) < ((((n / s + 1) * s : ℕ) : ℕ) : ℝ) := by exact_mod_cast hlt_nat
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hs_pos)]
    push_cast at this ⊢; linarith
  -- (k+1) * log α ≤ (n/s) * log α  (log α < 0 reverses the inequality)
  have hineq : (((n / s : ℕ) : ℝ) + 1) * Real.log α ≤ (n : ℝ) / (s : ℝ) * Real.log α :=
    mul_le_mul_of_nonpos_right (le_of_lt hlt_real) (le_of_lt hlog_neg)
  -- log α / s * n = (n / s) * log α  (rearrangement)
  have hrearr : Real.log α / (s : ℝ) * (n : ℝ) = (n : ℝ) / (s : ℝ) * Real.log α := by ring
  -- α^(n/s+1) ≤ exp(log α / s * n)
  have hpow_le : α ^ (n / s + 1) ≤ Real.exp (Real.log α / (s : ℝ) * (n : ℝ)) := by
    have hpow_eq : α ^ (n / s + 1) = Real.exp (Real.log α * (((n / s : ℕ) : ℝ) + 1)) := by
      rw [← Real.rpow_natCast α (n / s + 1), Real.rpow_def_of_pos hα_pos]
      push_cast; ring
    rw [hpow_eq, hrearr]
    exact Real.exp_le_exp.mpr (by linarith [mul_comm (Real.log α) (((n / s : ℕ) : ℝ) + 1)])
  -- α^(n/s) = (1/α) * α^(n/s+1) ≤ (1/α) * exp(log α / s * n)
  calc α ^ (n / s)
      = (1 / α) * α ^ (n / s + 1) := by field_simp; ring
    _ ≤ (1 / α) * Real.exp (Real.log α / (s : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow_le (by positivity)

/-! ## Phase 9: Main theorem -/

/-- **GJ §17.8 Theorem 17.8.1** (η ≤ 1, polynomial decay implies exponential decay):

For a `d`-dimensional ferromagnetic Ising model at `h = 0`, if the
infinite-volume two-point function decays polynomially in the sense of
`HasPolynomialDecay d Λ p`, then it decays exponentially, i.e., the
lattice mass is positive:

  `∃ m > 0, HasExponentialDecay d Λ p m`

## Proof structure

1. **Find a contraction radius `R`**: By `polynomialDecay_contraction_factor_tendsto`,
   `contractionFactor d Λ p r → 0 < 1`, so there exists `R : ℕ` with
   `contractionFactor d Λ p R < 1/2`.

2. **Set `α = contractionFactor d Λ p R`**: We have `0 ≤ α < 1`.

3. **Handle `α = 0`**: Use `m = 1`, `C = exp(R+2)`.
   For `dist(i,j) < R+2`: bound `|corr| ≤ 1 ≤ exp(R+2) * exp(-dist)`.
   For `dist(i,j) ≥ R+2`: `corr∞ = 0` by `shellSup_iterated_bound` with `k=1`, `α^1 = 0`.

4. **Handle `0 < α < 1`**: Set `s = R + 2`, `m = -log(α)/s > 0`, `C = 1/α`.

5. **Pointwise bound via shells**: For any `x` with `dist(0, x) = n ≥ 1`,
   set `k = n / s`. By `shellSup_iterated_bound`, `corr∞{0, x} ≤ α^k`.

6. **Convert to exponential**: By `pow_div_le_inv_mul_exp`,
   `α^k ≤ (1/α) * exp(-m * n) = C * exp(-m * dist(i,j))`.

7. **Apply `truncated2Infinite_eq_correlationInfinite_pair_h_zero`**: At `h = 0`,
   `|truncated2Infinite G Λ p i j| = corr∞{i, j}` (non-negative).

8. **Translation invariance**: `corr∞{i, j} = corr∞{0, j-i}` by
   `correlationInfinite_vaddFinset_of_translationInvariant` with `t = i`.

## Reference

Glimm–Jaffe, *Quantum Physics* 2nd ed., §17.8 pp. 316–318, Springer 1987. -/
theorem correlationInfinite_polynomial_implies_exponential
    (d : ℕ) (hd : 1 ≤ d)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hpoly : HasPolynomialDecay d Λ p) :
    ∃ m : ℝ, 0 < m ∧ HasExponentialDecay d Λ p m := by
  -- Step 1: Extract contraction radius R with α_R < 1/2.
  have hcf_tendsto := polynomialDecay_contraction_factor_tendsto d hd Λ p hf hh hpoly
  rw [Metric.tendsto_atTop] at hcf_tendsto
  obtain ⟨R, hR⟩ := hcf_tendsto (1 / 2) (by norm_num)
  have hR_val : |contractionFactor d Λ p R - 0| < 1 / 2 := hR R le_rfl
  simp only [sub_zero] at hR_val
  have hα_lt_half : contractionFactor d Λ p R < 1 / 2 := lt_of_abs_lt hR_val
  have hα_lt_one : contractionFactor d Λ p R < 1 := lt_trans hα_lt_half (by norm_num)
  have hα_nonneg : 0 ≤ contractionFactor d Λ p R := contractionFactor_nonneg d Λ p hf R
  set α := contractionFactor d Λ p R with hα_def
  -- Step 2: Case split on α = 0 or 0 < α < 1.
  rcases eq_or_lt_of_le hα_nonneg with hα_zero | hα_pos
  · -- Case α = 0: Use m = 1, C = exp(R+2).
    -- For dist(i,j) < R+2: |corr| ≤ 1 ≤ exp(R+2) * exp(-dist).
    -- For dist(i,j) ≥ R+2: corr∞{0,j-i} = 0 by shellSup_iterated_bound with k=1, α^1=0.
    refine ⟨1, one_pos, Real.exp (R + 2 : ℕ), (Real.exp_pos _).le, fun i j hij => ?_⟩
    -- At h = 0, |truncated2Infinite| = correlationInfinite.
    have htrunc : truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} := by
      have hp_eq : p = (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := by
        obtain ⟨J, h, β⟩ := p; simp only at hh ⊢; subst hh; rfl
      conv_lhs => rw [hp_eq]
      conv_rhs => rw [hp_eq]
      exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ p.J p.β i j
    rw [htrunc]
    have hcorr_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
    rw [abs_of_nonneg hcorr_nn]
    -- Translation invariance: corr∞{i, j} = corr∞{0, j-i}.
    have htrans : correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i} := by
      rw [show ({i, j} : Finset (Fin d → ℤ)) = vaddFinset i {(0 : Fin d → ℤ), j - i} from by
        rw [vaddFinset_pair]; simp [vadd_eq_add]]
      exact correlationInfinite_vaddFinset_of_translationInvariant
        (IsingModel.latticeGraph d) Λ i p hf {(0 : Fin d → ℤ), j - i}
    rw [htrans]
    have hdist_eq : IsingModel.latticeDistance d i j = IsingModel.latticeDistance d 0 (j - i) := by
      unfold IsingModel.latticeDistance
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Pi.zero_apply, zero_sub, Pi.sub_apply]
      congr 1; ring
    set n := IsingModel.latticeDistance d 0 (j - i) with hn_def
    have hjmi_ne : j - i ≠ 0 := fun h => hij (by
      have : j = i + (j - i) := by abel
      rw [h, add_zero] at this; exact this.symm)
    -- Case split: small or large distance.
    rcases Nat.lt_or_ge n (R + 2) with hdist_small | hdist_large
    · -- Small distance (n < R+2): bound corr∞ ≤ 1 ≤ exp(R+2) * exp(-1 * dist(i,j)).
      calc correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i}
          ≤ 1 := correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
        _ ≤ Real.exp (↑(R + 2)) * Real.exp (-1 * (IsingModel.latticeDistance d i j : ℝ)) := by
            rw [← Real.exp_add, Real.one_le_exp_iff, hdist_eq]
            have h2r : (n : ℝ) < ((R : ℝ) + 2) := by exact_mod_cast hdist_small
            have h3 : ((R + 2 : ℕ) : ℝ) = (R : ℝ) + 2 := by push_cast; ring
            push_cast [hn_def, h3]; linarith
    · -- Large distance (n ≥ R+2): corr∞{0, j-i} = 0 by the iterated bound with α^1 = 0.
      have hcorr_zero : correlationInfinite (IsingModel.latticeGraph d) Λ p
          {(0 : Fin d → ℤ), j - i} = 0 := by
        -- shellSup_iterated_bound with k=1, n ≥ R+2 gives iSup ≤ α^1 = 0.
        have h_iter := shellSup_iterated_bound d hd R Λ p hf hh hα_lt_one 1 n
          (by omega : 1 * (R + 2) ≤ n)
        -- After `set α := contractionFactor d Λ p R`, h_iter uses α.
        have hαpow : α ^ 1 = 0 := by simp [← hα_zero]
        rw [hαpow] at h_iter
        -- corr∞{0, j-i} ≤ iSup ≤ 0, combined with nonnegativity.
        have hle_iSup : correlationInfinite (IsingModel.latticeGraph d) Λ p
            {(0 : Fin d → ℤ), j - i} ≤
            ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
              correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val} :=
          le_ciSup_of_le (shellSup_bddAbove d n Λ p) ⟨j - i, le_refl n, hjmi_ne⟩ (le_refl _)
        have hnn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p
            {(0 : Fin d → ℤ), j - i} :=
          correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
        linarith [hle_iSup.trans h_iter]
      rw [hcorr_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · -- Case 0 < α < 1.
    -- Step 3: Set step size s = R + 2, mass m = -log(α)/s > 0, constant C = 1/α.
    set s := R + 2 with hs_def
    have hs_pos : (0 : ℕ) < s := by omega
    have hs_pos_r : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs_pos
    have hlog_neg : Real.log α < 0 := Real.log_neg hα_pos hα_lt_one
    set m := -Real.log α / (s : ℝ) with hm_def
    have hm_pos : 0 < m := div_pos (neg_pos.mpr hlog_neg) hs_pos_r
    set C := 1 / α with hC_def
    have hC_pos : 0 < C := div_pos one_pos hα_pos
    -- Step 4: Witness m and C for HasExponentialDecay.
    refine ⟨m, hm_pos, C, hC_pos.le, fun i j hij => ?_⟩
    -- Step 5: At h = 0, |truncated2Infinite| = correlationInfinite.
    have htrunc : truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} := by
      have hp_eq : p = (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := by cases p; simp_all
      conv_lhs => rw [hp_eq]
      conv_rhs => rw [hp_eq]
      exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ p.J p.β i j
    rw [htrunc]
    have hcorr_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
    rw [abs_of_nonneg hcorr_nn]
    -- Step 6: Translation invariance — corr∞{i, j} = corr∞{0, j - i}.
    -- Use t = i: by vaddFinset_pair, vaddFinset i {0, j-i} = {i +ᵥ 0, i +ᵥ (j-i)} = {i, j}.
    have htrans : correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i} := by
      rw [show ({i, j} : Finset (Fin d → ℤ)) = vaddFinset i {(0 : Fin d → ℤ), j - i} from by
        rw [vaddFinset_pair]
        simp [vadd_eq_add]]
      exact correlationInfinite_vaddFinset_of_translationInvariant
        (IsingModel.latticeGraph d) Λ i p hf {(0 : Fin d → ℤ), j - i}
    rw [htrans]
    -- Step 7: Set n = latticeDistance d 0 (j - i) = latticeDistance d i j.
    have hdist : IsingModel.latticeDistance d i j = IsingModel.latticeDistance d 0 (j - i) := by
      unfold IsingModel.latticeDistance
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Pi.zero_apply, zero_sub, Pi.sub_apply]
      congr 1; ring
    set n := IsingModel.latticeDistance d 0 (j - i) with hn_def
    -- n ≥ 1 since i ≠ j implies j - i ≠ 0.
    have hjmi_ne : j - i ≠ 0 := fun h => hij (by
      have : j = i + (j - i) := by abel
      rw [h, add_zero] at this; exact this.symm)
    have hn_pos : 0 < n := by
      rw [hn_def, Nat.pos_iff_ne_zero]
      simp only [ne_eq, IsingModel.latticeDistance_eq_zero_iff]
      exact fun h => hjmi_ne h.symm
    -- Step 8: Set k = n / s, then k * s ≤ n.
    set k := n / s with hk_def
    have hk_le : k * s ≤ n := Nat.div_mul_le_self n s
    -- Step 9: Apply shellSup_iterated_bound to get corr∞{0, j-i} ≤ α^k.
    have hshell_le : correlationInfinite (IsingModel.latticeGraph d) Λ p
        {(0 : Fin d → ℤ), j - i} ≤ α ^ k := by
      rw [hα_def]
      have h_iter := shellSup_iterated_bound d hd R Λ p hf hh hα_lt_one k n hk_le
      apply le_trans _ h_iter
      -- corr∞{0, j-i} is a term in the iSup at shell level n.
      apply le_ciSup_of_le (shellSup_bddAbove d n Λ p)
        ⟨j - i, le_refl n, hjmi_ne⟩
      -- The value at ⟨j-i, ...⟩ is corr∞{0, j-i}: proved by le_refl.
      exact le_refl _
    -- Step 10: Apply pow_div_le_inv_mul_exp to bound α^k ≤ C * exp(-m * n).
    have hαk_le : α ^ k ≤ C * Real.exp (-m * n) := by
      have hpow := pow_div_le_inv_mul_exp α hα_pos hα_lt_one s hs_pos n
      -- pow_div_le_inv_mul_exp gives: α^(n/s) ≤ (1/α) * exp(log α / s * n)
      -- We have k = n/s and C = 1/α and -m * n = log α / s * n.
      rw [← hk_def] at hpow
      rw [hC_def, hm_def]
      have heq : -(-Real.log α / (s : ℝ)) * n = Real.log α / s * n := by
        ring
      rw [heq]
      exact hpow
    -- Step 11: Combine: corr∞{0, j-i} ≤ α^k ≤ C * exp(-m * n) = C * exp(-m * dist(i,j)).
    calc correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i}
        ≤ α ^ k := hshell_le
      _ ≤ C * Real.exp (-m * n) := hαk_le
      _ = C * Real.exp (-m * (IsingModel.latticeDistance d i j : ℝ)) := by rw [← hdist]

end Ambient

end IsingModel
