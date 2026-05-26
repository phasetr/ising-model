import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Disconnection

/-!
# Theorem eta-le-1 split — Phases 2-4 lattice ball defs, polynomial decay, ball-boundary axiom

Part of the split eta<=1 polynomial-to-exponential decay layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

/-- **Cardinality bound for `latticeBallBoundaryEdges`**: the ball-boundary edge
set has at most as many edges as the induced graph on the cube `cubicBox d (r+1)`,
since it is a filtered image of that graph's edge finset.

This bounds the size of the separating surface `E₀` in the ball-boundary
Simon--Lieb inequality by the (polynomially-growing) edge count of the cube,
the input needed to control the contraction factor (Issue #2931, Phase 3a). -/
theorem latticeBallBoundaryEdges_card_le (d r : ℕ) :
    (latticeBallBoundaryEdges d r).card
      ≤ (inducedGraph (IsingModel.latticeGraph d)
          (cubicBox d (r + 1))).edgeFinset.card := by
  classical
  refine le_trans (Finset.card_filter_le _ _) ?_
  exact Finset.card_image_le

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


end Ambient
end IsingModel
