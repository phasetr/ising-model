import IsingModel.Peierls.PeierlsContourCountPow
import IsingModel.Conditioning.CountGeometricCapstone

/-!
# The Peierls low-temperature droplet sum (FV §3.7.2)

Feeding the `32^ℓ` contour count (`peierls_contour_count_pow`) into the geometric tail estimate
(`sum_pow_le_geometric_tail_of_count`), the Peierls droplet sum
`∑_S exp(-2βJ · |cutEdges S|)` is bounded by `(32 q)^n / (1 - 32 q)` with `q = exp(-2βJ)`, whenever
`32 q < 1` (the low-temperature regime). As `β → ∞` this tail vanishes (for `n ≥ 1`), giving
`m*(β) > 0`.

* `peierls_sum_le` — the geometric tail bound on the droplet sum.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The Peierls droplet sum is geometrically small at low temperature**: for `q = exp(-2βJ)` with
`32 q < 1`, the sum `∑_S exp(-2βJ · |cut S|)` over single-orbit box droplets is at most
`(32 q)^n / (1 - 32 q)`, where `n` lower-bounds the cut sizes. -/
theorem peierls_sum_le {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {g : ↑Λ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hone : ∀ S ∈ D, ∀ d e : BoundaryDart (S.image Subtype.val), d.SameOrbit e)
    {β J : ℝ} (n : ℕ)
    (hge : ∀ S ∈ D, n ≤ (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card)
    (hr0 : 0 < 32 * Real.exp (-2 * β * J)) (hr1 : 32 * Real.exp (-2 * β * J) < 1) :
    ∑ S ∈ D, Real.exp (-2 * β * J * ↑(cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card)
      ≤ (32 * Real.exp (-2 * β * J)) ^ n / (1 - 32 * Real.exp (-2 * β * J)) := by
  classical
  set G := Ambient.inducedGraph (latticeGraph 2) Λ with hGdef
  have hexp : ∀ S : Finset ↑Λ,
      Real.exp (-2 * β * J * ↑(cutEdges G S).card)
      = Real.exp (-2 * β * J) ^ (cutEdges G S).card := by
    intro S
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [Finset.sum_congr rfl (fun S _ => hexp S)]
  have hbound := sum_pow_le_geometric_tail_of_count D
    (fun S => (cutEdges G S).card) (q := Real.exp (-2 * β * J))
    (Real.exp_nonneg _) (M := 32) n hge
    (fun ℓ => peierls_contour_count_pow hpre D hdual hi hne hg hone ℓ)
    (by exact_mod_cast hr0) (by exact_mod_cast hr1)
  refine hbound.trans (le_of_eq ?_)
  norm_num

end IsingModel
