import IsingModel.Peierls.PeierlsSum
import IsingModel.Peierls.FilledConnectedBound
import IsingModel.Peierls.Prop542

/-!
# The finite-volume Peierls bound on the down-spin probability (FV §3.7.2)

Combining the filled-connected Peierls bound (`spontaneous_magnetization_plus_filled_connected`,
which bounds the `+`-state down-spin probability by a sum over filled connected droplets) with the
geometric tail estimate on that sum (`peierls_sum_le`), the `+`-boundary probability that
`σ_i = -1` is at most `32 q / (1 - 32 q)` with `q = exp(-2βJ)`, in the low-temperature regime
`32 q < 1`. As `β → ∞` this vanishes, the finite-volume input to `m*(β) > 0`.

* `peierls_plusGibbs_le` — `μ⁺_Λ(σ_i = -1) ≤ 32 q / (1 - 32 q)`.

The single-orbit (discrete Jordan) input enters only through `hone`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset

open Classical in
/-- **The finite-volume Peierls bound**: for a connected boundary `B ∋ g` of the box `Λ` and a site
`i`, the `+`-state probability of `σ_i = -1` is at most `32 q / (1 - 32 q)` (`q = exp(-2βJ)`,
`32 q < 1`), provided every relevant filled connected droplet is neighbour-closed, has dual support
in `Λd`, and is a single boundary-dart orbit. -/
theorem peierls_plusGibbs_le {Λ Λd : Finset (Fin 2 → ℤ)}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (J β : ℝ) (B : Finset ↑Λ) (i g : ↑Λ)
    (hBconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) B) (hgB : g ∈ B)
    (hdual : ∀ S ∈ Finset.univ.filter (fun S : Finset ↑Λ =>
        i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S),
      dualSupport (S.image Subtype.val) ⊆ Λd)
    (hne : ∀ S ∈ Finset.univ.filter (fun S : Finset ↑Λ =>
        i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S),
      NeighbourClosed Λ S)
    (hone : ∀ S ∈ Finset.univ.filter (fun S : Finset ↑Λ =>
        i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S),
      ∀ d e : BoundaryDart (S.image Subtype.val), d.SameOrbit e)
    (hr0 : 0 < 32 * Real.exp (-2 * β * J)) (hr1 : 32 * Real.exp (-2 * β * J) < 1) :
    plusGibbsExpectation (Ambient.inducedGraph (latticeGraph 2) Λ) ⟨J, 0, β⟩ B
        (fun σ => if σ i = Spin.down then 1 else 0)
      ≤ 32 * Real.exp (-2 * β * J) / (1 - 32 * Real.exp (-2 * β * J)) := by
  classical
  set G := Ambient.inducedGraph (latticeGraph 2) Λ with hGdef
  set D := Finset.univ.filter (fun S : Finset ↑Λ =>
    i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S) with hDdef
  refine (spontaneous_magnetization_plus_filled_connected G hpre J β B i g hBconn hgB).trans ?_
  have hg : ∀ S ∈ D, g ∉ S := by
    intro S hS
    have hdisj : Disjoint S B := (Finset.mem_filter.mp hS).2.2.1
    exact fun hgS => (Finset.disjoint_left.mp hdisj) hgS hgB
  have hge : ∀ S ∈ D, 1 ≤ (cutEdges G S).card := by
    intro S hS
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2.1
    have hneV : S ≠ Finset.univ := fun h => (hg S hS) (h ▸ Finset.mem_univ g)
    exact (cutEdges_nonempty_of_connected G hpre S ⟨i, hiS⟩ hneV).card_pos
  have hsum := peierls_sum_le (i := (↑i : Fin 2 → ℤ)) hpre D hdual
    (fun S hS => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hS).2.1)
    hne hg hone 1 hge hr0 hr1
  rw [pow_one] at hsum
  exact hsum

end IsingModel
