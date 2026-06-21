import IsingModel.Peierls.PeierlsMagnetizationPos
import IsingModel.Peierls.PeierlsContourCountFilled

/-!
# Unconditional positivity of the spontaneous magnetization (FV §3.7.2)

With the filled-droplet Peierls sum unconditional (`peierls_sum_le_filled`), the down-spin
probability bound, the infinite-volume magnetization bound, and the positivity of the spontaneous
magnetization no longer need the single-orbit hypothesis `hone`: the connectedness
(`IsConnectedDroplet`) and filledness (`IsFilled`) of the droplets entering the Peierls sum are
already part of the index filter, so they are supplied for free from filter membership.

This completes the FV §3.7.2 low-temperature Peierls argument: at low temperature the genuine
`+`-state magnetization `m*(β) > 0`, with the only remaining inputs the box-geometry bookkeeping
(`hpre`, `hBconn`, `hgB`, `hdual`, `hne`) — not the discrete-Jordan single-orbit hypothesis.

* `peierls_plusGibbs_le_filled` — `μ⁺_Λ(σ_i = -1) ≤ 32 q / (1 - 32 q)`, no `hone`.
* `peierls_plusGibbsLiminf_le_filled` — `1 - μ⁺(σ_i) ≤ 2·32 q / (1 - 32 q)`, no `hone`.
* `peierls_plusGibbsLiminf_pos_filled` — `0 < μ⁺(σ_i)` (Peierls phase transition), no `hone`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset Filter Topology

open Classical in
/-- **The finite-volume Peierls bound without the single-orbit hypothesis**: for a connected
boundary `B ∋ g` of the box `Λ` and a site `i`, the `+`-state probability of `σ_i = -1` is at most
`32 q / (1 - 32 q)` (`q = exp(-2βJ)`, `32 q < 1`), provided every relevant filled connected droplet
is neighbour-closed and has dual support in `Λd`. The connectedness and filledness needed for the
unconditional filled contour count come for free from the index filter. -/
theorem peierls_plusGibbs_le_filled {Λ Λd : Finset (Fin 2 → ℤ)}
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
  have hconn : ∀ S ∈ D, IsConnectedDroplet G S := fun S hS =>
    (Finset.mem_filter.mp hS).2.2.2.1
  have hfill : ∀ S ∈ D, IsFilled G g S := fun S hS => (Finset.mem_filter.mp hS).2.2.2.2
  have hge : ∀ S ∈ D, 1 ≤ (cutEdges G S).card := by
    intro S hS
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2.1
    have hneV : S ≠ Finset.univ := fun h => (hg S hS) (h ▸ Finset.mem_univ g)
    exact (cutEdges_nonempty_of_connected G hpre S ⟨i, hiS⟩ hneV).card_pos
  have hsum := peierls_sum_le_filled (i := (↑i : Fin 2 → ℤ)) hpre D hdual
    (fun S hS => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hS).2.1)
    hne hg hconn hfill 1 hge hr0 hr1
  rw [pow_one] at hsum
  exact hsum

open scoped Classical in
/-- **The infinite-volume Peierls magnetization bound without the single-orbit hypothesis**: under
per-stage neighbour-closure and dual-support hypotheses for the boxes `Λ.volume n`, the genuine
`+`-state magnetization satisfies `1 - μ⁺(σ_i) ≤ 2·32 q / (1 - 32 q)`. -/
theorem peierls_plusGibbsLiminf_le_filled
    (Λ : Ambient.Exhaustion (Fin 2 → ℤ))
    [∀ n, DecidableRel (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)).Adj]
    [∀ n, Fintype (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)).edgeSet]
    (Λd : ℕ → Finset (Fin 2 → ℤ)) (J β : ℝ)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _)) (i g : ∀ n, (↑(Λ.volume n) : Type _))
    (hpre : ∀ n, (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)).Preconnected)
    (hBconn : ∀ n,
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (B n))
    (hgB : ∀ n, g n ∈ B n)
    (hdual : ∀ n, ∀ S ∈ Finset.univ.filter (fun S : Finset (↑(Λ.volume n) : Type _) =>
        i n ∈ S ∧ Disjoint S (B n) ∧
          IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (g n) S),
      dualSupport (S.image Subtype.val) ⊆ Λd n)
    (hne : ∀ n, ∀ S ∈ Finset.univ.filter (fun S : Finset (↑(Λ.volume n) : Type _) =>
        i n ∈ S ∧ Disjoint S (B n) ∧
          IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (g n) S),
      NeighbourClosed (Λ.volume n) S)
    (hr0 : 0 < 32 * Real.exp (-2 * β * J)) (hr1 : 32 * Real.exp (-2 * β * J) < 1) :
    1 - plusGibbsExpectationLiminf (latticeGraph 2) Λ (⟨J, 0, β⟩ : IsingParams ℝ) B
          (fun n σ => Spin.sign ℝ (σ (i n)))
      ≤ 2 * (32 * Real.exp (-2 * β * J) / (1 - 32 * Real.exp (-2 * β * J))) := by
  have hper : ∀ n, 1 - plusGibbsExpectation (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) (B n) (fun σ => Spin.sign ℝ (σ (i n)))
      ≤ 2 * (32 * Real.exp (-2 * β * J) / (1 - 32 * Real.exp (-2 * β * J))) := by
    intro n
    have hsign := plusGibbsExpectation_sign_eq
      (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (⟨J, 0, β⟩ : IsingParams ℝ) (B n) (i n)
    have hbound := peierls_plusGibbs_le_filled (Λd := Λd n) (hpre n) J β (B n) (i n) (g n)
      (hBconn n) (hgB n) (hdual n) (hne n) hr0 hr1
    rw [hsign, sub_sub_cancel]
    have hb' : plusGibbsExpectation (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) (B n) (fun σ => if σ (i n) = Spin.down then (1 : ℝ) else 0)
        ≤ 32 * Real.exp (-2 * β * J) / (1 - 32 * Real.exp (-2 * β * J)) := by
      convert hbound using 3
    gcongr
  have hub : ∀ n, plusGibbsExpectation (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) (B n) (fun σ => Spin.sign ℝ (σ (i n))) ≤ 1 := fun n =>
    plusGibbsExpectation_sign_le_one
      (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (⟨J, 0, β⟩ : IsingParams ℝ) (B n) (i n)
  unfold plusGibbsExpectationLiminf
  exact one_sub_liminf_le hper hub

open scoped Classical in
/-- **Unconditional positivity of the spontaneous magnetization** (FV §3.7.2 phase transition): if
the low-temperature tail `2·32 q / (1 - 32 q) < 1` (large `β`), the genuine `+`-state magnetization
is positive — `m*(β) > 0` — with no single-orbit (discrete Jordan) hypothesis, the planar bond
lemma now being discharged unconditionally. -/
theorem peierls_plusGibbsLiminf_pos_filled
    (Λ : Ambient.Exhaustion (Fin 2 → ℤ))
    [∀ n, DecidableRel (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)).Adj]
    [∀ n, Fintype (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)).edgeSet]
    (Λd : ℕ → Finset (Fin 2 → ℤ)) (J β : ℝ)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _)) (i g : ∀ n, (↑(Λ.volume n) : Type _))
    (hpre : ∀ n, (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)).Preconnected)
    (hBconn : ∀ n,
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (B n))
    (hgB : ∀ n, g n ∈ B n)
    (hdual : ∀ n, ∀ S ∈ Finset.univ.filter (fun S : Finset (↑(Λ.volume n) : Type _) =>
        i n ∈ S ∧ Disjoint S (B n) ∧
          IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (g n) S),
      dualSupport (S.image Subtype.val) ⊆ Λd n)
    (hne : ∀ n, ∀ S ∈ Finset.univ.filter (fun S : Finset (↑(Λ.volume n) : Type _) =>
        i n ∈ S ∧ Disjoint S (B n) ∧
          IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (g n) S),
      NeighbourClosed (Λ.volume n) S)
    (hr0 : 0 < 32 * Real.exp (-2 * β * J)) (hr1 : 32 * Real.exp (-2 * β * J) < 1)
    (hsmall : 2 * (32 * Real.exp (-2 * β * J) / (1 - 32 * Real.exp (-2 * β * J))) < 1) :
    0 < plusGibbsExpectationLiminf (latticeGraph 2) Λ (⟨J, 0, β⟩ : IsingParams ℝ) B
          (fun n σ => Spin.sign ℝ (σ (i n))) := by
  have hbound :=
    peierls_plusGibbsLiminf_le_filled Λ Λd J β B i g hpre hBconn hgB hdual hne hr0 hr1
  linarith

end IsingModel
