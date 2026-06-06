import IsingModel.Peierls.PeierlsPlusGibbs
import IsingModel.Peierls.PlusGibbsSign
import IsingModel.Peierls.PlusGibbsMono
import IsingModel.Peierls.LiminfBound
import IsingModel.PeierlsInfinite

/-!
# The infinite-volume Peierls magnetization bound (FV §3.7.2)

Pushing the volume-independent finite-volume Peierls bound (`peierls_plusGibbs_le`) through the
infinite-volume liminf (`one_sub_liminf_le`), the genuine `+`-state magnetization
`plusGibbsExpectationLiminf(σ_i)` satisfies `1 - μ⁺(σ_i) ≤ 2·32 q / (1 - 32 q)`, `q = exp(-2βJ)`,
in the low-temperature regime `32 q < 1`. As `β → ∞` the right side vanishes, so `μ⁺(σ_i) → 1`: the
spontaneous magnetization is positive — `m*(β) > 0`, the Peierls phase transition. This replaces the
volume-dependent count of `prop_5_4_2_plusGibbsExpectationLiminf_bound` with the
volume-independent contour count built this issue.

* `peierls_plusGibbsLiminf_le` — `1 - μ⁺(σ_i) ≤ 2·32 q / (1 - 32 q)`.

The single-orbit (discrete Jordan) input enters only through the per-stage `hone`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset Filter Topology

open scoped Classical in
/-- **The infinite-volume Peierls magnetization bound**: under per-stage neighbour-closure,
dual-support, and single-orbit hypotheses for the boxes `Λ.volume n`, the genuine `+`-state
magnetization satisfies `1 - μ⁺(σ_i) ≤ 2·32 q / (1 - 32 q)`. -/
theorem peierls_plusGibbsLiminf_le
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
    (hone : ∀ n, ∀ S ∈ Finset.univ.filter (fun S : Finset (↑(Λ.volume n) : Type _) =>
        i n ∈ S ∧ Disjoint S (B n) ∧
          IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) (Λ.volume n)) (g n) S),
      ∀ d e : BoundaryDart (S.image Subtype.val), d.SameOrbit e)
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
    have hbound := peierls_plusGibbs_le (Λd := Λd n) (hpre n) J β (B n) (i n) (g n)
      (hBconn n) (hgB n) (hdual n) (hne n) (hone n) hr0 hr1
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

end IsingModel
