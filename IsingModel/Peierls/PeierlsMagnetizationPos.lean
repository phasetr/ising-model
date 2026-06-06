import IsingModel.Peierls.PeierlsLiminf

/-!
# Positivity of the spontaneous magnetization (FV §3.7.2)

When the low-temperature tail is small enough — `2·32 q / (1 - 32 q) < 1`, i.e. `β` large — the
infinite-volume Peierls bound `1 - μ⁺(σ_i) ≤ 2·32 q / (1 - 32 q)` forces the genuine `+`-state
magnetization to be **positive**. This is the Peierls phase transition: spontaneous magnetization
`m*(β) > 0` at low temperature (`β c < ∞`), modulo the per-stage single-orbit input.

* `peierls_plusGibbsLiminf_pos` — `0 < μ⁺(σ_i)`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset Filter Topology

open scoped Classical in
/-- **Positivity of the spontaneous magnetization** (FV §3.7.2 phase transition): if the
low-temperature tail `2·32 q / (1 - 32 q) < 1` (large `β`), the genuine `+`-state magnetization is
positive. -/
theorem peierls_plusGibbsLiminf_pos
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
    (hr0 : 0 < 32 * Real.exp (-2 * β * J)) (hr1 : 32 * Real.exp (-2 * β * J) < 1)
    (hsmall : 2 * (32 * Real.exp (-2 * β * J) / (1 - 32 * Real.exp (-2 * β * J))) < 1) :
    0 < plusGibbsExpectationLiminf (latticeGraph 2) Λ (⟨J, 0, β⟩ : IsingParams ℝ) B
          (fun n σ => Spin.sign ℝ (σ (i n))) := by
  have hbound := peierls_plusGibbsLiminf_le Λ Λd J β B i g hpre hBconn hgB hdual hne hone hr0 hr1
  linarith

end IsingModel
