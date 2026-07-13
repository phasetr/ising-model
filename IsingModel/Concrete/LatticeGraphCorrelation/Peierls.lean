import IsingModel.PeierlsInfinite

/-!
# Concrete Peierls wrappers for the lattice graph

This module contains thin ℤ^d forwarders for the along-exhaustion Peierls
bounds from `IsingModel.PeierlsInfinite`.
-/

namespace IsingModel

namespace Ambient

/-! #### GJ §5.4 Prop 5.4.2 along-exhaustion wrappers (Peierls)

Direct ℤ^d forwarders for `prop_5_4_2_along_exhaustion` and
`prop_5_4_2_limsup_le` from `IsingModel/PeierlsInfinite.lean`, at the
ambient `latticeGraph d` on an arbitrary `Ambient.Exhaustion (Fin d → ℤ)`.
The caller supplies stage-wise `Preconnected` + `Fintype G_n.edgeSet`
instances and the geometric choice of `B n`, `i n`, and the exponential
bound hypothesis; the `DecidableRel (inducedGraph …).Adj` instance
required by the abstract theorems is supplied via `classical` in the
proof body (so it does not appear in the wrapper signatures). -/

/-- **ℤ^d GJ §5.4 Prop 5.4.2 per-stage along-exhaustion**
(Λ-induced): pointwise Peierls bound at every stage of the exhaustion.
Thin pass-through of `IsingModel.prop_5_4_2_along_exhaustion`; the
proof uses `classical` to supply the stage-wise
`DecidableRel (inducedGraph …).Adj` instance without exposing it in
the type. -/
theorem prop_5_4_2_along_exhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (hconn : ∀ n, (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _))
    (hB : ∀ n, (B n).Nonempty)
    (i : ∀ n, (↑(Λ.volume n) : Type _))
    (hexp : ∀ n,
      2 * ((2 : ℝ) ^ Fintype.card (↑(Λ.volume n) : Type _)) *
          Real.exp (-2 * β * J) ≤
        Real.exp (-c * β)) :
    ∀ n,
      0 ≤ 1 - IsingModel.plusGibbsExpectation
              (Ambient.inducedGraph
                (IsingModel.latticeGraph d) (Λ.volume n))
              ⟨J, 0, β⟩ (B n) (fun σ => IsingModel.Spin.sign ℝ (σ (i n))) ∧
      1 - IsingModel.plusGibbsExpectation
            (Ambient.inducedGraph
              (IsingModel.latticeGraph d) (Λ.volume n))
            ⟨J, 0, β⟩ (B n) (fun σ => IsingModel.Spin.sign ℝ (σ (i n))) ≤
        Real.exp (-c * β) := by
  classical
  exact IsingModel.prop_5_4_2_along_exhaustion
    (IsingModel.latticeGraph d) Λ hconn J β c hβ hJ B hB i hexp

/-- **ℤ^d GJ §5.4 Prop 5.4.2 limsup bound** (Λ-induced): the
`Filter.limsup` at `atTop` of the `n ↦ 1 − plusGibbsExpectation`
sequence is bounded above by `exp(-c·β)`. Thin pass-through of
`IsingModel.prop_5_4_2_limsup_le`; proof uses `classical` to supply
the stage-wise `DecidableRel` instance without exposing it in the
type. -/
theorem prop_5_4_2_limsup_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (hconn : ∀ n, (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _))
    (hB : ∀ n, (B n).Nonempty)
    (i : ∀ n, (↑(Λ.volume n) : Type _))
    (hexp : ∀ n,
      2 * ((2 : ℝ) ^ Fintype.card (↑(Λ.volume n) : Type _)) *
          Real.exp (-2 * β * J) ≤
        Real.exp (-c * β)) :
    Filter.limsup
      (fun n : ℕ =>
        1 - IsingModel.plusGibbsExpectation
              (Ambient.inducedGraph
                (IsingModel.latticeGraph d) (Λ.volume n))
              ⟨J, 0, β⟩ (B n) (fun σ => IsingModel.Spin.sign ℝ (σ (i n))))
      Filter.atTop ≤ Real.exp (-c * β) := by
  classical
  exact IsingModel.prop_5_4_2_limsup_le
    (IsingModel.latticeGraph d) Λ hconn J β c hβ hJ B hB i hexp

end Ambient
end IsingModel
