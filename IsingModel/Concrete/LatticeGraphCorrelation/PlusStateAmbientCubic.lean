import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateExhaustion

/-!
# Ambient independence of the cubic `+` local expectation (Issue #3581)

A step towards exhaustion independence: the cubic `+` local expectation
`plusBoxLocalExpectation n (n+1) O` (free inner box `cubicBox d n`, immediate
boundary layer) is realised on **any** ambient `Ω ⊇ cubicBox d (n+1)` — the `+`
boundary expectation of `O` with the cubic inner region on `Ω` equals the natural
cubic value, by the general ambient independence
(`gibbsExpectationBC_screening_of_neighbors`) since a `cubicBox d n` site's
neighbours lie in `cubicBox d (n+1)`.

* `plusBoxLocalExpectation_eq_on_ambient` — the ambient-independent realisation.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset

variable {d : ℕ}

/-- **Ambient-independent realisation of the cubic `+` local expectation**: for any
ambient `Ω ⊇ cubicBox d (n+1)`, the `+` boundary expectation of `O` with the cubic
inner region `cubicBox d n` on `Ω` equals the natural cubic
`plusBoxLocalExpectation n (n+1) O`. -/
theorem plusBoxLocalExpectation_eq_on_ambient {n : ℕ} {Ω : Finset (Fin d → ℤ)}
    (h12 : cubicBox d (n + 1) ⊆ Ω)
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Ω).edgeSet]
    {J h β : ℝ} (O : LocalMonotoneObservable d) (hSn1 : O.S ⊆ cubicBox d (n + 1)) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) Ω) β (fun _ => J) h
        ((plusBoxInterior d n (n + 1)).map (subtypeInclEmb h12)) (plusConfig _)
        (O.lift (hSn1.trans h12))
      = plusBoxLocalExpectation n (n + 1) J h β O hSn1 := by
  unfold plusBoxLocalExpectation plusBoxExpectation
  refine gibbsExpectationBC_screening_of_neighbors h12 (plusBoxInterior d n (n + 1))
    (fun k hk y hadj => cubicBox_adj_mem_succ (mem_plusBoxInterior.mp hk) hadj)
    (O.lift (hSn1.trans h12)) (O.lift hSn1) (fun σ₁ σ₂ => ?_)
  change O.φ (restrictConfig (hSn1.trans h12) ((configEquivSubtypeProd h12).symm (σ₁, σ₂)))
    = O.φ (restrictConfig hSn1 σ₁)
  rw [restrictConfig_trans hSn1 h12, restrictConfig_configEquivSubtypeProd_symm]

end Ambient

end IsingModel
