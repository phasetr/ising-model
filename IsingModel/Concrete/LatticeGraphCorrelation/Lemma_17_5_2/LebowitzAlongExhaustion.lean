import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CorrelationAlongExhaustionDeriv

/-!
# Lebowitz β-derivative bound on `correlationAlongExhaustion` at ℤ^d

This module composes the per-stage Lebowitz β-derivative bound for the induced
lattice graph (`inducedLatticeGraph_beta_deriv_le`, Step 157 in
`LatticeMassLebowitzDerivative.lean`) with the covered-stage
`HasDerivAt` transfer (`hasDerivAt_correlationAlongExhaustion_of_hasDerivAt_inducedGraph`,
PR #3143 in `CorrelationAlongExhaustionDeriv.lean`) to yield the Lebowitz
β-derivative bound on `correlationAlongExhaustion` in the volume coverage
regime.

This is the per-stage real-axis input for Issue #2965 Phase C: the alternative
route to the Lemma 17.5.2 β-derivative increment bound bypassing the CE /
Cauchy decomposition entirely.

References:

* Glimm-Jaffe, *Quantum Physics* (2nd ed.), §17.5, Cor. 4.3.3 (Lebowitz),
  pp. 311-312.
* Issue #2965 (Phase C: real-axis Lebowitz route).
-/

namespace IsingModel
namespace Ambient

variable {d : ℕ}

/-- **Lebowitz β-derivative bound on `correlationAlongExhaustion`** at the
induced lattice subgraph of ℤ^d (Issue #2965 Phase C, real-axis Lebowitz
route).

Given a covered pair `{r, s} ⊆ Λ.volume n`, the β-derivative of the family
`fun β' => correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β'⟩ {r, s} n`
at any `β > 0` exists and is bounded by the standard Lebowitz edge sum on
the induced subgraph plus the uniform `J · 4d` boundary correction:

    ∂_β c_n ≤ J · ∑_{e ∈ E(G_n)} [c_n(r,u)·c_n(s,v) + c_n(r,v)·c_n(s,u)]
            + J · 4d

where `c_n(·, ·) := correlation (inducedGraph (latticeGraph d) (Λ.volume n)) ⟨J,0,β⟩ {·, ·}`.

Composes `inducedLatticeGraph_beta_deriv_le` (Step 157) with
`hasDerivAt_correlationAlongExhaustion_of_hasDerivAt_inducedGraph` (PR #3143). -/
theorem correlationAlongExhaustion_latticeGraph_beta_deriv_le
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    ∃ dval : ℝ,
      HasDerivAt
        (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s} n) dval β ∧
      dval ≤ J * ∑ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), u} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), v} +
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), v} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), u},
              fun u v => by ring⟩ e
          + J * (4 * ↑d) := by
  classical
  have hrs_sub_subtypes :
      (⟨r, hr⟩ : ↑(Λ.volume n)) ≠ ⟨s, hs⟩ := fun heq =>
    hrs (congrArg Subtype.val heq)
  obtain ⟨dval, hd_ind, hbound⟩ :=
    inducedLatticeGraph_beta_deriv_le (Λ.volume n) J β hJ hβ
      (⟨r, hr⟩ : ↑(Λ.volume n)) ⟨s, hs⟩ hrs_sub_subtypes
  -- The induced-graph derivative HasDerivAt lifts to correlationAlongExhaustion
  -- via PR #3143's transfer, using that liftFinset {r, s} hrs_sub = {⟨r, hr⟩, ⟨s, hs⟩}.
  refine ⟨dval, ?_, hbound⟩
  have h_lift :
      Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub
        = ({(⟨r, hr⟩ : ↑(Λ.volume n)), ⟨s, hs⟩} : Finset ↑(Λ.volume n)) :=
    Ambient.liftFinset_pair hrs_sub hr hs
  have h_ind' : HasDerivAt
      (fun β' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β'⟩ : IsingParams ℝ)
        (Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub)) dval β := by
    rw [show (fun β' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β'⟩ : IsingParams ℝ)
        (Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub)) =
      (fun β' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β'⟩ : IsingParams ℝ)
        ({(⟨r, hr⟩ : ↑(Λ.volume n)), ⟨s, hs⟩} : Finset ↑(Λ.volume n)))
      from funext (fun β' => by rw [h_lift])]
    exact hd_ind
  exact hasDerivAt_correlationAlongExhaustion_of_hasDerivAt_inducedGraph
    (IsingModel.latticeGraph d) Λ J 0 ({r, s} : Finset (Fin d → ℤ)) n hrs_sub h_ind'

end Ambient
end IsingModel
