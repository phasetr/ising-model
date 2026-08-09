import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d positivity of the infinite-volume free-energy density

Instantiates at `IsingModel.latticeGraph d` the strict positivity and the nonnegativity of
`freeEnergyInfinite`, which is the `limsup` of the finite-volume free-energy densities along
an exhaustion rather than a limit. Along an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ` the
statements carry, besides the ferromagnetic hypothesis on the parameter record and
the instance `Nonempty (Fin d → ℤ)`, a hypothesis bounding the stage edge count linearly by
the stage vertex count; along `Ambient.cubicExhaustion d` that hypothesis is discharged by
`inducedLatticeGraph_card_edgeFinset_le`, so only the ferromagnetic hypothesis and the
nonemptiness instance remain.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyInfinite is strictly positive** (ferromagnetic). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_pos
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 < freeEnergyInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_pos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d freeEnergyInfinite is nonnegative** (ferromagnetic). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_pos d p hf).le

/-- **ℤ^d freeEnergyInfinite strictly positive** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_pos
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 < freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_pos (IsingModel.latticeGraph d) Λ p hf (c := c) hc

/-- **ℤ^d freeEnergyInfinite nonnegative** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_nonneg
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  (freeEnergyInfinite_latticeGraph_pos d Λ p hf hc).le

end Ambient
end IsingModel
