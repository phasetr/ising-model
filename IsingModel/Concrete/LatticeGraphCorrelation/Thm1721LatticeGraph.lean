import IsingModel.Inequalities.Lebowitz.Thm1721
import IsingModel.AmbientLattice.Defs.Core
import IsingModel.Lattice

/-!
# ℤ^d specialisation of GJ Theorem 17.2.1 (general odd-subset bound)

Pass-through of `IsingModel.Lebowitz.thm_17_2_1` to the `Λ`-induced subgraph of the
`d`-dimensional integer lattice `latticeGraph d`, matching the existing `_latticeGraph`
wrapper convention.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), Theorem 17.2.1,
p. 305.
-/

namespace IsingModel

namespace Lebowitz

/-- **ℤ^d general odd-subset correlation bound, finite-volume** (GJ §17.2 Theorem 17.2.1,
`Λ`-induced, ferromagnetic at `h = 0`).  Pass-through of `thm_17_2_1` on
`Ambient.inducedGraph (latticeGraph d) Λ` for disjoint even-cardinality site sets. -/
theorem thm_17_2_1_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (A B : Finset (↑Λ : Type _)) (hAB : Disjoint A B)
    (hA : Even A.card) (hB : Even B.card) :
    correlation (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, 0, β⟩ (A ∪ B)
        - correlation (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, 0, β⟩ A
          * correlation (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, 0, β⟩ B
      ≤ ∑ A₁ ∈ A.powerset.filter (fun s => Odd s.card),
          ∑ B₁ ∈ B.powerset.filter (fun s => Odd s.card),
            correlation (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                ⟨J, 0, β⟩ (A₁ ∪ B₁)
              * correlation (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                  ⟨J, 0, β⟩ ((A \ A₁) ∪ (B \ B₁)) :=
  thm_17_2_1 (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hf A B hAB hA hB

end Lebowitz

end IsingModel
