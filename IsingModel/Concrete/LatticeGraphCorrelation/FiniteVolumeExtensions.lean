import IsingModel.Lattice
import IsingModel.AmbientLattice.Monotonicity.Factoring

/-!
# Concrete finite-volume extension wrappers

Thin `ℤ^d` specializations of finite-volume extension graph wrappers used by
the Lambda-layer correlation monotonicity API.  Import this module directly
when only the extension graph comparison/equality wrappers are needed.
-/

namespace IsingModel

namespace Ambient

/-! ## Finite-volume extension wrappers -/

/-- **ℤ^d extendGraphFromΛ₁_le_induce**:
`extendGraphFromΛ₁ (latticeGraph d) Λ₁ Λ₂ ≤ inducedGraph (latticeGraph d) Λ₂`. -/
theorem extendGraphFromΛ₁_le_induce_latticeGraph
    (d : ℕ) (Λ₁ Λ₂ : Finset (Fin d → ℤ)) :
    Ambient.extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂
      ≤ Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂ :=
  Ambient.extendGraphFromΛ₁_le_induce (IsingModel.latticeGraph d) Λ₁ Λ₂

/-- **ℤ^d correlationΛ_extendGraph_eq**: correlation equality between
the extended graph and the induced Λ₁ subgraph. -/
theorem correlationΛ_latticeGraph_extendGraph_eq
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.extendGraphFromΛ₁
      (IsingModel.latticeGraph d) Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} (hA : A ⊆ Λ₁) :
    IsingModel.correlation
        (Ambient.extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂) p
        (Ambient.liftFinset A (hA.trans h12))
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁) p
          (Ambient.liftFinset A hA) :=
  Ambient.correlationΛ_extendGraph_eq (IsingModel.latticeGraph d) h12 p hA

end Ambient

end IsingModel
