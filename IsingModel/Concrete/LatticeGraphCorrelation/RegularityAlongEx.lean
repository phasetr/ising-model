import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# Concrete ℤ^d along-exhaustion `hasDerivAt` wrappers (GJ §17.5–§17.6)

Instantiates the along-exhaustion parameter derivatives of the correlation at
`IsingModel.latticeGraph d`, in the `β`, general-field `β`, `J` and field directions. Each
is stated in existence form `∃ d : ℝ, HasDerivAt _ d _`, which is what the GJ §17.5–§17.6
arguments consume.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-exhaustion `hasDerivAt` wrappers (GJ §17.5–§17.6)

Direct instantiations at `G := IsingModel.latticeGraph d` of the
along-exhaustion `hasDerivAt` family from
`AmbientLattice/BetaDerivative.lean`,
`AmbientLattice/JDerivative.lean` and
`AmbientLattice/FieldDerivative.lean`. -/

/-- **ℤ^d along-ex: `correlationAlongExhaustion` HasDerivAt in β at h = 0**. -/
theorem correlationAlongExhaustion_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) A n) c β :=
  Ambient.correlationAlongExhaustion_hasDerivAt_beta
    (IsingModel.latticeGraph d) Λ J β A n

/-- **ℤ^d along-ex: `correlationAlongExhaustion` HasDerivAt in β at general h**. -/
theorem correlationAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) A n) c β :=
  Ambient.correlationAlongExhaustion_hasDerivAt_beta_general_h_gen
    (IsingModel.latticeGraph d) Λ J h β A n

/-- **ℤ^d along-ex: `correlationAlongExhaustion` HasDerivAt in J**. -/
theorem correlationAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) A n) c J :=
  Ambient.correlationAlongExhaustion_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β A n

/-- **ℤ^d along-ex: `correlationAlongExhaustion` HasDerivAt in h**. -/
theorem correlationAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) A n) c h :=
  Ambient.correlationAlongExhaustion_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β A n

end Ambient

end IsingModel
