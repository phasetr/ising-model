import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularity

/-!
# Concrete magnetization regularity wrappers

Narrow child module for concrete finite-stage magnetization `Continuous` and
`Differentiable` wrappers on the lattice graph. The theorem names are the same
as the former legacy declarations, but callers can now avoid importing the
monolithic concrete legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### magnetization regularity ℤ^d wraps -/

/-- **ℤ^d Λ: magnetization Continuous in `h`**. -/
theorem magnetizationΛ_latticeGraph_continuous_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.magnetizationΛ_continuous_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: magnetization Differentiable in `h`**. -/
theorem magnetizationΛ_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun h' =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.magnetizationΛ_differentiable_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: magnetization Continuous in `J`**. -/
theorem magnetizationΛ_latticeGraph_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.magnetizationΛ_continuous_J
    (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d Λ: magnetization Differentiable in `J`**. -/
theorem magnetizationΛ_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun J' =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.magnetizationΛ_differentiable_J
    (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d along-ex: magnetization Continuous in `h`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_field
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex: magnetization Differentiable in `h`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_field
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex: magnetization Continuous in `J`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_J
    (IsingModel.latticeGraph d) Λ h β i n

/-- **ℤ^d along-ex: magnetization Differentiable in `J`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_J
    (IsingModel.latticeGraph d) Λ h β i n

/-! ### ℤ^d along-ex `magnetizationAlongExhaustion` β-direction
Continuous/Differentiable wrappers (general h) -/

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` Continuous in β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_beta
    (IsingModel.latticeGraph d) Λ J h i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` Differentiable in β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_beta
    (IsingModel.latticeGraph d) Λ J h i n

end Ambient
end IsingModel
