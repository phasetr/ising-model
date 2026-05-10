import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.FreeEnergy

/-!
# Concrete finite-volume energy closed forms and direct graph wrappers

Narrow child module for concrete `latticeGraph` finite-volume Hamiltonian
closed-form wrappers, direct finite-volume energy / partition / free-energy
bounds, and base spin-product helper wrappers. The theorem names are the same
as the former legacy declarations, but callers can now avoid importing the
monolithic concrete legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume Hamiltonian closed forms -/

/-- **ℤ^d hamiltonianΛ at `J = 0`** (Λ-induced subgraph): the Hamiltonian
reduces to `-h · Σ sign σ`. -/
theorem hamiltonianΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = -h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-- **ℤ^d hamiltonianΛ at zero parameters** (Λ-induced subgraph):
`H_Λ ⟨0, 0, β⟩ σ = 0`. -/
theorem hamiltonianΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) σ = 0 :=
  IsingModel.hamiltonian_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β σ

/-- **ℤ^d hamiltonianΛ equals `⊥`-hamiltonian at `J = 0`** (Λ-induced subgraph):
at `J = 0` the Hamiltonian is graph-independent. -/
theorem hamiltonianΛ_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) σ :=
  IsingModel.hamiltonian_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-! ### Hamiltonian / Z bound / `J = 0` closed-form wrappers -/

/-- **ℤ^d boltzmannWeight_pos direct** (Λ-induced): `0 < w(σ)` pointwise.
Thin pass-through of `IsingModel.boltzmannWeight_pos`. -/
theorem boltzmannWeight_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    0 < IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.boltzmannWeight_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-- **ℤ^d hamiltonian_abs_le direct** (Λ-induced):
`|H(σ)| ≤ |J| · |E(latticeGraph d)|_Λ + |h| · |Λ|`. Thin pass-through of
`IsingModel.hamiltonian_abs_le`. Finite-volume energy bound (GJ §10.3). -/
theorem hamiltonian_abs_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ|
      ≤ |p.J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        + |p.h| * Fintype.card (↑Λ : Type _) :=
  IsingModel.hamiltonian_abs_le
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-- **ℤ^d partitionFunction_upper direct** (Λ-induced):
`Z ≤ 2^|Λ| · exp(|β|·(|J|·|E|_Λ + |h|·|Λ|))` (GJ §10.3, Cor 10.3.2).
Thin pass-through of `IsingModel.partitionFunction_upper`. -/
theorem partitionFunction_upper_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|p.β| *
            (|p.J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |p.h| * Fintype.card (↑Λ : Type _))) :=
  IsingModel.partitionFunction_upper
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d partitionFunction_lower direct** (Λ-induced):
`exp(-|β|·(|J|·|E|_Λ + |h|·|Λ|)) ≤ Z`. Thin pass-through of
`IsingModel.partitionFunction_lower`. -/
theorem partitionFunction_lower_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    Real.exp (-(|p.β| *
        (|p.J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          + |p.h| * Fintype.card (↑Λ : Type _))))
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_lower
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d freeEnergy_upper_bound direct** (Λ-induced, nonempty `Λ`):
`f ≤ log 2 + |β|·(|J|·|E|_Λ + |h|·|Λ|) / |Λ|` (GJ §10.3). Thin
pass-through of `IsingModel.freeEnergy_upper_bound`. -/
theorem freeEnergy_upper_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      ≤ Real.log 2 +
          |p.β| *
            (|p.J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |p.h| * Fintype.card (↑Λ : Type _))
          / Fintype.card (↑Λ : Type _) :=
  IsingModel.freeEnergy_upper_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hne

/-- **ℤ^d hamiltonian_J_zero direct** (Λ-induced): at `J = 0`,
`H = -h · ∑ sign(σ_i)`. Thin pass-through of
`IsingModel.hamiltonian_J_zero`. -/
theorem hamiltonian_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = -h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-! ### Hamiltonian spin-flip, `J = 0` graph-independence, and spinProduct helpers -/

/-- **ℤ^d hamiltonian_flip_eq direct** (Λ-induced, `h = 0`): at `h = 0`
the Hamiltonian is invariant under global spin flip. Thin pass-through
of `IsingModel.hamiltonian_flip_eq`. -/
theorem hamiltonian_flip_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hp : p.h = 0)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ.flip
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.hamiltonian_flip_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hp σ

/-- **ℤ^d hamiltonian_neg_h direct** (Λ-induced): the `h → -h` reflection
corresponds to the global spin flip:
`H(σ; J, -h, β) = H(σ.flip; J, h, β)`. Thin pass-through of
`IsingModel.hamiltonian_neg_h`. -/
theorem hamiltonian_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) σ.flip :=
  IsingModel.hamiltonian_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β σ

/-- **ℤ^d hamiltonian_zero_params direct** (Λ-induced): at `J = h = 0`,
`H = 0`. Thin pass-through of `IsingModel.hamiltonian_zero_params`. -/
theorem hamiltonian_zero_params_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) σ = 0 :=
  IsingModel.hamiltonian_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β σ

/-- **ℤ^d hamiltonian_eq_bot_at_J_zero direct** (Λ-induced):
at `J = 0` the Hamiltonian coincides with the one on the edgeless graph
`⊥`. Thin pass-through of `IsingModel.hamiltonian_eq_bot_at_J_zero`. -/
theorem hamiltonian_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) σ :=
  IsingModel.hamiltonian_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-- **ℤ^d partitionFunction_eq_bot_at_J_zero direct** (Λ-induced):
`Z_G ⟨0, h, β⟩ = Z_⊥ ⟨0, h, β⟩`. Thin pass-through of
`IsingModel.partitionFunction_eq_bot_at_J_zero`. -/
theorem partitionFunction_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d correlation_eq_bot_at_J_zero direct** (Λ-induced):
`⟨σ^A⟩_G = ⟨σ^A⟩_⊥` at `J = 0`. Thin pass-through of
`IsingModel.correlation_eq_bot_at_J_zero`. -/
theorem correlation_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β A

/-- **ℤ^d spinProduct_singleton direct** (Λ-induced):
`spinProduct {i} σ = sign(σ_i)`. Thin pass-through of
`IsingModel.spinProduct_singleton`. -/
theorem spinProduct_singleton_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (i : (↑Λ : Type _))
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct ({i} : Finset (↑Λ : Type _)) σ
      = ((σ i).toSign : ℝ) :=
  IsingModel.spinProduct_singleton i σ

/-- **ℤ^d spinProduct_union direct** (Λ-induced): for disjoint
`A, B : Finset (↑Λ)`, `spinProduct (A ∪ B) = spinProduct A · spinProduct B`.
Thin pass-through of `IsingModel.spinProduct_union`. -/
theorem spinProduct_union_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {A B : Finset (↑Λ : Type _)} (hAB : Disjoint A B)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct (A ∪ B) σ
      = IsingModel.spinProduct A σ * IsingModel.spinProduct B σ :=
  IsingModel.spinProduct_union hAB σ

/-- **ℤ^d spinProduct_sq direct** (Λ-induced):
`(spinProduct A σ)^2 = 1` since each factor is `±1`. Thin pass-through
of `IsingModel.spinProduct_sq`. -/
theorem spinProduct_sq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (A : Finset (↑Λ : Type _))
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct A σ ^ 2 = 1 :=
  IsingModel.spinProduct_sq A σ

end Ambient
end IsingModel
