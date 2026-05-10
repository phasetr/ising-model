import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.AmbientLattice.Monotonicity
import IsingModel.FreeEnergy

/-!
# Concrete finite-volume basic wrappers

Narrow child module for concrete `latticeGraph` finite-volume graph, spin
algebra, bottom-graph, and Hamiltonian symmetry wrappers. The theorem names are
the same as the former legacy declarations, but callers can now avoid importing
the monolithic concrete legacy module.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume basic wrappers -/

/-- **ℤ^d inducedGraph_mono**: `G₁ ≤ G₂` lifts to `inducedGraph G₁ Λ ≤ inducedGraph G₂ Λ`. -/
theorem inducedGraph_mono_latticeGraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ)) :
    Ambient.inducedGraph G₁ Λ ≤ Ambient.inducedGraph G₂ Λ :=
  Ambient.inducedGraph_mono h Λ

/-- **ℤ^d `partitionFunction` of `⊥` at Λ**: closed form
`Z_⊥ = (2 cosh(βh))^|Λ|`. -/
theorem partitionFunction_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p
      = (2 * Real.cosh (p.β * p.h)) ^ Fintype.card (↑Λ : Type _) :=
  IsingModel.partitionFunction_bot (ι := (↑Λ : Type _)) p

/-- **ℤ^d `partitionFunction (⊥) ≥ 1`** at Λ-induced subgraph. -/
theorem partitionFunction_bot_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (1 : ℝ) ≤ IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p :=
  IsingModel.partitionFunction_bot_ge_one (ι := (↑Λ : Type _)) p

/-- **ℤ^d `partitionFunction (⊥) ≥ 2^|Λ|`** at Λ-induced subgraph. -/
theorem partitionFunction_bot_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (2 : ℝ) ^ Fintype.card (↑Λ : Type _)
      ≤ IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p :=
  IsingModel.partitionFunction_bot_ge_two_pow_card (ι := (↑Λ : Type _)) p

/-- **ℤ^d `partitionFunction_eq_bot_at_J_zero`** at Λ-induced: at `J = 0`
the partition function is graph-independent (equals the `⊥`-graph value). -/
theorem partitionFunctionΛ_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `correlation_eq_bot_at_J_zero`** at Λ-induced: at `J = 0`
the correlation is graph-independent. -/
theorem correlationΛ_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β A

/-- **ℤ^d `correlation_bot_closed`** at Λ-induced:
`⟨σ^A⟩_⊥ = tanh(β·h)^|A|`. -/
theorem correlation_bot_closed_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation (⊥ : SimpleGraph (↑Λ : Type _)) p A
      = Real.tanh (p.β * p.h) ^ A.card :=
  IsingModel.correlation_bot_closed p A

/-- **ℤ^d sum_config_spinProduct_eq_zero at Λ-induced**:
for nonempty `A`, `Σ_σ σ^A = 0`. -/
theorem sum_config_spinProduct_eq_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    ∑ σ : IsingModel.Config (↑Λ : Type _), IsingModel.spinProduct A σ = 0 :=
  IsingModel.sum_config_spinProduct_eq_zero A hA

/-- **ℤ^d sum_config_spinProduct_empty at Λ-induced**:
`Σ_σ σ^∅ = |Config ↑Λ|`. -/
theorem sum_config_spinProduct_empty_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ∑ σ : IsingModel.Config (↑Λ : Type _), IsingModel.spinProduct ∅ σ
      = (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) :=
  IsingModel.sum_config_spinProduct_empty

/-- **ℤ^d spinProduct_mul at Λ-induced**:
`σ^A · σ^C = σ^{A Δ C}`. -/
theorem spinProduct_mul_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A C : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct A σ * IsingModel.spinProduct C σ
      = IsingModel.spinProduct (symmDiff A C) σ :=
  IsingModel.spinProduct_mul A C σ

/-- **ℤ^d edgeSpin_sq at Λ-induced**: `edgeSpin σ e ^ 2 = 1`. -/
theorem edgeSpin_sq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ : IsingModel.Config (↑Λ : Type _)) (e : Sym2 (↑Λ : Type _)) :
    IsingModel.edgeSpin (K := ℝ) σ e ^ 2 = 1 :=
  IsingModel.edgeSpin_sq σ e

/-- **ℤ^d one_sub_spinProduct_nonneg at Λ-induced**: `0 ≤ 1 - σ^B`. -/
theorem one_sub_spinProduct_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (B : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    0 ≤ 1 - IsingModel.spinProduct B σ :=
  IsingModel.one_sub_spinProduct_nonneg B σ

/-- **ℤ^d abs_spinProduct_eq_one at Λ-induced**: `|σ^A| = 1`. -/
theorem abs_spinProduct_eq_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.spinProduct A σ| = 1 :=
  IsingModel.abs_spinProduct_eq_one A σ

/-- **ℤ^d abs_spinProduct_le_one at Λ-induced**: `|σ^A| ≤ 1`. -/
theorem abs_spinProduct_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.spinProduct A σ| ≤ 1 :=
  IsingModel.abs_spinProduct_le_one A σ

/-- **ℤ^d Walsh orthogonality at Λ-induced**. -/
theorem walsh_orthogonality_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (S T : Finset (↑Λ : Type _)) (hST : S ≠ T) :
    ∑ σ : IsingModel.Config (↑Λ : Type _),
      IsingModel.spinProduct S σ * IsingModel.spinProduct T σ = 0 :=
  IsingModel.walsh_orthogonality S T hST

/-- **ℤ^d Walsh completeness at Λ-induced**:
`Σ_S σ^S(σ) σ^S(τ) = card · [σ = τ]`. -/
theorem walsh_completeness_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ τ : IsingModel.Config (↑Λ : Type _)) :
    ∑ S : Finset (↑Λ : Type _),
        IsingModel.spinProduct S σ * IsingModel.spinProduct S τ
      = if σ = τ then (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) else 0 :=
  IsingModel.walsh_completeness σ τ

/-- **ℤ^d Walsh Fourier inversion at Λ-induced**:
`f(σ) = Σ_S ĉ_S σ^S` where `ĉ_S = card⁻¹ Σ_τ σ^S(τ) f(τ)`. -/
theorem walsh_fourier_inversion_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (f : IsingModel.Config (↑Λ : Type _) → ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    f σ = ∑ S : Finset (↑Λ : Type _),
      ((Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ)⁻¹
        * ∑ τ : IsingModel.Config (↑Λ : Type _),
            IsingModel.spinProduct S τ * f τ)
      * IsingModel.spinProduct S σ :=
  IsingModel.walsh_fourier_inversion f σ

/-- **ℤ^d Walsh normalization at Λ-induced**. -/
theorem walsh_normalization_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (S : Finset (↑Λ : Type _)) :
    ∑ σ : IsingModel.Config (↑Λ : Type _),
        IsingModel.spinProduct S σ * IsingModel.spinProduct S σ
      = Fintype.card (IsingModel.Config (↑Λ : Type _)) :=
  IsingModel.walsh_normalization S

/-- **ℤ^d `card_config_eq_two_pow` at Λ**:
`|Config ↑Λ| = 2^|Λ|`. -/
theorem card_config_eq_two_pow_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Fintype.card (IsingModel.Config (↑Λ : Type _))
      = 2 ^ Fintype.card (↑Λ : Type _) :=
  IsingModel.card_config_eq_two_pow

/-- **ℤ^d edgeSpin_flip at Λ-induced**:
`edgeSpin(σ.flip, e) = edgeSpin(σ, e)`. -/
theorem edgeSpin_flip_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ : IsingModel.Config (↑Λ : Type _)) (e : Sym2 (↑Λ : Type _)) :
    IsingModel.edgeSpin (K := ℝ) σ.flip e = IsingModel.edgeSpin σ e :=
  IsingModel.edgeSpin_flip σ e

/-- **ℤ^d interactionEnergy_flip at Λ-induced**:
`interactionEnergy_Λ(J, σ.flip) = interactionEnergy_Λ(J, σ)`. -/
theorem interactionEnergy_flip_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.interactionEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ.flip
      = IsingModel.interactionEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ :=
  IsingModel.interactionEnergy_flip
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ

/-- **ℤ^d hamiltonian_flip_eq at Λ-induced**: at `h = 0` the Hamiltonian
is invariant under spin flip. -/
theorem hamiltonianΛ_flip_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hp : p.h = 0)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ.flip
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.hamiltonian_flip_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hp σ

/-- **ℤ^d hamiltonian_neg_h at Λ-induced**:
`H_Λ(σ; -h) = H_Λ(σ.flip; h)`. -/
theorem hamiltonianΛ_neg_h_latticeGraph
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

/-- **ℤ^d hamiltonian_bot at Λ**: `H_⊥(σ) = -h · Σ sign σ`. -/
theorem hamiltonian_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian (⊥ : SimpleGraph (↑Λ : Type _)) p σ
      = -p.h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_bot p σ

end Ambient
end IsingModel
