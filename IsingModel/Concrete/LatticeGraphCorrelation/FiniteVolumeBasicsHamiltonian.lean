import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete edgeSpin / interaction-energy flip and bottom-graph wrappers

Narrow child module for three ℤ^d flip / bottom-graph wrappers at the Λ layer
(`edgeSpin_flip`, `interactionEnergy_flip`, and `hamiltonian_bot`). Each
wrapper is a thin pass-through to the corresponding `IsingModel.*` lemma at the
induced graph.

The Hamiltonian's own spin-flip invariance at `h = 0` and its `h ↦ -h`
reflection are stated once, in `EnergyClosedFormsHamiltonian.lean`, as
`hamiltonian_flip_eq_latticeGraph` and `hamiltonian_neg_h_latticeGraph`; the
identically-stated copies that used to sit here have been removed.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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

/-- **ℤ^d hamiltonian_bot at Λ**: `H_⊥(σ) = -h · Σ sign σ`. -/
theorem hamiltonian_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian (⊥ : SimpleGraph (↑Λ : Type _)) p σ
      = -p.h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_bot p σ

end Ambient
end IsingModel
