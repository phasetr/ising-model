import IsingModel.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Ring

/-!
# Ising Hamiltonian

Definition of the Ising model Hamiltonian on a finite simple graph,
with interaction and external field terms.
-/

namespace IsingModel

/-! ## Per-edge interaction -/

/-- Per-edge interaction: `s(σ_i) * s(σ_j)` for an edge `{i, j}`. -/
def edgeSpin {ι K : Type*} [Field K] (σ : Config ι) : Sym2 ι → K :=
  Sym2.lift ⟨fun i j => Spin.sign K (σ i) * Spin.sign K (σ j),
    fun _ _ => mul_comm _ _⟩

/-- The per-edge spin product is invariant under spin flip: `(-1)·(-1) = 1·1`. -/
theorem edgeSpin_flip {ι K : Type*} [Field K] (σ : Config ι) (e : Sym2 ι) :
    edgeSpin (K := K) σ.flip e = edgeSpin σ e := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeSpin, Sym2.lift_mk, Config.flip, Spin.sign_flip]
  ring

/-! ## External field energy -/

/-- The external field energy: `-h * ∑_i s(σ_i)`. -/
def externalFieldEnergy {ι K : Type*} [Field K] [Fintype ι]
    (h : K) (σ : Config ι) : K :=
  -h * ∑ i : ι, Spin.sign K (σ i)

/-! ## Interaction energy and Hamiltonian -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

open Finset

/-- The interaction energy: `-J * ∑_{e ∈ edges} s(σ_i) * s(σ_j)`. -/
def interactionEnergy (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : K) (σ : Config ι) : K :=
  -J * ∑ e ∈ G.edgeFinset, edgeSpin σ e

/-- The Ising Hamiltonian: `H(σ) = interactionEnergy + externalFieldEnergy`. -/
def hamiltonian (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams K) (σ : Config ι) : K :=
  interactionEnergy G p.J σ + externalFieldEnergy p.h σ

/-! ## Spin flip symmetry -/

omit [Fintype ι] [DecidableEq ι] [LinearOrder K] [IsStrictOrderedRing K] in
/-- The interaction energy is invariant under spin flip. -/
theorem interactionEnergy_flip (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : K) (σ : Config ι) :
    interactionEnergy G J σ.flip = interactionEnergy G J σ := by
  unfold interactionEnergy
  congr 1
  exact Finset.sum_congr rfl fun e _ => edgeSpin_flip σ e

omit [DecidableEq ι] in
/-- When `h = 0`, the Hamiltonian is invariant under spin flip. -/
theorem hamiltonian_flip_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams K) (hp : p.h = 0) (σ : Config ι) :
    hamiltonian G p σ.flip = hamiltonian G p σ := by
  unfold hamiltonian
  rw [interactionEnergy_flip]
  congr 1
  unfold externalFieldEnergy Config.flip
  simp [hp]

end IsingModel
