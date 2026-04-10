import IsingModel.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Ring

/-!
# Ising Hamiltonian

Definition of the Ising model Hamiltonian on a finite simple graph,
with interaction and external field terms.
-/

namespace IsingModel

/-! ## Spin flip -/

/-- Flip a spin: `up ↔ down`. -/
def Spin.flip : Spin → Spin
  | .up   => .down
  | .down => .up

/-- Flip all spins in a configuration. -/
def Config.flip {ι : Type*} (σ : Config ι) : Config ι := fun i => (σ i).flip

@[simp]
theorem Spin.toSign_flip (s : Spin) : s.flip.toSign = -s.toSign := by
  cases s <;> simp [Spin.flip, Spin.toSign]

@[simp]
theorem Spin.flip_flip (s : Spin) : s.flip.flip = s := by
  cases s <;> rfl

@[simp]
theorem Config.flip_flip {ι : Type*} (σ : Config ι) : σ.flip.flip = σ := by
  ext i; exact Spin.flip_flip (σ i)

/-! ## Spin sign as field element -/

/-- The spin sign cast into the field `K`. -/
def Spin.sign (K : Type*) [CommRing K] (s : Spin) : K := ↑s.toSign

@[simp]
theorem Spin.sign_flip {K : Type*} [CommRing K] (s : Spin) :
    Spin.sign K s.flip = -Spin.sign K s := by
  cases s <;> simp [Spin.sign, Spin.flip, Spin.toSign]

/-! ## Hamiltonian -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Per-edge interaction: `s(σ_i) * s(σ_j)` for an edge `{i, j}`. -/
def edgeSpin (σ : Config ι) : Sym2 ι → K :=
  Sym2.lift ⟨fun i j => Spin.sign K (σ i) * Spin.sign K (σ j),
    fun _ _ => mul_comm _ _⟩

/-- The interaction energy: `-J * ∑_{e ∈ edges} s(σ_i) * s(σ_j)`. -/
def interactionEnergy (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : K) (σ : Config ι) : K :=
  -J * ∑ e ∈ G.edgeFinset, edgeSpin σ e

/-- The external field energy: `-h * ∑_i s(σ_i)`. -/
def externalFieldEnergy (h : K) (σ : Config ι) : K :=
  -h * ∑ i : ι, Spin.sign K (σ i)

/-- The Ising Hamiltonian: `H(σ) = interactionEnergy + externalFieldEnergy`. -/
def hamiltonian (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams K) (σ : Config ι) : K :=
  interactionEnergy G p.J σ + externalFieldEnergy p.h σ

/-! ## Spin flip symmetry -/

omit [Fintype ι] [DecidableEq ι] [LinearOrder K] [IsStrictOrderedRing K] in
theorem edgeSpin_flip (σ : Config ι) (e : Sym2 ι) :
    edgeSpin (K := K) σ.flip e = edgeSpin σ e := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeSpin, Sym2.lift_mk, Config.flip, Spin.sign_flip]
  ring

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
