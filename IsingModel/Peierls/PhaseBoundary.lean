import IsingModel.Lattice
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Peierls argument — phase boundary (contour) on a finite graph

This module is part of the split `IsingModel.Peierls` development. It
defines the phase boundary `∂σ` (the set of edges where adjacent spins
disagree) and computes the zero-field Hamiltonian
`-J·(|E| - 2·|∂σ|)`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase boundary (contour) on a finite graph

For any graph G and configuration σ, the phase boundary is the set of
edges where neighboring spins disagree. In the Peierls argument, this
is used with + boundary conditions on a finite box in ℤ^d. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Whether an edge has disagreeing spins (-1 edge spin). -/
def edgeDisagrees (σ : Config ι) (e : Sym2 ι) : Bool :=
  Sym2.lift ⟨fun i j => decide (σ i ≠ σ j), fun i j => by
    simp only [ne_comm]⟩ e

/-- The phase boundary `∂σ`: the set of edges where adjacent spins disagree. -/
def phaseBoundary (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) : Finset (Sym2 ι) :=
  G.edgeFinset.filter (fun e => edgeDisagrees σ e)

/-- The number of disagreeing edges (length of the phase boundary). -/
def phaseBoundarySize (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) : ℕ :=
  (phaseBoundary G σ).card

omit [Fintype ι] [DecidableEq ι] in
/-- An edge is in the phase boundary iff the spins at its endpoints disagree. -/
theorem mem_phaseBoundary (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) (e : Sym2 ι) :
    e ∈ phaseBoundary G σ ↔
      e ∈ G.edgeFinset ∧ edgeDisagrees σ e = true := by
  simp [phaseBoundary, Finset.mem_filter]

/-! ## Energy in terms of phase boundary

For the Ising model with h = 0 and uniform coupling J, the Hamiltonian
can be expressed in terms of the phase boundary size:
  H(σ) = -J · (|E| - 2|∂σ|)
where |E| is the total number of edges and |∂σ| is the phase boundary size. -/

omit [Fintype ι] [DecidableEq ι] in
/-- The edge spin equals -1 on disagreeing edges and +1 on agreeing edges. -/
private theorem edgeSpin_ite_disagrees (σ : Config ι) (e : Sym2 ι) :
    edgeSpin (K := ℝ) σ e = if edgeDisagrees σ e then -1 else 1 := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeSpin, edgeDisagrees, Sym2.lift_mk, Spin.sign, decide_eq_true_eq]
  cases σ i <;> cases σ j <;> simp [Spin.toSign]

omit [DecidableEq ι] in
/-- For h = 0, the Hamiltonian equals `-J * (|E| - 2|∂σ|)` where |∂σ| is
the phase boundary size. Each agreeing edge contributes +1 to the edge sum
and each disagreeing edge contributes -1, so the sum = |E| - 2|∂σ|. -/
theorem hamiltonian_boundary (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    (J β : ℝ) (σ : Config ι) :
    hamiltonian G ⟨J, 0, β⟩ σ =
      -J * (↑G.edgeFinset.card - 2 * ↑(phaseBoundarySize G σ)) := by
  simp only [hamiltonian, interactionEnergy, externalFieldEnergy, phaseBoundarySize]
  simp only [neg_zero, zero_mul, add_zero]
  congr 1
  have hedge : ∀ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e =
      if edgeDisagrees σ e = true then (-1 : ℝ) else 1 := fun e _ =>
    edgeSpin_ite_disagrees σ e
  rw [Finset.sum_congr rfl hedge]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hfilt : G.edgeFinset.filter (fun e => edgeDisagrees σ e = true) =
      phaseBoundary G σ := by
    ext e; simp [phaseBoundary, Finset.mem_filter, and_comm]
  rw [hfilt]
  have htotal := Finset.card_filter_add_card_filter_not
    (s := G.edgeFinset) (fun e => edgeDisagrees σ e = true)
  rw [hfilt] at htotal
  have htotalR : (↑(phaseBoundary G σ).card : ℝ) +
      ↑(G.edgeFinset.filter (fun a => ¬(edgeDisagrees σ a = true))).card =
      ↑G.edgeFinset.card := by exact_mod_cast htotal
  linarith


end IsingModel
