import IsingModel.Basic
import IsingModel.Hamiltonian
import Mathlib.Tactic.FinCases

/-!
# Test generators for Ising model property tests (Issue #888 Step P1)

Small-graph definitions and all-configuration enumeration for use in
property-test sentinel files.

All computations use ℤ for spin algebra — no `Real.exp` — enabling the
kernel-decidable sanity checks in the `test` library
(`test/IsingModel/Generators.lean`).
-/

namespace IsingModel.TestGenerators

/-! ## Small graph definitions

All graphs carry explicit `DecidableRel` and `Fintype edgeSet` instances
so that edge counts and spin sums are decidable by the kernel. -/

/-- **2-site complete graph**: single edge {0,1} on `Fin 2`. -/
abbrev chainGraph2 : SimpleGraph (Fin 2) := SimpleGraph.completeGraph (Fin 2)

/-- **3-site path graph**: edges {0,1} and {1,2} on `Fin 3`.

Uses `SimpleGraph.fromRel` (adjacency = i ≠ j and related in either direction) with the
path relation `i.val + 1 = j.val`. `DecidableRel` is derived automatically
from the decidability of ℕ equality. -/
def chainGraph3 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun i j : Fin 3 => i.val + 1 = j.val)

/-- **Triangle (K₃) graph**: complete graph on `Fin 3`. -/
abbrev triangleGraph : SimpleGraph (Fin 3) := SimpleGraph.completeGraph (Fin 3)

/-- **4-cycle (square) graph**: edges {0,1},{1,2},{2,3},{3,0} on `Fin 4`.
Note: `j.val ≤ 3` is redundant for `j : Fin 4` but makes the intent explicit. -/
def squareGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j : Fin 4 =>
    (i.val + 1 = j.val) ∨ (i.val = 3 ∧ j.val = 0))

/-- **Complete graph K₄**: all pairs on `Fin 4`. -/
abbrev k4Graph : SimpleGraph (Fin 4) := SimpleGraph.completeGraph (Fin 4)

-- DecidableRel instances (automatically derived for completeGraph and fromRel)
instance : DecidableRel chainGraph2.Adj := by
  unfold chainGraph2; infer_instance

instance : DecidableRel chainGraph3.Adj := by
  unfold chainGraph3; infer_instance

instance : DecidableRel triangleGraph.Adj := by
  unfold triangleGraph; infer_instance

instance : DecidableRel squareGraph.Adj := by
  unfold squareGraph; infer_instance

instance : DecidableRel k4Graph.Adj := by
  unfold k4Graph; infer_instance

-- Fintype edgeSet instances (derived once DecidableRel is available)
instance : Fintype chainGraph2.edgeSet := inferInstance
instance : Fintype chainGraph3.edgeSet := inferInstance
instance : Fintype triangleGraph.edgeSet := inferInstance
instance : Fintype squareGraph.edgeSet := inferInstance
instance : Fintype k4Graph.edgeSet := inferInstance

/-! ## Configuration enumeration -/

/-- All `Fin n → Spin` configurations as a `Finset` (2^n elements). -/
def allConfigsFinset (n : ℕ) : Finset (Fin n → Spin) :=
  Fintype.piFinset fun _ => Finset.univ

/-! ## Spin algebra (ℤ-valued, computable) -/

/-- Product ∏_{i ∈ A} σ_i (ℤ-valued). -/
def spinProductZ {n : ℕ} (A : Finset (Fin n)) (σ : Fin n → Spin) : ℤ :=
  ∏ i ∈ A, (σ i).toSign

/-- Sum ∑_e (σ_i · σ_j) over edges (ℤ-valued). -/
def edgeCouplingSum {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Fin n → Spin) : ℤ :=
  ∑ e : G.edgeSet,
    Sym2.lift ⟨fun i j => (σ i).toSign * (σ j).toSign,
      fun i j => mul_comm ((σ i).toSign) ((σ j).toSign)⟩ (e : Sym2 (Fin n))

/-- Formal coupling sum ∑_σ ∑_e (σ_i · σ_j) (ℤ-valued). -/
def formalCouplingSum {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [Fintype G.edgeSet] : ℤ :=
  ∑ σ : Fin n → Spin, edgeCouplingSum G σ

end IsingModel.TestGenerators
