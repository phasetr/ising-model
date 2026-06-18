import IsingModel.TransferMatrix.MarkedTraceClosedWalk

/-!
# General finite layer transfer matrix (GJ §17.1)

Glimm--Jaffe §17.1 rewrites finite-volume Ising partition functions by grouping
spins into hyperplane layers and using a transfer matrix between adjacent layers.
This file records the finite matrix core in an abstract form: a finite layer state
space `Ω`, a one-layer weight `u`, and an inter-layer transition weight `k`.

The concrete lattice/hyperplane identification and the spectral-gap decay
arguments are intentionally left to later files.  The results here are
unconditional specialisations of the existing closed-walk and marked-trace
identities.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [CommSemiring R]

/-! ## Layer transfer matrix and cyclic weights -/

/-- **General finite layer transfer matrix** (GJ §17.1): for a finite layer state
space `Ω`, one-layer weight `u`, and transition weight `k`, the transfer matrix
has entry `u b * k a b` from layer state `a` to the next layer state `b`. -/
def layerTransferMatrix (u : Ω → R) (k : Ω → Ω → R) : Matrix Ω Ω R :=
  fun a b => u b * k a b

/-- The trace-side finite periodic layer partition function:
`Tr(T^n)` for the general layer transfer matrix. -/
def layerTransferPartitionTrace (u : Ω → R) (k : Ω → Ω → R) (n : ℕ) : R :=
  (layerTransferMatrix u k ^ n).trace

/-- The cyclic closed-walk weight induced by the general layer transfer matrix. -/
def layerClosedWalkWeight (u : Ω → R) (k : Ω → Ω → R) {n : ℕ} [NeZero n]
    (c : Fin n → Ω) : R :=
  closedWalkWeight (layerTransferMatrix u k) c

omit [Fintype Ω] [DecidableEq Ω] in
/-- The layer closed-walk weight is the product of one-layer weights and transition
weights around the cycle. -/
theorem layerClosedWalkWeight_eq_prod (u : Ω → R) (k : Ω → Ω → R) {n : ℕ}
    [NeZero n] (c : Fin n → Ω) :
    layerClosedWalkWeight u k c =
      ∏ i : Fin n, u (c (i + 1)) * k (c i) (c (i + 1)) := by
  rfl

/-- **General finite-layer trace identity** (GJ §17.1): the trace of a periodic
layer transfer matrix of length `m+1` is the sum over cyclic layer configurations
of their layer closed-walk weights.  This is the direct layer specialisation of
`trace_pow_eq_sum_cycle`. -/
theorem layerTransferPartition_trace (u : Ω → R) (k : Ω → Ω → R) (m : ℕ) :
    layerTransferPartitionTrace u k (m + 1)
      = ∑ c : Fin (m + 1) → Ω, layerClosedWalkWeight u k c := by
  exact trace_pow_eq_sum_cycle (layerTransferMatrix u k) m

/-- Product-expanded form of `layerTransferPartition_trace`: `Tr(T^(m+1))` is the
sum over cyclic layer configurations of
`∏ i, u(c(i+1)) * k(c i, c(i+1))`. -/
theorem layerTransferPartition_trace_eq_sum_prod
    (u : Ω → R) (k : Ω → Ω → R) (m : ℕ) :
    layerTransferPartitionTrace u k (m + 1)
      = ∑ c : Fin (m + 1) → Ω,
          ∏ i : Fin (m + 1), u (c (i + 1)) * k (c i) (c (i + 1)) := by
  rw [layerTransferPartition_trace]
  refine Finset.sum_congr rfl (fun c _ => layerClosedWalkWeight_eq_prod u k c)

/-! ## Marked layer traces -/

/-- The unnormalised one-insertion layer trace `Tr(D_f T^n)`. -/
def layerTransferOnePointTrace (u : Ω → R) (k : Ω → Ω → R) (f : Ω → R)
    (n : ℕ) : R :=
  (Matrix.diagonal f * layerTransferMatrix u k ^ n).trace

/-- The one-insertion layer trace expanded as diagonal matrix entries. -/
theorem layerTransferOnePointTrace_eq_sum
    (u : Ω → R) (k : Ω → Ω → R) (f : Ω → R) (n : ℕ) :
    layerTransferOnePointTrace u k f n
      = ∑ a : Ω, f a * (layerTransferMatrix u k ^ n) a a := by
  exact trace_diagonal_mul_pow (layerTransferMatrix u k) f n

/-- The marked closed-walk layer weight with the nonzero total length inferred
from the positive second separation `hb : 0 < b`. -/
def layerMarkedClosedWalkWeight (u : Ω → R) (k : Ω → Ω → R) (f : Ω → R)
    {a b : ℕ} (hb : 0 < b) (c : Fin (a + b) → Ω) : R := by
  haveI : NeZero (a + b) := ⟨by omega⟩
  exact markedClosedWalkWeight (layerTransferMatrix u k) f hb c

/-- The unnormalised two-insertion layer trace
`Tr(D_f T^a D_f T^b)`, the matrix numerator shape for later layer
correlation representations. -/
def layerTransferCorrelation_matrixElement (u : Ω → R) (k : Ω → Ω → R)
    (f : Ω → R) (a b : ℕ) : R :=
  (Matrix.diagonal f * layerTransferMatrix u k ^ a
      * Matrix.diagonal f * layerTransferMatrix u k ^ b).trace

/-- **Marked finite-layer trace identity** (GJ §17.1): the two-insertion layer
trace is the sum over marked closed walks with the same transfer matrix. -/
theorem layerTransferCorrelation_matrixElement_eq_sum_markedClosedWalk
    (u : Ω → R) (k : Ω → Ω → R) (f : Ω → R) {a b : ℕ}
    [NeZero a] (hb : 0 < b) :
    layerTransferCorrelation_matrixElement u k f a b
      = ∑ c : Fin (a + b) → Ω,
          layerMarkedClosedWalkWeight u k f hb c := by
  haveI : NeZero (a + b) := ⟨by omega⟩
  exact trace_diagonal_pow_diagonal_pow_eq_sum_markedClosedWalk
    (layerTransferMatrix u k) f hb

omit [Fintype Ω] [DecidableEq Ω] in
/-- Product-expanded form of the marked layer closed-walk weight. -/
theorem layerMarkedClosedWalkWeight_eq_prod
    (u : Ω → R) (k : Ω → Ω → R) (f : Ω → R) {a b : ℕ}
    (hb : 0 < b) (c : Fin (a + b) → Ω) :
    layerMarkedClosedWalkWeight u k f hb c
      = letI : NeZero (a + b) := ⟨by omega⟩
        f (c 0) * f (c ⟨a, Nat.lt_add_of_pos_right hb⟩)
          * ∏ i : Fin (a + b), u (c (i + 1)) * k (c i) (c (i + 1)) := by
  dsimp [layerMarkedClosedWalkWeight]
  rfl

/-- Product-expanded form of the two-insertion layer trace. -/
theorem layerTransferCorrelation_matrixElement_eq_sum_prod
    (u : Ω → R) (k : Ω → Ω → R) (f : Ω → R) {a b : ℕ}
    [NeZero a] (hb : 0 < b) :
    layerTransferCorrelation_matrixElement u k f a b
      = ∑ c : Fin (a + b) → Ω,
          letI : NeZero (a + b) := ⟨by omega⟩
          f (c 0) * f (c ⟨a, Nat.lt_add_of_pos_right hb⟩)
            * ∏ i : Fin (a + b), u (c (i + 1)) * k (c i) (c (i + 1)) := by
  rw [layerTransferCorrelation_matrixElement_eq_sum_markedClosedWalk u k f hb]
  refine Finset.sum_congr rfl
    (fun c _ => layerMarkedClosedWalkWeight_eq_prod u k f hb c)

end TransferMatrix

end IsingModel
