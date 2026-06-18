import Mathlib.Data.Real.Basic
import IsingModel.Basic
import IsingModel.TransferMatrix.LayerTransfer

/-!
# Finite cyclic layer Gibbs representation (GJ §17.1)

Glimm--Jaffe §17.1 groups a finite-volume Ising model into hyperplane layers and
reads the periodic direction as a finite cyclic product of layer weights.  This
file records the Gibbs-sum side of that abstraction and connects it to the
general layer transfer matrix from `LayerTransfer`.

The state space `Ω` should be read as one hyperplane configuration.  The
one-layer weight is `u : Ω → ℝ`, the adjacent-layer interaction is
`k : Ω → Ω → ℝ`, and a periodic stack `c : Fin N → Ω` has weight
`∏ i, u (c (i+1)) * k (c i) (c (i+1))`.

No concrete `ℤ^d` box decomposition, Perron--Frobenius theory, thermodynamic
limit, or exponential-decay estimate is included here.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Cyclic layer Gibbs weights -/

/-- The positive-length cyclic Gibbs weight of a finite layer stack. -/
def layerCyclicGibbsWeight (u : Ω → ℝ) (k : Ω → Ω → ℝ) {N : ℕ} [NeZero N]
    (c : Fin N → Ω) : ℝ :=
  ∏ i : Fin N, u (c (i + 1)) * k (c i) (c (i + 1))

/-- The positive-length finite cyclic layer partition sum. -/
def layerCyclicPartition (u : Ω → ℝ) (k : Ω → Ω → ℝ) (N : ℕ) [NeZero N] : ℝ :=
  ∑ c : Fin N → Ω, layerCyclicGibbsWeight u k c

omit [Fintype Ω] [DecidableEq Ω] in
/-- The cyclic Gibbs weight is the layer closed-walk weight of the transfer
matrix. -/
theorem layerCyclicGibbsWeight_eq_layerClosedWalkWeight
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) {N : ℕ} [NeZero N] (c : Fin N → Ω) :
    layerCyclicGibbsWeight u k c = layerClosedWalkWeight u k c := by
  rw [layerCyclicGibbsWeight, layerClosedWalkWeight_eq_prod]

omit [DecidableEq Ω] in
/-- Product-expanded form of the finite cyclic layer partition sum. -/
theorem layerCyclicPartition_eq_sum_prod (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (N : ℕ) [NeZero N] :
    layerCyclicPartition u k N
      = ∑ c : Fin N → Ω,
          ∏ i : Fin N, u (c (i + 1)) * k (c i) (c (i + 1)) := by
  rfl

/-- **Finite cyclic layer partition representation** (GJ §17.1): the cyclic
layer Gibbs partition sum equals the trace of the finite layer transfer matrix. -/
theorem layerCyclicPartition_eq_trace (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (N : ℕ) [NeZero N] :
    layerCyclicPartition u k N = layerTransferPartitionTrace u k N := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rw [layerCyclicPartition_eq_sum_prod, layerTransferPartition_trace_eq_sum_prod]

omit [Fintype Ω] [DecidableEq Ω] in
/-- A cyclic layer stack has positive weight when all layer and transition
weights are positive. -/
theorem layerCyclicGibbsWeight_pos (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ x, 0 < u x) (hk : ∀ x y, 0 < k x y)
    {N : ℕ} [NeZero N] (c : Fin N → Ω) :
    0 < layerCyclicGibbsWeight u k c := by
  unfold layerCyclicGibbsWeight
  exact Finset.prod_pos (fun i _ => mul_pos (hu _) (hk _ _))

omit [DecidableEq Ω] in
/-- The finite cyclic layer partition sum is positive when the layer state space
is nonempty and all layer and transition weights are positive. -/
theorem layerCyclicPartition_pos [Nonempty Ω] (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ x, 0 < u x) (hk : ∀ x y, 0 < k x y)
    (N : ℕ) [NeZero N] :
    0 < layerCyclicPartition u k N := by
  unfold layerCyclicPartition
  exact Finset.sum_pos (fun c _ => layerCyclicGibbsWeight_pos u k hu hk c)
    Finset.univ_nonempty

/-! ## Two layer insertions -/

/-- The marked cyclic layer Gibbs weight with two insertions separated by `a`
steps and by the positive complementary length `b`. -/
def layerMarkedCyclicGibbsWeight (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    {a b : ℕ} (hb : 0 < b) (c : Fin (a + b) → Ω) : ℝ := by
  haveI : NeZero (a + b) := ⟨by omega⟩
  exact f (c 0) * f (c ⟨a, Nat.lt_add_of_pos_right hb⟩)
    * layerCyclicGibbsWeight u k c

omit [Fintype Ω] [DecidableEq Ω] in
/-- Product-expanded form of the marked cyclic layer Gibbs weight. -/
theorem layerMarkedCyclicGibbsWeight_eq_prod
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) {a b : ℕ}
    (hb : 0 < b) (c : Fin (a + b) → Ω) :
    layerMarkedCyclicGibbsWeight u k f hb c
      = letI : NeZero (a + b) := ⟨by omega⟩
        f (c 0) * f (c ⟨a, Nat.lt_add_of_pos_right hb⟩)
          * ∏ i : Fin (a + b), u (c (i + 1)) * k (c i) (c (i + 1)) := by
  dsimp [layerMarkedCyclicGibbsWeight, layerCyclicGibbsWeight]

/-- The unnormalised finite cyclic layer two-point numerator. -/
def layerTwoPointNumerator (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    {a b : ℕ} (hb : 0 < b) : ℝ :=
  ∑ c : Fin (a + b) → Ω, layerMarkedCyclicGibbsWeight u k f hb c

/-- **Finite cyclic layer two-point numerator representation** (GJ §17.1): the
marked Gibbs sum equals the transfer-matrix trace with two diagonal insertions. -/
theorem layerTwoPointNumerator_eq_trace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) {a b : ℕ}
    [NeZero a] (hb : 0 < b) :
    layerTwoPointNumerator u k f (a := a) (b := b) hb
      = layerTransferCorrelation_matrixElement u k f a b := by
  rw [layerTwoPointNumerator, layerTransferCorrelation_matrixElement_eq_sum_prod u k f hb]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [layerMarkedCyclicGibbsWeight_eq_prod]

/-- The normalised finite cyclic layer two-point function. -/
noncomputable def layerTwoPoint (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    {a b : ℕ} [NeZero a] (hb : 0 < b) : ℝ := by
  haveI : NeZero (a + b) := ⟨by omega⟩
  exact layerTwoPointNumerator u k f (a := a) (b := b) hb
    / layerCyclicPartition u k (a + b)

/-- **Finite cyclic layer two-point trace ratio** (GJ §17.1): the normalised
layer two-point function is the marked transfer trace divided by the partition
trace. -/
theorem layerTwoPoint_eq_trace_ratio
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) {a b : ℕ}
    [NeZero a] (hb : 0 < b) :
    layerTwoPoint u k f (a := a) (b := b) hb
      = layerTransferCorrelation_matrixElement u k f a b
        / layerTransferPartitionTrace u k (a + b) := by
  dsimp [layerTwoPoint]
  rw [layerTwoPointNumerator_eq_trace u k f (a := a) (b := b) hb,
    layerCyclicPartition_eq_trace]

/-! ## Hyperplane-facing spin observables -/

/-- A finite hyperplane layer state is a spin configuration on its cross-section. -/
abbrev LayerState (S : Type*) := Config S

/-- The global spin flip as an equivalence of finite layer states. -/
def layerStateFlipEquiv (S : Type*) : LayerState S ≃ LayerState S where
  toFun := Config.flip
  invFun := Config.flip
  left_inv := Config.flip_flip
  right_inv := Config.flip_flip

/-- Evaluation of the global layer-state spin flip equivalence. -/
@[simp]
theorem layerStateFlipEquiv_apply {S : Type*} (ω : LayerState S) :
    layerStateFlipEquiv S ω = Config.flip ω :=
  rfl

/-- The spin observable at a fixed transverse site inside one layer. -/
def layerSpinAt {S : Type*} (x : S) (ω : LayerState S) : ℝ :=
  Spin.sign ℝ (ω x)

/-- The fixed-site layer spin observable is odd under global spin flip. -/
@[simp]
theorem layerSpinAt_flip {S : Type*} (x : S) (ω : LayerState S) :
    layerSpinAt x (layerStateFlipEquiv S ω) = -layerSpinAt x ω := by
  simp [layerSpinAt, Config.flip]

/-- The finite cyclic layer two-point function for the spin at a fixed transverse
site of each layer. -/
noncomputable def layerSpinTwoPoint {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S) {a b : ℕ} [NeZero a] (hb : 0 < b) : ℝ :=
  layerTwoPoint u k (layerSpinAt x) (a := a) (b := b) hb

/-- Trace-ratio form of the finite cyclic layer spin two-point function. -/
theorem layerSpinTwoPoint_eq_trace_ratio {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S) {a b : ℕ} [NeZero a] (hb : 0 < b) :
    layerSpinTwoPoint u k x (a := a) (b := b) hb
      = layerTransferCorrelation_matrixElement u k (layerSpinAt x) a b
        / layerTransferPartitionTrace u k (a + b) :=
  layerTwoPoint_eq_trace_ratio u k (layerSpinAt x) (a := a) (b := b) hb

end TransferMatrix

end IsingModel
