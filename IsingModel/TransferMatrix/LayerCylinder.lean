import IsingModel.GibbsMeasure
import IsingModel.TransferMatrix.LayerGibbs

/-!
# Finite cyclic layer cylinders (GJ §17.1)

This file adds the finite, concrete stack side of the layer formalism.  A
configuration on a cyclic cylinder with longitudinal coordinate `Fin N` and
finite transverse section `S` is reindexed as a cyclic family of layer states
`Fin N → LayerState S`.  Internal layer weights and adjacent-layer transition
weights then give a finite cylinder partition function, which is identified with
the abstract cyclic layer Gibbs partition function and hence with the transfer
matrix trace from `LayerGibbs`.

The graph edge decomposition of a specific lattice slab, Perron--Frobenius
theory, thermodynamic limits, and exponential decay estimates are intentionally
left for later files.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Cylinder configurations -/

/-- A site of a finite cyclic layer cylinder with longitudinal length `N` and
finite transverse section `S`. -/
abbrev LayerCylinderSite (N : ℕ) (S : Type*) := Fin N × S

/-- Reindex a spin configuration on `Fin N × S` as a family of layer
configurations indexed by `Fin N`. -/
def layerCylinderConfigEquiv (N : ℕ) :
    Config (LayerCylinderSite N S) ≃ (Fin N → LayerState S) where
  toFun σ := fun i x => σ (i, x)
  invFun c := fun ix => c ix.1 ix.2
  left_inv σ := by
    ext ix
    rfl
  right_inv c := by
    ext i x
    rfl

omit [Fintype S] [DecidableEq S] in
/-- Evaluation of `layerCylinderConfigEquiv`. -/
@[simp]
theorem layerCylinderConfigEquiv_apply (N : ℕ) (σ : Config (LayerCylinderSite N S))
    (i : Fin N) (x : S) :
    layerCylinderConfigEquiv (S := S) N σ i x = σ (i, x) :=
  rfl

omit [Fintype S] [DecidableEq S] in
/-- Evaluation of the inverse of `layerCylinderConfigEquiv`. -/
@[simp]
theorem layerCylinderConfigEquiv_symm_apply (N : ℕ) (c : Fin N → LayerState S)
    (i : Fin N) (x : S) :
    (layerCylinderConfigEquiv (S := S) N).symm c (i, x) = c i x :=
  rfl

/-! ## Layer cylinder weights -/

/-- The one-layer Ising weight of a transverse graph `H`.

It contains all edges inside the layer and the external-field contribution on
that layer. -/
noncomputable def layerInternalWeight (H : SimpleGraph S) [Fintype H.edgeSet]
    (p : IsingParams ℝ) (ω : LayerState S) : ℝ :=
  Real.exp
    (p.β * p.J * ∑ e ∈ H.edgeFinset, edgeSpin (K := ℝ) ω e
      + p.β * p.h * ∑ x : S, Spin.sign ℝ (ω x))

/-- The adjacent-layer Ising weight for a finite set of directed transverse
pairs.  Each pair `(x, y)` couples site `x` in the current layer to site `y` in
the next layer. -/
noncomputable def layerTransitionWeight (E : Finset (S × S)) (p : IsingParams ℝ)
    (ω η : LayerState S) : ℝ :=
  Real.exp
    (p.β * p.J * ∑ xy ∈ E, Spin.sign ℝ (ω xy.1) * Spin.sign ℝ (η xy.2))

omit [DecidableEq S] in
/-- The one-layer weight is invariant under global spin flip at zero external
field. -/
theorem layerInternalWeight_flip_of_h_zero (H : SimpleGraph S) [Fintype H.edgeSet]
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState S) :
    layerInternalWeight H p (layerStateFlipEquiv S ω) = layerInternalWeight H p ω := by
  simp [layerInternalWeight, hp, edgeSpin_flip]

omit [Fintype S] [DecidableEq S] in
/-- The adjacent-layer transition weight is invariant under simultaneous global
spin flip of both neighbouring layers. -/
theorem layerTransitionWeight_flip_flip (E : Finset (S × S)) (p : IsingParams ℝ)
    (ω η : LayerState S) :
    layerTransitionWeight E p (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η)
      = layerTransitionWeight E p ω η := by
  simp [layerTransitionWeight, Config.flip]

/-- The cyclic layer-cylinder Gibbs weight of a concrete stack configuration. -/
noncomputable def layerCylinderStackWeight
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    {N : ℕ} [NeZero N] (σ : Config (LayerCylinderSite N S)) : ℝ :=
  layerCyclicGibbsWeight u k ((layerCylinderConfigEquiv (S := S) N) σ)

/-- The partition function of a finite cyclic layer cylinder, summed over
ordinary spin configurations on `Fin N × S`. -/
noncomputable def layerCylinderPartition
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (N : ℕ) [NeZero N] : ℝ :=
  ∑ σ : Config (LayerCylinderSite N S), layerCylinderStackWeight u k σ

/-- The cylinder partition sum over concrete stack configurations is the
abstract cyclic layer Gibbs partition sum. -/
theorem layerCylinderPartition_eq_layerCyclicPartition
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (N : ℕ) [NeZero N] :
    layerCylinderPartition u k N = layerCyclicPartition u k N := by
  unfold layerCylinderPartition layerCylinderStackWeight layerCyclicPartition
  exact Fintype.sum_equiv (layerCylinderConfigEquiv (S := S) N)
    (fun σ : Config (LayerCylinderSite N S) =>
      layerCyclicGibbsWeight u k ((layerCylinderConfigEquiv (S := S) N) σ))
    (fun c : Fin N → LayerState S => layerCyclicGibbsWeight u k c)
    (fun _ => rfl)

/-- **Finite cyclic layer-cylinder trace representation** (GJ §17.1): the
concrete stack partition sum equals the transfer-matrix trace. -/
theorem layerCylinderPartition_eq_trace
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (N : ℕ) [NeZero N] :
    layerCylinderPartition u k N = layerTransferPartitionTrace u k N := by
  rw [layerCylinderPartition_eq_layerCyclicPartition, layerCyclicPartition_eq_trace]

/-- The Ising-weight specialisation of the finite cyclic layer-cylinder
partition function. -/
noncomputable def isingLayerCylinderPartition (H : SimpleGraph S) [Fintype H.edgeSet]
    (E : Finset (S × S)) (p : IsingParams ℝ) (N : ℕ) [NeZero N] : ℝ :=
  layerCylinderPartition (layerInternalWeight H p) (layerTransitionWeight E p) N

/-- The Ising-weight cyclic cylinder partition function equals the abstract
cyclic layer Gibbs partition with the corresponding internal and transition
weights. -/
theorem isingLayerCylinderPartition_eq_layerCyclicPartition
    (H : SimpleGraph S) [Fintype H.edgeSet] (E : Finset (S × S))
    (p : IsingParams ℝ) (N : ℕ) [NeZero N] :
    isingLayerCylinderPartition H E p N
      = layerCyclicPartition (layerInternalWeight H p) (layerTransitionWeight E p) N :=
  layerCylinderPartition_eq_layerCyclicPartition _ _ N

/-- The Ising-weight cyclic cylinder partition function as a transfer-matrix
trace. -/
theorem isingLayerCylinderPartition_eq_trace
    (H : SimpleGraph S) [Fintype H.edgeSet] (E : Finset (S × S))
    (p : IsingParams ℝ) (N : ℕ) [NeZero N] :
    isingLayerCylinderPartition H E p N
      = layerTransferPartitionTrace (layerInternalWeight H p) (layerTransitionWeight E p) N :=
  layerCylinderPartition_eq_trace _ _ N

/-! ## Two layer insertions -/

/-- The unnormalised two-point numerator on a concrete cyclic layer cylinder,
with both insertions at the same transverse site. -/
noncomputable def layerCylinderSpinTwoPointNumerator
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S) {a b : ℕ} (hb : 0 < b) : ℝ := by
  haveI : NeZero (a + b) := ⟨by omega⟩
  exact ∑ σ : Config (LayerCylinderSite (a + b) S),
    Spin.sign ℝ (σ (0, x))
      * Spin.sign ℝ (σ (⟨a, Nat.lt_add_of_pos_right hb⟩, x))
      * layerCylinderStackWeight u k σ

/-- The concrete cylinder two-point numerator is the abstract layer numerator
with the spin observable at the selected transverse site. -/
theorem layerCylinderSpinTwoPointNumerator_eq_layerTwoPointNumerator
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S) {a b : ℕ} (hb : 0 < b) :
    layerCylinderSpinTwoPointNumerator u k x (a := a) (b := b) hb
      = layerTwoPointNumerator u k (layerSpinAt x) (a := a) (b := b) hb := by
  haveI : NeZero (a + b) := ⟨by omega⟩
  unfold layerCylinderSpinTwoPointNumerator layerTwoPointNumerator
    layerMarkedCyclicGibbsWeight layerCylinderStackWeight layerSpinAt
  exact Fintype.sum_equiv (layerCylinderConfigEquiv (S := S) (a + b))
    (fun σ : Config (LayerCylinderSite (a + b) S) =>
      Spin.sign ℝ (σ (0, x))
        * Spin.sign ℝ (σ (⟨a, Nat.lt_add_of_pos_right hb⟩, x))
        * layerCyclicGibbsWeight u k
          ((layerCylinderConfigEquiv (S := S) (a + b)) σ))
    (fun c : Fin (a + b) → LayerState S =>
      Spin.sign ℝ (c 0 x)
        * Spin.sign ℝ (c ⟨a, Nat.lt_add_of_pos_right hb⟩ x)
        * layerCyclicGibbsWeight u k c)
    (fun _ => rfl)

/-- The normalised same-transverse-site two-point function on the concrete
cyclic layer cylinder. -/
noncomputable def layerCylinderSpinTwoPoint
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S) {a b : ℕ} [NeZero a] (hb : 0 < b) : ℝ := by
  haveI : NeZero (a + b) := ⟨by omega⟩
  exact layerCylinderSpinTwoPointNumerator u k x (a := a) (b := b) hb
    / layerCylinderPartition u k (a + b)

/-- The concrete cylinder spin two-point function is the abstract cyclic layer
spin two-point function. -/
theorem layerCylinderSpinTwoPoint_eq_layerSpinTwoPoint
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S) {a b : ℕ} [NeZero a] (hb : 0 < b) :
    layerCylinderSpinTwoPoint u k x (a := a) (b := b) hb
      = layerSpinTwoPoint u k x (a := a) (b := b) hb := by
  dsimp [layerCylinderSpinTwoPoint, layerSpinTwoPoint, layerTwoPoint]
  rw [layerCylinderSpinTwoPointNumerator_eq_layerTwoPointNumerator,
    layerCylinderPartition_eq_layerCyclicPartition]

/-- The concrete cylinder spin two-point function as a transfer-matrix trace
ratio. -/
theorem layerCylinderSpinTwoPoint_eq_trace_ratio
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S) {a b : ℕ} [NeZero a] (hb : 0 < b) :
    layerCylinderSpinTwoPoint u k x (a := a) (b := b) hb
      = layerTransferCorrelation_matrixElement u k (layerSpinAt x) a b
        / layerTransferPartitionTrace u k (a + b) := by
  rw [layerCylinderSpinTwoPoint_eq_layerSpinTwoPoint,
    layerSpinTwoPoint_eq_trace_ratio]

end TransferMatrix

end IsingModel
