import IsingModel.TransferMatrix.CubicLayerCylinder
import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow
import IsingModel.TransferMatrix.LayerSpectral

/-!
# Finite layer-cylinder spectral decay

This file consumes the finite balanced min-gap certificates from the layer
spectral scaffold as actual project-level correlation bounds on finite
periodic layer-cylinder graphs.

The statements remain finite and periodic.  They do not build open slabs,
thermodynamic limits, or a physical interacting cubic-layer spectral window.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-! ## Positive physical layer weights -/

/-- The physical one-layer Ising weight is strictly positive. -/
theorem layerInternalWeight_pos
    {S : Type*} [Fintype S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (p : IsingParams ℝ)
    (ω : LayerState S) :
    0 < layerInternalWeight H p ω :=
  Real.exp_pos _

/-- The physical adjacent-layer Ising transition weight is strictly positive. -/
theorem layerTransitionWeight_pos
    {S : Type*} (E : Finset (S × S)) (p : IsingParams ℝ) (ω η : LayerState S) :
    0 < layerTransitionWeight E p ω η :=
  Real.exp_pos _

/-! ## Certificate consumers on finite cylinders -/

/-- A balanced min-gap certificate gives the same two-arc decay bound for the
concrete finite cyclic layer-cylinder spin two-point function. -/
theorem layerCylinderSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (hu : ∀ ω, 0 < u ω)
    (cert : LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerCylinderSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (cert.prefactor / cert.partitionPrefactor) * cert.theta ^ min a b := by
  rw [layerCylinderSpinTwoPoint_eq_layerSpinTwoPoint]
  exact layerSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
    u k x hu cert hb

/-- A balanced min-gap certificate gives finite periodic layer-cylinder
project-level same-transverse-site correlation decay. -/
theorem
    correlation_layerCylinderGraph_same_transverse_abs_le_min_of_balancedMinSpectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (E : Finset (S × S))
    (p : IsingParams ℝ) (x : S)
    (cert : LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight E p) (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) (hN : 3 ≤ a + b) :
    |correlation (layerCylinderGraph (S := S) H E (a + b)) p
      ({Prod.mk (0 : Fin (a + b)) x,
        Prod.mk ⟨a, Nat.lt_add_of_pos_right hb⟩ x} :
          Finset (LayerCylinderSite (a + b) S))|
      ≤ (cert.prefactor / cert.partitionPrefactor) * cert.theta ^ min a b := by
  rw [correlation_layerCylinderGraph_same_transverse_eq_layerCylinderSpinTwoPoint
    (S := S) H E p x hb hN]
  exact
    layerCylinderSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight E p) x
      (layerInternalWeight_pos H p) cert hb

/-- Cubic transverse boxes inherit finite periodic layer-cylinder correlation
decay from a balanced min-gap certificate. -/
theorem
    correlation_cubicLayerCylinderGraph_same_transverse_abs_le_min_of_cert
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (cert : LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) (hN : 3 ≤ a + b) :
    |correlation (cubicLayerCylinderGraph d R (a + b)) p
      ({Prod.mk (0 : Fin (a + b)) x,
        Prod.mk ⟨a, Nat.lt_add_of_pos_right hb⟩ x} :
          Finset (LayerCylinderSite (a + b) (CubicLayerSite d R)))|
      ≤ (cert.prefactor / cert.partitionPrefactor) * cert.theta ^ min a b := by
  rw [cubicLayerCylinderGraph]
  exact
    correlation_layerCylinderGraph_same_transverse_abs_le_min_of_balancedMinSpectralGapCertificate
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p x cert hb hN

/-- The finite free-layer Walsh certificate gives a concrete periodic cylinder
decay bound with rate `tanh (p.β * p.J)`. -/
theorem correlation_freeLayerCylinderGraph_same_transverse_abs_le_tanh
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (hsmall :
      Real.tanh (p.β * p.J) <
        (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹)
    (x : S) {a b : ℕ} [NeZero a] (hb : 0 < b) (hN : 3 ≤ a + b) :
    |correlation
      (layerCylinderGraph (⊥ : SimpleGraph S) (layerIdentityTransitionPairs S) (a + b))
      p
      ({Prod.mk (0 : Fin (a + b)) x,
        Prod.mk ⟨a, Nat.lt_add_of_pos_right hb⟩ x} :
          Finset (LayerCylinderSite (a + b) S))|
      ≤
        ((freeLayerBalancedMinGapCertificate_tanh (S := S) p hp hβJ hsmall x).prefactor /
          (freeLayerBalancedMinGapCertificate_tanh (S := S) p hp hβJ hsmall x).partitionPrefactor)
        * Real.tanh (p.β * p.J) ^ min a b := by
  let cert := freeLayerBalancedMinGapCertificate_tanh (S := S) p hp hβJ hsmall x
  simpa [cert] using
    (correlation_layerCylinderGraph_same_transverse_abs_le_min_of_balancedMinSpectralGapCertificate
      (S := S) (⊥ : SimpleGraph S) (layerIdentityTransitionPairs S) p x cert hb hN)

end TransferMatrix

end IsingModel
