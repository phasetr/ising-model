import IsingModel.Concrete.CubicExhaustion
import IsingModel.TransferMatrix.LayerCylinderGraph

/-!
# Cubic transverse boxes as finite layer cylinders (GJ §17.1)

This file specialises the finite periodic layer-cylinder graph bridge to a
concrete transverse box of the integer lattice.  The transverse layer is the
finite induced lattice graph on `Ambient.cubicBox d R`; adjacent layers are
coupled by identity pairs, giving a periodic cylinder over the cubic section.

Open longitudinal slabs/boxes, Perron--Frobenius theory, thermodynamic limits,
and exponential decay estimates are intentionally left for later files.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-! ## Cubic transverse layers -/

/-- The finite transverse layer given by the cubic box `[-R,R]^d`. -/
noncomputable abbrev CubicLayerSite (d R : ℕ) := ↑(Ambient.cubicBox d R)

/-- Identity transition pairs between consecutive copies of a finite layer. -/
noncomputable def layerIdentityTransitionPairs
    (S : Type*) [Fintype S] [DecidableEq S] : Finset (S × S) :=
  (Finset.univ : Finset S).image fun x => (x, x)

/-- The induced nearest-neighbour lattice graph on the transverse cubic box. -/
noncomputable def cubicLayerGraph (d R : ℕ) : SimpleGraph (CubicLayerSite d R) :=
  Ambient.inducedGraph (latticeGraph d) (Ambient.cubicBox d R)

/-- Identity transition pairs for a cubic transverse box. -/
noncomputable def cubicLayerTransitionPairs (d R : ℕ) :
    Finset (CubicLayerSite d R × CubicLayerSite d R) :=
  layerIdentityTransitionPairs (CubicLayerSite d R)

/-- The finite periodic cylinder over a cubic transverse box. -/
noncomputable def cubicLayerCylinderGraph (d R N : ℕ) [NeZero N] :
    SimpleGraph (LayerCylinderSite N (CubicLayerSite d R)) :=
  layerCylinderGraph (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) N

/-! ## Project-level Gibbs bridges -/

/-- The project-level Boltzmann weight of the cubic layer-cylinder graph is the
corresponding finite layer stack weight. -/
theorem boltzmannWeight_cubicLayerCylinderGraph_eq_layerCylinderStackWeight
    (d R : ℕ) (p : IsingParams ℝ) {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (σ : Config (LayerCylinderSite N (CubicLayerSite d R))) :
    boltzmannWeight (cubicLayerCylinderGraph d R N) p σ =
      layerCylinderStackWeight
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p) σ := by
  rw [cubicLayerCylinderGraph]
  exact boltzmannWeight_layerCylinderGraph_eq_layerCylinderStackWeight
    (S := CubicLayerSite d R) (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p hN σ

/-- The project-level partition function of the cubic layer-cylinder graph is
the finite Ising layer-cylinder partition function. -/
theorem partitionFunction_cubicLayerCylinderGraph_eq_isingLayerCylinderPartition
    (d R : ℕ) (p : IsingParams ℝ) {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    partitionFunction (cubicLayerCylinderGraph d R N) p =
      isingLayerCylinderPartition
        (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p N := by
  rw [cubicLayerCylinderGraph]
  exact partitionFunction_layerCylinderGraph_eq_isingLayerCylinderPartition
    (S := CubicLayerSite d R) (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p hN

/-- Same-transverse-site correlations on the cubic layer-cylinder graph are the
finite layer transfer-matrix trace ratio. -/
theorem correlation_cubicLayerCylinderGraph_same_transverse_eq_trace_ratio
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    {a b : ℕ} [NeZero a] (hb : 0 < b) (hN : 3 ≤ a + b) :
    correlation (cubicLayerCylinderGraph d R (a + b)) p
        ({Prod.mk (0 : Fin (a + b)) x,
          Prod.mk ⟨a, Nat.lt_add_of_pos_right hb⟩ x} :
            Finset (LayerCylinderSite (a + b) (CubicLayerSite d R))) =
      layerTransferCorrelation_matrixElement
          (layerInternalWeight (cubicLayerGraph d R) p)
          (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
          (layerSpinAt x) a b
        / layerTransferPartitionTrace
          (layerInternalWeight (cubicLayerGraph d R) p)
          (layerTransitionWeight (cubicLayerTransitionPairs d R) p) (a + b) := by
  rw [cubicLayerCylinderGraph]
  exact correlation_layerCylinderGraph_same_transverse_eq_trace_ratio
    (S := CubicLayerSite d R) (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p x hb hN

end TransferMatrix

end IsingModel
