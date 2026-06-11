import IsingModel.Concrete.CubicTiling
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivity
import IsingModel.AmbientLatticeSumGeFerromagnetic

/-!
# Free-energy convergence on the cubic exhaustion — analytic layer (GJ §4.6)

The analytic side of GJ Proposition 4.6.1 on the cubic exhaustion: the family form of the
ferromagnetic `log Z` super-additivity, ready to be applied to the cubic tiling of
`IsingModel.Concrete.CubicTiling`.

* `log_partitionFunctionΛ_latticeGraph_biUnion_super_additive` — `∑_i log Z_{B i} ≤ log Z_{⋃ B i}`
  for pairwise disjoint families.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Proposition 4.6.1, p. 68.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **`log Z` is super-additive over finite disjoint families** (ferromagnetic, ℤ^d): Finset
induction over the binary disjoint-union super-additivity, with the ferromagnetic
non-negativity of `log Z` at the empty family. -/
theorem log_partitionFunctionΛ_latticeGraph_biUnion_super_additive
    {d : ℕ} {ι : Type*} (I : Finset ι) (B : ι → Finset (Fin d → ℤ))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∑ i ∈ I, Real.log (partitionFunctionΛ (latticeGraph d) (B i) p)
      ≤ Real.log (partitionFunctionΛ (latticeGraph d) (I.biUnion B) p) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.biUnion_empty]
    exact log_partitionFunctionΛ_nonneg_of_ferromagnetic _ _ p hf
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    have hd : Disjoint (B a) (I.biUnion B) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj a (Finset.mem_insert_self a I) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))
    have hih := ih (fun i hi j hj hij =>
      hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    calc Real.log (partitionFunctionΛ (latticeGraph d) (B a) p)
          + ∑ i ∈ I, Real.log (partitionFunctionΛ (latticeGraph d) (B i) p)
        ≤ Real.log (partitionFunctionΛ (latticeGraph d) (B a) p)
          + Real.log (partitionFunctionΛ (latticeGraph d) (I.biUnion B) p) := by
          exact add_le_add le_rfl hih
      _ ≤ Real.log (partitionFunctionΛ (latticeGraph d) (B a ∪ I.biUnion B) p) :=
          log_partitionFunctionΛ_latticeGraph_disjUnion_super_additive d hd p hf

end Ambient

end IsingModel
