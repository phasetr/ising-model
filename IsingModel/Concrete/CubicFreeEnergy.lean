import IsingModel.Concrete.CubicTiling
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivity
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationShiftsVaddFinset
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

/-- **Tiling lower bound for `log Z` on cubes** (ferromagnetic): the cube of radius
`(2r+1)M + r` contains `(2M+1)^d` disjoint translates of the radius-`r` cube, so
`(2M+1)^d · log Z_{B_r} ≤ log Z_{B_{(2r+1)M+r}}`. -/
theorem log_partitionFunctionΛ_cubicBox_tiling_le (d r M : ℕ) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    ((2 * M + 1 : ℕ) ^ d : ℝ)
        * Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d r) p)
      ≤ Real.log (partitionFunctionΛ (latticeGraph d)
          (cubicBox d ((2 * r + 1) * M + r)) p) := by
  have hsum := log_partitionFunctionΛ_latticeGraph_biUnion_super_additive
    (cubicBox d M) (cubicTile d r)
    (fun i _ j _ hij => cubicTile_disjoint hij) p hf
  have hterm : ∀ k ∈ cubicBox d M,
      Real.log (partitionFunctionΛ (latticeGraph d) (cubicTile d r k) p)
        = Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d r) p) := by
    intro k _
    exact log_partitionFunctionΛ_latticeGraph_vaddFinset_eq d (cubicTileCenter r k)
      (cubicBox d r) p
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_cubicBox, nsmul_eq_mul] at hsum
  rw [partitionFunctionΛ_latticeGraph_congr_finset d (biUnion_cubicTile d r M) p] at hsum
  exact_mod_cast hsum

end Ambient

end IsingModel
