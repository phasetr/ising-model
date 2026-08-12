import IsingModel.AmbientLattice.CorrelationDecay
import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.Lattice
import IsingModel.Inequalities.HighTemp.SummabilityCluster

/-!
# ℤ^d cluster decay and high-temperature correlation bounds

Concrete `latticeGraph d` statements about how the infinite-volume Ursell two-point function
falls off with distance, and about exponential bounds on the finite-volume pair correlation
at zero external field.

Along an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ` and for an arbitrary parameter record,
summability of `j ↦ truncated2Infinite … i j` at a fixed site `i` gives convergence to `0`
along `Filter.cofinite`, and equally along the filter pulled back from `Filter.atTop` by
`latticeDistance d i`. That summability is then discharged in the ferromagnetic
high-temperature regime: for `⟨J, 0, β⟩` satisfying `Ferromagnetic` and `β * J * (2 * d) < 1`
the function is summable, since the induced lattice graph has at most `2 * d` incident edges
at each vertex, so the cofinite and the pulled-back convergence hold in that regime with no
summability assumed.

At zero external field, and under `0 ≤ J` and `0 < β`, the pair correlation of two vertices
is bounded by `2` raised to the induced edge-set cardinality times the exponential of minus
`highTempExpRate β J` times the induced-graph distance, and, in the monotone form, of minus
any `α ≤ highTempExpRate β J` times that distance. The vertices are not assumed distinct.
Each of these bounds appears for an arbitrary finite volume and at one stage of an arbitrary
exhaustion, the stage form additionally requiring a `Fintype` instance on the induced edge
set at every stage. A file-local `Fintype` instance supplies that finiteness on an arbitrary
finite volume.
-/

namespace IsingModel
namespace Ambient

/-- The finite induced subgraph of `latticeGraph d` on any finite volume
has a finite edge set. This local instance keeps the lightweight concrete
correlation-decay wrappers independent of heavier concrete modules. -/
noncomputable local instance fintype_induced_latticeGraph_edgeSet
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
  classical
  exact SimpleGraph.fintypeEdgeSet _

/-- **ℤ^d conditional cluster decay (cofinite form)**: on ℤ^d, if the
∞-volume Ursell 2-point function at a fixed site `i : Fin d → ℤ`,
viewed as a function of the free site `j : Fin d → ℤ`, is summable,
then it tends to `0` along `Filter.cofinite` (which on `Fin d → ℤ`
coincides with the "|r| → ∞" filter). Concrete `latticeGraph d`
wrapper for PR #779's
`truncated2Infinite_tendsto_cofinite_zero_of_summable`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_summable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ)
    (hsum : Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)
      Filter.cofinite (nhds 0) :=
  truncated2Infinite_tendsto_cofinite_zero_of_summable
    (IsingModel.latticeGraph d) Λ p i hsum

/-- **ℤ^d distance-based conditional cluster decay**: under
summability of `j ↦ U_2(i, j)` at a fixed basepoint
`i : Fin d → ℤ`, the ∞-volume Ursell 2-point function tends to `0`
as the lattice distance `latticeDistance d i j` tends to infinity.

Equivalent ε-N statement: for every `ε > 0` there exists `N : ℕ`
such that `latticeDistance d i j ≥ N` implies
`|truncated2Infinite (latticeGraph d) Λ p i j| < ε`.

A `Summable`-conditioned corollary, not a standalone Glimm–Jaffe
result: it presents the §5.1 cluster picture in its distance-based
form, with the `Summable` hypothesis serving as a placeholder for
the unconditional summability later supplied in high-temperature regimes by
the Simon–Lieb stack (Simon 1980; Lieb 1980). This PR #783-era capstone
of the §5.1 cluster-decay infrastructure stack (PR #779 + PR #781 + PR #782)
remains the conditional distance-form wrapper. The proof is a one-line rewrite
of the comap filter via `comap_latticeDistance_atTop_eq_cofinite`, followed by
PR #779's cofinite version.

References: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1
pp. 72–74; for the Simon–Lieb inequality, Simon 1980, Comm.
Math. Phys. 77, 111–126 and Lieb 1980, Comm. Math. Phys. 77,
127–135. -/
theorem truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ)
    (hsum : Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)
      (Filter.comap (fun j : Fin d → ℤ =>
        IsingModel.latticeDistance d i j) Filter.atTop) (nhds 0) := by
  rw [IsingModel.comap_latticeDistance_atTop_eq_cofinite]
  exact truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_summable
    d Λ p i hsum

/-- **ℤ^d Λ ferromagnetic §18.7 named-rate capstone**: under
`0 ≤ J, 0 < β`, the finite-volume pair-correlation distance bound on
`latticeGraph d` is written with `highTempExpRate`. -/
theorem
correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j

/-- **ℤ^d along-ex ferromagnetic §18.7 named-rate capstone at stage
`n`**: under `0 ≤ J, 0 < β`, the finite-volume pair-correlation distance
bound on `latticeGraph d` is written with `highTempExpRate`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_highTempExpRate_dist_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_highTempExpRate_dist_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n i j

/-- **ℤ^d Λ ferromagnetic §18.7 named monotone-rate capstone**: under
`0 ≤ J, 0 < β`, any `α ≤ highTempExpRate β J` gives the finite-volume
pair-correlation distance bound on `latticeGraph d` with rate `α`. -/
theorem correlationΛ_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β α : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ highTempExpRate β J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β α hJ hβ hα i j

/-- **ℤ^d along-ex ferromagnetic §18.7 named monotone-rate capstone at
stage `n`**: under `0 ≤ J, 0 < β`, any
`α ≤ highTempExpRate β J` gives the finite-volume pair-correlation
distance bound on `latticeGraph d` with rate `α`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ highTempExpRate β J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-α *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferro
    (IsingModel.latticeGraph d) Λ J β α hJ hβ hα n i j

/-- **ℤ^d high-temperature summability of the Ursell two-point function** (GJ §5.1; FV §3.7.3): for
the `d`-dimensional lattice with any exhaustion `Λ`, ferromagnetic `⟨J, 0, β⟩`, and `β·J·2d < 1`,
the infinite-volume Ursell two-point function `j ↦ U₂(i, j)` is summable.  The induced cubic-lattice
graph has per-vertex incident-edge count `≤ 2d`, so `truncated2Infinite_summable_of_high_temp`
applies with `D = 2d`. -/
theorem truncated2Infinite_latticeGraph_summable_of_high_temp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β J : ℝ}
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j) := by
  classical
  refine truncated2Infinite_summable_of_high_temp
    (IsingModel.latticeGraph d) Λ hf (D := 2 * d) ?_ hlt i
  intro n v
  rw [edgeFilter_card_eq_degree v]
  exact inducedLatticeGraph_degree_le d _ v

/-- **ℤ^d unconditional high-temperature distance cluster decay** (GJ §5.1).

Unconditional version of `truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable`: for the
`d`-dimensional lattice with any exhaustion `Λ`, ferromagnetic `⟨J, 0, β⟩`, and the Simon–Lieb
high-temperature condition `β·J·2d < 1`, the infinite-volume Ursell two-point function `U₂(i, j)`
tends to `0` as `latticeDistance d i j → ∞`.  The `Summable` hypothesis is discharged by
`truncated2Infinite_latticeGraph_summable_of_high_temp`. -/
theorem truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_high_temp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β J : ℝ}
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j)
      (Filter.comap (fun j : Fin d → ℤ => IsingModel.latticeDistance d i j) Filter.atTop)
      (nhds 0) :=
  truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) i
    (truncated2Infinite_latticeGraph_summable_of_high_temp d Λ hf hlt i)

/-- **ℤ^d unconditional high-temperature distance cluster decay (cofinite form)** (GJ §5.1): the
`Filter.cofinite` companion of `truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_high_temp`. -/
theorem truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_high_temp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β J : ℝ}
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j)
      Filter.cofinite (nhds 0) :=
  truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_summable d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) i
    (truncated2Infinite_latticeGraph_summable_of_high_temp d Λ hf hlt i)

end Ambient
end IsingModel
