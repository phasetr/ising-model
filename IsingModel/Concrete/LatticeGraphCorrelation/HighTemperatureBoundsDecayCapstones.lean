import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesDist

/-!
# ℤ^d exponential decay of the pair correlation in graph distance (§18.7)

Instantiates at `IsingModel.latticeGraph d`, at the parameter record `⟨J, 0, β⟩`, the decay
bound `2 ^ |E| * tanh (β * J) ^ dist i j` on the pair correlation, on a fixed finite volume
`Λ` and at a stage `n` of an `Ambient.Exhaustion` of `Fin d → ℤ`. Each version is stated under
`0 ≤ β * J` and again in a ferromagnetic form under `0 ≤ J` together with `0 < β`. The
distance is graph distance in the induced subgraph carrying the correlation, and the
along-exhaustion version is stated for `correlationΛ` on `Λ.volume n` rather than for
`correlationAlongExhaustion`.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ §18.7 capstone: high-temperature exponential decay of the
pair correlation in graph distance**. Under `0 ≤ β·J` for `i, j : ↑Λ`,
`⟨σ_iσ_j⟩^Λ_{β,0} ≤ 2^{|E_Λ|} ·
    tanh(β·J)^{(inducedGraph (latticeGraph d) Λ).dist i j}`.
ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`. -/
theorem
correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound on `latticeGraph d` for `i, j : ↑Λ`. -/
theorem
correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j :=
  correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    d Λ J β (mul_nonneg hβ.le hJ) i j

/-- **ℤ^d along-ex §18.7 capstone: high-temperature exponential decay
of the pair correlation in graph distance, at stage `n`**. Under
`0 ≤ β·J` for `i, j : ↑(Λ.volume n)`,
`⟨σ_iσ_j⟩^{Λ_n}_{β,0} ≤ 2^{|E_{Λ_n}|} ·
    tanh(β·J)^{(inducedGraph (latticeGraph d) (Λ.volume n)).dist i j}`.
ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`. -/
theorem
correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).dist i j :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (IsingModel.latticeGraph d) Λ J β hβJ n i j

/-- **ℤ^d along-ex §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound at stage `n` on `latticeGraph d`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).dist i j :=
correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
  d Λ J β (mul_nonneg hβ.le hJ) n i j

end Ambient

end IsingModel
