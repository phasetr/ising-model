import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxPlusStateBounds
import IsingModel.Concrete.CubicBoxAdjacencyGeometry
import IsingModel.AmbientLattice.Monotonicity.InducedWeightFactor

/-!
# Cubic-box screening conditions for the `+` state (Issue #3565)

The frozen-`+` ingredients that turn the generic Boltzmann-weight factoring
(`boltzmannWeight_inducedGraph_restrict_factor_const`, #3571) into the
nearest-neighbour **screening** of the cubic-box `+` state:

* `boltzmannWeightJ_uniform_eq` — the inhomogeneous Boltzmann weight at a uniform
  coupling equals the ordinary Boltzmann weight, bridging the boundary-condition
  framework (`boltzmannWeightBC = indicator · boltzmannWeightJ`) to the
  uniform-coupling factoring lemmas.
* `cubicBox_extra_edge_endpoints_not_mem_inner` — both endpoints of an extra edge
  (in the induced graph on `cubicBox d (m+1)` but not in the extension graph over
  `cubicBox d m`) lie outside `cubicBox d n`, for `n + 1 ≤ m`.

These feed the `hcompl` / `hextra` hypotheses of
`boltzmannWeight_inducedGraph_restrict_factor_const` when the configuration is
`+` outside `cubicBox d n`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22, §6.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Uniform inhomogeneous weight equals the ordinary Boltzmann weight**: for the
constant coupling `fun _ => J`, `boltzmannWeightJ G β (fun _ => J) h σ =
boltzmannWeight G ⟨J, h, β⟩ σ`.  Bridges the boundary-condition framework (built on
`boltzmannWeightJ`) to the uniform-coupling factoring lemmas. -/
theorem boltzmannWeightJ_uniform_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (σ : Config ι) :
    boltzmannWeightJ G β (fun _ => J) h σ = boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ := by
  have hI : interactionEnergyJ G (fun _ => J) σ = interactionEnergy G J σ := by
    unfold interactionEnergyJ interactionEnergy
    simp [Finset.mul_sum]
  unfold boltzmannWeightJ boltzmannWeight hamiltonianJ hamiltonian
  rw [hI]

namespace Ambient

/-- **Both endpoints of a cubic-box extra edge avoid the inner box**: for
`n + 1 ≤ m`, if an edge `e` of `inducedGraph (latticeGraph d) (cubicBox d (m+1))`
is **not** an edge of `extendGraphFromΛ₁ (latticeGraph d) (cubicBox d m)
(cubicBox d (m+1))` (an "extra edge", touching the shell), then both endpoints `u`
of `e` have `u.val ∉ cubicBox d n`.  Consequently, for a configuration that is `+`
outside `cubicBox d n`, the edge spin on every extra edge is `1`.

Proof: the edge is adjacent in the lattice graph; not being in the extension graph
means at least one endpoint lies outside `cubicBox d m` (in the shell), and then
`cubicBox_shell_adj_not_mem_inner` places the other endpoint outside
`cubicBox d n` as well. -/
theorem cubicBox_extra_edge_endpoints_not_mem_inner {d n m : ℕ} (hnm : n + 1 ≤ m)
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
      (cubicBox d (m + 1))).edgeSet]
    {e : Sym2 ↑(cubicBox d (m + 1))}
    (hmem : e ∈ (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (m + 1))).edgeFinset \
        (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
          (cubicBox d (m + 1))).edgeFinset) :
    ∀ u ∈ e, (u : Fin d → ℤ) ∉ cubicBox d n := by
  rw [Finset.mem_sdiff] at hmem
  obtain ⟨hin, hout⟩ := hmem
  revert hin hout
  refine Sym2.ind (fun a b => ?_) e
  intro hin hout
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hin
  have hadj : (IsingModel.latticeGraph d).Adj (a : Fin d → ℤ) (b : Fin d → ℤ) := hin
  -- Not in the extension graph (given adjacency) ⟹ some endpoint is outside `cubicBox d m`.
  have hnot : ¬ ((a : Fin d → ℤ) ∈ cubicBox d m ∧ (b : Fin d → ℤ) ∈ cubicBox d m) := by
    intro ⟨ha, hb⟩
    exact hout (by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ⟨ha, hb, hadj⟩)
  -- Whichever endpoint is in the shell, both endpoints avoid `cubicBox d n`.
  have hnm' : n ≤ m := by omega
  have key : (a : Fin d → ℤ) ∉ cubicBox d n ∧ (b : Fin d → ℤ) ∉ cubicBox d n := by
    by_cases ha : (a : Fin d → ℤ) ∈ cubicBox d m
    · -- then `b ∉ box m`, so `b` is a shell site
      have hb : (b : Fin d → ℤ) ∉ cubicBox d m := fun hb => hnot ⟨ha, hb⟩
      have hbshell : (b : Fin d → ℤ) ∈ cubicBox d (m + 1) \ cubicBox d m :=
        Finset.mem_sdiff.mpr ⟨b.2, hb⟩
      exact ⟨cubicBox_shell_adj_not_mem_inner hnm hbshell hadj.symm,
        fun hbn => hb (cubicBox_mono d hnm' hbn)⟩
    · -- `a` is a shell site
      have hashell : (a : Fin d → ℤ) ∈ cubicBox d (m + 1) \ cubicBox d m :=
        Finset.mem_sdiff.mpr ⟨a.2, ha⟩
      exact ⟨fun han => ha (cubicBox_mono d hnm' han),
        cubicBox_shell_adj_not_mem_inner hnm hashell hadj⟩
  intro u hu
  rw [Sym2.mem_iff] at hu
  rcases hu with rfl | rfl
  · exact key.1
  · exact key.2

end Ambient

end IsingModel
