import IsingModel.AmbientLattice.TruncatedFunctions.TwoPoint

/-!
# Infinite-volume cluster property and two-point monotonicity

Mechanical child split from `AmbientLattice/TruncatedFunctions.lean`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## §5.1 cluster property: definition + sufficient condition + trivial slices

Bundled formalization of the Glimm–Jaffe §5.1 cluster property
for ferromagnets. The cluster property states that the truncated
2-point function $U_2(i, j) = \langle\sigma_i\sigma_j\rangle -
\langle\sigma_i\rangle\langle\sigma_j\rangle$ decays to $0$ as the
second site moves away to infinity.

Captured here: the formal predicate, a summable sufficient
condition consolidating
`truncated2Infinite_tendsto_cofinite_zero_of_summable`, and the
two trivial slices ($J = 0$ ferromagnetic, $\beta = 0$). The
general (non-trivial) case requires the Simon–Lieb inequality
(Simon 1980, Comm. Math. Phys. 77, 111–126; Lieb 1980, Comm.
Math. Phys. 77, 127–135) or random-current representation, both
research-level.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 76–79. -/

/-- **§5.1 cluster property** for the ∞-volume Ursell 2-point
function: at every fixed basepoint `i : V`, the function
`j ↦ truncated2Infinite G Λ p i j` tends to `0` along the
cofinite filter on `V`. A Glimm–Jaffe §5.1-motivated predicate
on `(G, Λ, p)`; the predicate itself does not build in a
ferromagnetic hypothesis, but the expected nontrivial positive
results (e.g.\ at high temperature or under a Simon–Lieb-type
summability assumption) apply in ferromagnetic regimes. -/
def clusterProperty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : Prop :=
  ∀ i : V, Filter.Tendsto (fun j : V => truncated2Infinite G Λ p i j)
    Filter.cofinite (nhds 0)

/-- **Cluster property from per-site summability**: if the
∞-volume Ursell 2-point function `j ↦ U_2(i, j)` is `Summable`
for every basepoint `i : V`, then the cluster property holds.
Per-site application of `truncated2Infinite_tendsto_cofinite_zero_of_summable`. -/
theorem clusterProperty_of_summable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hsum : ∀ i : V,
      Summable (fun j : V => truncated2Infinite G Λ p i j)) :
    clusterProperty G Λ p :=
  fun i => truncated2Infinite_tendsto_cofinite_zero_of_summable G Λ p i (hsum i)

/-- **Cluster property at the `J = 0` trivial slice (ferromagnetic)**.
At zero coupling with `0 ≤ h, 0 < β`, the truncated 2-point function
vanishes off-diagonally (`truncated2Infinite_J_zero_of_ne`). The
cofinite filter on `V` eventually avoids the singleton `{i}`, so
the function is eventually zero, hence trivially `Tendsto`s to `0`. -/
theorem clusterProperty_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    clusterProperty G Λ (⟨0, h, β⟩ : IsingParams ℝ) := by
  intro i
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  -- Eventually along cofinite: the function equals the constant 0.
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨{i}ᶜ, ?_, ?_⟩
  · rw [Filter.mem_cofinite]
    simp [Set.finite_singleton]
  · intro j hj
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hj
    exact (truncated2Infinite_J_zero_of_ne G Λ h β hf (Ne.symm hj)).symm

/-- **Cluster property at the `β = 0` trivial slice**. At infinite
temperature, the truncated 2-point function vanishes identically
(`truncated2Infinite_beta_zero`), so the function is the constant
zero, which trivially `Tendsto`s to `0`. No ferromagnetic
hypothesis required. -/
theorem clusterProperty_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) :
    clusterProperty G Λ (⟨J, h, 0⟩ : IsingParams ℝ) := by
  intro i
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  intro j _
  exact (truncated2Infinite_beta_zero G Λ J h i j).symm

/-! ## GHS consequence at infinite volume: truncated2Infinite antitone in h (Step 125)

Lift Step 124 (`truncated2_antitoneOn_h_of_ne`) from finite to infinite volume
via the exhaustion limit.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.4; Friedli–Velenik §3.6.3. -/

/-- **Truncated 2-point along an exhaustion** (local helper): the stage-`n`
finite-volume approximation to `truncated2Infinite`.  Parallel to
`truncated3AlongExhaustion`; bridges the finite-volume
`truncated2_antitoneOn_h_of_ne` (Step 124) with the infinite-volume limit. -/
private noncomputable def truncated2AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j : V) (n : ℕ) : ℝ :=
  correlationAlongExhaustion G Λ p {i, j} n
    - correlationAlongExhaustion G Λ p {i} n
      * correlationAlongExhaustion G Λ p {j} n

/-- **Tendsto for the truncated 2-point sequence**: `truncated2AlongExhaustion`
converges to `truncated2Infinite`.  Apply `Tendsto.sub` and `Tendsto.mul` to
the three convergences from
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
private theorem tendsto_truncated2AlongExhaustion_truncated2Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    Filter.Tendsto
      (truncated2AlongExhaustion G Λ p i j)
      Filter.atTop
      (nhds (truncated2Infinite G Λ p i j)) := by
  unfold truncated2AlongExhaustion truncated2Infinite
  have h_ij := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i, j}
  have h_i := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i}
  have h_j := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j}
  exact h_ij.sub (h_i.mul h_j)

/-- **GHS consequence at infinite volume**: for ferromagnetic Ising and distinct
sites `i ≠ j`, the function `h ↦ truncated2Infinite G Λ ⟨J, h, β⟩ i j` is
antitone on `[0, ∞)`.

Proof: at each stage `n` with `{i, j} ⊆ Λ.volume n`, Step 124
(`truncated2_antitoneOn_h_of_ne`) gives the finite-volume antitone bound.
Pass to the limit via `le_of_tendsto_of_tendsto`.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.4; Friedli–Velenik §3.6.3. -/
theorem truncated2Infinite_antitoneOn_h_of_ne
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) {i j : V} (hij : i ≠ j) :
    AntitoneOn (fun h => truncated2Infinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i j) (Set.Ici 0) := by
  intro h₁ hh₁ h₂ hh₂ hle
  refine le_of_tendsto_of_tendsto
    (tendsto_truncated2AlongExhaustion_truncated2Infinite G Λ ⟨J, h₂, β⟩
      ⟨hJ, Set.mem_Ici.mp hh₂, hβ⟩ i j)
    (tendsto_truncated2AlongExhaustion_truncated2Infinite G Λ ⟨J, h₁, β⟩
      ⟨hJ, Set.mem_Ici.mp hh₁, hβ⟩ i j)
    ?_
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j} : Finset V)
  unfold Filter.EventuallyLE
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hab : ({i, j} : Finset V) ⊆ Λ.volume n := hN n hn
  have ha : ({i} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx; exact hab (by simp)
  have hb : ({j} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx; exact hab (by simp)
  change truncated2AlongExhaustion G Λ ⟨J, h₂, β⟩ i j n ≤
    truncated2AlongExhaustion G Λ ⟨J, h₁, β⟩ i j n
  unfold truncated2AlongExhaustion
  rw [correlationAlongExhaustion_of_subset G Λ ⟨J, h₂, β⟩ hab,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₂, β⟩ ha,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₂, β⟩ hb,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₁, β⟩ hab,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₁, β⟩ ha,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₁, β⟩ hb]
  have hlift_ij : liftFinset ({i, j} : Finset V) hab
      = ({⟨i, ha (by simp)⟩, ⟨j, hb (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (by rfl)
    · rintro (rfl | rfl) <;> simp
  have hlift_i : liftFinset ({i} : Finset V) ha
      = ({⟨i, ha (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_j : liftFinset ({j} : Finset V) hb
      = ({⟨j, hb (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  simp only [correlationΛ, hlift_ij, hlift_i, hlift_j]
  have hij' : (⟨i, ha (by simp)⟩ : ↑(Λ.volume n)) ≠ ⟨j, hb (by simp)⟩ :=
    fun h => hij (Subtype.mk.inj h)
  have hanti := IsingModel.truncated2_antitoneOn_h_of_ne
    (inducedGraph G (Λ.volume n)) J hJ β hβ hij' hh₁ hh₂ hle
  unfold IsingModel.truncated2 at hanti
  linarith


end Ambient
end IsingModel
