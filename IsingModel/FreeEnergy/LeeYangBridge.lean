import IsingModel.FreeEnergy.ParameterMonotonicity

/-!
# Free energy Lee-Yang bridge

Mechanical child split from `IsingModel.FreeEnergy`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Configuration ↔ Finset bijection

The Lee-Yang polynomial sums over subsets `X ⊆ ι` (the "down spin" set),
while the partition function sums over configurations `σ : ι → Spin`.
The bijection is: `σ ↦ {i : σ i = down}` with inverse
`X ↦ fun i => if i ∈ X then down else up`.

This gives the connection identity (Friedli–Velenik, (3.63)–(3.65)):
`Z(J, h, β) = exp(βJ|E| + βhN) · P(z)` where `P = isingEdgePoly`,
`z_i = e^{-2βh}`, `t_e = e^{-2βJ}`. -/

/-- The "down spin" set of a configuration: `{i | σ i = Spin.down}`. -/
def configToFinset (σ : Config ι) : Finset ι :=
  Finset.univ.filter (fun i => σ i = Spin.down)

/-- The configuration corresponding to a subset (down spins). -/
def finsetToConfig (X : Finset ι) : Config ι :=
  fun i => if i ∈ X then Spin.down else Spin.up

/-- `finsetToConfig` is a left inverse of `configToFinset`. -/
@[simp]
theorem finsetToConfig_configToFinset (σ : Config ι) :
    finsetToConfig (configToFinset σ) = σ := by
  ext i; unfold finsetToConfig configToFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases σ i <;> simp

/-- `configToFinset` is a left inverse of `finsetToConfig`. -/
@[simp]
theorem configToFinset_finsetToConfig (X : Finset ι) :
    configToFinset (finsetToConfig X) = X := by
  ext i; unfold configToFinset finsetToConfig
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split <;> simp_all

/-- The bijection between configurations and subsets (down spin sets). -/
def configFinsetEquiv : Config ι ≃ Finset ι where
  toFun := configToFinset
  invFun := finsetToConfig
  left_inv := finsetToConfig_configToFinset
  right_inv := configToFinset_finsetToConfig

/-! ## Analyticity of the partition polynomial (Theorem 4.6.2, finite volume)

The Lee-Yang circle theorem (`lee_yang_circle`) shows that the Ising
partition polynomial `P(z) = Σ_{X⊆ι} w(X) ∏_{i∈X} z_i` does not vanish
on the open unit polydisk `{z : |z_k| < 1}`.

The connection `Z = exp(βJ|E| + βhN) · P(z)` via `configFinsetEquiv`
shows that `Z ≠ 0` whenever `P ≠ 0`. For the full complex analyticity
(log Z analytic on the polydisk), we need `P(z) ∈ slitPlane`, which
follows from continuity and `P(0) = 1 > 0` via a winding number argument.

Reference: Glimm–Jaffe, Theorem 4.6.2, p. 68;
Friedli–Velenik, (3.63)–(3.65), pp. 122–123. -/

/-- Convert a SimpleGraph's edges to the edge list format used by `lee_yang_circle`.
Each edge `e` is represented as `(e.out.1, e.out.2, t)` with uniform coupling `t`. -/
noncomputable def graphToEdgeList (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) : List (ι × ι × ℝ) :=
  G.edgeFinset.toList.map fun e => ((Quot.out e).1, (Quot.out e).2, t)

omit [Fintype ι] [DecidableEq ι] in
/-- Each entry in `graphToEdgeList` has distinct endpoints. -/
private theorem graphToEdgeList_distinct (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) : ∀ e ∈ graphToEdgeList G t, e.1 ≠ e.2.1 := by
  intro e he
  simp only [graphToEdgeList, List.mem_map, Finset.mem_toList] at he
  obtain ⟨edge, he_mem, he_eq⟩ := he
  have hadj : G.Adj (Quot.out edge).1 (Quot.out edge).2 := by
    have h := SimpleGraph.mem_edgeFinset.mp he_mem
    rwa [show edge = s((Quot.out edge).1, (Quot.out edge).2) from by
      conv_lhs => rw [← Quot.out_eq edge], SimpleGraph.mem_edgeSet] at h
  simp only [← he_eq]; exact hadj.ne

omit [Fintype ι] [DecidableEq ι] in
/-- Each entry in `graphToEdgeList` has coupling in `[0, 1)`. -/
private theorem graphToEdgeList_coupling (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ∀ e ∈ graphToEdgeList G t, 0 ≤ e.2.2 ∧ e.2.2 < 1 := by
  intro e he
  simp only [graphToEdgeList, List.mem_map, Finset.mem_toList] at he
  obtain ⟨_, _, he_eq⟩ := he
  simp only [← he_eq]; exact ⟨ht₀, ht₁⟩

/-- **Lee-Yang nonvanishing for the Ising partition polynomial**
(Glimm–Jaffe, §4.5–4.6; Friedli–Velenik, Theorem 3.43, pp. 122–127):

For the Ising model on graph `G` with coupling `t = e^{-2βJ}` (`0 ≤ t < 1`,
i.e., `J > 0`), the partition polynomial `P(z)` does not vanish on the
open unit polydisk `{z : |z_k| < 1}`. Here `z_k = e^{-2βh_k}` is the
fugacity at site `k`.

This is the finite-volume version of Theorem 4.6.2: since
`Z = exp(βJ|E| + βhN) · P(z)` and `exp(...) > 0`, the nonvanishing
of `P` is equivalent to `Z ≠ 0`. -/
theorem isingEdgePoly_nonvanishing_of_graph
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (z : ι → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    (isingEdgePoly (graphToEdgeList G t)).eval z ≠ 0 :=
  lee_yang_circle _ (graphToEdgeList_distinct G t) (graphToEdgeList_coupling G t ht₀ ht₁) z hz

end IsingModel
