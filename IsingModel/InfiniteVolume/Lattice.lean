import IsingModel.InfiniteVolume.MonotoneH

/-!
# Infinite-volume correlations split — monotonicity and convergence along subgraph chains

Part of the split infinite-volume correlation layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in the lattice (Theorem 4.2.3, lattice version)

For a fixed ambient finite lattice `ι` and ferromagnetic parameters `p`,
if `G₁ ≤ G₂` (subgraph of the interaction graph), then the correlation
function is monotone: `⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}`.

This is the *discretized* formalization of GJ §4.2 Thm 4.2.3's statement
"`Λ ↑ ℝᵈ`": increasing the lattice corresponds to turning on couplings
`J_A : 0 → βJ` for new edges. The original GJ statement is over an
infinite ambient lattice with finite-volume exhaustions; our version
uses a fixed finite ambient lattice with growing subgraphs, preserving
the proof mechanism (GKS-I + monotonicity + boundedness).

Reference: Glimm–Jaffe, Theorem 4.2.3, p. 59. -/

/-- HNC of a product `∏_{e ∈ E} exp(K e · edgeSpin σ e)` over an arbitrary
non-diagonal Finset `E` of `Sym2 ι`, with non-negative `K`.
A graph-free variant of `hasNonnegCorrelations_edge_site_product`. -/
private theorem hasNonnegCorrelations_edge_prod_of_finset
    (E : Finset (Sym2 ι)) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (K : Sym2 ι → ℝ) (hK : ∀ e ∈ E, 0 ≤ K e) :
    HasNonnegCorrelations
      (fun σ => ∏ e ∈ E, Real.exp (K e * edgeSpin (K := ℝ) σ e)) := by
  apply hasNonnegCorrelations_finset_prod
  intro e he
  obtain ⟨⟨i, j⟩, rfl⟩ := Quot.exists_rep e
  have hne : i ≠ j := fun hij => hE _ he (Sym2.mk_isDiag_iff.mpr hij)
  refine ⟨Real.cosh (K (Quot.mk _ (i, j))),
    Real.sinh (K (Quot.mk _ (i, j))), {i, j},
    (Real.cosh_pos _).le,
    Real.sinh_nonneg_iff.mpr (hK _ he), fun σ => ?_⟩
  simp only [spinProduct, Finset.prod_pair hne]
  exact exp_edgeSpin_decomp _ σ _

/-- The Boltzmann weight on a larger graph factors through a reweighting
`R(σ) = ∏_{e ∈ E(G₂)\E(G₁)} exp(βJ · edgeSpin σ e)`:
`w_{G₂}(σ) = R(σ) · w_{G₁}(σ)`. -/
theorem boltzmannWeight_subgraph_factor
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (σ : Config ι) :
    boltzmannWeight G₂ p σ =
    (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
      Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
    boltzmannWeight G₁ p σ := by
  have hsub : G₁.edgeFinset ⊆ G₂.edgeFinset := SimpleGraph.edgeFinset_mono h₁₂
  rw [← Real.exp_sum]
  unfold boltzmannWeight
  rw [← Real.exp_add]
  congr 1
  unfold hamiltonian interactionEnergy externalFieldEnergy
  have hdis : ∑ e ∈ G₂.edgeFinset, edgeSpin (K := ℝ) σ e =
      ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset, edgeSpin (K := ℝ) σ e +
      ∑ e ∈ G₁.edgeFinset, edgeSpin (K := ℝ) σ e := by
    rw [← Finset.sum_sdiff hsub, add_comm]
  rw [show ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset, p.β * p.J * edgeSpin (K := ℝ) σ e =
      p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset, edgeSpin (K := ℝ) σ e from by
      rw [Finset.mul_sum]]
  rw [hdis]
  ring

/-- **Theorem 4.2.3** (Glimm–Jaffe, p. 59; lattice version):
For a ferromagnetic Ising model, the correlation function is monotone
under the subgraph ordering: if `G₁ ≤ G₂` (as `SimpleGraph` on the
ambient lattice `ι`), then `⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}`.

Proof: Factor `w_{G₂} = R · w_{G₁}` where `R` has HNC (since it is a
product of non-negative-coefficient exponentials of edge spins), then
apply `cov_hnc_boltzmann_nonneg` on the base graph `G₁`. -/
theorem correlation_monotone_subgraph
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset ι) :
    correlation G₁ p A ≤ correlation G₂ p A := by
  set R : Config ι → ℝ := fun σ =>
    ∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
      Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e) with hR_def
  have hR : HasNonnegCorrelations R :=
    hasNonnegCorrelations_edge_prod_of_finset
      (G₂.edgeFinset \ G₁.edgeFinset)
      (fun e he =>
        G₂.not_isDiag_of_mem_edgeFinset (Finset.mem_sdiff.mp he).1)
      (fun _ => p.β * p.J)
      (fun _ _ => mul_nonneg hf.hβ.le hf.hJ)
  have hfact : ∀ σ, boltzmannWeight G₂ p σ = R σ * boltzmannWeight G₁ p σ :=
    fun σ => boltzmannWeight_subgraph_factor h₁₂ p σ
  have hcov := cov_hnc_boltzmann_nonneg G₁ p hf R hR A
  have hnum : ∑ σ : Config ι, spinProduct A σ * R σ * boltzmannWeight G₁ p σ =
      ∑ σ, spinProduct A σ * boltzmannWeight G₂ p σ := by
    apply Finset.sum_congr rfl; intro σ _
    rw [hfact σ]; ring
  have hden : ∑ σ : Config ι, R σ * boltzmannWeight G₁ p σ =
      ∑ σ, boltzmannWeight G₂ p σ := by
    apply Finset.sum_congr rfl; intro σ _
    exact (hfact σ).symm
  rw [hnum, hden] at hcov
  have hZ₁ := partitionFunction_pos G₁ p
  have hZ₂ := partitionFunction_pos G₂ p
  unfold correlation gibbsExpectation partitionFunction
  unfold partitionFunction at hZ₁ hZ₂
  rw [mul_comm ((∑ σ : Config ι, boltzmannWeight G₁ p σ)⁻¹)
      (∑ σ, spinProduct A σ * boltzmannWeight G₁ p σ),
      mul_comm ((∑ σ : Config ι, boltzmannWeight G₂ p σ)⁻¹)
      (∑ σ, spinProduct A σ * boltzmannWeight G₂ p σ)]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ hZ₁ hZ₂]
  linarith

/-! ## Convergence along an increasing chain of subgraphs

For an increasing sequence of subgraphs `Gn : ℕ → SimpleGraph ι` with
ferromagnetic parameters, the correlation function `n ↦ ⟨σ^A⟩_{Gn n}`
is monotone (by `correlation_monotone_subgraph`) and bounded above by
`1` (by `correlation_le_one`), hence convergent by monotone-bounded. -/

/-- **Theorem 4.2.3** (Glimm–Jaffe, p. 59; lattice version, convergence):
For any increasing sequence of subgraphs `Gₙ ↑` on a fixed ambient finite
lattice, with ferromagnetic parameters, the correlation function
`n ↦ ⟨σ^A⟩_{Gₙ}` converges as `n → ∞`. -/
theorem correlation_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation (Gn n) p A)
      Filter.atTop (nhds L) := by
  have hcorr_mono : Monotone (fun n : ℕ => correlation (Gn n) p A) :=
    fun a b hab => correlation_monotone_subgraph (hmono hab) p hf A
  have hbdd : BddAbove (Set.range (fun n : ℕ => correlation (Gn n) p A)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ correlation_le_one (Gn n) p A⟩
  exact ⟨_, tendsto_atTop_ciSup hcorr_mono hbdd⟩

/-! ## Named corollaries of the lattice-growth convergence

Direct specializations of `correlation_convergent_subgraph` at the most
physically relevant subsets: single-site magnetization `⟨σᵢ⟩` and
two-point correlation `⟨σᵢσⱼ⟩`.  Both are used downstream in §5
(symmetry breaking, phase transitions). -/

/-- **Magnetization convergence** (Glimm–Jaffe, §5.3 context):
the single-site magnetization `⟨σᵢ⟩_{Gₙ}` converges along any increasing
subgraph sequence. Direct specialization of `correlation_convergent_subgraph`
to `A = {i}`. -/
theorem magnetization_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation (Gn n) p {i})
      Filter.atTop (nhds L) :=
  correlation_convergent_subgraph Gn hmono p hf {i}

/-- **Two-point correlation convergence** (Glimm–Jaffe, §5.1 context):
the two-point correlation `⟨σᵢσⱼ⟩_{Gₙ}` converges along any increasing
subgraph sequence. Direct specialization of `correlation_convergent_subgraph`
to `A = {i, j}`. -/
theorem twoPoint_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation (Gn n) p {i, j})
      Filter.atTop (nhds L) :=
  correlation_convergent_subgraph Gn hmono p hf {i, j}


end IsingModel
