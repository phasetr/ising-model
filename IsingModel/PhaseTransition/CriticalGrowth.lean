import IsingModel.PhaseTransition.MagnetizationSusceptibility

/-!
# Critical-growth and convergence wrappers

This module contains the critical-exponent and lattice-growth wrappers split from
`IsingModel.PhaseTransition`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Free energy convexity and phase transitions (§16.1)

Glimm–Jaffe §16.1 (pp. 280–284) discusses the thermodynamic
characterization of phase transitions.

Key results for the Ising model:
1. `da/dh = ⟨σ_i⟩ = M` (magnetization) — eq. (16.1.8)
2. `d²a/dh² = Σ_j ⟨σ_i; σ_j⟩ = χ ≥ 0` (susceptibility) — eq. (16.1.9)
3. `a(h)` is convex in `h` since `χ ≥ 0`
4. A first-order phase transition occurs at `h₀` iff `M(h)` is
   discontinuous at `h₀`

For finite volume: `f(h)` is real-analytic (`freeEnergyH_analyticOn`),
so there are no phase transitions. Phase transitions appear only in the
infinite volume limit `Λ ↑ Zᵈ`.

The convexity `χ ≥ 0` is already proved as `susceptibility_nonneg`.
The monotonicity `M(h₁) ≤ M(h₂)` for `h₁ ≤ h₂` follows from
`correlation_monotone_h`. -/

/-- **Magnetization monotonicity** (Glimm–Jaffe, §16.1, p. 283).
The magnetization `M(i) = ⟨σ_i⟩` is monotone increasing in `h` on `[0, ∞)`
for ferromagnetic parameters. This is the lattice version of the fact
that `da/dh` is monotone (since `d²a/dh² = χ ≥ 0`). -/
theorem magnetization_monotone_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : ι) :
    MonotoneOn (fun h => magnetization G ⟨J, h, β⟩ i) (Set.Ici 0) := by
  intro h₁ hh₁ h₂ hh₂ hh
  unfold magnetization
  exact correlation_monotone_h G J hJ β hβ {i} hh₁ hh₂ hh

/-- **Magnetization β-monotonicity**: for `J, h ≥ 0`, the magnetization
`Mᵢ = ⟨σᵢ⟩` is monotone increasing in `β` on `(0, ∞)`.
Direct specialization of `correlation_monotone_beta` at `A = {i}`. -/
theorem magnetization_monotone_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ι) :
    MonotoneOn (fun β : ℝ => magnetization G ⟨J, h, β⟩ i) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  unfold magnetization
  exact correlation_monotone_beta G J hJ h hh {i} hβ₁ hβ₂ hβ

/-- **Magnetization β → ∞ convergence**: for `J, h ≥ 0`, the sequence
`n ↦ Mᵢ(J, h, n+1)` converges as `n → ∞`.
Direct specialization of `correlation_convergent_beta` at `A = {i}`. -/
theorem magnetization_convergent_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetization G ⟨J, h, (n + 1 : ℝ)⟩ i)
      Filter.atTop (nhds L) :=
  correlation_convergent_beta G J hJ h hh {i}

/-- **Magnetization h → ∞ convergence**: for `J ≥ 0`, `β > 0`, the sequence
`n ↦ Mᵢ(J, n, β)` converges as `n → ∞`.
Direct specialization of `correlation_convergent_h` at `A = {i}`. -/
theorem magnetization_convergent_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetization G ⟨J, (n : ℝ), β⟩ i)
      Filter.atTop (nhds L) :=
  correlation_convergent_h G J hJ β hβ {i}

/-! ## Critical exponents (§17.7)

Glimm–Jaffe §17.7 (pp. 314–316) derives bounds on critical exponents
from correlation inequalities. For single-component φ⁴/Ising models:

- `η ≥ 0`: from `⟨σ_iσ_j⟩_T ≥ 0` (GKS-II, already `truncated2_nonneg`)
- `ζ ≥ 0`: from `U₄ ≤ 0` (Cor 4.3.3, already `cor_4_3_3` for h = 0)
- `γ ≥ 1`: from susceptibility bounds (χ monotone, requires more)
- `ν ≥ ½`: from correlation length bounds (requires spectral theory)

The Gaussian (mean field) values are: ν_cl = ½, γ_cl = 1, η_cl = 0, ζ_cl = 0.
Theorem 17.7.1 states each exponent ≥ its classical value. -/

/-- **η ≥ 0** (Glimm–Jaffe, Thm 17.7.1, lattice version).
The critical exponent `η` measures the anomalous dimension:
`⟨σ(0)σ(x)⟩ ~ |x|^{-(d-2+η)}` at the critical point.
The bound `η ≥ 0` follows from `⟨σ_iσ_j⟩_T ≥ 0` (GKS-II).

In finite volume, this is simply `truncated2_nonneg`. -/
theorem eta_nonneg_finite_vol (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    0 ≤ truncated2 G p i j :=
  truncated2_nonneg G p hf i j

/-- **ζ ≥ 0** (Glimm–Jaffe, Thm 17.7.1, finite-volume lattice version,
at `h = 0`). The critical exponent `ζ` measures the anomalous dimension
of the four-point truncated correlator; `ζ ≥ 0` follows from
`U₄(i, j, k, l) ≤ 0` (Cor 4.3.3) for pairwise-distinct sites at `h = 0`.

Explicit named alias of `cor_4_3_3` matching the `eta_nonneg_finite_vol`
pattern. -/
theorem zeta_nonneg_finite_vol (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4 G ⟨J, 0, β⟩ i j k l ≤ 0 :=
  cor_4_3_3 G J β hf i j k l hij hik hil hjk hjl hkl

/-- **Absence of even bound states — finite-volume lattice** (Glimm–Jaffe
§17.2, pp. 311–313). For a ferromagnetic Ising model at zero external
field, the truncated four-point correlator `U₄(i,j,k,l) ≤ 0` is
negative semidefinite. Physically this means there are no even-sector
bound states in the two-body spectrum beyond those already captured by
disconnected one-body contributions.

This is an explicit named alias of `cor_4_3_3` (= Lebowitz inequality at
`h = 0`), matching the `eta_nonneg_finite_vol` / `zeta_nonneg_finite_vol`
convention. It is *not* the spectral Corollary 17.2.2 (absence of even
bound states in the energy interval `(0, 2m)` of the actual Hamiltonian
via reflection positivity + Osterwalder–Schrader reconstruction), which
is permanently out of scope for this classical lattice Gibbs-measure
project. The general correlation-inequality content of §17.2, **GJ
Theorem 17.2.1** (the ordered odd-subset upper bound for arbitrary even
`A`, `B`), *is* now formalised in-scope as
`IsingModel.Lebowitz.thm_17_2_1`
(`Inequalities/Lebowitz/Thm1721.lean`); this four-point statement is the
special case `A = {i,j}`, `B = {k,l}`. -/
theorem absence_of_even_bound_states_finite_vol
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4 G ⟨J, 0, β⟩ i j k l ≤ 0 :=
  cor_4_3_3 G J β hf i j k l hij hik hil hjk hjl hkl

/-! ## Lattice-growth convergence of §5 quantities

Named corollaries of `correlation_convergent_subgraph` (PR #64) for the
derived quantities of §5: truncated 2-point function, susceptibility,
and total magnetization.  These are all immediate consequences of the
correlation convergence combined with standard mathlib limit operations
(`Tendsto.sub`, `Tendsto.mul`, `tendsto_finset_sum`).

These results are the *existence* of the infinite-volume limits (in our
discretized fixed-finite-ambient subgraph setting); Glimm–Jaffe does not
name these particular convergence results as standalone theorems, though
the infinite-volume limits of the truncated function and susceptibility
are standard objects in §5.1 (p. 73), §5.3 (pp. 77–80).

Note on `magnetization_total_convergent_subgraph`: `Σᵢ⟨σᵢ⟩` is the
*extensive* total, not the per-site density. In the true thermodynamic
limit (infinite ambient lattice) the physically meaningful quantity is
`|Λ|⁻¹ Σᵢ⟨σᵢ⟩`. Since our ambient `|ι|` is fixed and finite, the two
differ only by a fixed multiplicative constant and convergence transfers
trivially between them. -/

-- Note: `magnetization_convergent_subgraph` already exists in
-- `InfiniteVolume.lean` (PR #64), stated on `correlation G p {i}`.
-- Since `magnetization G p i` is definitionally `correlation G p {i}`,
-- that theorem applies directly to the magnetization.

/-- The truncated 2-point function `⟨σᵢ;σⱼ⟩_{Gₙ}` converges along any
increasing subgraph sequence.

Proof: Each of `⟨σᵢσⱼ⟩_{Gₙ}`, `⟨σᵢ⟩_{Gₙ}`, `⟨σⱼ⟩_{Gₙ}` converges by
`correlation_convergent_subgraph`; apply `Tendsto.sub` and `Tendsto.mul`. -/
theorem truncated2_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => truncated2 (Gn n) p i j)
      Filter.atTop (nhds L) := by
  obtain ⟨Lij, hij⟩ := correlation_convergent_subgraph Gn hmono p hf {i, j}
  obtain ⟨Li, hi⟩ := correlation_convergent_subgraph Gn hmono p hf {i}
  obtain ⟨Lj, hj⟩ := correlation_convergent_subgraph Gn hmono p hf {j}
  refine ⟨Lij - Li * Lj, ?_⟩
  exact hij.sub (hi.mul hj)

/-- The susceptibility `χᵢ(Gₙ) = Σⱼ ⟨σᵢ;σⱼ⟩_{Gₙ}` converges along any
increasing subgraph sequence.

Proof: Finite sum of convergent sequences, via `tendsto_finset_sum`. -/
theorem susceptibility_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibility (Gn n) p i)
      Filter.atTop (nhds L) := by
  choose Lj hLj using fun j =>
    truncated2_convergent_subgraph Gn hmono p hf i j
  refine ⟨∑ j : ι, Lj j, ?_⟩
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => hLj j)

/-- The total magnetization `M_tot(Gₙ) = Σᵢ ⟨σᵢ⟩_{Gₙ}` converges along any
increasing subgraph sequence.

Proof: Finite sum of convergent sequences, via `tendsto_finset_sum`. -/
theorem magnetization_total_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ i : ι, magnetization (Gn n) p i)
      Filter.atTop (nhds L) := by
  choose Li hLi using fun i =>
    correlation_convergent_subgraph Gn hmono p hf {i}
  refine ⟨∑ i : ι, Li i, ?_⟩
  simp only [magnetization]
  exact tendsto_finset_sum _ (fun i _ => hLi i)

end IsingModel
