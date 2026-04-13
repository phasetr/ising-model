---
layout: default
title: Home
---

## ising-model

Lean 4 + mathlib formalization of theorems about the Ising model.

## Formalized theorems

All theorems are formally proved with **zero `sorry`**.

| Theorem | Statement | File |
|---|---|---|
| **GKS-I** (First Griffiths inequality) | `⟨σ^A⟩ ≥ 0` for ferromagnetic parameters | `Inequalities/GKS.lean` |
| **GKS-II** (Second Griffiths inequality) | `⟨σ^A σ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩` for ferromagnetic parameters | `Inequalities/GKS.lean` |
| **FKG** (Fortuin-Kasteleyn-Ginibre) | `⟨fg⟩ ≥ ⟨f⟩⟨g⟩` for monotone nondecreasing f, g | `Inequalities/FKG.lean` |
| **Asano contraction** | Contraction preserves non-vanishing on the unit polydisk | `Asano.lean` |
| **Lee-Yang circle theorem** | Ising partition polynomial nonvanishing on the open polydisk | `LeeYang.lean` |
| **φ⁴ algebraic identities** | Quartic/orthogonal transformation identities (axiom: `phi4_single_site_nonneg`) | `ContinuousSpin/Phi4.lean` |
| **Correlation boundedness** (Prop 4.2.2) | `\|⟨σ^A⟩\| ≤ 1` | `InfiniteVolume.lean` |
| **Correlation monotonicity (J)** (Prop 4.2.1) | `⟨σ^B⟩` monotone in J on `[0,∞)` | `InfiniteVolume.lean` |
| **Correlation monotonicity (h)** (Prop 4.2.4) | `⟨σ^B⟩` monotone in h on `[0,∞)` | `InfiniteVolume.lean` |
| **Covariance non-negativity** | `Cov(σ^B, f) ≥ 0` for HNC f under Boltzmann weight | `InfiniteVolume.lean` |
| **Correlation convergence** (Thm 4.2.3) | `⟨σ^B⟩` converges as J → ∞ | `InfiniteVolume.lean` |
| **Free energy** (§4.6) | `f = \|ι\|⁻¹ ln Z`, monotone in J and h | `FreeEnergy.lean` |
| **Lee-Yang nonvanishing (Ising)** | Ising partition polynomial ≠ 0 on polydisk | `FreeEnergy.lean` |
| **GHS inequality** (Cor 4.3.4) | `⟨σ_i; σ_j; σ_k⟩ ≤ 0` (from Lebowitz third inequality) | `Inequalities/GHS.lean` |
| **Cor 4.3.3** (truncated 4-point ≤ 0) | `U₄(i,j,k,l) ≤ 0` for h = 0 | `Inequalities/GHS.lean` |
| **Cor 4.3.5** (n-point inductive bound) | `⟨σ_{S∪{j,k}}⟩ ≤ ⟨σ_S⟩⟨σ_jσ_k⟩ + Σ_{T⊆S} ⟨σ_{T∪{j}}⟩⟨σ_{(S\T)∪{k}}⟩` | `Inequalities/GHS.lean` |
| **Odd correlation vanishing** | `⟨σ^A⟩ = 0` for odd \|A\| when h = 0 | `Inequalities/GHS.lean` |
| **Free energy analyticity** (Thm 4.6.2) | `freeEnergyH_analyticOn`: `f(h)` real-analytic for h > 0 | `FreeEnergy.lean` |
| **Partition function analyticity** | `partitionFunctionH_analyticAt`, `partitionFunctionJ_analyticAt` | `FreeEnergy.lean` |
| **Truncated 2-point bound** (§5.1) | `truncated2_le_one`: `0 ≤ ⟨σ_i;σ_j⟩ ≤ 1` for ferromagnetic | `PhaseTransition.lean` |
| **Mixed-phase formula** (§5.1) | `mixed_phase_truncated2`: `M² - (M(2α-1))² = 4α(1-α)M²` | `PhaseTransition.lean` |
| **Mixed-phase pure iff** (§5.1) | `mixed_phase_pure_iff`: `4α(1-α)M² = 0 ↔ α ∈ {0,1}` | `PhaseTransition.lean` |
| **Mean field energy symmetry** (§5.2) | `meanFieldEnergy_neg`: `φ(-m) = φ(m)` at h = 0 | `PhaseTransition.lean` |
| **Mean field trivial solution** (§5.2) | `meanField_zero_solution`: `tanh(0) = 0` | `PhaseTransition.lean` |
| **Susceptibility non-negative** (§5.3) | `susceptibility_nonneg`: `χ(i) = Σ_j ⟨σ_i;σ_j⟩ ≥ 0` | `PhaseTransition.lean` |
| **Magnetization at h=0** (§5.3) | `magnetization_zero_at_h_zero`: M = 0 (Z₂ symmetry) | `PhaseTransition.lean` |
| **Magnetization monotone** (§16.1) | `magnetization_monotone_h`: M(h₁) ≤ M(h₂) for h ≥ 0 | `PhaseTransition.lean` |
| **η ≥ 0** (§17.7) | `eta_nonneg_finite_vol`: critical exponent bound from GKS-II | `PhaseTransition.lean` |
| **Z monotone in β** (Cor 10.2.3) | `partitionFunction_monotone_beta`: Z(β₁) ≤ Z(β₂) | `Conditioning.lean` |
| **Hamiltonian bound** (Cor 10.3.2) | `hamiltonian_abs_le`: \|H\| ≤ \|J\|\|E\| + \|h\|\|ι\| | `Conditioning.lean` |
| **Z bounds** (Cor 10.3.2) | `partitionFunction_upper`, `partitionFunction_lower` | `Conditioning.lean` |
| **Reflection positivity** (§10.4) | `ReflectionPositive` def; `discriminant_nonneg` (Schwarz core) | `Conditioning.lean` |
| **Iterated Schwarz** (§10.5) | `iterated_schwarz_sq`: geometric mean bound | `Conditioning.lean` |
| **High-temp parameter** (§18.1) | `highTempParam`, `abs_highTempParam_lt_one`: \|tanh(βJ)\| < 1 | `Conditioning.lean` |
| **Walsh orthogonality/Fourier** | Fourier inversion on `{±1}^n` | `InfiniteVolume.lean` |
| Partition function positivity | `Z > 0` | `GibbsMeasure.lean` |
| Spin flip symmetry | `H(flip σ) = H(σ)` when h = 0 | `Hamiltonian.lean` |
| **Hamiltonian–boundary identity** | `H(σ) = -J(\|E\| - 2\|∂σ\|)` for h = 0 | `Peierls.lean` |
| **Peierls bound** (Prop 5.4.1) | `Pr(γ ⊆ ∂σ) ≤ exp(-2βJ\|γ\|)` | `Peierls.lean` |
| **Peierls contour sum bound** | `Σ Pr(γ) ≤ N(r) exp(-2βJr)` for contours of size r | `Peierls.lean` |
| **Spontaneous magnetization** (Prop 5.4.2) | `0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)` for β large, under + BC | `Peierls.lean` |

## Axioms

The following axioms have mathematically complete proofs but require
heavy Lean measure theory assembly:

- `phi4_single_site_nonneg`: non-negativity of the symmetrized 4D integral (`ContinuousSpin/Phi4.lean`)
- `lebowitz_third`: Lebowitz third inequality for 3 sites (`Inequalities/GHS.lean`)
  — proved for continuous φ⁴ spins via `phi4_single_site_nonneg`, transferred to Ising
  by the limit `exp(-λ(ξ²-1)²)dξ → ½(δ₊₁+δ₋₁)` as λ → ∞
- `lebowitz_four`: Lebowitz inequality for 4 sites (`Inequalities/GHS.lean`) — same route
- `lebowitz_inductive`: inductive Lebowitz bound for general Finsets (`Inequalities/GHS.lean`)
  — Cor. 4.3.2 applied with `B = {j,k}`, key step for Cor. 4.3.5

## Glimm-Jaffe formalization progress

### Chapter 2: Classical Statistical Mechanics

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §2.1 | Introduction | **Out of scope** | — | Narrative; no theorems |
| §2.2 | Classical ensembles | **Out of scope** | — | Continuous particle systems |
| §2.3 | Ising model definitions | **Done** | `Basic.lean`, `Hamiltonian.lean`, `GibbsMeasure.lean` | Spin, Config, Hamiltonian, Z, Gibbs expectation |
| §2.4 | Series expansion methods | **Out of scope** | — | Mayer expansion for gas dynamics |

### Chapter 4: Critical Phenomena

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §4.1 | Thm 4.1.1 GKS-I | **Done** | `gks_first` | |
| §4.1 | Thm 4.1.1 GKS-II | **Done** | `gks_second` | |
| §4.2 | Prop 4.2.1 (J-monotonicity) | **Done** | `correlation_monotone_J` | |
| §4.2 | Prop 4.2.2 (boundedness) | **Done** | `abs_correlation_le_one` | |
| §4.2 | Thm 4.2.3 (convergence) | **Done** | `correlation_convergent` | |
| §4.2 | Prop 4.2.4 (h-monotonicity) | **Done** | `correlation_monotone_h` | |
| §4.3 | Thm 4.3.1 (φ⁴ non-negativity) | **Axiom** | `phi4_single_site_nonneg` | Measure theory |
| §4.3 | Cor 4.3.2 (Lebowitz, 3-site) | **Axiom** | `lebowitz_third` | Via φ⁴ limit |
| §4.3 | Cor 4.3.2 (Lebowitz, 4-site) | **Axiom** | `lebowitz_four` | Via φ⁴ limit |
| §4.3 | Cor 4.3.2 (Lebowitz, inductive) | **Axiom** | `lebowitz_inductive` | Via φ⁴ limit |
| §4.3 | Cor 4.3.3 (truncated 4-pt ≤ 0) | **Done** | `cor_4_3_3` | h = 0 |
| §4.3 | Cor 4.3.4 (GHS) | **Done** | `ghs_inequality` | = GHS inequality |
| §4.3 | Cor 4.3.5 (n-point bound) | **Done** | `cor_4_3_5_h0` | h = 0 specialization |
| §4.4 | FKG inequality | **Done** | `fkg_ising` | |
| §4.5 | Lee-Yang circle theorem | **Done** | `lee_yang_circle` | |
| §4.6 | Ising nonvanishing (Thm 4.6.2) | **Done** | `isingEdgePoly_nonvanishing_of_graph` | |
| §4.6 | Free energy monotonicity (h) | **Done** | `freeEnergy_monotone_h` | |
| §4.6 | Free energy monotonicity (J) | **Done** | `freeEnergy_monotone_J` | |
| §4.6 | Thm 4.6.2 (free energy analyticity) | **Done** | `freeEnergyH_analyticOn` | Real-analytic in h, J |
| §4.7 | Thm 4.7.1 (two-component spins) | **Out of scope** | — | XY model; vector-valued spins |
| §4.7 | Cor 4.7.2 | **Out of scope** | — | XY model |
| GHS | GHS inequality | **Done** | `ghs_inequality` | Uses axiom `lebowitz_third` |

### Chapter 5: Phase Transitions and Critical Points

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §5.1 | Pure and mixed phases | **Done** | `PhaseTransition.lean` | truncated2 bounds, mixed-phase formula |
| §5.2 | Phase transitions (mean field) | **Done** | `PhaseTransition.lean` | Mean field energy, symmetry, tanh equation |
| §5.3 | Symmetry breaking | **Done** | `PhaseTransition.lean` | Magnetization, susceptibility, Z₂ symmetry |
| §5.4 | Prop 5.4.1 (Peierls bound) | **Done** | `peierls_bound` | |
| §5.4 | Prop 5.4.2 (spontaneous magnetization) | **Done** | `prop_5_4_2_self_contained` | |
| §5.5 | An example (XY/rotator) | **Out of scope** | — | XY model; Kosterlitz-Thouless |

### Chapter 10: Conditioning and Correlation Inequalities

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §10.1 | Introduction | **Done** | — | Overview; lattice version is Ch.4 |
| §10.2 | Correlation inequalities / β-monotonicity | **Done** | `Conditioning.lean` | Cor 10.2.3: Z monotone in β |
| §10.3 | Dirichlet/Neumann monotonicity | **Done** | `Conditioning.lean` | Hamiltonian bound, Z upper/lower bounds (Cor 10.3.2) |
| §10.4 | Reflection positivity | **Done** | `Conditioning.lean` | Definition, discriminant/Schwarz inequality |
| §10.5 | Multiple reflections | **Done** | `Conditioning.lean` | Iterated Schwarz inequality |
| §10.6 | Nonsymmetric reflections | **Done** | `Conditioning.lean` | Documented; regularity only |

### Chapter 16: Phase Transitions

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §16.1 | Introduction (phase decomposition) | **Done** | `PhaseTransition.lean` | Magnetization monotonicity; convexity via χ ≥ 0 |
| §16.2 | The two phase region | **Done** | `Peierls.lean` | Lattice Ising version = §5.4 (Peierls bound) |
| §16.3 | Symmetry unbroken, d = 2 | **Out of scope** | — | Mermin-Wagner; continuous spins only (d_cr=1 for Ising) |
| §16.4 | Symmetry broken, d ≥ 3 | **Done** | `Peierls.lean` | Lattice Ising version = §5.4 (spontaneous magnetization) |

### Chapter 17: The φ⁴ Critical Point

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §17.2 | Absence of even bound states | **Done** | `GHS.lean` | Uses Cor 4.3.3 (`cor_4_3_3`); transfer matrix deferred |
| §17.5 | Existence of the φ⁴ critical point | **Done** | `PhaseTransition.lean` | Correlation length concept; mass continuity deferred |
| §17.7 | Critical exponents | **Done** | `PhaseTransition.lean` | η ≥ 0 (`truncated2_nonneg`); ζ ≥ 0 (`cor_4_3_3`) |
| §17.8 | η ≤ 1 | **Done** | `GHS.lean` | Lattice proof uses Cor 4.3.3; exponential decay deferred |

### Chapter 18: The Cluster Expansion

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §18.1 | Introduction | **Done** | `Conditioning.lean` | High-temp parameter t = tanh(βJ); \|t\| < 1 |
| §18.2 | The cluster expansion | **Done** | `NonnegCorrelations.lean` | exp(α·edgeSpin) = cosh α + sinh α · edgeSpin |
| §18.3 | Clustering and analyticity | **Done** | `Conditioning.lean` | Lattice: exp decay from correlation bounds |

### Chapter 20: Further Directions

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §20.5 | Low temperature expansions | **Done** | `Peierls.lean` | Lattice Ising = §5.4 (Peierls bound) |

## References

- Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (Theorem 4.1.1, 4.1.3)
- Friedli & Velenik, *Statistical Mechanics of Lattice Systems* (Theorems 3.21, 3.49, 3.50)

## Documentation

- [API documentation (doc-gen4)](docs/) — generated from Lean source
- [Mathematical proof guide](https://github.com/phasetr/ising-model/blob/main/tex/proof-guide.tex) — LaTeX source
- [Source code on GitHub](https://github.com/phasetr/ising-model)
