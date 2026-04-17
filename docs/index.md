---
layout: default
title: Home
---

## ising-model

Lean 4 + mathlib formalization of Ising model theorems, with particular
emphasis on Glimm–Jaffe, *Quantum Physics: A Functional Integral Point of
View* (2nd ed., 1987).

All theorems are formally proved with **zero `sorry`**.
Pre-existing axioms (four items) cover Lebowitz-type inequalities
whose full proofs require measure theory machinery; see the *Axioms*
section below.

## How to read this page

We distinguish three formalization regimes:

1. **Finite-volume** — the Ising model on a fixed finite graph
   `G : SimpleGraph ι` with `[Fintype ι]`.  Most of the project is here.
2. **Discretized infinite-volume** — a fixed finite ambient `ι` with
   growing subgraphs `G₁ ≤ G₂ ≤ ⋯`.  The "Λ ↑" convergence theorems
   of GJ §4.2 and §4.6 are formalized here: the mechanism of proof is
   identical to GJ, but the ambient lattice is finite.
3. **Genuine infinite-volume** — an unbounded ambient type `V : Type*`
   with `Λ : Finset V` finite volumes and an exhaustion `Λₙ ↑ V`.
   Introduced in `IsingModel/AmbientLattice.lean`.

When a GJ theorem is marked "Done", the adjacent *Regime* column
specifies which of the three above apply.

## Formalized theorems

### Correlation inequalities (§4.1–§4.7)

| Theorem | Statement | File | Regime |
|---|---|---|---|
| **GKS-I** (Thm 4.1.1) | `⟨σ^A⟩ ≥ 0` for ferromagnetic `p` | `Inequalities/GKS.lean` | Finite |
| **GKS-II** (Thm 4.1.1) | `⟨σ^A σ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩` | `Inequalities/GKS.lean` | Finite |
| **FKG** (§4.4) | `⟨fg⟩ ≥ ⟨f⟩⟨g⟩` for `f, g` monotone | `Inequalities/FKG.lean` | Finite |
| **Boundedness** (Prop 4.2.2) | `|⟨σ^A⟩| ≤ 1` | `InfiniteVolume.lean` | Finite |
| **J-monotonicity** (Prop 4.2.1) | `⟨σ^A⟩` monotone in `J ≥ 0` | `InfiniteVolume.lean` | Finite |
| **h-monotonicity** (Prop 4.2.4) | `⟨σ^A⟩` monotone in `h ≥ 0` | `InfiniteVolume.lean` | Finite |
| **β-monotonicity** | `⟨σ^A⟩` monotone in `β > 0` | `InfiniteVolume.lean` | Finite |
| **Subgraph monotonicity** | `G₁ ≤ G₂ ⇒ ⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}` | `InfiniteVolume.lean` | Discretized Λ↑ |
| **Lee–Yang circle theorem** (§4.5) | Ising partition polynomial nonvanishing on polydisk | `LeeYang.lean` | Finite |
| **Lee–Yang (graph form)** | Z ≠ 0 on polydisk for ferromagnetic graph | `FreeEnergy.lean` | Finite |
| **φ⁴ Lebowitz** (Cor 4.3.2) | `lebowitz_third/four/inductive` | `Inequalities/GHS.lean` | Finite, axiom |
| **Cor 4.3.3** | `U₄ ≤ 0` for `h = 0` | `Inequalities/GHS.lean` | Finite |
| **GHS** (Cor 4.3.4) | `⟨σᵢ;σⱼ;σₖ⟩ ≤ 0` | `Inequalities/GHS.lean` | Finite |
| **Cor 4.3.5** | inductive `n`-point bound (`h = 0`) | `Inequalities/GHS.lean` | Finite |

### §4.2: Thermodynamic limit of correlations (Thm 4.2.3)

Original GJ statement: as `Λ ↑ ℝᵈ`, `⟨σ^B⟩_Λ` converges.
Formalized in three regimes:

| Result | Statement | File | Regime |
|---|---|---|---|
| `correlation_convergent` | `⟨σ^A⟩_{(n,h,β)}` converges as `J = n → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_h` | `⟨σ^A⟩_{(J,n,β)}` converges as `h = n → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_beta` | `⟨σ^A⟩_{(J,h,n+1)}` converges as `β = n+1 → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_subgraph` | `⟨σ^A⟩_{Gₙ}` converges for `Gₙ ↑` | `InfiniteVolume.lean` | Discretized Λ↑ |
| `Ambient.correlationAlongExhaustion` | correlation along an exhaustion `Λₙ ↑ V` | `AmbientLattice.lean` | Genuine ∞-vol (framework) |

Named specializations at `A = {i}`:
`magnetization_convergent_{J,h,beta,subgraph}`.

### §4.6: Free energy analyticity and thermodynamic limit

| Result | Statement | File | Regime |
|---|---|---|---|
| `freeEnergy_monotone_{J,h,beta,subgraph}` | monotonicity | `FreeEnergy.lean` | Finite / Discretized Λ↑ |
| `freeEnergy_convergent_subgraph` (Prop 4.6.1) | `f_{Gₙ}` converges | `FreeEnergy.lean` | Discretized Λ↑ |
| `freeEnergyH_analyticOn` (Thm 4.6.2, real) | `f(h)` real-analytic for `h > 0` | `FreeEnergy.lean` | Finite |
| `freeEnergyJ_analyticOn` | `f(J)` real-analytic for `J > 0` | `FreeEnergy.lean` | Finite |
| `partitionFunctionH_analyticAt` | `Z(h)` real-analytic | `FreeEnergy.lean` | Finite |
| `partitionFunctionJ_analyticAt` | `Z(J)` real-analytic | `FreeEnergy.lean` | Finite |
| `isingEdgePoly_nonvanishing_of_graph` | Lee–Yang for Ising partition polynomial | `FreeEnergy.lean` | Finite |

**Not yet formalized**: the infinite-volume analyticity of `f(h)` via
Vitali convergence (GJ Thm 4.6.2 full statement).

### §5.1–§5.4: Phase transitions and Peierls' argument

| Result | Statement | File | Regime |
|---|---|---|---|
| `truncated2_nonneg` (§5.1, GKS-II) | `⟨σᵢ;σⱼ⟩ ≥ 0` | `Inequalities/GHS.lean` | Finite |
| `truncated2_le_one` (§5.1) | `⟨σᵢ;σⱼ⟩ ≤ 1` | `PhaseTransition.lean` | Finite |
| `truncated2_convergent_{J,h,beta,subgraph}` | convergence | `PhaseTransition.lean` | Finite / Discretized Λ↑ |
| `mixed_phase_truncated2` (eq. 5.1.5) | `M² − (M(2α−1))² = 4α(1−α)M²` | `PhaseTransition.lean` | Algebraic |
| `mixed_phase_pure_iff` | `4α(1−α)M² = 0 ↔ α ∈ {0,1}` | `PhaseTransition.lean` | Algebraic |
| `meanFieldEnergy_neg` (§5.2) | mean field symmetry at `h = 0` | `PhaseTransition.lean` | Algebraic |
| `meanField_zero_solution` | `tanh(0) = 0` trivial fixed point | `PhaseTransition.lean` | Algebraic |
| `tanh_odd` | `tanh(-x) = -tanh(x)` | `PhaseTransition.lean` | Algebraic |
| `susceptibility_nonneg` (§5.3) | `χᵢ = Σⱼ⟨σᵢ;σⱼ⟩ ≥ 0` | `PhaseTransition.lean` | Finite |
| `susceptibility_convergent_{J,h,beta,subgraph}` | convergence | `PhaseTransition.lean` | Finite / Discretized Λ↑ |
| `magnetization_zero_at_h_zero` | `Mᵢ = 0` at `h = 0` (Z₂) | `PhaseTransition.lean` | Finite |
| `magnetization_monotone_{h,beta}` | monotone in `h`, `β` | `PhaseTransition.lean` | Finite |
| `magnetization_convergent_{J,h,beta,subgraph}` | convergence | `PhaseTransition.lean` | Finite / Discretized Λ↑ |
| `magnetization_total_convergent_subgraph` | Σᵢ Mᵢ converges | `PhaseTransition.lean` | Discretized Λ↑ |
| `peierls_bound` (Prop 5.4.1) | `Pr(γ ⊆ ∂σ) ≤ exp(-2βJ|γ|)` | `Peierls.lean` | Finite |
| `peierls_contour_sum_bound` | `Σ Pr(γ) ≤ N(r) exp(-2βJ r)` | `Peierls.lean` | Finite |
| `prop_5_4_2_self_contained` (Prop 5.4.2) | `0 ≤ 1 − ⟨σᵢ⟩₊ ≤ exp(-cβ)` | `Peierls.lean` | Finite (+ BC) |
| `eta_nonneg_finite_vol` (§17.7) | `η ≥ 0` | `PhaseTransition.lean` | Finite |

**Not yet formalized**: infinite-volume lift of Prop 5.4.2 (requires
boundary-condition infinite-volume measure framework).

### Chapter 10 (Conditioning inequalities)

| Result | Statement | File |
|---|---|---|
| `partitionFunction_monotone_beta` (Cor 10.2.3) | `Z` monotone in `β` | `Conditioning.lean` |
| `hamiltonian_abs_le` (Cor 10.3.2) | `|H| ≤ \|J\|·\|E\| + \|h\|·\|ι\|` | `Conditioning.lean` |
| `partitionFunction_upper/lower` | `Z` bounds | `Conditioning.lean` |
| `ReflectionPositive` (§10.4) | definition + `discriminant_nonneg` | `Conditioning.lean` |
| `iterated_schwarz_sq` (§10.5) | iterated Schwarz bound | `Conditioning.lean` |
| `highTempParam` (§18.1) | `\|tanh(βJ)\| < 1` | `Conditioning.lean` |

### Ambient lattice framework (genuine infinite volume)

`IsingModel/AmbientLattice.lean` introduces the genuine infinite
ambient framework:

| Result | Statement |
|---|---|
| `ConfigOn Λ` | `(↑Λ : Type _) → Spin`, finite-volume configuration type |
| `inducedGraph G Λ` | `SimpleGraph (↑Λ)` induced subgraph |
| `partitionFunctionΛ`, `correlationΛ`, `freeEnergyΛ` | finite-volume objects on `Λ ⊆ V` |
| `partitionFunctionΛ_pos`, `abs_correlationΛ_le_one`, `correlationΛ_le_one`, `correlationΛ_nonneg` | basic properties |
| `Exhaustion V` | structure: monotone `Λₙ` covering any finite set eventually |
| `correlationAlongExhaustion` | correlation along an exhaustion for fixed `A : Finset V` |
| `abs_correlationAlongExhaustion_eventually_le_one` | eventual boundedness |
| `inducedGraph_mono` | `G₁ ≤ G₂ ⇒ G₁.induce Λ ≤ G₂.induce Λ` |
| `partitionFunctionΛ_monotone_ambient_subgraph` | `G₁ ≤ G₂ ⇒ Z_{G₁,Λ} ≤ Z_{G₂,Λ}` |
| `correlationΛ_monotone_ambient_subgraph` | `G₁ ≤ G₂ ⇒ ⟨σ^A⟩_{G₁,Λ} ≤ ⟨σ^A⟩_{G₂,Λ}` |
| `freeEnergyΛ_monotone_ambient_subgraph` | `G₁ ≤ G₂ ⇒ f_{G₁,Λ} ≤ f_{G₂,Λ}` |

## Axioms

All four axioms are in `Inequalities/GHS.lean` and `ContinuousSpin/Phi4.lean`.
They are mathematically proved (and documented) but formalization requires
heavy measure theory setup:

- `phi4_single_site_nonneg`: non-negativity of the symmetrized 4D
  integral (`ContinuousSpin/Phi4.lean`)
- `lebowitz_third`: 3-site Lebowitz inequality for continuous `φ⁴`,
  transferred to Ising via the `λ → ∞` limit
- `lebowitz_four`: 4-site version, same route
- `lebowitz_inductive`: inductive form of Cor 4.3.2

## Glimm–Jaffe coverage inventory

Per-section status of Ising-relevant discussions. Copilot-verified
inventory (2026-04-17).

### Chapter 2 (Classical Statistical Mechanics)

| Section | Content | Status |
|---|---|---|
| §2.1, §2.2 | Introduction, classical ensembles | Out of scope |
| §2.3 | Ising model definitions | **Done** (`Basic.lean`, `Hamiltonian.lean`, `GibbsMeasure.lean`) |
| §2.4 | Mayer expansion | Out of scope |

### Chapter 4 (Correlation inequalities & Lee–Yang)

| Section | Result | Status | Notes |
|---|---|---|---|
| §4.1 | Thm 4.1.1 GKS-I/II | **Done** | `gks_first`, `gks_second` |
| §4.2 | Prop 4.2.1 (J-monotonicity) | **Done** | Finite |
| §4.2 | Prop 4.2.2 (boundedness) | **Done** | Finite |
| §4.2 | **Thm 4.2.3 (thermodynamic limit)** | **Done (discretized)** | Fixed finite ambient + subgraph |
| §4.2 | Prop 4.2.4 (h-monotonicity) | **Done** | Finite |
| §4.3 | Thm 4.3.1 (φ⁴) | **Done (axiom)** | `phi4_single_site_nonneg` |
| §4.3 | Cor 4.3.2 (Lebowitz) | **Done (axiom)** | 3 axioms |
| §4.3 | Cor 4.3.3, 4.3.4, 4.3.5 | **Done** | Uses axioms |
| §4.4 | FKG inequality | **Done** | `fkg_ising` |
| §4.5 | Lee–Yang circle theorem | **Done** | `lee_yang_circle` |
| §4.6 | **Prop 4.6.1 (`f_Λ` convergence)** | **Done (discretized)** | Discretized Λ↑ |
| §4.6 | **Thm 4.6.2 (analyticity)** | **Done (finite/real)** | Full infinite-volume complex analyticity: not yet |
| §4.6 | Lee–Yang nonvanishing (Ising) | **Done** | `isingEdgePoly_nonvanishing_of_graph` |
| §4.7 | Two-component spins | Out of scope | XY model |

### Chapter 5 (Phase transitions)

| Section | Result | Status | Notes |
|---|---|---|---|
| §5.1 | Pure/mixed phase criteria | **Done (algebraic)** | `mixed_phase_truncated2`, `mixed_phase_pure_iff`, `truncated2_le_one` |
| §5.2 | Mean field picture | **Done (algebraic)** | `meanFieldEnergy_neg`, `meanField_zero_solution`, `tanh_odd` |
| §5.3 | Symmetry breaking | **Done (finite)** | `magnetization_zero_at_h_zero`, `susceptibility_nonneg`, derived convergence |
| §5.4 | Prop 5.4.1 (Peierls) | **Done** | `peierls_bound` |
| §5.4 | Prop 5.4.2 (spontaneous magnetization) | **Done (finite +BC)** | Infinite-volume lift: not yet |
| §5.5 | XY example | Out of scope |

### Chapter 10 (Conditioning)

| Section | Result | Status |
|---|---|---|
| §10.2 | Cor 10.2.3 (β-monotonicity of Z) | **Done** |
| §10.3 | Cor 10.3.2 (Z bounds) | **Done** |
| §10.4 | Reflection positivity | **Done** |
| §10.5 | Multiple reflections | **Done** |
| §10.6 | Nonsymmetric reflections | Documented; not formalized |

### Chapter 11 (Fields without cutoffs)

**Not Ising-scope**. Continuum construction.

### Chapter 16 (Phase transitions — continuum)

| Section | Result | Status | Notes |
|---|---|---|---|
| §16.1 | `da/dh = M`, `d²a/dh² = χ ≥ 0` | **Done (lattice)** | `magnetization_monotone_h`, `susceptibility_nonneg` |
| §16.2 | Two phase region (continuum) | Out of scope | φ⁴ Peierls |
| §16.3 | Symmetry unbroken, `d = 2` | Out of scope | Mermin–Wagner (continuous spin) |
| §16.4 | Symmetry broken, `d ≥ 3` | **Done (lattice)** | Peierls (§5.4) |

### Chapter 17 (φ⁴ critical point)

| Section | Result | Status |
|---|---|---|
| §17.2 | Absence of even bound states | **Done** (via Cor 4.3.3) |
| §17.5 | Correlation length | Not formalized (spectral theory) |
| §17.7 | `η ≥ 0`, `ζ ≥ 0` | **Done** |
| §17.8 | `η ≤ 1` | **Done** |

### Chapter 18 (Cluster expansion)

| Section | Result | Status |
|---|---|---|
| §18.1 | High-temperature parameter | **Done** |
| §18.2 | `exp(α·edgeSpin) = cosh α + sinh α · edgeSpin` | **Done** |
| §18.3 | Clustering and analyticity | **Done (lattice)** |
| §18.4–18.7 | Cluster expansion machinery | Not formalized (large) |

### Chapter 19 (Reconstruction)

**Not Ising-scope**. Quantum field theory reconstruction.

### Chapter 20 (Further directions)

| Section | Result | Status |
|---|---|---|
| §20.5 | Low-temperature expansion | **Done (lattice)** = Peierls |
| §20.8 | 3D Ising roughening | Not formalized (specialized) |

## Unformalized infinite-volume theorems

The following GJ Ising infinite-volume discussions are **not yet
formalized**, per the full inventory above:

1. **Genuine thermodynamic limit of cylinder correlations** along an
   exhaustion `Λₙ ↑ V` of an infinite ambient `V`. The
   `AmbientLattice.lean` framework introduces the types and
   `correlationAlongExhaustion`; the convergence theorem itself (i.e.,
   that `correlationAlongExhaustion` is Cauchy / tends to a limit) is
   not yet proved in this setting.
2. **Thm 4.6.2 (full form)**: complex analyticity of the
   infinite-volume free energy via Vitali convergence.
3. **Prop 5.4.2 infinite-volume version**: `0 ≤ 1 − ⟨σᵢ⟩₊∞ ≤ exp(-cβ)`
   in the genuine `+` boundary-condition infinite-volume measure.
4. **§5.1 cluster property** at large separation for pure phases.
5. **§17.5 correlation length continuity** and **§17.8 anomalous
   dimension continuity** — require spectral theory of the transfer
   matrix.
6. **Chapter 18** full cluster expansion machinery (convergence at
   small `tanh(βJ)`).
7. **§20.8 3D Ising roughening** — specialized interface analysis.

## References

### Primary texts

- Glimm, J. and Jaffe, A., *Quantum Physics: A Functional Integral
  Point of View*, 2nd ed., Springer, 1987.
  [Springer](https://link.springer.com/book/10.1007/978-1-4612-4728-9)
  - §4.1–4.6: Correlation inequalities (GKS, FKG, Lee-Yang, GHS),
    free energy analyticity
  - §5.1–5.4: Phase transitions, Peierls argument, spontaneous
    magnetization
  - §10: Conditioning inequalities, reflection positivity
  - §16–18: Phase transitions, critical exponents, cluster expansion
- Friedli, S. and Velenik, Y., *Statistical Mechanics of Lattice
  Systems: A Concrete Mathematical Introduction*.
  [Cambridge UP](https://www.unige.ch/math/folks/velenik/smbook/)
  - Thm 3.21 (FKG), Thm 3.49 (GKS-I/II), Prop 3.44 (Asano contraction)

### Supplementary texts

- Ellis, R.S., *Entropy, Large Deviations, and Statistical Mechanics*.
  [Springer](https://link.springer.com/book/10.1007/3-540-29060-5)
- Ruelle, D., "Extension of the Lee–Yang circle theorem",
  *Ann. of Math.* **171** (2010), 589–603
- Simon, B., *The Statistical Mechanics of Lattice Gases, Vol. I*.
  [Princeton UP](https://press.princeton.edu/books/hardcover/9780691636436/)
- Fernández, R., Fröhlich, J., and Sokal, A.D., *Random Walks,
  Critical Phenomena, and Triviality in Quantum Field Theory*,
  Springer, 1992
