---
layout: default
title: Correlation theorems
---
[Theorem catalogue](index.md) · [Documentation home](../index.md) · [Current status](../status.md)

## Correlation inequalities (§4.1–§4.7)

| Theorem | Statement | File | Regime |
|---|---|---|---|
| **GKS-I** (Thm 4.1.1) | `⟨σ^A⟩ ≥ 0` for ferromagnetic `p` | `Inequalities/GKS.lean` | Finite |
| **GKS-II** (Thm 4.1.3, (4.1.11)) | `⟨σ^A σ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩` | `Inequalities/GKS.lean` | Finite |
| **FKG** (§4.4) | `⟨fg⟩ ≥ ⟨f⟩⟨g⟩` for `f, g` monotone | `Inequalities/FKG.lean` | Finite |
| **Boundedness** (Prop 4.2.2) | `|⟨σ^A⟩| ≤ 1` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol |
| **J-monotonicity** (Prop 4.2.1) | `⟨σ^A⟩` monotone in `J ≥ 0` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol |
| **h-monotonicity** (Prop 4.2.1, singleton couplings) | `⟨σ^A⟩` monotone in `h ≥ 0` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol |
| **β-monotonicity** | `⟨σ^A⟩` monotone in `β > 0` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol |
| **Subgraph monotonicity** | `G₁ ≤ G₂ ⇒ ⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + Discretized Λ↑ + genuine ∞-vol |
| **GKS-II at ∞-vol** (Thm 4.1.3, (4.1.11)) | `⟨σ^A⟩ · ⟨σ^B⟩ ≤ ⟨σ^{A∆B}⟩` | `AmbientLattice.lean` | Genuine ∞-vol (ferromagnetic) |
| **Exhaustion-independence** | `correlationInfinite G Λ = correlationInfinite G Λ'` | `AmbientLattice.lean` | Genuine ∞-vol |
| **Lee–Yang circle theorem** (§4.5) | Ising partition polynomial nonvanishing on polydisk | `LeeYang.lean` | Finite |
| **Lee–Yang (graph form)** | Z ≠ 0 on polydisk for ferromagnetic graph | `FreeEnergy.lean` | Finite |
| **Cor 4.3.2 (Lebowitz t/q inequalities, Ising)** | `cor_4_3_2_tt`/`_qq`/`_tq` — proven without axioms | `Inequalities/Lebowitz/Cor432.lean` | Finite (PR #3908) |
| **GHS-corollary Lebowitz inputs** | **All discharged (Issue #3906)**: `lebowitz_four` deleted in PR #3909 and `lebowitz_third` deleted in PR #3910 (both false as stated, replaced by the proven `lebowitz_four_zero_field` / `Lebowitz.cor_4_3_4`); `lebowitz_inductive` (true as stated) replaced by the proven `Lebowitz.lebowitz_inductive_bound` in PR #3911 | `Inequalities/Lebowitz/` | Finite, proven |
| **Cor 4.3.3** | `U₄ ≤ 0` for `h = 0` | `Inequalities/GHS.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol (`truncated4Infinite_nonpos_h_zero`) |
| **GHS** (Cor 4.3.4) | `⟨σᵢ;σⱼ;σₖ⟩ ≤ 0` (axiom-free since PR #3910 via `Lebowitz.cor_4_3_4`) | `Inequalities/GHS.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol (`truncated3Infinite_nonpos`) |
| **Cor 4.3.5** | inductive `n`-point bound (`h = 0`) | `Inequalities/GHS.lean` | Finite |
| **Truncated-3 contraction** (`abs_truncated3_le_weighted`, `abs_truncated3_le`) | Ferromagnetic, `h ≥ 0`: `\|⟨σᵢ;σⱼ;σₖ⟩\| ≤ ⟨σᵢ⟩·⟨σⱼ;σₖ⟩ + ⟨σⱼ⟩·⟨σᵢ;σₖ⟩` (weighted form), hence (`C = 1` corollary) `\|⟨σᵢ;σⱼ;σₖ⟩\| ≤ ⟨σᵢ;σₖ⟩ + ⟨σⱼ;σₖ⟩`, via GHS (Cor 4.3.4, p. 62) + GKS-II (Thm 4.1.3, (4.1.11), p. 57) | `Inequalities/GHS/Truncated3Contraction.lean` | **Implemented (finite-volume correlation inequality; axiom-free).** Brick 1 toward GJ Thm 17.6.1 (p. 313) ∂/∂h (μ-direction) ∞-vol differentiability (Issue #4413); pure finite-volume correlation inequality, **not** an ∞-vol or differentiability result itself |
| **Semi-truncated 2-block susceptibility bounds** (`semiTruncated_pair_nonneg`, `semiTruncated_pair_le`) | Ferromagnetic, `h ≥ 0`, for distinct sites `i, j` with off-diagonal site `l ∉ {i,j}`: (lower) `0 ≤ ⟨σ_iσ_j; σ_l⟩ := ⟨σ_iσ_j σ_l⟩ − ⟨σ_iσ_j⟩⟨σ_l⟩` via GKS-II (pair case, `|B|=2`); (upper) `⟨σ_iσ_j; σ_l⟩ ≤ τ₂(i,l) + τ₂(j,l)` via GHS + GKS-I regrouping. The field derivative of the pair moment is `∂_h⟨σ_iσ_j⟩ = β·∑_{l≠i,j}⟨σ_iσ_j; σ_l⟩`, giving the equi-Lipschitz foundation for the ∂/∂h capstone | `Inequalities/GHS/Truncated3Contraction.lean` | **Implemented (finite-volume; axiom-free).** Corrected brick 1 toward GJ Thm 17.6.1 (p. 313) ∂/∂h route; finite-volume susceptibility bound, independent of `h` and `Λ` (Issue #4413) |
| **Field/volume-uniform majorant for ∂/∂h site-sum** (Ursell terms: `truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg`, `summable_truncated2FiniteVolumeMajorant`, `sum_abs_truncated3_le_finiteVolumeMajorant`; semi-truncated: `sum_semiTruncated_pair_le_finiteVolumeMajorant`) | Finite volume, ferromagnetic, `h ≥ 0`, high-temperature window `0 < β J·2d < 1`: (2a) per-term exponential bound `⟨σᵢ;σⱼ⟩ ≤ exp(m)·exp(-m·d(i,j))` with `m = simonLiebRate β J d` uniform in `h` and `Λ` (via GHS field-antitonicity to `h = 0` + Z₂ singleton collapse + Simon–Lieb decay); (2b) summability `∑_k exp(m)·exp(-m·d(x,k)) < ∞`; (2c-Ursell) composed site-sum bound `∑_{k≠i,j} \|U₃(i,j,k)\| ≤ M(i) + M(j)` with finite `M` independent of `Λ` and `h`; (2c-semi-truncated) two-sided off-diagonal bound `0 ≤ ∑_{l≠i,j}⟨σᵢσⱼ; σ_l⟩ ≤ M(i) + M(j)` for the pair semi-truncated susceptibility via brick-1 upper bound, giving uniform Lipschitz `0 ≤ ∂_h⟨σᵢσⱼ⟩_Λ ≤ β(M(i) + M(j))` | `Concrete/LatticeGraphCorrelation/Truncated2GeneralFieldFiniteVolumeMajorant.lean` | **Conditional / limited-range (high-temperature window; axiom-free).** Bricks 2 toward GJ Thm 17.6.1 (p. 313); static pointwise-plus-summable bound (Ursell terms) and equi-Lipschitz-of-moments result (semi-truncated), **not** the equicontinuity/derivative-limit wall (Issue #4413) |
| **GJ Thm 17.6.1 Option B capstone: finite-volume ∂/∂h uniform bound** (`hasDerivAt_correlation_h_uniform_bound`) | Finite volume, ferromagnetic, `h ≥ 0`, high-temperature window `0 < β J·2d < 1`, on a `Preconnected` induced subgraph, distinct sites `i ≠ j`: the map `h' ↦ ⟨σ_iσ_j⟩_{h'}` is differentiable at `h` with derivative `g'` satisfying the two-sided field- and volume-uniform bound `0 ≤ g' ≤ β(M(i) + M(j) + 2)`, where `M(x) = ∑_l exp(m)·exp(-m·d(x,l))` and `m = simonLiebRate β J d`. This is the **book-faithful finite deliverable**: differentiability plus field/volume-uniform derivative bound by sums of products of two-point functions (GJ Thm 17.6.1, p. 313, via Lebowitz Cor. 4.3.3/4.3.4). It remains distinct from the downstream infinite-volume reduced-field derivative: the latter covers a nonempty general observable only for normalized `⟨a,b,1⟩`, small `a`, and `0 < b < r < π/2`, and supplies no U3-series identity or uniform bound. | `Concrete/LatticeGraphCorrelation/Truncated2FieldDerivativeUniformBound.lean` | **Conditional / limited-range (high-temperature window; axiom-free).** GJ Thm 17.6.1 Option B capstone (Issue #4790): finite-volume differentiability + field/volume-uniform derivative bound |
| **Tail/collar uniform-smallness bound for ∂/∂h site-sum** (`tendsto_finiteVolumeMajorant_compl_atTop_zero`, `sum_abs_truncated3_collar_le_majorant_tail`) | Finite volume, ferromagnetic, `h ≥ 0`, high-temperature window `0 < β J·2d < 1`: (3a) majorant-tail vanishing `(∑_{x ∉ Λ_N} g_i(x) + ∑_{x ∉ Λ_N} g_j(x)) → 0` as `N → ∞`, with `g_a(x) = exp(m)·exp(-m·d(a,x))` and `m = simonLiebRate β J d`; (3b) collar off-diagonal bound `∑_{k ∈ Λfull, k ∉ Λcut} \|U₃(i,j,k)\| ≤ (∑_{x ∉ Λcut} g_i(x)) + (∑_{x ∉ Λcut} g_j(x))`, uniform in both `h` and `Λfull` (depends only on `Λcut`, the pair `i,j`, and the rate); (3c) this tail bound does not establish the unresolved real infinite-volume derivative identity tracked by #4790 | `Concrete/LatticeGraphCorrelation/Truncated3FieldDerivCollarTail.lean` | **Conditional / limited-range (high-temperature window; axiom-free).** Brick 3 toward GJ Thm 17.6.1 (p. 313); pure Weierstrass-M-test tail/collar unit, **no** infinite-volume objects or equicontinuity (Issue #4790) |
| **Infinite-volume Weierstrass majorant for ∂/∂h site-sum** (`abs_truncated3Infinite_le`, `summable_truncated3Infinite`, `sum_abs_truncated3Infinite_compl_le_majorant_tail`) | Infinite-volume, ferromagnetic, `h ≥ 0`, high-temperature window `0 < β J·2d < 1`, exhaustion with `Preconnected` induced subgraphs: (3c-i) per-term exponential majorant `\|U₃^∞(i,j,k)\| ≤ exp(m)·exp(-m·d(i,k)) + exp(m)·exp(-m·d(j,k))` for distinct `i, j, k`; (3c-ii) summability of `k ↦ U₃^∞(i,j,k)` off-diagonal (dominated by brick 2b's `summable_truncated2FiniteVolumeMajorant`); (3c-iii) complement-tail bound `∑_{k ∉ Λcut} \|U₃^∞(i,j,k)\| ≤ (∑_{x ∉ Λcut} g_i(x)) + (∑_{x ∉ Λcut} g_j(x))`, where right-hand side is brick 3a's `Rem(m) → 0`. **Derivative identity `g'=β∑U^∞` remains unresolved under #4790.** | `Concrete/LatticeGraphCorrelation/Truncated3FieldDerivInfiniteMajorant.lean` | **Conditional / limited-range (high-temperature window; axiom-free).** Reduced brick 3c toward GJ Thm 17.6.1 (p. 313); **first infinite-volume statement** of the ∂/∂h brick chain; pure domination/summability layer, **not** equicontinuity (Issue #4790) |

## §4.2: Thermodynamic limit of correlations (Thm 4.2.3)

Original GJ statement: as `Λ ↑ ℝᵈ`, `⟨σ^B⟩_Λ` converges.
Formalized in three regimes:

| Result | Statement | File | Regime |
|---|---|---|---|
| `correlation_convergent` | `⟨σ^A⟩_{(n,h,β)}` converges as `J = n → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_h` | `⟨σ^A⟩_{(J,n,β)}` converges as `h = n → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_beta` | `⟨σ^A⟩_{(J,h,n+1)}` converges as `β = n+1 → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_subgraph` | `⟨σ^A⟩_{Gₙ}` converges for `Gₙ ↑` | `InfiniteVolume.lean` | Discretized Λ↑ |
| `Ambient.correlationInfinite` | `correlationInfinite := ⨆ n, correlationAlongExhaustion G Λ p A n` | `AmbientLattice.lean` | **Genuine ∞-vol (full)**: convergence, Λ-independence, GKS-I/II, J/h/β monotonicity |

Named specializations at `A = {i}`:
- Finite / Discretized: `magnetization_convergent_{J,h,beta,subgraph}`
- Genuine ∞-vol: `Ambient.magnetizationInfinite`
  (nonneg / le_one / indep_exhaustion / monotone_{J,h,beta} inherited from `correlationInfinite`)

Named specialization at `A = {i, j}`: `twoPoint_convergent_subgraph`
(`IsingModel/InfiniteVolume/Lattice.lean`) — the two-point form of
`correlation_convergent_subgraph`, supplying the convergence of `⟨σᵢσⱼ⟩_{Gₙ}` that the
§5.1 two-point discussion of symmetry breaking presupposes.
