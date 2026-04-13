---
layout: default
title: Home
---

## ising-model

Lean 4 + mathlib formalization of theorems about the Ising model.

## Formalized theorems

All theorems are formally proved with **zero `sorry`**.

| Theorem                                   | Statement                                                                                           | File                       |
|-------------------------------------------|-----------------------------------------------------------------------------------------------------|----------------------------|
| **GKS-I** (First Griffiths inequality)    | `⟨σ^A⟩ ≥ 0` for ferromagnetic parameters                                                          | `Inequalities/GKS.lean`    |
| **GKS-II** (Second Griffiths inequality)  | `⟨σ^A σ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩` for ferromagnetic parameters                                          | `Inequalities/GKS.lean`    |
| **FKG** (Fortuin-Kasteleyn-Ginibre)       | `⟨fg⟩ ≥ ⟨f⟩⟨g⟩` for monotone nondecreasing f, g                                                    | `Inequalities/FKG.lean`    |
| **Asano contraction**                     | Contraction preserves non-vanishing on the unit polydisk                                            | `Asano.lean`               |
| **Lee-Yang circle theorem**               | Ising partition polynomial nonvanishing on the open polydisk                                        | `LeeYang.lean`             |
| **φ⁴ algebraic identities**             | Quartic/orthogonal transformation identities (axioms: `phi4_integrable`, `phi4_single_site_nonneg`) | `ContinuousSpin/Phi4.lean` |
| **Correlation boundedness** (Prop 4.2.2)  | `|⟨σ^A⟩| ≤ 1`                                                                                     | `InfiniteVolume.lean`      |
| **Correlation monotonicity (J)** (Prop 4.2.1) | `⟨σ^B⟩` monotone in J on `[0,∞)`                                                               | `InfiniteVolume.lean`      |
| **Correlation monotonicity (h)** (Prop 4.2.4) | `⟨σ^B⟩` monotone in h on `[0,∞)`                                                               | `InfiniteVolume.lean`      |
| **Covariance non-negativity**             | `Cov(σ^B, f) ≥ 0` for HNC f under Boltzmann weight                                                | `InfiniteVolume.lean`      |
| **Correlation convergence** (Thm 4.2.3)   | `⟨σ^B⟩` converges as J → ∞                                                                       | `InfiniteVolume.lean`      |
| **Free energy** (§4.6)                   | `f = |ι|⁻¹ ln Z`, monotone in J and h                                                             | `FreeEnergy.lean`          |
| **Lee-Yang nonvanishing (Ising)**         | Ising partition polynomial ≠ 0 on polydisk                                                         | `FreeEnergy.lean`          |
| **GHS inequality** (Cor 4.3.4)            | `⟨σ_i; σ_j; σ_k⟩ ≤ 0` (from Lebowitz third inequality)                                          | `Inequalities/GHS.lean`    |
| **Cor 4.3.3** (truncated 4-point ≤ 0)     | `U₄(i,j,k,l) ≤ 0` for h = 0                                                                      | `Inequalities/GHS.lean`    |
| **Cor 4.3.5** (n-point inductive bound)   | `⟨σ_{S∪{j,k}}⟩ ≤ ⟨σ_S⟩⟨σ_jσ_k⟩ + Σ_{T⊆S} ⟨σ_{T∪{j}}⟩⟨σ_{(S\T)∪{k}}⟩` | `Inequalities/GHS.lean`    |
| **Odd correlation vanishing**              | `⟨σ^A⟩ = 0` for odd \|A\| when h = 0                                                              | `Inequalities/GHS.lean`    |
| **Truncated 2-point bound** (§5.1)        | `0 ≤ ⟨σ_i;σ_j⟩ ≤ 1` for ferromagnetic                                                            | `PhaseTransition.lean`     |
| **Mixed-phase formula** (§5.1)            | `mixed_phase_truncated2`: `M² - (M(2α-1))² = 4α(1-α)M²`                                          | `PhaseTransition.lean`     |
| **Mixed-phase pure iff** (§5.1)           | `mixed_phase_pure_iff`: `4α(1-α)M² = 0 ↔ α ∈ {0,1}`                                              | `PhaseTransition.lean`     |
| **Mean field energy symmetry** (§5.2)     | `meanFieldEnergy_neg`: `φ(-m) = φ(m)` at h = 0                                                    | `PhaseTransition.lean`     |
| **Mean field trivial solution** (§5.2)    | `meanField_zero_solution`: `tanh(0) = 0`                                                          | `PhaseTransition.lean`     |
| **Free energy analyticity** (Thm 4.6.2)   | `f(h)` real-analytic for h > 0; `Z(h)`, `Z(J)` real-analytic                                      | `FreeEnergy.lean`          |
| **Walsh orthogonality/Fourier**           | Fourier inversion on `{±1}^n`                                                                      | `InfiniteVolume.lean`      |
| Partition function positivity             | `Z > 0`                                                                                             | `GibbsMeasure.lean`        |
| Spin flip symmetry                        | `H(flip σ) = H(σ)` when h = 0                                                                     | `Hamiltonian.lean`         |
| **Hamiltonian–boundary identity**         | `H(σ) = -J(|E| - 2|∂σ|)` for h = 0                                                               | `Peierls.lean`             |
| **Peierls bound** (Prop 5.4.1)            | `Pr(γ ⊆ ∂σ) ≤ exp(-2βJ|γ|)`                                                                      | `Peierls.lean`             |
| **Peierls contour sum bound**             | `Σ Pr(γ) ≤ N(r) exp(-2βJr)` for contours of size r                                                | `Peierls.lean`             |
| **Spontaneous magnetization** (Prop 5.4.2) | `0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)` for β large, under + BC                                             | `Peierls.lean`             |

## Axioms

Two axioms whose proofs are mathematically complete but require
measure-theoretic infrastructure not yet formalized in Lean:

- `phi4_single_site_nonneg` — φ⁴ single-site non-negativity (`ContinuousSpin/Phi4.lean`)
- `lebowitz_third` — Lebowitz inequality for 3 sites via φ⁴ limit (`Inequalities/GHS.lean`)
- `lebowitz_four` — Lebowitz inequality for 4 sites via φ⁴ limit (`Inequalities/GHS.lean`)
- `lebowitz_inductive` — inductive Lebowitz bound for general Finsets (`Inequalities/GHS.lean`)

## References

- Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (Theorem 4.1.1, 4.1.3)
- Friedli & Velenik, *Statistical Mechanics of Lattice Systems* (Theorems 3.21, 3.49, 3.50)

## Documentation

- [API documentation (doc-gen4)](docs/) — generated from Lean source
- [Mathematical proof guide](https://github.com/phasetr/ising-model/blob/main/tex/proof-guide.tex) — LaTeX source
- [Source code on GitHub](https://github.com/phasetr/ising-model)
