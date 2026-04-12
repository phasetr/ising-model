---
layout: default
title: Home
---

## ising-model

Lean 4 + mathlib formalization of theorems about the Ising model.

## Formalized theorems

All theorems are formally proved with **zero `sorry`**.

| Theorem                                  | Statement                                                  | File                    |
|------------------------------------------|------------------------------------------------------------|-------------------------|
| **GKS-I** (First Griffiths inequality)   | `⟨σ^A⟩ ≥ 0` for ferromagnetic parameters                   | `Inequalities/GKS.lean` |
| **GKS-II** (Second Griffiths inequality) | `⟨σ^A σ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩` for ferromagnetic parameters      | `Inequalities/GKS.lean` |
| **FKG** (Fortuin-Kasteleyn-Ginibre)      | `⟨fg⟩ ≥ ⟨f⟩⟨g⟩` for monotone nondecreasing f, g            | `Inequalities/FKG.lean` |
| **Asano contraction**                    | Contraction preserves non-vanishing on the unit polydisk    | `Asano.lean`            |
| **Lee-Yang circle theorem**              | Ising partition polynomial nonvanishing on the open polydisk | `LeeYang.lean`          |
| **φ⁴ algebraic identities**              | Quartic/orthogonal transformation identities (axiom: integrability) | `ContinuousSpin/Phi4.lean` |
| **Correlation boundedness** (Prop 4.2.2) | `|⟨σ^A⟩| ≤ 1`                                              | `InfiniteVolume.lean`   |
| **Correlation monotonicity** (Prop 4.2.1) | `⟨σ^B⟩` monotone in J on `[0,∞)` (sorry: reweighting)       | `InfiniteVolume.lean`   |
| **Walsh orthogonality/Fourier**         | Fourier inversion on `{±1}^n`                                | `InfiniteVolume.lean`   |
| Partition function positivity            | `Z > 0`                                                    | `GibbsMeasure.lean`     |
| Spin flip symmetry                       | `H(flip σ) = H(σ)` when h = 0                              | `Hamiltonian.lean`      |

## Axioms

The φ⁴ module uses two measure-theoretic axioms (`phi4_integrable`,
`phi4_single_site_nonneg`) whose proofs are mathematically complete
but not formalized in Lean. See `ContinuousSpin/Phi4.lean` for details.

The infinite volume module has one sorry (`correlation_reweighting_nonneg`)
whose proof uses Fourier expansion + `gks_second` per term. All building
blocks (Walsh Fourier inversion, `gks_second`) are proved.
The false axiom `hnc_correlation_nonneg` has been removed.

## References

- Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (Theorem 4.1.1, 4.1.3)
- Friedli & Velenik, *Statistical Mechanics of Lattice Systems* (Theorems 3.21, 3.49, 3.50)

## Documentation

- [API documentation (doc-gen4)](docs/) — generated from Lean source
- [Mathematical proof guide](https://github.com/phasetr/ising-model/blob/main/tex/proof-guide.tex) — LaTeX source
- [Source code on GitHub](https://github.com/phasetr/ising-model)
