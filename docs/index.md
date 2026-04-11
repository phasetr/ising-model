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
| **GKS-I** (First Griffiths inequality)   | `⟨σ_A⟩ ≥ 0` for ferromagnetic parameters                   | `Inequalities/GKS.lean` |
| **GKS-II** (Second Griffiths inequality) | `⟨σ_A σ_B⟩ ≥ ⟨σ_A⟩⟨σ_B⟩` for ferromagnetic parameters      | `Inequalities/GKS.lean` |
| **FKG** (Fortuin-Kasteleyn-Ginibre)      | `⟨fg⟩ ≥ ⟨f⟩⟨g⟩` for monotone nondecreasing f, g            | `Inequalities/FKG.lean` |
| **Asano contraction**                    | Contraction preserves non-vanishing on the unit polydisk    | `Asano.lean`            |
| Partition function positivity            | `Z > 0`                                                    | `GibbsMeasure.lean`     |
| Spin flip symmetry                       | `H(flip σ) = H(σ)` when h = 0                              | `Hamiltonian.lean`      |

## References

- Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (Theorem 4.1.1, 4.1.3)
- Friedli & Velenik, *Statistical Mechanics of Lattice Systems* (Theorems 3.21, 3.49, 3.50)

## Documentation

- [API documentation (doc-gen4)](docs/) — generated from Lean source
- [Mathematical proof guide](https://github.com/phasetr/ising-model/blob/main/tex/proof-guide.tex) — LaTeX source
- [Source code on GitHub](https://github.com/phasetr/ising-model)
