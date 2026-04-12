# ising-model

A Lean 4 + mathlib project for formalizing theorems about the Ising model.

## About this project

This repository is written by a programmer without an academic position, whose
interests lie in non-relativistic quantum field theory and rigorous statistical
mechanics. Continuing a long-standing interest in mathematical physics from my
student days, and combined with the goal of improving my technical skills as a
programmer, I started `ising-model` as a personal hobby project to become
proficient in Lean 4 by formalizing results around the Ising model.

The intended scope is limited to finite-volume results such as correlation
inequalities and the infinite volume limit of correlation functions. This project is not intended to interfere with the work of researchers in
the field, and if any overlap arises I am happy to coordinate accordingly.

## Formalized theorems

All theorems are formally proved with **zero `sorry`**.

| Theorem | Statement                          | Reference                                       |
|---------|------------------------------------|-------------------------------------------------|
| GKS-I   | `⟨σ^A⟩ ≥ 0`                        | Glimm-Jaffe Thm 4.1.1, Friedli-Velenik Thm 3.49 |
| GKS-II  | `⟨σ^A σ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩`           | Friedli-Velenik Thm 3.49                        |
| FKG     | `⟨fg⟩ ≥ ⟨f⟩⟨g⟩` for monotone f, g  | Friedli-Velenik Thm 3.21/3.50                   |
| Asano contraction | contraction preserves non-vanishing | Friedli-Velenik Prop 3.44     |
| Lee-Yang circle   | Ising partition poly nonvanishing on polydisk | Ruelle, Ann. of Math. 171 (2010); Harcos notes |
| Partition function positivity | `Z > 0` | — |
| Spin flip symmetry | `H(flip σ) = H(σ)` when h = 0 | — |
| φ⁴ algebraic identities | quartic/orthogonal transformation identities | Glimm-Jaffe §4.3 |
| Correlation boundedness | `\|⟨σ^A⟩\| ≤ 1` (Prop 4.2.2) | Glimm-Jaffe §4.2 |

### Axioms (measure-theoretic prerequisites, not formalized)

The φ⁴ inequalities (`ContinuousSpin/Phi4.lean`) use two axioms for
measure-theoretic properties whose proofs are mathematically complete
but require heavy Lean measure theory assembly:

- `phi4_integrable`: integrability of polynomial × exp(-quartic)
- `phi4_single_site_nonneg`: non-negativity of the symmetrized 4D integral

These axioms are prerequisites for the Lebowitz inequality and truncated
3-point correlation bound (Corollaries 4.3.2–4.3.4, to be formalized).

- `hnc_correlation_nonneg`: HNC covariance inequality (Fourier expansion + generalized GKS-II)
- `correlation_reweighting_nonneg`: exp splitting + hnc_correlation_nonneg application

## Documentation

- Project page: [https://phasetr.github.io/ising-model/](https://phasetr.github.io/ising-model/)
- API documentation (doc-gen4): [https://phasetr.github.io/ising-model/docs/](https://phasetr.github.io/ising-model/docs/)

Mathematical documentation for the formalized proofs is in `tex/` as
LaTeX source files. To compile:

```sh
cd tex
latexmk -lualatex proof-guide.tex
```

Requires a TeX Live installation with LuaLaTeX. PDFs are not committed
to the repository.

| File                       | Description                                          |
|----------------------------|------------------------------------------------------|
| `tex/proof-guide.tex`      | Mathematical walkthrough of the formalized proofs    |

## Related projects and references

- Glimm, J. and Jaffe, A., *Quantum Physics: A Functional Integral Point of View* — [Springer](https://link.springer.com/book/10.1007/978-1-4612-4728-9)
- 田崎晴明, 原隆, 『相転移と臨界現象の数理』 — [共立出版](https://www.kyoritsu-pub.co.jp/book/b10003637.html)
- 江沢洋, 新井朝雄, 『場の量子論と統計力学』 — [日本評論社](https://www.nippyo.co.jp/shop/book/9014.html)
- [YaelDillies/gibbs-measure](https://github.com/YaelDillies/gibbs-measure) — Lean 4 formalization project on Gibbs measures
- [leanprover-community/physlib](https://github.com/leanprover-community/physlib) — A physics library in Lean 4
- Friedli, S. and Velenik, Y., *Statistical Mechanics of Lattice Systems: A Concrete Mathematical Introduction* — [Cambridge UP](https://www.unige.ch/math/folks/velenik/smbook/)
- Simon, B., *The Statistical Mechanics of Lattice Gases, Vol. I* — [Princeton UP](https://press.princeton.edu/books/hardcover/9780691636436/the-statistical-mechanics-of-lattice-gases-volume-i)
- Ellis, R.S., *Entropy, Large Deviations, and Statistical Mechanics* — [Springer](https://link.springer.com/book/10.1007/3-540-29060-5)
- Dembo, A. and Zeitouni, O., *Large Deviations Techniques and Applications* — [Springer](https://link.springer.com/book/10.1007/978-3-642-03311-7)

## Learning resources

- [The Mechanics of Proof (Math 2001)](https://hrmacbeth.github.io/math2001/) by Heather Macbeth
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/index.html)
