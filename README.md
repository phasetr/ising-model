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
inequalities; the thermodynamic limit and related topics are out of scope for
now. This project is not intended to interfere with the work of researchers in
the field, and if any overlap arises I am happy to coordinate accordingly.

## Documentation

Mathematical documentation for the formalized proofs is in `docs/` as
LaTeX source files. To compile:

```sh
cd docs
latexmk -lualatex gks-proof-guide.tex
```

Requires a TeX Live installation with LuaLaTeX. PDFs are not committed
to the repository.

| File                       | Description                                 |
|----------------------------|---------------------------------------------|
| `docs/gks-proof-guide.tex` | Mathematical walkthrough of the GKS-I proof |

## Related projects and references

- Glimm, J. and Jaffe, A., *Quantum Physics: A Functional Integral Point of View* — [Springer](https://link.springer.com/book/10.1007/978-1-4612-4728-9)
- 田崎晴明, 原隆, 『相転移と臨界現象の数理』 — [共立出版](https://www.kyoritsu-pub.co.jp/book/b10003637.html)
- 江沢洋, 新井朝雄, 『場の量子論と統計力学』 — [日本評論社](https://www.nippyo.co.jp/shop/book/9014.html)
- [YaelDillies/gibbs-measure](https://github.com/YaelDillies/gibbs-measure) — Lean 4 formalization project on Gibbs measures
- [leanprover-community/physlib](https://github.com/leanprover-community/physlib) — A physics library in Lean 4
- Friedli, S. and Velenik, Y., *Statistical Mechanics of Lattice Systems: A Concrete Mathematical Introduction* — [De Gruyter](https://www.degruyterbrill.com/document/doi/10.1515/9783110250329/html)

## Learning resources

- [The Mechanics of Proof (Math 2001)](https://hrmacbeth.github.io/math2001/) by Heather Macbeth
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/index.html)
