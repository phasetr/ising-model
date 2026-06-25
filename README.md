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

## Formalization status

All library theorems are formally proved with **zero `sorry`**, **zero `admit`**, and
**no `native_decide`** in proofs. The Glimm–Jaffe §17–18 programme (the rigorous
statistical mechanics of the ferromagnetic Ising model — GKS/FKG correlation
inequalities, Simon–Lieb decay, the random-walk / high-temperature representation,
the cluster expansion, infinite-volume limits, free-energy and two-point-function
analyticity, and the §17.5 sharp Hardy–Littlewood–Sobolev constant) is formalized in
book order.

The classical **Vitali–Porter convergence theorem** (normal families) — the function-theory
input behind the infinite-volume two-point correlation analyticity (GJ §18.6/§18.7) — was
formerly a declared axiom and is now **proved from Mathlib** inside the project: an in-project
complex **Montel theorem** (Cauchy-estimate equicontinuity + per-compact Arzelà–Ascoli over a
compact exhaustion + a diagonal extraction) together with the identity-theorem **uniqueness**
core. The infinite-volume two-point correlation analyticity is therefore now **fully axiom-free**.

The project is now **fully axiom-free**: every theorem reduces to `propext`,
`Classical.choice`, and `Quot.sound` only, with **no declared axioms**. The last
scope-excluded axiom — the locally-uniform derivative-limit provider for the GJ §17.5 sharp HLS
constant (Theorem 17.5.1 / Lemma 17.5.2) — has been **discharged** (Issue #4289 / #4296): it is
replaced by the in-project `ConvergenceRegion.derivativeLimit_on_window`, which proves the
locally-uniform convergence of the finite-stage β-derivatives on the genuine cluster-expansion
convergence window (`window d J ⊆ Ioo 0 (1/(J·2d))`) with no axiom, and the sharp-HLS capstone is
scoped to that window accordingly.

For the complete list of formalized theorems, the axiom-freeness audit, and the Glimm–Jaffe
chapter-by-chapter progress table, see the
**[project page](https://phasetr.github.io/ising-model/)**.

## Documentation

- Project page: [https://phasetr.github.io/ising-model/](https://phasetr.github.io/ising-model/)
- API documentation (doc-gen4): **temporarily unavailable** (automatic
  publication paused). See note below.

> **Note:** automatic publication of the doc-gen4 API reference to
> GitHub Pages is currently paused because each main-push run of the
> `docs` job was taking roughly an hour and queuing up behind every
> merge. The `docs` job in `.github/workflows/lean_action_ci.yml` is
> commented out until we accelerate the docgen step (caching, a
> scheduled run, or an alternative pipeline). To build the API
> reference locally, run `lake -R -Kenv=dev build IsingModel:docs`
> and open `.lake/build/doc/index.html`.

Mathematical documentation for the formalized proofs is in `tex/` as
LaTeX source files. To compile:

```sh
cd tex
latexmk -lualatex -f -interaction=nonstopmode proof-guide.tex
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
