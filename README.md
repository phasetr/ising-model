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
| Correlation monotonicity (J) | `⟨σ^B⟩` monotone in J on `[0,∞)` (Prop 4.2.1) | Glimm-Jaffe §4.2 |
| Correlation monotonicity (h) | `⟨σ^B⟩` monotone in h on `[0,∞)` (Prop 4.2.4) | Glimm-Jaffe §4.2 |
| Covariance non-negativity | `Cov(σ^B, f) ≥ 0` for HNC f | Glimm-Jaffe §4.2 |
| Correlation convergence | `⟨σ^B⟩` converges as J → ∞ (Thm 4.2.3) | Glimm-Jaffe §4.2 |
| Free energy monotonicity | Z and f monotone in J and h on [0,∞) | Glimm-Jaffe §4.6 |
| Lee-Yang nonvanishing (Ising) | partition polynomial ≠ 0 on polydisk | Glimm-Jaffe §4.5-4.6 |
| GHS inequality | `⟨σ_i; σ_j; σ_k⟩ ≤ 0` | Ellis §V.3, Lebowitz (1974) |
| Cor 4.3.3 (truncated 4-point ≤ 0) | `U₄(i,j,k,l) ≤ 0` for h = 0 | Glimm-Jaffe §4.3 |
| Odd correlation vanishing | `⟨σ^A⟩ = 0` for odd \|A\| when h = 0 | Spin-flip symmetry |
| Free energy analyticity (Thm 4.6.2) | `freeEnergyH_analyticOn`: `f(h)` real-analytic for h > 0 | Glimm-Jaffe §4.6 |
| Partition function analyticity | `partitionFunctionH_analyticAt`, `partitionFunctionJ_analyticAt` | Glimm-Jaffe §4.6 |
| Truncated 2-point bound (§5.1) | `truncated2_le_one`: `0 ≤ ⟨σ_i;σ_j⟩ ≤ 1` | Glimm-Jaffe §5.1 |
| Mixed-phase formula (§5.1) | `mixed_phase_truncated2`: `M² - (M(2α-1))² = 4α(1-α)M²` | Glimm-Jaffe §5.1 |
| Mixed-phase pure iff (§5.1) | `mixed_phase_pure_iff`: `4α(1-α)M² = 0 ↔ α ∈ {0,1}` | Glimm-Jaffe §5.1 |
| Mean field energy symmetry (§5.2) | `meanFieldEnergy_neg`: `φ(-m) = φ(m)` at h = 0 | Glimm-Jaffe §5.2 |
| Mean field trivial solution (§5.2) | `meanField_zero_solution`: `tanh(β(Jz·0+0)) = 0` | Glimm-Jaffe §5.2 |
| Susceptibility non-negative (§5.3) | `susceptibility_nonneg`: `χ(i) = Σ_j ⟨σ_i;σ_j⟩ ≥ 0` | Glimm-Jaffe §5.3 |
| Magnetization vanishes at h=0 (§5.3) | `magnetization_zero_at_h_zero`: Z₂ symmetry | Glimm-Jaffe §5.3 |
| Z monotone in β (Cor 10.2.3) | `partitionFunction_monotone_beta`: Z(β₁) ≤ Z(β₂) | Glimm-Jaffe §10.2 |
| Hamiltonian bound (Cor 10.3.2) | `hamiltonian_abs_le`: \|H(σ)\| ≤ \|J\|\|E\| + \|h\|\|ι\| | Glimm-Jaffe §10.3 |
| Z upper bound (Cor 10.3.2) | `partitionFunction_upper`: Z ≤ 2^\|ι\| exp(\|β\| bound) | Glimm-Jaffe §10.3 |
| Z lower bound (Cor 10.3.2) | `partitionFunction_lower`: exp(-\|β\| bound) ≤ Z | Glimm-Jaffe §10.3 |
| Reflection positivity (§10.4) | `ReflectionPositive`: b(x,x) ≥ 0 | Glimm-Jaffe §10.4 |
| Discriminant lemma (§10.4) | `discriminant_nonneg`: b² ≤ ac from nonneg quadratic | Glimm-Jaffe §10.4 |
| Iterated Schwarz (§10.5) | `iterated_schwarz_sq`: x² ≤ ax ⟹ x ≤ a | Glimm-Jaffe §10.5 |
| Magnetization monotone in h (§16.1) | `magnetization_monotone_h`: M(h₁) ≤ M(h₂) | Glimm-Jaffe §16.1 |
| Hamiltonian–boundary identity | `H(σ) = -J(|E| - 2|∂σ|)` for h = 0 | Glimm-Jaffe §5.4 |
| Peierls bound (Prop 5.4.1) | `Pr(γ ⊆ ∂σ) ≤ exp(-2βJ|γ|)` | Glimm-Jaffe §5.4 |
| Peierls contour sum bound | `Σ Pr(γ) ≤ N(r) exp(-2βJr)` | Glimm-Jaffe §5.4 |
| Spontaneous magnetization (Prop 5.4.2) | `0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)` for β large | Glimm-Jaffe §5.4 |

### Axioms

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
| §16.2 | The two phase region | **Not started** | — | Ising model phase coexistence |
| §16.3 | Symmetry unbroken, d = 2 | **Not started** | — | Mermin-Wagner for continuous spins |
| §16.4 | Symmetry broken, d ≥ 3 | **Not started** | — | Ising model; d_cr = 2 |

### Chapter 17: The φ⁴ Critical Point

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §17.2 | Absence of even bound states | **Not started** | — | φ⁴/Ising |
| §17.5 | Existence of the φ⁴ critical point | **Not started** | — | Ising limit |
| §17.7 | Critical exponents | **Not started** | — | Ising model |
| §17.8 | φ⁴₁ | **Not started** | — | Ising model |

### Chapter 18: The Cluster Expansion

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §18.1 | Introduction | **Not started** | — | Lattice models |
| §18.2 | The cluster expansion | **Not started** | — | |
| §18.3 | Clustering and analyticity | **Not started** | — | |

### Chapter 20: Further Directions

| Section | Result | Status | Lean | Notes |
|---|---|---|---|---|
| §20.5 | Low temperature expansions | **Not started** | — | Ising model; Peierls-type |

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
