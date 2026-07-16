import IsingModel.AmbientLattice.SpontaneousMagnetization

/-!
# Infinite-volume truncated two-point functions

Mechanical child split from `AmbientLattice/TruncatedFunctions.lean`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Truncated 2-point correlation at infinite volume

Specialize `correlationInfinite_gks_second` (PR #94) to the
two-point case, obtaining the truncated 2-point correlation function
$U_2(i, j) := \langle \sigma_i \sigma_j \rangle_\infty
  - \langle \sigma_i \rangle_\infty \langle \sigma_j \rangle_\infty$
and the nonnegativity $U_2 \ge 0$ for $i \ne j$.

Reference: Glimm–Jaffe §4.2 p. 57ff, Friedli–Velenik §3.6.3. -/

/-- **Truncated 2-point correlation at infinite volume**:
$U_2(i, j) := \langle \sigma_i \sigma_j \rangle_\infty
  - \langle \sigma_i \rangle_\infty \langle \sigma_j \rangle_\infty$. -/
noncomputable def truncated2Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j : V) : ℝ :=
  correlationInfinite G Λ p {i, j}
    - correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j}

/-- **Unfolding of `truncated2Infinite`**: the defining Ursell 2-point
(covariance) formula as a named identity. -/
theorem truncated2Infinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j : V) :
    truncated2Infinite G Λ p i j
      = correlationInfinite G Λ p {i, j}
        - correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j} := rfl

/-- **Symmetry in the two arguments**: $U_2(i, j) = U_2(j, i)$. -/
theorem truncated2Infinite_symm
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j : V) :
    truncated2Infinite G Λ p i j = truncated2Infinite G Λ p j i := by
  unfold truncated2Infinite
  rw [Finset.pair_comm, mul_comm]

/-- **Nonnegativity for distinct sites**: $U_2(i, j) \ge 0$ for
$i \ne j$.  Direct corollary of `correlationInfinite_gks_second`:
$\{i, j\} = \{i\} \,\triangle\, \{j\}$ when $i \ne j$. -/
theorem truncated2Infinite_nonneg_of_ne
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j : V} (hij : i ≠ j) :
    0 ≤ truncated2Infinite G Λ p i j := by
  unfold truncated2Infinite
  have hset : ({i, j} : Finset V) = ({i} : Finset V) ∆ ({j} : Finset V) := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hij⟩
      · exact Or.inr ⟨rfl, hij.symm⟩
    · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [hset]
  linarith [correlationInfinite_gks_second G Λ p hf {i} {j}]

/-- **Nonnegativity for coincident sites**: $U_2(i, i) \ge 0$.
On the diagonal `{i, i} = {i}` so $U_2(i, i) = M(i) - M(i)^2
  = M(i)(1 - M(i)) \ge 0$ since $M(i) \in [0, 1]$. -/
theorem truncated2Infinite_nonneg_of_eq
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    0 ≤ truncated2Infinite G Λ p i i := by
  unfold truncated2Infinite
  have hset : ({i, i} : Finset V) = {i} := by simp
  rw [hset]
  have h0 : 0 ≤ correlationInfinite G Λ p {i} :=
    correlationInfinite_nonneg G Λ p hf {i}
  have h1 : correlationInfinite G Λ p {i} ≤ 1 :=
    correlationInfinite_le_one G Λ p {i}
  nlinarith

/-- **∞-volume truncated 2-point function vanishes at `J = 0`**
(ferromagnetic, distinct sites): for `⟨0, h, β⟩` ferromagnetic and
`i ≠ j`, `truncated2Infinite G Λ ⟨0, h, β⟩ i j = 0`.

Infinite-volume counterpart of `truncated2_J_zero_of_ne` (finite
volume, PR #207 in `Inequalities/GHS.lean`). Uses the closed form
`correlationInfinite_J_zero` at `{i,j}`, `{i}`, `{j}` together with
the Finset-card identities `{i,j}.card = 2`,
`{i}.card = {j}.card = 1`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.1 (infinite-temperature slice). -/
theorem truncated2Infinite_J_zero_of_ne
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j : V} (hij : i ≠ j) :
    truncated2Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i j = 0 := by
  unfold truncated2Infinite
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_pair : ({i, j} : Finset V).card = 2 := Finset.card_pair hij
  have hcard_i : ({i} : Finset V).card = 1 := Finset.card_singleton i
  have hcard_j : ({j} : Finset V).card = 1 := Finset.card_singleton j
  rw [hcard_pair, hcard_i, hcard_j]
  ring

/-- **∞-volume truncated 2-point at `J = 0` diagonal**:
`truncated2Infinite ⟨0, h, β⟩ i i = tanh(β·h) · (1 − tanh(β·h))`
(ferromagnetic). Complements `truncated2Infinite_J_zero_of_ne`
(off-diagonal = 0). Uses the Finset collapse `{i,i} = {i}`, so
`⟨σ_i σ_i⟩ = ⟨σ_i⟩` at the Finset level — the same caveat as
`susceptibility_J_zero` and `twoPointFunction_zero`. Pure algebraic
identity at `J = 0` via `correlationInfinite_J_zero`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated2Infinite_J_zero_diagonal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : V) :
    truncated2Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) := by
  unfold truncated2Infinite
  have hpair : ({i, i} : Finset V) = {i} := by simp
  have h1 : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  rw [hpair, h1]
  ring

/-- **∞-volume truncated 2-point function vanishes at `β = 0`**
for any `J, h` and any sites `i, j : V` (distinct or not).

Infinite-volume counterpart of `truncated2_beta_zero` (finite
volume, PR #208 in `Inequalities/GHS.lean`). Uses
`correlationInfinite_beta_zero_vanish` on each of
`{i, j}`, `{i}`, `{j}` (all nonempty). No distinctness hypothesis
is required: when `i = j`, `{i, j}` collapses to `{i}` at the
Finset level inside `truncated2Infinite`, and the same vanishing
applies.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.1 infinite-temperature slice. -/
theorem truncated2Infinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i j : V) :
    truncated2Infinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i j = 0 := by
  unfold truncated2Infinite
  rw [correlationInfinite_beta_zero_vanish G Λ J h
        {i, j} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i} (Finset.singleton_nonempty i),
      correlationInfinite_beta_zero_vanish G Λ J h
        {j} (Finset.singleton_nonempty j)]
  ring

/-- **Nonnegativity of `truncated2Infinite`** (general): $U_2(i, j) \ge 0$
for all `i, j : V`, combining the `_of_ne` and `_of_eq` cases. -/
theorem truncated2Infinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    0 ≤ truncated2Infinite G Λ p i j := by
  by_cases hij : i = j
  · subst hij
    exact truncated2Infinite_nonneg_of_eq G Λ p hf i
  · exact truncated2Infinite_nonneg_of_ne G Λ p hf hij

/-- **Upper bound by `correlationInfinite`**: for ferromagnetic `p`,
`truncated2Infinite G Λ p i j ≤ correlationInfinite G Λ p {i, j}`.
The product term `⟨σ_i⟩·⟨σ_j⟩` is nonneg by GKS-I, so subtracting it
from `correlationInfinite {i, j}` reduces the value. -/
theorem truncated2Infinite_le_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    truncated2Infinite G Λ p i j
      ≤ correlationInfinite G Λ p {i, j} := by
  unfold truncated2Infinite
  have hi := correlationInfinite_nonneg G Λ p hf {i}
  have hj := correlationInfinite_nonneg G Λ p hf {j}
  have : 0 ≤ correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j} :=
    mul_nonneg hi hj
  linarith

/-- **`truncated2Infinite ≤ 1`** for ferromagnetic `p`: from
`truncated2Infinite_le_correlationInfinite` and
`correlationInfinite_le_one`. -/
theorem truncated2Infinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    truncated2Infinite G Λ p i j ≤ 1 := by
  have h₁ := truncated2Infinite_le_correlationInfinite G Λ p hf i j
  have h₂ := correlationInfinite_le_one G Λ p {i, j}
  linarith

/-- **`-1 ≤ truncated2Infinite`** for ferromagnetic `p`: direct from
`truncated2Infinite_nonneg`. -/
theorem neg_one_le_truncated2Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    -1 ≤ truncated2Infinite G Λ p i j := by
  have := truncated2Infinite_nonneg G Λ p hf i j
  linarith

/-- **`|truncated2Infinite| ≤ 1`** for ferromagnetic `p`. -/
theorem abs_truncated2Infinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    |truncated2Infinite G Λ p i j| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_truncated2Infinite G Λ p hf i j,
    truncated2Infinite_le_one G Λ p hf i j⟩

/-- **`truncated2Infinite² ≤ 1`** for ferromagnetic `p`. -/
theorem truncated2Infinite_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    truncated2Infinite G Λ p i j ^ 2 ≤ 1 := by
  have h := abs_truncated2Infinite_le_one G Λ p hf i j
  have : |truncated2Infinite G Λ p i j| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Exhaustion-independence of `truncated2Infinite`**: the value
does not depend on the choice of exhaustion.  Follows from
`correlationInfinite_indep_exhaustion` applied to each of the three
`correlationInfinite` occurrences in the definition. -/
theorem truncated2Infinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    truncated2Infinite G Λ p i j = truncated2Infinite G Λ' p i j := by
  unfold truncated2Infinite
  rw [correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j}]

/-- **`truncated2Infinite` at `h = 0`**: since
$\langle \sigma_i \rangle_\infty = \langle \sigma_j \rangle_\infty = 0$
at $h = 0$ (singletons have odd cardinality 1, so
`correlationInfinite_h_zero` applies), the truncated 2-point function
reduces to the raw 2-point correlation:
$U_2(i, j; \langle J, 0, \beta \rangle) = \langle \sigma_i \sigma_j \rangle_\infty$.

Holds for all `i, j : V` (no distinctness needed): if `i = j`, both
sides equal `correlationInfinite G Λ ⟨J, 0, β⟩ {i}` which is `0` by
the same Z₂ argument.  Useful as a closed-form expression for the
truncated correlation at zero external field (connects to
susceptibility/fluctuation analysis). -/
theorem truncated2Infinite_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i j : V) :
    truncated2Infinite G Λ ⟨J, 0, β⟩ i j
      = correlationInfinite G Λ ⟨J, 0, β⟩ {i, j} := by
  unfold truncated2Infinite
  have h_i : Odd ({i} : Finset V).card := by simp
  have h_j : Odd ({j} : Finset V).card := by simp
  rw [correlationInfinite_h_zero G Λ J β _ h_i,
      correlationInfinite_h_zero G Λ J β _ h_j]
  ring

-- (Step 275 duplicates removed: see truncated2Infinite_J_zero_of_ne and
-- truncated2Infinite_J_zero_diagonal earlier in this file.)

/-- **Conditional cluster decay (cofinite form)**: if the ∞-volume
Ursell 2-point function at a fixed site `i : V`, viewed as a function
of the free site `j : V`, is *summable* over `V`, then it tends to `0`
along the cofinite filter:
`Tendsto (fun j => truncated2Infinite G Λ p i j) Filter.cofinite (nhds 0)`.

Direct application of mathlib's `Summable.tendsto_cofinite_zero`.

**Interpretation.** The summability hypothesis is a finiteness
condition on the two-point function summed over the free argument `j`.
In translation-invariant / connected-correlation settings (e.g. a
pure phase of a ℤ^d Ising model) this matches the physical notion of
finite susceptibility `χ_∞ < ∞`, expected to hold away from the
critical line; in the general ambient setup here it is just the
real-analysis condition `Summable`. `Filter.cofinite` on `V` is the
filter of cofinite subsets — eventually avoiding every finite subset
— which on `V = Fin d → ℤ` (with `d ≥ 1`) aligns with the usual
"$|r| \to \infty$" interpretation (bounded subsets of the lattice are
finite). So this is a *conditional* cluster decay statement in the
spirit of Glimm–Jaffe §5.1.

Unconditional exponential cluster decay in pure phases (Simon–Lieb
inequality and follow-ups) remains unformalized; this lemma is the
elementary real-analysis building block waiting to be composed with a
future proof of summability.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated2Infinite_tendsto_cofinite_zero_of_summable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V)
    (hsum : Summable (fun j : V => truncated2Infinite G Λ p i j)) :
    Filter.Tendsto (fun j : V => truncated2Infinite G Λ p i j)
      Filter.cofinite (nhds 0) :=
  hsum.tendsto_cofinite_zero


end Ambient
end IsingModel
