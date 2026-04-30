import IsingModel.AmbientLattice.SpontaneousMagnetization

/-!
# Truncated correlation functions at infinite volume

Definitions and properties of the infinite-volume truncated n-point
Ursell functions: `truncated2Infinite`, `truncated3Infinite`, `truncated4Infinite`.

Includes: cluster property definition (§5.1), GHS inequality at infinite
volume, U₄ ≤ 0 at h=0, and antitone-in-h results.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.3, §5.1.
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

/-! ## §5.1 cluster property: definition + sufficient condition + trivial slices

Bundled formalization of the Glimm–Jaffe §5.1 cluster property
for ferromagnets. The cluster property states that the truncated
2-point function $U_2(i, j) = \langle\sigma_i\sigma_j\rangle -
\langle\sigma_i\rangle\langle\sigma_j\rangle$ decays to $0$ as the
second site moves away to infinity.

Captured here: the formal predicate, a summable sufficient
condition consolidating
`truncated2Infinite_tendsto_cofinite_zero_of_summable`, and the
two trivial slices ($J = 0$ ferromagnetic, $\beta = 0$). The
general (non-trivial) case requires the Simon–Lieb inequality
(FV Prop 9.31) or random-current representation, both
research-level.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 76–79. -/

/-- **§5.1 cluster property** for the ∞-volume Ursell 2-point
function: at every fixed basepoint `i : V`, the function
`j ↦ truncated2Infinite G Λ p i j` tends to `0` along the
cofinite filter on `V`. A Glimm–Jaffe §5.1-motivated predicate
on `(G, Λ, p)`; the predicate itself does not build in a
ferromagnetic hypothesis, but the expected nontrivial positive
results (e.g.\ at high temperature or under a Simon–Lieb-type
summability assumption) apply in ferromagnetic regimes. -/
def clusterProperty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : Prop :=
  ∀ i : V, Filter.Tendsto (fun j : V => truncated2Infinite G Λ p i j)
    Filter.cofinite (nhds 0)

/-- **Cluster property from per-site summability**: if the
∞-volume Ursell 2-point function `j ↦ U_2(i, j)` is `Summable`
for every basepoint `i : V`, then the cluster property holds.
Per-site application of `truncated2Infinite_tendsto_cofinite_zero_of_summable`. -/
theorem clusterProperty_of_summable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hsum : ∀ i : V,
      Summable (fun j : V => truncated2Infinite G Λ p i j)) :
    clusterProperty G Λ p :=
  fun i => truncated2Infinite_tendsto_cofinite_zero_of_summable G Λ p i (hsum i)

/-- **Cluster property at the `J = 0` trivial slice (ferromagnetic)**.
At zero coupling with `0 ≤ h, 0 < β`, the truncated 2-point function
vanishes off-diagonally (`truncated2Infinite_J_zero_of_ne`). The
cofinite filter on `V` eventually avoids the singleton `{i}`, so
the function is eventually zero, hence trivially `Tendsto`s to `0`. -/
theorem clusterProperty_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    clusterProperty G Λ (⟨0, h, β⟩ : IsingParams ℝ) := by
  intro i
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  -- Eventually along cofinite: the function equals the constant 0.
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨{i}ᶜ, ?_, ?_⟩
  · rw [Filter.mem_cofinite]
    simp [Set.finite_singleton]
  · intro j hj
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hj
    exact (truncated2Infinite_J_zero_of_ne G Λ h β hf (Ne.symm hj)).symm

/-- **Cluster property at the `β = 0` trivial slice**. At infinite
temperature, the truncated 2-point function vanishes identically
(`truncated2Infinite_beta_zero`), so the function is the constant
zero, which trivially `Tendsto`s to `0`. No ferromagnetic
hypothesis required. -/
theorem clusterProperty_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) :
    clusterProperty G Λ (⟨J, h, 0⟩ : IsingParams ℝ) := by
  intro i
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  intro j _
  exact (truncated2Infinite_beta_zero G Λ J h i j).symm

/-! ## GHS consequence at infinite volume: truncated2Infinite antitone in h (Step 125)

Lift Step 124 (`truncated2_antitoneOn_h_of_ne`) from finite to infinite volume
via the exhaustion limit.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.4; Friedli–Velenik §3.6.3. -/

/-- **Truncated 2-point along an exhaustion** (local helper): the stage-`n`
finite-volume approximation to `truncated2Infinite`.  Parallel to
`truncated3AlongExhaustion`; bridges the finite-volume
`truncated2_antitoneOn_h_of_ne` (Step 124) with the infinite-volume limit. -/
private noncomputable def truncated2AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j : V) (n : ℕ) : ℝ :=
  correlationAlongExhaustion G Λ p {i, j} n
    - correlationAlongExhaustion G Λ p {i} n
      * correlationAlongExhaustion G Λ p {j} n

/-- **Tendsto for the truncated 2-point sequence**: `truncated2AlongExhaustion`
converges to `truncated2Infinite`.  Apply `Tendsto.sub` and `Tendsto.mul` to
the three convergences from
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
private theorem tendsto_truncated2AlongExhaustion_truncated2Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    Filter.Tendsto
      (truncated2AlongExhaustion G Λ p i j)
      Filter.atTop
      (nhds (truncated2Infinite G Λ p i j)) := by
  unfold truncated2AlongExhaustion truncated2Infinite
  have h_ij := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i, j}
  have h_i := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i}
  have h_j := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j}
  exact h_ij.sub (h_i.mul h_j)

/-- **GHS consequence at infinite volume**: for ferromagnetic Ising and distinct
sites `i ≠ j`, the function `h ↦ truncated2Infinite G Λ ⟨J, h, β⟩ i j` is
antitone on `[0, ∞)`.

Proof: at each stage `n` with `{i, j} ⊆ Λ.volume n`, Step 124
(`truncated2_antitoneOn_h_of_ne`) gives the finite-volume antitone bound.
Pass to the limit via `le_of_tendsto_of_tendsto`.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.4; Friedli–Velenik §3.6.3. -/
theorem truncated2Infinite_antitoneOn_h_of_ne
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) {i j : V} (hij : i ≠ j) :
    AntitoneOn (fun h => truncated2Infinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i j) (Set.Ici 0) := by
  intro h₁ hh₁ h₂ hh₂ hle
  refine le_of_tendsto_of_tendsto
    (tendsto_truncated2AlongExhaustion_truncated2Infinite G Λ ⟨J, h₂, β⟩
      ⟨hJ, Set.mem_Ici.mp hh₂, hβ⟩ i j)
    (tendsto_truncated2AlongExhaustion_truncated2Infinite G Λ ⟨J, h₁, β⟩
      ⟨hJ, Set.mem_Ici.mp hh₁, hβ⟩ i j)
    ?_
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j} : Finset V)
  unfold Filter.EventuallyLE
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hab : ({i, j} : Finset V) ⊆ Λ.volume n := hN n hn
  have ha : ({i} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx; exact hab (by simp)
  have hb : ({j} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx; exact hab (by simp)
  change truncated2AlongExhaustion G Λ ⟨J, h₂, β⟩ i j n ≤
    truncated2AlongExhaustion G Λ ⟨J, h₁, β⟩ i j n
  unfold truncated2AlongExhaustion
  rw [correlationAlongExhaustion_of_subset G Λ ⟨J, h₂, β⟩ hab,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₂, β⟩ ha,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₂, β⟩ hb,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₁, β⟩ hab,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₁, β⟩ ha,
      correlationAlongExhaustion_of_subset G Λ ⟨J, h₁, β⟩ hb]
  have hlift_ij : liftFinset ({i, j} : Finset V) hab
      = ({⟨i, ha (by simp)⟩, ⟨j, hb (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (by rfl)
    · rintro (rfl | rfl) <;> simp
  have hlift_i : liftFinset ({i} : Finset V) ha
      = ({⟨i, ha (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_j : liftFinset ({j} : Finset V) hb
      = ({⟨j, hb (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  simp only [correlationΛ, hlift_ij, hlift_i, hlift_j]
  have hij' : (⟨i, ha (by simp)⟩ : ↑(Λ.volume n)) ≠ ⟨j, hb (by simp)⟩ :=
    fun h => hij (Subtype.mk.inj h)
  have hanti := IsingModel.truncated2_antitoneOn_h_of_ne
    (inducedGraph G (Λ.volume n)) J hJ β hβ hij' hh₁ hh₂ hle
  unfold IsingModel.truncated2 at hanti
  linarith

/-! ## Truncated 3-point correlation + GHS at infinite volume

Lift the finite-volume GHS inequality (`ghs_inequality`,
`Inequalities/GHS.lean`) to the thermodynamic limit.
For ferromagnetic Ising and pairwise distinct sites,
$U_3(i, j, k) \le 0$ at infinite volume.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.4, pp. 68ff;
Friedli–Velenik §3.6.4. -/

/-- **Truncated 3-point correlation at infinite volume**:
the thermodynamic-limit analog of `IsingModel.truncated3`:
$U_3 := \langle \sigma^{\{i,j,k\}} \rangle_\infty
  - \langle \sigma^{\{i\}} \rangle_\infty \langle \sigma^{\{j,k\}} \rangle_\infty
  - \langle \sigma^{\{j\}} \rangle_\infty \langle \sigma^{\{i,k\}} \rangle_\infty
  - \langle \sigma^{\{k\}} \rangle_\infty \langle \sigma^{\{i,j\}} \rangle_\infty
  + 2 \langle \sigma^{\{i\}} \rangle_\infty \langle \sigma^{\{j\}} \rangle_\infty
    \langle \sigma^{\{k\}} \rangle_\infty$. -/
noncomputable def truncated3Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) : ℝ :=
  correlationInfinite G Λ p {i, j, k}
    - correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j, k}
    - correlationInfinite G Λ p {j} * correlationInfinite G Λ p {i, k}
    - correlationInfinite G Λ p {k} * correlationInfinite G Λ p {i, j}
    + 2 * correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j}
      * correlationInfinite G Λ p {k}

/-- **Unfolding of `truncated3Infinite`**: the defining Ursell 3-point
formula as a named identity. -/
theorem truncated3Infinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) :
    truncated3Infinite G Λ p i j k
      = correlationInfinite G Λ p {i, j, k}
        - correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j, k}
        - correlationInfinite G Λ p {j} * correlationInfinite G Λ p {i, k}
        - correlationInfinite G Λ p {k} * correlationInfinite G Λ p {i, j}
        + 2 * correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j}
          * correlationInfinite G Λ p {k} := rfl

/-- **`truncated3Infinite` symmetry under swapping `i, j`**. The defining
formula is symmetric in the three site arguments, using that Finsets are
unordered. -/
theorem truncated3Infinite_swap_ij
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ p j i k := by
  unfold truncated3Infinite
  have h1 : ({i, j, k} : Finset V) = {j, i, k} := by
    rw [Finset.insert_comm]
  have h2 : ({i, j} : Finset V) = {j, i} := Finset.pair_comm i j
  rw [h1, h2]
  ring

/-- **`truncated3Infinite` symmetry under swapping `j, k`**. -/
theorem truncated3Infinite_swap_jk
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ p i k j := by
  unfold truncated3Infinite
  have h1 : ({i, j, k} : Finset V) = {i, k, j} := by
    congr 1
    exact Finset.pair_comm j k
  have h2 : ({j, k} : Finset V) = {k, j} := Finset.pair_comm j k
  rw [h1, h2]
  ring

/-- **`truncated3Infinite` symmetry under swapping `i, k`**: obtained by
chaining the `ij` and `jk` swaps. -/
theorem truncated3Infinite_swap_ik
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ p k j i := by
  rw [truncated3Infinite_swap_ij G Λ p i j k,
      truncated3Infinite_swap_jk G Λ p j i k,
      truncated3Infinite_swap_ij G Λ p j k i]

/-- **Truncated 3-point along an exhaustion** (local helper): evaluates
the `truncated3`-style algebraic expression at the `n`-th volume of
the exhaustion, using `correlationAlongExhaustion` instead of the
limit `correlationInfinite`.  Bridges the finite-volume
`ghs_inequality` and the infinite-volume `truncated3Infinite_nonpos`
via `le_of_tendsto`. -/
private noncomputable def truncated3AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) (n : ℕ) : ℝ :=
  correlationAlongExhaustion G Λ p {i, j, k} n
    - correlationAlongExhaustion G Λ p {i} n
      * correlationAlongExhaustion G Λ p {j, k} n
    - correlationAlongExhaustion G Λ p {j} n
      * correlationAlongExhaustion G Λ p {i, k} n
    - correlationAlongExhaustion G Λ p {k} n
      * correlationAlongExhaustion G Λ p {i, j} n
    + 2 * correlationAlongExhaustion G Λ p {i} n
      * correlationAlongExhaustion G Λ p {j} n
      * correlationAlongExhaustion G Λ p {k} n

/-- **Tendsto for the truncated 3-point sequence**: the pointwise
`truncated3AlongExhaustion` converges to `truncated3Infinite`.

Key technical step establishing that the thermodynamic limit of
the finite-volume truncated 3-point correlation exists and equals
the infinite-volume definition.  Proof: apply `Tendsto.sub`,
`Tendsto.add`, and `Tendsto.mul` to the seven `correlationInfinite`
convergences from
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
private theorem tendsto_truncated3AlongExhaustion_truncated3Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : V) :
    Filter.Tendsto
      (truncated3AlongExhaustion G Λ p i j k)
      Filter.atTop
      (nhds (truncated3Infinite G Λ p i j k)) := by
  unfold truncated3AlongExhaustion truncated3Infinite
  have h_ijk := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,j,k}
  have h_jk := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j,k}
  have h_ik := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,k}
  have h_ij := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,j}
  have h_i := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i}
  have h_j := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j}
  have h_k := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {k}
  exact ((((h_ijk.sub (h_i.mul h_jk)).sub (h_j.mul h_ik)).sub
    (h_k.mul h_ij)).add
    (((tendsto_const_nhds (x := (2 : ℝ))).mul h_i).mul h_j |>.mul h_k))

/-- **GHS at infinite volume**: for a ferromagnetic Ising model and
pairwise distinct sites `i, j, k`, $U_3(i, j, k) \le 0$.

Proof: at each `n` with `{i, j, k} ⊆ Λ.volume n`, the finite-volume
`ghs_inequality` gives `truncated3AlongExhaustion n ≤ 0` after
identifying the along-exhaustion sequence with the lifted
finite-volume `truncated3`.  Pass to the limit using
`tendsto_truncated3AlongExhaustion_truncated3Infinite` and
`le_of_tendsto`. -/
theorem truncated3Infinite_nonpos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite G Λ p i j k ≤ 0 := by
  refine le_of_tendsto
    (tendsto_truncated3AlongExhaustion_truncated3Infinite G Λ p hf i j k) ?_
  -- Eventually at atTop: truncated3AlongExhaustion n ≤ 0
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j, k} : Finset V)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have habc : ({i, j, k} : Finset V) ⊆ Λ.volume n := hN n hn
  have ha : ({i} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx
    exact habc (by simp)
  have hb : ({j} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx
    exact habc (by simp)
  have hc : ({k} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx
    exact habc (by simp)
  have hab : ({i, j} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact habc (by simp)
    · exact habc (by simp)
  have hac : ({i, k} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact habc (by simp)
    · exact habc (by simp)
  have hbc : ({j, k} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact habc (by simp)
    · exact habc (by simp)
  -- Rewrite truncated3AlongExhaustion using correlationAlongExhaustion_of_subset
  change truncated3AlongExhaustion G Λ p i j k n ≤ 0
  unfold truncated3AlongExhaustion
  rw [correlationAlongExhaustion_of_subset G Λ p habc,
      correlationAlongExhaustion_of_subset G Λ p ha,
      correlationAlongExhaustion_of_subset G Λ p hb,
      correlationAlongExhaustion_of_subset G Λ p hc,
      correlationAlongExhaustion_of_subset G Λ p hab,
      correlationAlongExhaustion_of_subset G Λ p hac,
      correlationAlongExhaustion_of_subset G Λ p hbc]
  -- Convert to finite-volume ghs_inequality on inducedGraph
  -- Build the lifted indices via subtype coercion
  have := IsingModel.ghs_inequality (inducedGraph G (Λ.volume n)) p hf
    ⟨i, ha (by simp)⟩ ⟨j, hb (by simp)⟩ ⟨k, hc (by simp)⟩
    (by intro h; apply hij; exact Subtype.mk.inj h)
    (by intro h; apply hjk; exact Subtype.mk.inj h)
    (by intro h; apply hik; exact Subtype.mk.inj h)
  unfold IsingModel.truncated3 at this
  -- Show liftFinset {...} equals { ⟨·, ...⟩, ... }
  -- Instead, rewrite the goal to match ghs_inequality
  -- The finite-volume ghs_inequality uses {i', j', k'} : Finset ↑(Λ.volume n)
  -- where i' = ⟨i, _⟩ etc. This coincides with liftFinset {i,j,k} etc.
  have hlift_ijk : liftFinset ({i, j, k} : Finset V) habc
      = ({⟨i, ha (by simp)⟩, ⟨j, hb (by simp)⟩, ⟨k, hc (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (Or.inl (by rfl))
      · exact Or.inr (Or.inr (by rfl))
    · rintro (rfl | rfl | rfl) <;> simp
  have hlift_i : liftFinset ({i} : Finset V) ha
      = ({⟨i, ha (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_j : liftFinset ({j} : Finset V) hb
      = ({⟨j, hb (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_k : liftFinset ({k} : Finset V) hc
      = ({⟨k, hc (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_ij : liftFinset ({i, j} : Finset V) hab
      = ({⟨i, ha (by simp)⟩, ⟨j, hb (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (by rfl)
    · rintro (rfl | rfl) <;> simp
  have hlift_ik : liftFinset ({i, k} : Finset V) hac
      = ({⟨i, ha (by simp)⟩, ⟨k, hc (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (by rfl)
    · rintro (rfl | rfl) <;> simp
  have hlift_jk : liftFinset ({j, k} : Finset V) hbc
      = ({⟨j, hb (by simp)⟩, ⟨k, hc (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (by rfl)
    · rintro (rfl | rfl) <;> simp
  simp only [correlationΛ, hlift_ijk, hlift_i, hlift_j, hlift_k,
    hlift_ij, hlift_ik, hlift_jk]
  linarith [this]

/-- **`truncated3Infinite` at `h = 0`**: for pairwise distinct sites,
$U_3 = 0$ at vanishing external field.

All singletons $\{i\}, \{j\}, \{k\}$ have odd cardinality, so their
`correlationInfinite` at $h = 0$ vanishes (`correlationInfinite_h_zero`),
making the three product terms and the triple product vanish.  With
distinct sites, $\{i, j, k\}$ also has odd cardinality (= 3), so the
first term vanishes too.  All five terms are zero. -/
theorem truncated3Infinite_h_zero_of_distinct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite G Λ ⟨J, 0, β⟩ i j k = 0 := by
  unfold truncated3Infinite
  have h_ijk : Odd ({i, j, k} : Finset V).card := by
    rw [show ({i, j, k} : Finset V).card = 3 from ?_]
    · exact ⟨1, by norm_num⟩
    · rw [Finset.card_insert_of_notMem (by
        simp [Finset.mem_insert, Finset.mem_singleton, hij, hik])]
      rw [Finset.card_insert_of_notMem (by
        simp [Finset.mem_singleton, hjk])]
      simp
  have h_i : Odd ({i} : Finset V).card := by simp
  have h_j : Odd ({j} : Finset V).card := by simp
  have h_k : Odd ({k} : Finset V).card := by simp
  rw [correlationInfinite_h_zero G Λ J β _ h_ijk,
      correlationInfinite_h_zero G Λ J β _ h_i,
      correlationInfinite_h_zero G Λ J β _ h_j,
      correlationInfinite_h_zero G Λ J β _ h_k]
  ring

/-- **∞-volume Ursell 3-point at `h = 0` pair coincidence**:
for `i ≠ k`,
`truncated3Infinite ⟨J,0,β⟩ i i k = correlationInfinite ⟨J,0,β⟩ {i,k}`.

Extension of `truncated3Infinite_h_zero_of_distinct` (three distinct
→ 0) to the two-coincident case. Z₂ symmetry at `h = 0` kills all
odd-cardinality correlations via `correlationInfinite_h_zero`; the
Ursell 3-point retains only the `{i,i,k} = {i,k}` even-cardinality
term (card 2), so the 3-point reduces to the 2-point.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated3Infinite_h_zero_of_pair_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) {i k : V} (_hik : i ≠ k) :
    truncated3Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i i k
      = correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, k} := by
  unfold truncated3Infinite
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiik : ({i, i, k} : Finset V) = {i, k} := by ext x; simp
  have h_i_odd : Odd ({i} : Finset V).card := by simp
  have h_k_odd : Odd ({k} : Finset V).card := by simp
  rw [hii, hiik,
      correlationInfinite_h_zero G Λ J β {i} h_i_odd,
      correlationInfinite_h_zero G Λ J β {k} h_k_odd]
  ring

/-- **∞-volume Ursell 3-point at `h = 0` all-coincident vanishes**:
`truncated3Infinite ⟨J,0,β⟩ i i i = 0`. All Finsets in the Ursell
formula collapse to `{i}` (card 1, odd), so Z₂ symmetry forces
every term to vanish.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated3Infinite_h_zero_all_coincident
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    truncated3Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i i i = 0 := by
  unfold truncated3Infinite
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiii : ({i, i, i} : Finset V) = {i} := by ext x; simp
  have h_i_odd : Odd ({i} : Finset V).card := by simp
  rw [hiii, hii, correlationInfinite_h_zero G Λ J β {i} h_i_odd]
  ring

/-- **Exhaustion-independence of `truncated3Infinite`**: the value
does not depend on the choice of exhaustion. -/
theorem truncated3Infinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ' p i j k := by
  unfold truncated3Infinite
  rw [correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, k}]

/-- **∞-volume Ursell 3-point vanishes at `J = 0`** (ferromagnetic,
pairwise distinct sites): infinite-volume counterpart of
`truncated3_J_zero_of_pairwise_distinct` (finite volume, PR #209).

For pairwise distinct `i, j, k` and `⟨0, h, β⟩` ferromagnetic,
`correlationInfinite G Λ ⟨0, h, β⟩ A = tanh(β·h)^|A|` gives
cardinalities `3, 1+2, 1+2, 1+2, 1+1+1`, and the Ursell
combination becomes `t³ - 3·t³ + 2·t³ = 0` where `t = tanh(β·h)`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.1 / §4.3. -/
theorem truncated3Infinite_J_zero_of_pairwise_distinct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i j k = 0 := by
  unfold truncated3Infinite
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_i : ({i} : Finset V).card = 1 := Finset.card_singleton i
  have hcard_j : ({j} : Finset V).card = 1 := Finset.card_singleton j
  have hcard_k : ({k} : Finset V).card = 1 := Finset.card_singleton k
  have hcard_ij : ({i, j} : Finset V).card = 2 := Finset.card_pair hij
  have hcard_jk : ({j, k} : Finset V).card = 2 := Finset.card_pair hjk
  have hcard_ik : ({i, k} : Finset V).card = 2 := Finset.card_pair hik
  have hi_nin_jk : i ∉ ({j, k} : Finset V) := by simp [hij, hik]
  have hcard_ijk : ({i, j, k} : Finset V).card = 3 := by
    rw [show ({i, j, k} : Finset V) = insert i ({j, k} : Finset V) from rfl,
        Finset.card_insert_of_notMem hi_nin_jk, hcard_jk]
  rw [hcard_i, hcard_j, hcard_k, hcard_ij, hcard_jk, hcard_ik, hcard_ijk]
  ring

/-- **∞-volume Ursell 3-point vanishes at `J = 0` with pair coincidence**
(ferromagnetic): if `i = j` and `i ≠ k`, then
`truncated3Infinite ⟨0,h,β⟩ i i k = 0`. Extension of
`truncated3Infinite_J_zero_of_pairwise_distinct` (all three distinct)
to the two-coincident case.

Proof: with `t := tanh(β·h)`, using Finset collapses `{i,i,k} = {i,k}`
(card 2) and `{i,i} = {i}` (card 1):
`U_3(i,i,k) = t² − t·t² − t·t² − t·t + 2·t·t·t = t² − 2t³ − t² + 2t³ = 0`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated3Infinite_J_zero_of_pair_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : V} (hik : i ≠ k) :
    truncated3Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i k = 0 := by
  unfold truncated3Infinite
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiik : ({i, i, k} : Finset V) = {i, k} := by
    ext x; simp
  rw [hii, hiik]
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_i : ({i} : Finset V).card = 1 := Finset.card_singleton i
  have hcard_k : ({k} : Finset V).card = 1 := Finset.card_singleton k
  have hcard_ik : ({i, k} : Finset V).card = 2 := Finset.card_pair hik
  rw [hcard_i, hcard_k, hcard_ik]
  ring

/-- **∞-volume Ursell 3-point at `J = 0` all-coincident closed form**
(ferromagnetic): `truncated3Infinite ⟨0,h,β⟩ i i i = t·(1−t)·(1−2t)`
with `t := tanh(β·h)`.

Completes the J=0 trivial-slice cascade: all-distinct vanishes
(`truncated3Infinite_J_zero_of_pairwise_distinct`), pair-coincident
vanishes (`truncated3Infinite_J_zero_of_pair_coincidence`), and
all-coincident is the cubic polynomial `t − 3t² + 2t³`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated3Infinite_J_zero_all_coincident
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : V) :
    truncated3Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h))
          * (1 - 2 * Real.tanh (β * h)) := by
  unfold truncated3Infinite
  have h1 : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiii : ({i, i, i} : Finset V) = {i} := by ext x; simp
  rw [hiii, hii, h1]
  ring

/-- **∞-volume Ursell 3-point vanishes at `β = 0`** for any sites.

Infinite-volume counterpart of `truncated3_beta_zero` (finite
volume, PR #209). Every correlation in the Ursell combination is
over a nonempty Finset, so
`correlationInfinite_beta_zero_vanish` makes each
term zero — the linear combination vanishes trivially. No
distinctness hypotheses are needed at `β = 0`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.1 infinite-temperature slice. -/
theorem truncated3Infinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i j k : V) :
    truncated3Infinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i j k = 0 := by
  unfold truncated3Infinite
  rw [correlationInfinite_beta_zero_vanish G Λ J h
        {i, j, k} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i} (Finset.singleton_nonempty i),
      correlationInfinite_beta_zero_vanish G Λ J h
        {j} (Finset.singleton_nonempty j),
      correlationInfinite_beta_zero_vanish G Λ J h
        {k} (Finset.singleton_nonempty k),
      correlationInfinite_beta_zero_vanish G Λ J h
        {j, k} ⟨j, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, k} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, j} ⟨i, by simp⟩]
  ring

/-! ## Truncated 4-point correlation + `U_4 ≤ 0` at `h = 0`

Lift `IsingModel.cor_4_3_3` (finite-volume `U_4 ≤ 0` at $h = 0$) to
the thermodynamic limit. For ferromagnetic Ising at $h = 0$ and
four pairwise-distinct sites:
$U_4(i, j, k, l) := \langle \sigma^{\{i,j,k,l\}} \rangle_\infty
  - \sum_\text{pairings} \langle \sigma^{\{·,·\}} \rangle_\infty
    \langle \sigma^{\{·,·\}} \rangle_\infty \le 0$.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.3, pp. 68ff;
Friedli–Velenik §3.6.4. -/

/-- **Truncated 4-point correlation at infinite volume**:
the thermodynamic-limit analog of `IsingModel.truncated4`. -/
noncomputable def truncated4Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) : ℝ :=
  correlationInfinite G Λ p {i, j, k, l}
    - correlationInfinite G Λ p {i, j} * correlationInfinite G Λ p {k, l}
    - correlationInfinite G Λ p {i, k} * correlationInfinite G Λ p {j, l}
    - correlationInfinite G Λ p {i, l} * correlationInfinite G Λ p {j, k}

/-- **Unfolding of `truncated4Infinite`**: the defining pair-split
Ursell 4-point formula as a named identity. -/
theorem truncated4Infinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) :
    truncated4Infinite G Λ p i j k l
      = correlationInfinite G Λ p {i, j, k, l}
        - correlationInfinite G Λ p {i, j} * correlationInfinite G Λ p {k, l}
        - correlationInfinite G Λ p {i, k} * correlationInfinite G Λ p {j, l}
        - correlationInfinite G Λ p {i, l} * correlationInfinite G Λ p {j, k} := rfl

/-- **`truncated4Infinite` symmetry under swapping `i, j`**: adjacent
swap. The pair-split formula is fully symmetric in the four arguments. -/
theorem truncated4Infinite_swap_ij
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ p j i k l := by
  unfold truncated4Infinite
  have h1 : ({i, j, k, l} : Finset V) = {j, i, k, l} := by rw [Finset.insert_comm]
  have h2 : ({i, j} : Finset V) = {j, i} := Finset.pair_comm i j
  rw [h1, h2]
  ring

/-- **`truncated4Infinite` symmetry under swapping `k, l`**: adjacent swap. -/
theorem truncated4Infinite_swap_kl
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ p i j l k := by
  unfold truncated4Infinite
  have h1 : ({i, j, k, l} : Finset V) = {i, j, l, k} := by
    congr 1; congr 1
    exact Finset.pair_comm k l
  have h2 : ({k, l} : Finset V) = {l, k} := Finset.pair_comm k l
  rw [h1, h2]
  ring

/-- **`truncated4Infinite` symmetry under swapping `j, k`**: adjacent swap. -/
theorem truncated4Infinite_swap_jk
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ p i k j l := by
  unfold truncated4Infinite
  have h1 : ({i, j, k, l} : Finset V) = {i, k, j, l} := by
    congr 1
    rw [Finset.insert_comm]
  have h2 : ({j, k} : Finset V) = {k, j} := Finset.pair_comm j k
  rw [h1, h2]
  ring

/-- **Truncated 4-point along an exhaustion** (local helper): evaluates
the `truncated4`-style algebraic expression at the `n`-th volume of
the exhaustion, using `correlationAlongExhaustion` instead of the
limit `correlationInfinite`.  This is the pointwise sequence whose
limit as `n → ∞` is `truncated4Infinite`; established separately so
that the `le_of_tendsto`-based `_nonpos_h_zero` proof can apply the
finite-volume `cor_4_3_3` to each term of the sequence. -/
private noncomputable def truncated4AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) (n : ℕ) : ℝ :=
  correlationAlongExhaustion G Λ p {i, j, k, l} n
    - correlationAlongExhaustion G Λ p {i, j} n
      * correlationAlongExhaustion G Λ p {k, l} n
    - correlationAlongExhaustion G Λ p {i, k} n
      * correlationAlongExhaustion G Λ p {j, l} n
    - correlationAlongExhaustion G Λ p {i, l} n
      * correlationAlongExhaustion G Λ p {j, k} n

/-- **Tendsto for the truncated 4-point sequence**: the pointwise
`truncated4AlongExhaustion` converges to `truncated4Infinite`.

This is the key technical step establishing that the thermodynamic
limit of the finite-volume truncated 4-point correlation exists and
equals the infinite-volume definition.  Proof: apply `Tendsto.sub`
and `Tendsto.mul` to the 7 `correlationInfinite` convergences from
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
private theorem tendsto_truncated4AlongExhaustion_truncated4Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : V) :
    Filter.Tendsto
      (truncated4AlongExhaustion G Λ p i j k l)
      Filter.atTop
      (nhds (truncated4Infinite G Λ p i j k l)) := by
  unfold truncated4AlongExhaustion truncated4Infinite
  have h_ijkl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,j,k,l}
  have h_ij := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,j}
  have h_kl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {k,l}
  have h_ik := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,k}
  have h_jl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {j,l}
  have h_il := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,l}
  have h_jk := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {j,k}
  exact ((h_ijkl.sub (h_ij.mul h_kl)).sub (h_ik.mul h_jl)).sub
    (h_il.mul h_jk)

/-- **`U_4 ≤ 0` at `h = 0`** at infinite volume: for a ferromagnetic
Ising model at vanishing external field and four pairwise-distinct
sites, $U_4 \le 0$.

Proof: at each `n` with `{i, j, k, l} ⊆ Λ.volume n`, the
finite-volume `cor_4_3_3` gives `truncated4AlongExhaustion n ≤ 0`
after identifying `liftFinset` patterns with the required subtype
Finsets.  Pass to the limit using
`tendsto_truncated4AlongExhaustion_truncated4Infinite` and
`le_of_tendsto`. -/
theorem truncated4Infinite_nonpos_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 := by
  refine le_of_tendsto
    (tendsto_truncated4AlongExhaustion_truncated4Infinite G Λ _ hf i j k l) ?_
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j, k, l} : Finset V)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have habcd : ({i, j, k, l} : Finset V) ⊆ Λ.volume n := hN n hn
  -- Site memberships
  have mem_i : i ∈ Λ.volume n := habcd (by simp)
  have mem_j : j ∈ Λ.volume n := habcd (by simp)
  have mem_k : k ∈ Λ.volume n := habcd (by simp)
  have mem_l : l ∈ Λ.volume n := habcd (by simp)
  -- Pair subsets via a reusable helper
  have pair_sub : ∀ {a b : V}, a ∈ Λ.volume n → b ∈ Λ.volume n →
      ({a, b} : Finset V) ⊆ Λ.volume n := by
    intro a b ha hb x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hab : ({i, j} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_j
  have hcd : ({k, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_k mem_l
  have hac : ({i, k} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_k
  have hbd : ({j, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_j mem_l
  have had : ({i, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_l
  have hbc : ({j, k} : Finset V) ⊆ Λ.volume n := pair_sub mem_j mem_k
  change truncated4AlongExhaustion G Λ ⟨J, 0, β⟩ i j k l n ≤ 0
  unfold truncated4AlongExhaustion
  rw [correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ habcd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hab,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hcd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hac,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hbd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ had,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hbc]
  -- Apply finite-volume cor_4_3_3
  have hfin := IsingModel.cor_4_3_3 (inducedGraph G (Λ.volume n)) J β hf
    ⟨i, mem_i⟩ ⟨j, mem_j⟩ ⟨k, mem_k⟩ ⟨l, mem_l⟩
    (by intro h; apply hij; exact Subtype.mk.inj h)
    (by intro h; apply hik; exact Subtype.mk.inj h)
    (by intro h; apply hil; exact Subtype.mk.inj h)
    (by intro h; apply hjk; exact Subtype.mk.inj h)
    (by intro h; apply hjl; exact Subtype.mk.inj h)
    (by intro h; apply hkl; exact Subtype.mk.inj h)
  unfold IsingModel.truncated4 at hfin
  -- Identify liftFinset patterns
  have hlift_ijkl : liftFinset ({i, j, k, l} : Finset V) habcd
      = ({⟨i, mem_i⟩, ⟨j, mem_j⟩, ⟨k, mem_k⟩, ⟨l, mem_l⟩} :
          Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl) <;> simp
  have hlift_ij : liftFinset ({i, j} : Finset V) hab
      = ({⟨i, mem_i⟩, ⟨j, mem_j⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_kl : liftFinset ({k, l} : Finset V) hcd
      = ({⟨k, mem_k⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_ik : liftFinset ({i, k} : Finset V) hac
      = ({⟨i, mem_i⟩, ⟨k, mem_k⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_jl : liftFinset ({j, l} : Finset V) hbd
      = ({⟨j, mem_j⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_il : liftFinset ({i, l} : Finset V) had
      = ({⟨i, mem_i⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_jk : liftFinset ({j, k} : Finset V) hbc
      = ({⟨j, mem_j⟩, ⟨k, mem_k⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  simp only [correlationΛ, hlift_ijkl, hlift_ij, hlift_kl, hlift_ik,
    hlift_jl, hlift_il, hlift_jk]
  linarith [hfin]

/-- **GJ §17.3 key inequality (17.3.1) — lower bound on truncated 4-point function**
(Glimm–Jaffe §17.3 p. 308 eq. (17.3.1), 2nd ed.):
for a ferromagnetic Ising model at `h = 0` and pairwise distinct sites `i, j, k, l`,
`-(⟨σᵢσₖ⟩·⟨σⱼσₗ⟩ + ⟨σᵢσₗ⟩·⟨σⱼσₖ⟩) ≤ U₄^∞(i,j,k,l)`.

Combined with `truncated4Infinite_nonpos_h_zero` (upper bound `≤ 0`), this gives
the two-sided bound `0 ≤ -U₄^∞(i,j,k,l) ≤ ⟨σᵢσₖ⟩·⟨σⱼσₗ⟩ + ⟨σᵢσₗ⟩·⟨σⱼσₖ⟩`.

Proof: unfold `truncated4Infinite`; GKS-II (`correlationInfinite_gks_second`) gives
`⟨σᵢσⱼ⟩·⟨σₖσₗ⟩ ≤ ⟨σᵢσⱼσₖσₗ⟩` via `{i,j} △ {k,l} = {i,j,k,l}` (disjoint union);
subtract `⟨σᵢσₖ⟩·⟨σⱼσₗ⟩ + ⟨σᵢσₗ⟩·⟨σⱼσₖ⟩` from both sides. -/
theorem truncated4Infinite_ge_neg_pair_correlations
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    -(correlationInfinite G Λ ⟨J, 0, β⟩ {i, k} *
        correlationInfinite G Λ ⟨J, 0, β⟩ {j, l} +
      correlationInfinite G Λ ⟨J, 0, β⟩ {i, l} *
        correlationInfinite G Λ ⟨J, 0, β⟩ {j, k})
    ≤ truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l := by
  rw [truncated4Infinite_apply]
  -- GKS-II: corr{i,j} * corr{k,l} ≤ corr{i,j,k,l}
  have hdisj : Disjoint ({i, j} : Finset V) {k, l} := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl
    · exact hik rfl
    · exact hil rfl
    · exact hjk rfl
    · exact hjl rfl
  have h_sdiff : ({i, j} : Finset V) ∆ {k, l} = {i, j, k, l} := by
    rw [hdisj.symmDiff_eq_sup, Finset.sup_eq_union]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h_gks : correlationInfinite G Λ ⟨J, 0, β⟩ {i, j} *
      correlationInfinite G Λ ⟨J, 0, β⟩ {k, l}
      ≤ correlationInfinite G Λ ⟨J, 0, β⟩ {i, j, k, l} := by
    rw [← h_sdiff]
    exact correlationInfinite_gks_second G Λ ⟨J, 0, β⟩ hf {i, j} {k, l}
  linarith

/-- **Exhaustion-independence of `truncated4Infinite`**. -/
theorem truncated4Infinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ' p i j k l := by
  unfold truncated4Infinite
  rw [correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j, k, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {k, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, k}]

/-- **∞-volume Lebowitz 4-point vanishes at `β = 0`** for any sites
`i, j, k, l : V`. Infinite-volume counterpart of
`truncated4_beta_zero` (finite volume, PR #214 in
`Inequalities/GHS.lean`).

Each of the seven Finset correlations in the Lebowitz combination
is over a nonempty Finset (every subset contains at least one of
the supplied sites), so
`correlationInfinite_beta_zero_vanish` makes every
term zero and the linear combination vanishes.

Unlike the `β = 0` case, `truncated4Infinite` at `J = 0` is
`-2·t⁴` (with `t = tanh(β·h)`) for pairwise distinct sites, which
is non-zero when `β·h ≠ 0`. So only the `β = 0` slice is added
here.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.3 Cor. 4.3.3. -/
theorem truncated4Infinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i j k l : V) :
    truncated4Infinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 := by
  unfold truncated4Infinite
  rw [correlationInfinite_beta_zero_vanish G Λ J h
        {i, j, k, l} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, j} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {k, l} ⟨k, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, k} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {j, l} ⟨j, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, l} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {j, k} ⟨j, by simp⟩]
  ring

/-- **∞-volume Lebowitz 4-point closed form at `J = 0`** for
ferromagnetic `⟨0, h, β⟩` and pairwise distinct sites:
`truncated4Infinite G Λ ⟨0, h, β⟩ i j k l = -2 · tanh(β·h)^4`.

Infinite-volume counterpart of
`truncated4_J_zero_of_pairwise_distinct` (finite volume, PR #215
in `Inequalities/GHS.lean`). Uses the ∞-vol closed form
`correlationInfinite_J_zero` at the four Finsets of card 4 and
six Finsets of card 2.

Complements `truncated4Infinite_beta_zero` (vanishing slice at
`β = 0`): this is the J=0 slice with explicit closed form `-2·t⁴`
(non-vanishing). Note `-2·t⁴ ≤ 0` always, consistent with
`truncated4Infinite_nonpos_h_zero`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster context); §4.3 Cor. 4.3.3 / Lebowitz. -/
theorem truncated4Infinite_J_zero_of_pairwise_distinct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 := by
  unfold truncated4Infinite
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_ijkl : ({i, j, k, l} : Finset V).card = 4 := by
    have h_jkl_card : ({j, k, l} : Finset V).card = 3 := by
      rw [show ({j, k, l} : Finset V) = insert j ({k, l} : Finset V) from rfl,
          Finset.card_insert_of_notMem (by simp [hjk, hjl]),
          Finset.card_pair hkl]
    have h_i_nin : i ∉ ({j, k, l} : Finset V) := by
      simp [hij, hik, hil]
    rw [show ({i, j, k, l} : Finset V) = insert i ({j, k, l} : Finset V)
            from rfl,
        Finset.card_insert_of_notMem h_i_nin, h_jkl_card]
  have hcard_ij : ({i, j} : Finset V).card = 2 := Finset.card_pair hij
  have hcard_ik : ({i, k} : Finset V).card = 2 := Finset.card_pair hik
  have hcard_il : ({i, l} : Finset V).card = 2 := Finset.card_pair hil
  have hcard_jk : ({j, k} : Finset V).card = 2 := Finset.card_pair hjk
  have hcard_jl : ({j, l} : Finset V).card = 2 := Finset.card_pair hjl
  have hcard_kl : ({k, l} : Finset V).card = 2 := Finset.card_pair hkl
  rw [hcard_ijkl, hcard_ij, hcard_kl, hcard_ik, hcard_jl, hcard_il, hcard_jk]
  ring

/-- **∞-volume Lebowitz 4-point at `J = 0` one-pair coincidence**
(ferromagnetic): if `i ≠ k`, `i ≠ l`, `k ≠ l`, then
`truncated4Infinite ⟨0,h,β⟩ i i k l = -2 · tanh(β·h)⁴`.

Same closed form as the pairwise-distinct case
(`truncated4Infinite_J_zero_of_pairwise_distinct`). Proof uses the
Finset collapses `{i,i,k,l} = {i,k,l}` (card 3) and `{i,i} = {i}`
(card 1); the three pair-pair products reduce to
`t³ + t⁴ + t⁴` giving `U_4 = t³ − t³ − 2t⁴ = −2t⁴`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated4Infinite_J_zero_of_one_pair_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k l : V} (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i k l
      = -2 * Real.tanh (β * h) ^ 4 := by
  unfold truncated4Infinite
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiikl : ({i, i, k, l} : Finset V) = {i, k, l} := by ext x; simp
  rw [hiikl, hii]
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_i : ({i} : Finset V).card = 1 := Finset.card_singleton i
  have hcard_ik : ({i, k} : Finset V).card = 2 := Finset.card_pair hik
  have hcard_il : ({i, l} : Finset V).card = 2 := Finset.card_pair hil
  have hcard_kl : ({k, l} : Finset V).card = 2 := Finset.card_pair hkl
  have hcard_ikl : ({i, k, l} : Finset V).card = 3 := by
    have h_i_nin : i ∉ ({k, l} : Finset V) := by simp [hik, hil]
    rw [show ({i, k, l} : Finset V) = insert i ({k, l} : Finset V) from rfl,
        Finset.card_insert_of_notMem h_i_nin, hcard_kl]
  rw [hcard_i, hcard_ik, hcard_il, hcard_kl, hcard_ikl]
  ring

/-- **∞-volume Lebowitz 4-point at `J = 0` two-pair coincidence**
(ferromagnetic): if `i ≠ k`, then
`truncated4Infinite ⟨0,h,β⟩ i i k k = -2 · tanh(β·h)⁴`.

Same closed form as pairwise-distinct and one-pair cases. Finset
collapses `{i,i,k,k} = {i,k}` (card 2), `{i,i} = {i}`, `{k,k} = {k}`
(card 1 each). U_4 = `t² − t² − 2t⁴ = −2t⁴`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated4Infinite_J_zero_of_two_pair_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : V} (hik : i ≠ k) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i k k
      = -2 * Real.tanh (β * h) ^ 4 := by
  unfold truncated4Infinite
  have h1i : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have h1k : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {k}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have hik2 : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i, k}
      = Real.tanh (β * h) ^ 2 := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_pair hik]
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hkk : ({k, k} : Finset V) = {k} := by simp
  have hiikk : ({i, i, k, k} : Finset V) = {i, k} := by ext x; simp
  rw [hiikk, hii, hkk, h1i, h1k, hik2]
  ring

/-- **∞-volume Lebowitz 4-point at `J = 0` triple coincidence**
(ferromagnetic): if `i ≠ l`, then
`truncated4Infinite ⟨0,h,β⟩ i i i l = t² − 3·t³` with `t = tanh(β·h)`.

Unlike the pair / two-pair / one-pair coincidence cases (all giving
`−2t⁴`), triple coincidence produces the asymmetric closed form
`t² − 3t³`. Finset collapses `{i,i,i,l} = {i,l}` (card 2),
`{i,i} = {i}` (card 1); each of the three pair-pair products equals
`t · t² = t³`, yielding `U_4 = t² − 3t³`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated4Infinite_J_zero_of_triple_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i l : V} (hil : i ≠ l) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i i l
      = Real.tanh (β * h) ^ 2 - 3 * Real.tanh (β * h) ^ 3 := by
  unfold truncated4Infinite
  have h1i : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have hil2 : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i, l}
      = Real.tanh (β * h) ^ 2 := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_pair hil]
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiiil : ({i, i, i, l} : Finset V) = {i, l} := by ext x; simp
  rw [hiiil, hii, h1i, hil2]
  ring

/-- **∞-volume Lebowitz 4-point at `J = 0` all-coincident**
(ferromagnetic): `truncated4Infinite ⟨0,h,β⟩ i i i i = t − 3·t²`
with `t = tanh(β·h)`.

Completes the J=0 trivial-slice cascade for the Lebowitz 4-point.
Finset collapses `{i,i,i,i} = {i}` (card 1), `{i,i} = {i}`; each of
the three pair-pair products equals `t · t = t²`, yielding
`U_4 = t − 3t²`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated4Infinite_J_zero_all_coincident
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : V) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i i i
      = Real.tanh (β * h) - 3 * Real.tanh (β * h) ^ 2 := by
  unfold truncated4Infinite
  have h1i : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiiii : ({i, i, i, i} : Finset V) = {i} := by ext x; simp
  rw [hiiii, hii, h1i]
  ring

-- (Steps 276-277 duplicates removed: see truncated3Infinite_J_zero_of_pairwise_distinct
-- and truncated4Infinite_J_zero_of_pairwise_distinct earlier in this file.)


end Ambient
end IsingModel
