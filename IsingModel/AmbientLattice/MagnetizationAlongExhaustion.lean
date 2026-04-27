import IsingModel.AmbientLattice.CorrelationInfinite

/-!
# Magnetization along an exhaustion and parameter monotonicity

Basic properties of `magnetizationAlongExhaustion` and its monotonicity
in the parameters `h`, `β`, `J`.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2–4.4.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Basic properties of `magnetizationAlongExhaustion` -/

/-- **Unfolding of `magnetizationAlongExhaustion`**:
`magnetizationAlongExhaustion G Λ p i n = correlationAlongExhaustion G Λ p {i} n`,
by definition. -/
theorem magnetizationAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ p i n
      = correlationAlongExhaustion G Λ p {i} n := rfl

/-- **Unfolding of `magnetizationAlongExhaustion` when `i ∈ Λ.volume n`**:
the stagewise value equals the lifted finite-volume correlation. -/
theorem magnetizationAlongExhaustion_of_mem
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {i : V} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion G Λ p i n
      = correlationΛ G (Λ.volume n) p
          (liftFinset {i} (Finset.singleton_subset_iff.mpr hi)) :=
  correlationAlongExhaustion_of_subset G Λ p
    (Finset.singleton_subset_iff.mpr hi)

/-- **Unfolding of `magnetizationAlongExhaustion` when `i ∉ Λ.volume n`**:
`magnetizationAlongExhaustion G Λ p i n = 0`. -/
theorem magnetizationAlongExhaustion_of_not_mem
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {i : V} {n : ℕ} (hi : i ∉ Λ.volume n) :
    magnetizationAlongExhaustion G Λ p i n = 0 :=
  correlationAlongExhaustion_of_not_subset G Λ p
    (fun hsub => hi (Finset.singleton_subset_iff.mp hsub))

/-- **`magnetizationAlongExhaustion ≤ 1`** per stage for any parameters.
Direct from `correlationAlongExhaustion_le_one` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ p i n ≤ 1 :=
  correlationAlongExhaustion_le_one G Λ p {i} n

/-- **`magnetizationAlongExhaustion ≥ 0`** per stage for ferromagnetic `p`.
Direct from `correlationAlongExhaustion_nonneg` at `A = {i}` (GKS-I). -/
theorem magnetizationAlongExhaustion_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) (n : ℕ) :
    0 ≤ magnetizationAlongExhaustion G Λ p i n :=
  correlationAlongExhaustion_nonneg G Λ p hf {i} n

/-- **Pointwise `|magnetizationAlongExhaustion| ≤ 1`** at every `n`.
Direct from `abs_correlationAlongExhaustion_le_one` at `A = {i}`. -/
theorem abs_magnetizationAlongExhaustion_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) (n : ℕ) :
    |magnetizationAlongExhaustion G Λ p i n| ≤ 1 :=
  abs_correlationAlongExhaustion_le_one G Λ p {i} n

/-- **Pointwise `-1 ≤ magnetizationAlongExhaustion`** at every `n`. -/
theorem neg_one_le_magnetizationAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) (n : ℕ) :
    -1 ≤ magnetizationAlongExhaustion G Λ p i n :=
  neg_one_le_correlationAlongExhaustion G Λ p {i} n

/-- **`liftFinset {i} _ = {⟨i, hi⟩}`** as a Finset on `↑Λ`: the lift of the
ambient singleton `{i}` (with `i ∈ Λ`) is the subtype singleton `{⟨i, hi⟩}`.
Small helper used to identify the along-exhaustion magnetization with
the Λ-layer magnetization at the subtype site. -/
theorem liftFinset_singleton {Λ : Finset V} {i : V} (hi : i ∈ Λ) :
    liftFinset {i} (Finset.singleton_subset_iff.mpr hi)
      = ({⟨i, hi⟩} : Finset (↑Λ : Type _)) := by
  ext x
  simp only [mem_liftFinset, Finset.mem_singleton, Subtype.ext_iff]

/-- **Link between `magnetizationAlongExhaustion` and `magnetizationΛ` on a
covered stage**: when `i ∈ Λ.volume n`,
`magnetizationAlongExhaustion G Λ p i n = magnetizationΛ G (Λ.volume n) p ⟨i, hi⟩`.
Upgrades `magnetizationAlongExhaustion_of_mem` (which returns
`correlationΛ … (liftFinset {i} _)`) to the `magnetizationΛ` form using
`liftFinset_singleton`. Convenient for along-exhaustion Z₂ symmetry
proofs that need the Λ-layer magnetization identity at the lifted site. -/
theorem magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {i : V} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion G Λ p i n
      = magnetizationΛ G (Λ.volume n) p ⟨i, hi⟩ := by
  rw [magnetizationAlongExhaustion_of_mem G Λ p hi, liftFinset_singleton hi]
  rfl

/-- **Susceptibility along an exhaustion** at a fixed ambient site `i : V`:
the stagewise sequence `n ↦ χ_{Λ_n}(⟨i, hi⟩)` when `i ∈ Λ.volume n`, and
`0` otherwise. Companion to `magnetizationAlongExhaustion` at the
susceptibility level; bridges the Λ-layer `susceptibilityΛ` (PR #776)
to the eventual `susceptibilityInfinite` (TODO).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
noncomputable def susceptibilityAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) (n : ℕ) : ℝ :=
  if h : i ∈ Λ.volume n then
    susceptibilityΛ G (Λ.volume n) p ⟨i, h⟩
  else 0

/-- **Unfolding of `susceptibilityAlongExhaustion`**: by definition the
stagewise value is the dependent `if`-expression over membership. -/
theorem susceptibilityAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) (n : ℕ) :
    susceptibilityAlongExhaustion G Λ p i n
      = if h : i ∈ Λ.volume n then
          susceptibilityΛ G (Λ.volume n) p ⟨i, h⟩
        else 0 := rfl

/-- **Unfolding of `susceptibilityAlongExhaustion` when `i ∈ Λ.volume n`**:
the stagewise value equals `susceptibilityΛ` at the lifted subtype site. -/
theorem susceptibilityAlongExhaustion_of_mem
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {i : V} {n : ℕ} (hi : i ∈ Λ.volume n) :
    susceptibilityAlongExhaustion G Λ p i n
      = susceptibilityΛ G (Λ.volume n) p ⟨i, hi⟩ := by
  unfold susceptibilityAlongExhaustion
  exact dif_pos hi

/-- **Unfolding of `susceptibilityAlongExhaustion` when `i ∉ Λ.volume n`**:
`susceptibilityAlongExhaustion G Λ p i n = 0`. -/
theorem susceptibilityAlongExhaustion_of_not_mem
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {i : V} {n : ℕ} (hi : i ∉ Λ.volume n) :
    susceptibilityAlongExhaustion G Λ p i n = 0 := by
  unfold susceptibilityAlongExhaustion
  exact dif_neg hi

/-- **`susceptibilityAlongExhaustion ≥ 0`** per stage for ferromagnetic `p`.
Case split on `i ∈ Λ.volume n`: the covered branch applies
`susceptibilityΛ_nonneg` (direct lift of `IsingModel.susceptibility_nonneg`,
which sums `truncated2_nonneg` over all `j : ↑Λ`); the uncovered branch
is `0`. -/
theorem susceptibilityAlongExhaustion_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) (n : ℕ) :
    0 ≤ susceptibilityAlongExhaustion G Λ p i n := by
  by_cases hi : i ∈ Λ.volume n
  · rw [susceptibilityAlongExhaustion_of_mem G Λ p hi]
    exact susceptibilityΛ_nonneg G (Λ.volume n) p hf ⟨i, hi⟩
  · rw [susceptibilityAlongExhaustion_of_not_mem G Λ p hi]



/-- **GKS-II at finite volume** (Λ-lifted form): for a ferromagnetic
Ising model and `A, B ⊆ Λ`,
`correlationΛ G Λ p (lift A) * correlationΛ G Λ p (lift B)
  ≤ correlationΛ G Λ p (lift (A ∆ B))`.

Obtained by applying `IsingModel.gks_second` at the induced graph
on `↑Λ` and rewriting the RHS via `liftFinset_symmDiff`. -/
theorem correlationΛ_gks_second
    (G : SimpleGraph V) {Λ : Finset V}
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A B : Finset V} (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    correlationΛ G Λ p (liftFinset A hA) * correlationΛ G Λ p (liftFinset B hB)
      ≤ correlationΛ G Λ p (liftFinset (A ∆ B) (symmDiff_subset_of_subset hA hB)) := by
  have hgks : IsingModel.correlation (inducedGraph G Λ) p (liftFinset A hA)
      * IsingModel.correlation (inducedGraph G Λ) p (liftFinset B hB)
      ≤ IsingModel.correlation (inducedGraph G Λ) p
          (liftFinset A hA ∆ liftFinset B hB) :=
    IsingModel.gks_second (inducedGraph G Λ) p hf _ _
  rw [liftFinset_symmDiff hA hB] at hgks
  exact hgks

/-- **GKS-II at infinite volume**: for a ferromagnetic Ising model on
an ambient type `V` with an exhaustion `Λ`,
`correlationInfinite G Λ p A * correlationInfinite G Λ p B
  ≤ correlationInfinite G Λ p (A ∆ B)`.

Proof: pick `N` via `Λ.exhaust (A ∪ B)` so that for `n ≥ N` both
`A, B ⊆ Λ.volume n` (hence `A ∆ B ⊆ Λ.volume n`).  Eventually the
finite-volume `correlationΛ_gks_second` gives the product inequality
for the three `correlationAlongExhaustion` sequences.  Pass to the
limit using `Tendsto.mul` +
`tendsto_correlationAlongExhaustion_correlationInfinite` and
`le_of_tendsto_of_tendsto'` to preserve the inequality. -/
theorem correlationInfinite_gks_second
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset V) :
    correlationInfinite G Λ p A * correlationInfinite G Λ p B
      ≤ correlationInfinite G Λ p (A ∆ B) := by
  have hlhs :
      Filter.Tendsto
        (fun n => correlationAlongExhaustion G Λ p A n
          * correlationAlongExhaustion G Λ p B n)
        Filter.atTop
        (nhds (correlationInfinite G Λ p A * correlationInfinite G Λ p B)) :=
    (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf A).mul
      (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf B)
  have hrhs :=
    tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf (A ∆ B)
  refine le_of_tendsto_of_tendsto' hlhs hrhs ?_
  intro n
  by_cases hAn : A ⊆ Λ.volume n
  · by_cases hBn : B ⊆ Λ.volume n
    · -- Both in: use finite-volume gks_second
      have hAΔB : A ∆ B ⊆ Λ.volume n := symmDiff_subset_of_subset hAn hBn
      rw [correlationAlongExhaustion_of_subset G Λ p hAn,
          correlationAlongExhaustion_of_subset G Λ p hBn,
          correlationAlongExhaustion_of_subset G Λ p hAΔB]
      exact correlationΛ_gks_second G p hf hAn hBn
    · -- B ⊄: LHS = 0, RHS ≥ 0
      rw [correlationAlongExhaustion_of_not_subset G Λ p hBn, mul_zero]
      exact correlationAlongExhaustion_nonneg G Λ p hf (A ∆ B) n
  · -- A ⊄: LHS = 0, RHS ≥ 0
    rw [correlationAlongExhaustion_of_not_subset G Λ p hAn, zero_mul]
    exact correlationAlongExhaustion_nonneg G Λ p hf (A ∆ B) n

/-- **Named alias for the FKG-form correlation inequality at infinite volume**.

For ferromagnetic Ising, the infinite-volume correlations satisfy
$\langle \sigma^A \rangle_\infty \langle \sigma^B \rangle_\infty
  \le \langle \sigma^{A \triangle B} \rangle_\infty$, which is the
numerical inequality one would obtain from the FKG inequality if one
naively applied it to $f = \sigma^A, g = \sigma^B$ together with the
spin-flip product identity $\sigma^A \cdot \sigma^B
  = \sigma^{A \triangle B}$.

**Important caveat**: spinProduct observables are **not** generally
monotone (e.g., flipping two spins increases a cardinality-2 product
from $+1$ to $+1$ but intermediate configurations have the product
equal to $-1$), so the general FKG inequality (Glimm–Jaffe §4.4 p. 67,
requiring monotone $f, g$) does not directly apply to arbitrary
spinProducts.  This theorem gives the same numerical conclusion via a
different route — it is literally the GKS-II theorem
(`correlationInfinite_gks_second`, PR #94), proved through the HNC /
log-supermodularity of Boltzmann weights rather than FKG's lattice
condition argument.

Provided for nomenclature/searchability and to document the §4.4
coverage (the full FKG inequality for general monotone observables at
infinite volume requires a monotone-function framework on infinite
configs, which is out of scope).

Reference: Glimm–Jaffe §4.4 p. 67 (FKG inequality general);
Friedli–Velenik §3.2.2 (FKG lattice condition). -/
theorem correlationInfinite_fkg_spinProduct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset V) :
    correlationInfinite G Λ p A * correlationInfinite G Λ p B
      ≤ correlationInfinite G Λ p (A ∆ B) :=
  correlationInfinite_gks_second G Λ p hf A B

/-! ## h-direction monotonicity at infinite volume

Lift `IsingModel.correlation_monotone_h` (finite volume, external
field direction) to the thermodynamic limit.  For fixed `J ≥ 0`,
`β > 0`, the map `h ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` is
monotone on `Set.Ici 0`.

Reference: Glimm–Jaffe, Proposition 4.2.4. -/

/-- **h-direction monotonicity of `correlationΛ`**: for fixed
`J ≥ 0`, `β > 0`, the correlation on `Λ : Finset V` is monotone in
the external field `h ∈ Set.Ici 0`. -/
theorem correlationΛ_monotone_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun h : ℝ => correlationΛ G Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  IsingModel.correlation_monotone_h (inducedGraph G Λ) J hJ β hβ A

/-- **h-direction monotonicity of `correlationAlongExhaustion`**:
pointwise on the exhaustion sequence.  For `0 ≤ h₁ ≤ h₂`,
`correlationAlongExhaustion G Λ ⟨J, h₁, β⟩ A n
  ≤ correlationAlongExhaustion G Λ ⟨J, h₂, β⟩ A n`
for every `n`. -/
theorem correlationAlongExhaustion_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset V) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J, h₁, β⟩ A n
      ≤ correlationAlongExhaustion G Λ ⟨J, h₂, β⟩ A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J, h₁, β⟩ hAn,
        correlationAlongExhaustion_of_subset G Λ ⟨J, h₂, β⟩ hAn]
    exact correlationΛ_monotone_h G (Λ.volume n) hJ hβ _ hh₁ (hh₁.trans hh₁₂) hh₁₂
  · rw [correlationAlongExhaustion_of_not_subset G Λ ⟨J, h₁, β⟩ hAn,
        correlationAlongExhaustion_of_not_subset G Λ ⟨J, h₂, β⟩ hAn]

/-- **h-direction monotonicity of `correlationInfinite`**: for fixed
`J ≥ 0`, `β > 0`, the thermodynamic-limit correlation is monotone in
the external field `h ∈ Set.Ici 0`.

Glimm–Jaffe, Proposition 4.2.4 at infinite volume. -/
theorem correlationInfinite_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset V) :
    MonotoneOn
      (fun h : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) := by
  intro h₁ hh₁ h₂ _ hh₁₂
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_h G Λ hJ hβ A hh₁ hh₁₂ n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G Λ ⟨J, h₂, β⟩ A) n)

/-! ## β-direction monotonicity at infinite volume

Lift `IsingModel.correlation_monotone_beta` (inverse-temperature
direction) to the thermodynamic limit.  For fixed `J ≥ 0`, `h ≥ 0`,
the map `β ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` is monotone on
`Set.Ioi 0`.

Reference: Glimm–Jaffe, Proposition 4.2.4 (β-direction). -/

/-- **β-direction monotonicity of `correlationΛ`**: for fixed
`J ≥ 0`, `h ≥ 0`, the correlation on `Λ : Finset V` is monotone in
the inverse temperature `β ∈ Set.Ioi 0`. -/
theorem correlationΛ_monotone_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => correlationΛ G Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  IsingModel.correlation_monotone_beta (inducedGraph G Λ) J hJ h hh A

/-- **β-direction monotonicity of `correlationAlongExhaustion`**:
pointwise on the exhaustion sequence.  For `0 < β₁ ≤ β₂`,
`correlationAlongExhaustion G Λ ⟨J, h, β₁⟩ A n
  ≤ correlationAlongExhaustion G Λ ⟨J, h, β₂⟩ A n`
for every `n`. -/
theorem correlationAlongExhaustion_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset V) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J, h, β₁⟩ A n
      ≤ correlationAlongExhaustion G Λ ⟨J, h, β₂⟩ A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J, h, β₁⟩ hAn,
        correlationAlongExhaustion_of_subset G Λ ⟨J, h, β₂⟩ hAn]
    exact correlationΛ_monotone_beta G (Λ.volume n) hJ hh _ hβ₁
      (lt_of_lt_of_le hβ₁ hβ₁₂) hβ₁₂
  · rw [correlationAlongExhaustion_of_not_subset G Λ ⟨J, h, β₁⟩ hAn,
        correlationAlongExhaustion_of_not_subset G Λ ⟨J, h, β₂⟩ hAn]

/-- **β-direction monotonicity of `correlationInfinite`**: for fixed
`J ≥ 0`, `h ≥ 0`, the thermodynamic-limit correlation is monotone in
the inverse temperature `β ∈ Set.Ioi 0`.

Glimm–Jaffe, Proposition 4.2.4 at infinite volume (β-direction). -/
theorem correlationInfinite_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset V) :
    MonotoneOn
      (fun β : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ₁₂
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_beta G Λ hJ hh A hβ₁ hβ₁₂ n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G Λ ⟨J, h, β₂⟩ A) n)

/-! ## J-direction monotonicity at infinite volume

Lift `IsingModel.correlation_monotone_J` (coupling-constant
direction) to the thermodynamic limit.  For fixed `h ≥ 0`, `β > 0`,
the map `J ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` is monotone on
`Set.Ici 0`.

Reference: Glimm–Jaffe, Proposition 4.2.4, p. 58 (J-direction). -/

/-- **J-direction monotonicity of `correlationΛ`**: for fixed
`h ≥ 0`, `β > 0`, the correlation on `Λ : Finset V` is monotone in
the coupling constant `J ∈ Set.Ici 0`. -/
theorem correlationΛ_monotone_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun J : ℝ => correlationΛ G Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  IsingModel.correlation_monotone_J (inducedGraph G Λ) h hh β hβ A

/-- **J-direction monotonicity of `correlationAlongExhaustion`**:
pointwise on the exhaustion sequence.  For `0 ≤ J₁ ≤ J₂`,
`correlationAlongExhaustion G Λ ⟨J₁, h, β⟩ A n
  ≤ correlationAlongExhaustion G Λ ⟨J₂, h, β⟩ A n`
for every `n`. -/
theorem correlationAlongExhaustion_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset V) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J₁, h, β⟩ A n
      ≤ correlationAlongExhaustion G Λ ⟨J₂, h, β⟩ A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J₁, h, β⟩ hAn,
        correlationAlongExhaustion_of_subset G Λ ⟨J₂, h, β⟩ hAn]
    exact correlationΛ_monotone_J G (Λ.volume n) hh hβ _ hJ₁ (hJ₁.trans hJ₁₂) hJ₁₂
  · rw [correlationAlongExhaustion_of_not_subset G Λ ⟨J₁, h, β⟩ hAn,
        correlationAlongExhaustion_of_not_subset G Λ ⟨J₂, h, β⟩ hAn]

/-! ## Parameter monotonicities of `magnetizationΛ` / `magnetizationAlongExhaustion` -/

/-- **h-monotonicity of `magnetizationΛ`**: `MonotoneOn` in `h` on `Ici 0`
for `J ≥ 0`, `β > 0`. Specialization of `correlationΛ_monotone_h`. -/
theorem magnetizationΛ_monotone_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun h : ℝ => magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  correlationΛ_monotone_h G Λ hJ hβ {i}

/-- **β-monotonicity of `magnetizationΛ`**: `MonotoneOn` in `β` on `Ioi 0`
for `J, h ≥ 0`. Specialization of `correlationΛ_monotone_beta`. -/
theorem magnetizationΛ_monotone_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : ↑Λ) :
    MonotoneOn
      (fun β : ℝ => magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi 0) :=
  correlationΛ_monotone_beta G Λ hJ hh {i}

/-- **J-monotonicity of `magnetizationΛ`**: `MonotoneOn` in `J` on `Ici 0`
for `h ≥ 0`, `β > 0`. Specialization of `correlationΛ_monotone_J`. -/
theorem magnetizationΛ_monotone_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun J : ℝ => magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  correlationΛ_monotone_J G Λ hh hβ {i}

/-- **h-monotonicity of `magnetizationAlongExhaustion`** per stage:
specialization of `correlationAlongExhaustion_monotone_h` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (i : V) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    magnetizationAlongExhaustion G Λ ⟨J, h₁, β⟩ i n
      ≤ magnetizationAlongExhaustion G Λ ⟨J, h₂, β⟩ i n :=
  correlationAlongExhaustion_monotone_h G Λ hJ hβ {i} hh₁ hh₁₂ n

/-- **β-monotonicity of `magnetizationAlongExhaustion`** per stage:
specialization of `correlationAlongExhaustion_monotone_beta` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (i : V) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    magnetizationAlongExhaustion G Λ ⟨J, h, β₁⟩ i n
      ≤ magnetizationAlongExhaustion G Λ ⟨J, h, β₂⟩ i n :=
  correlationAlongExhaustion_monotone_beta G Λ hJ hh {i} hβ₁ hβ₁₂ n

/-- **J-monotonicity of `magnetizationAlongExhaustion`** per stage:
specialization of `correlationAlongExhaustion_monotone_J` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (i : V) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    magnetizationAlongExhaustion G Λ ⟨J₁, h, β⟩ i n
      ≤ magnetizationAlongExhaustion G Λ ⟨J₂, h, β⟩ i n :=
  correlationAlongExhaustion_monotone_J G Λ hh hβ {i} hJ₁ hJ₁₂ n


/-- **J-direction monotonicity of `correlationInfinite`**: for fixed
`h ≥ 0`, `β > 0`, the thermodynamic-limit correlation is monotone in
the coupling constant `J ∈ Set.Ici 0`.

Glimm–Jaffe, Proposition 4.2.4 at infinite volume (J-direction). -/
theorem correlationInfinite_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset V) :
    MonotoneOn
      (fun J : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) := by
  intro J₁ hJ₁ J₂ _ hJ₁₂
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_J G Λ hh hβ A hJ₁ hJ₁₂ n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G Λ ⟨J₂, h, β⟩ A) n)


end Ambient
end IsingModel
