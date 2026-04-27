import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.Monotonicity
import IsingModel.AmbientLattice.CorrelationInfinite
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.InfiniteVolume
import IsingModel.FreeEnergy
import IsingModel.Inequalities.GHS
import IsingModel.Conditioning
import IsingModel.PhaseTransition
import IsingModel.FieldDerivative

/-!
# Genuine infinite-volume framework: ambient lattice

The existing `IsingModel` framework parametrizes everything by a fixed
`Fintype ι`.  This file introduces a **genuinely infinite ambient
lattice** `V : Type*` (no `Fintype V` assumption) and defines the
finite-volume Ising model on any `Λ : Finset V` by instantiating the
existing framework on the Fintype `(↑Λ : Type _)`.

This is the foundation for the true thermodynamic limit (Phase 2), where
an exhaustion `Λₙ ↑ V` covers the whole ambient lattice.

## Design

- Ambient type `V` carries an ambient `SimpleGraph V` (the interaction
  graph), and we demand `DecidableEq V` + `DecidableRel G.Adj` so that
  finite restrictions remain decidable.
- For `Λ : Finset V`, the type `(↑Λ : Type _)` is Fintype (mathlib
  `Finset.instFintypeCoe`).  The induced subgraph
  `G.induce (↑Λ : Set V)` gives a `SimpleGraph (↑Λ : Type _)` with
  `Fintype edgeSet` derivable from the ambient `DecidableRel`.
- Correlations, partition functions, and free energies on `Λ` are
  defined by forwarding to the existing `IsingModel` constructors.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2, §4.6 (the thermodynamic limit
  is stated over `Λ ↑ ℝᵈ`, i.e., an infinite ambient).
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Infinite-volume single-site magnetization

Specialize `correlationInfinite` to single sites `A = {i}` to obtain
the formal thermodynamic-limit magnetization `magnetizationInfinite`.
All basic properties follow directly from the general
`correlationInfinite` API (PR #91–#97).

Reference: Glimm–Jaffe §4.2 (pp. 57ff) / §5.1 (p. 77, $m^* := \lim_{h \to 0^+} M$). -/

/-- **Infinite-volume single-site magnetization**: for a ferromagnetic
Ising model on an ambient type `V`, exhaustion `Λ`, and site `i : V`,
`magnetizationInfinite G Λ p i := correlationInfinite G Λ p {i}`.

This is the formal thermodynamic-limit magnetization
$\langle \sigma_i \rangle_\infty^{\mathrm{FM}}$. -/
noncomputable def magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) : ℝ :=
  correlationInfinite G Λ p {i}

/-- **Unfolding of `magnetizationInfinite`**:
`magnetizationInfinite G Λ p i = correlationInfinite G Λ p {i}`,
by definition. -/
theorem magnetizationInfinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i = correlationInfinite G Λ p {i} := rfl

/-- **Nonnegativity of `magnetizationInfinite`** (ferromagnetic):
`0 ≤ magnetizationInfinite G Λ p i`.  Specialization of
`correlationInfinite_nonneg` at `A = {i}`. -/
theorem magnetizationInfinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    0 ≤ magnetizationInfinite G Λ p i :=
  correlationInfinite_nonneg G Λ p hf {i}

/-- **Upper bound**: `magnetizationInfinite G Λ p i ≤ 1`. Specialization
of `correlationInfinite_le_one`. -/
theorem magnetizationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i ≤ 1 :=
  correlationInfinite_le_one G Λ p {i}

/-- **Magnetization ∞-volume ambient-subgraph monotonicity**:
for `G₁ ≤ G₂` and ferromagnetic `p`. Specialization of
`correlationInfinite_monotone_ambient_subgraph` at `A = {i}`. -/
theorem magnetizationInfinite_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    magnetizationInfinite G₁ Λ p i ≤ magnetizationInfinite G₂ Λ p i :=
  correlationInfinite_monotone_ambient_subgraph h Λ p hf {i}

/-- **`|magnetizationInfinite| ≤ 1`** unconditionally (any parameters).
Direct specialization of `abs_correlationInfinite_le_one` at `A = {i}`. -/
theorem abs_magnetizationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    |magnetizationInfinite G Λ p i| ≤ 1 :=
  abs_correlationInfinite_le_one G Λ p {i}

/-- **`-1 ≤ magnetizationInfinite`** unconditionally. -/
theorem neg_one_le_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    -1 ≤ magnetizationInfinite G Λ p i :=
  neg_one_le_correlationInfinite G Λ p {i}

/-- **`magnetizationInfinite² ≤ 1`** unconditionally. From
`abs_magnetizationInfinite_le_one` via `sq_le_one'`. -/
theorem magnetizationInfinite_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i ^ 2 ≤ 1 := by
  have h := abs_magnetizationInfinite_le_one G Λ p i
  have : |magnetizationInfinite G Λ p i| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Convergence of `magnetizationAlongExhaustion` to `magnetizationInfinite`**
for ferromagnetic `p`:
`Tendsto (magnetizationAlongExhaustion G Λ p i) atTop (nhds (magnetizationInfinite G Λ p i))`.
Direct specialization of `tendsto_correlationAlongExhaustion_correlationInfinite`
at `A = {i}`, unfolding `magnetizationInfinite := correlationInfinite … {i}`. -/
theorem tendsto_magnetizationAlongExhaustion_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    Filter.Tendsto (magnetizationAlongExhaustion G Λ p i)
      Filter.atTop (nhds (magnetizationInfinite G Λ p i)) :=
  tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i}

/-- **Existential convergence of `magnetizationAlongExhaustion`** for
ferromagnetic `p`: `∃ L, Tendsto (magnetizationAlongExhaustion G Λ p i) atTop (nhds L)`.
Specialization of `correlationAlongExhaustion_convergent` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_convergent
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    ∃ L : ℝ, Filter.Tendsto (magnetizationAlongExhaustion G Λ p i)
      Filter.atTop (nhds L) :=
  correlationAlongExhaustion_convergent G Λ p hf {i}

/-- **Stage-index monotonicity of `magnetizationAlongExhaustion`** for
ferromagnetic `p`. Specialization of `correlationAlongExhaustion_monotone`
at `A = {i}`. -/
theorem magnetizationAlongExhaustion_monotone
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    Monotone (magnetizationAlongExhaustion G Λ p i) :=
  correlationAlongExhaustion_monotone G Λ p hf {i}

/-- **`magnetizationAlongExhaustion` is bounded above** (unconditional):
the range of `n ↦ magnetizationAlongExhaustion G Λ p i n` is
bounded above. Specialization of `correlationAlongExhaustion_bddAbove`
at `A = {i}`. -/
theorem magnetizationAlongExhaustion_bddAbove
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    BddAbove (Set.range (magnetizationAlongExhaustion G Λ p i)) :=
  correlationAlongExhaustion_bddAbove G Λ p {i}

/-- **`magnetizationAlongExhaustion` is bounded below** (unconditional):
specialization of `correlationAlongExhaustion_bddBelow` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_bddBelow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    BddBelow (Set.range (magnetizationAlongExhaustion G Λ p i)) :=
  correlationAlongExhaustion_bddBelow G Λ p {i}

/-- **Convergence to the supremum** for `magnetizationAlongExhaustion`
(ferromagnetic): `Tendsto … atTop (nhds (⨆ n, magnetizationAlongExhaustion G Λ p i n))`.
Specialization of `correlationAlongExhaustion_tendsto_ciSup` at
`A = {i}`. -/
theorem magnetizationAlongExhaustion_tendsto_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    Filter.Tendsto (magnetizationAlongExhaustion G Λ p i)
      Filter.atTop (nhds (⨆ n, magnetizationAlongExhaustion G Λ p i n)) :=
  correlationAlongExhaustion_tendsto_ciSup G Λ p hf {i}

/-- **`magnetizationInfinite` as `ciSup`**:
`magnetizationInfinite G Λ p i = ⨆ n, magnetizationAlongExhaustion G Λ p i n`.
Definitional identity threading `magnetizationInfinite := correlationInfinite … {i}`
and `correlationInfinite := ⨆ n, correlationAlongExhaustion …` through
`magnetizationAlongExhaustion := correlationAlongExhaustion … {i}`. -/
theorem magnetizationInfinite_eq_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i
      = ⨆ n, magnetizationAlongExhaustion G Λ p i n := rfl

/-- **Pointwise bound**: `magnetizationAlongExhaustion G Λ p i n ≤
magnetizationInfinite G Λ p i` at every `n`. Specialization at `A = {i}`. -/
theorem magnetizationAlongExhaustion_le_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ p i n ≤ magnetizationInfinite G Λ p i :=
  correlationAlongExhaustion_le_correlationInfinite G Λ p {i} n

/-- **Exhaustion-independence of `magnetizationInfinite`**:
the value does not depend on the choice of exhaustion.  Specialization
of `correlationInfinite_indep_exhaustion`. -/
theorem magnetizationInfinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    magnetizationInfinite G Λ p i = magnetizationInfinite G Λ' p i :=
  correlationInfinite_indep_exhaustion G Λ Λ' p hf {i}

/-- **J-direction monotonicity of `magnetizationInfinite`** (for
fixed `h ≥ 0, β > 0`).  Specialization of
`correlationInfinite_monotone_J`. -/
theorem magnetizationInfinite_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (i : V) :
    MonotoneOn
      (fun J : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  correlationInfinite_monotone_J G Λ hh hβ {i}

/-- **h-direction monotonicity of `magnetizationInfinite`** (for
fixed `J ≥ 0, β > 0`).  Specialization of
`correlationInfinite_monotone_h`. -/
theorem magnetizationInfinite_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (i : V) :
    MonotoneOn
      (fun h : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  correlationInfinite_monotone_h G Λ hJ hβ {i}

/-- **β-direction monotonicity of `magnetizationInfinite`** (for
fixed `J ≥ 0, h ≥ 0`).  Specialization of
`correlationInfinite_monotone_beta`. -/
theorem magnetizationInfinite_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (i : V) :
    MonotoneOn
      (fun β : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  correlationInfinite_monotone_beta G Λ hJ hh {i}

/-- **Z₂ symmetry at `h = 0` for `correlationΛ`**: at vanishing external
field, the correlation on `Λ` of an odd-cardinality set is zero.
Lift of `IsingModel.correlation_odd_vanish` (GHS.lean). -/
theorem correlationΛ_odd_vanish_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) (hodd : Odd A.card) :
    correlationΛ G Λ ⟨J, 0, β⟩ A = 0 :=
  IsingModel.correlation_odd_vanish (inducedGraph G Λ) J β A hodd

/-- **Z₂ odd-symmetry for `correlationΛ` under `h → -h`**:
`correlationΛ G Λ ⟨J, -h, β⟩ A = (-1)^|A| · correlationΛ G Λ ⟨J, h, β⟩ A`.
Λ-level lift of `IsingModel.correlation_neg_h`. Generalizes
`correlationΛ_odd_vanish_h_zero` from `h = 0` to arbitrary `h`. -/
theorem correlationΛ_neg_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ) A
      = (-1) ^ A.card * correlationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_neg_h (inducedGraph G Λ) J h β A

/-- **Z₂ odd-symmetry for `magnetizationΛ` under `h → -h`**:
`magnetizationΛ G Λ ⟨J, -h, β⟩ i = -magnetizationΛ G Λ ⟨J, h, β⟩ i`.
Direct specialization of `correlationΛ_neg_h` at `A = {i}`
(card 1, `(-1)^1 = -1`). -/
theorem magnetizationΛ_neg_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : (↑Λ : Type _)) :
    magnetizationΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i
      = -magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
  unfold magnetizationΛ
  rw [correlationΛ_neg_h, Finset.card_singleton, pow_one]
  ring

/-- **Λ-level `correlation_eq_abs_h_of_even_card`**: for `|A|` even,
`correlationΛ G Λ ⟨J, h, β⟩ A = correlationΛ G Λ ⟨J, |h|, β⟩ A`.
Λ-layer lift of `IsingModel.correlation_eq_abs_h_of_even_card`. -/
theorem correlationΛ_eq_abs_h_of_even_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) (heven : Even A.card) :
    correlationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) A
      = correlationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_abs_h_of_even_card (inducedGraph G Λ) J h β A heven

/-- **Λ-layer `|M_Λ(h)| = M_Λ(|h|)`** under ferromagnetism at `|h|`:
requires `0 ≤ J ∧ 0 < β` (so that `Ferromagnetic ⟨J, |h|, β⟩` holds
automatically via `0 ≤ |h|`). Λ-layer counterpart of
`IsingModel.abs_magnetization_eq_magnetization_abs_h` (PR #769).

Proof by `abs_choice h`: at `|h| = h` (`h ≥ 0`),
`magnetizationΛ_nonneg` gives the nonneg value matches `|·|`; at
`|h| = -h` (`h ≤ 0`), `magnetizationΛ_neg_h` flips sign and the
ferromagnetic nonnegativity at `|h|` makes the absolute value agree.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 (background). -/
theorem abs_magnetizationΛ_eq_magnetizationΛ_abs_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : (↑Λ : Type _)) :
    |magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i|
      = magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i := by
  have hf_abs : Ferromagnetic (⟨J, |h|, β⟩ : IsingParams ℝ) :=
    ⟨hJ, abs_nonneg _, hβ⟩
  have habs_nonneg :
      0 ≤ magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
    magnetizationΛ_nonneg G Λ _ hf_abs i
  rcases abs_choice h with habs | habs
  · -- |h| = h (h ≥ 0)
    have heq :
        magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i
          = magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
      rw [habs]
    rw [heq]
    apply abs_of_nonneg
    have h_ge : 0 ≤ h := by rw [← habs]; exact abs_nonneg h
    exact magnetizationΛ_nonneg G Λ _ ⟨hJ, h_ge, hβ⟩ i
  · -- |h| = -h (h ≤ 0)
    have hneg :
        magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i
          = -magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
      rw [habs]; exact magnetizationΛ_neg_h G Λ J h β i
    rw [hneg]
    apply abs_of_nonpos
    have hne :
        0 ≤ -magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
      rw [← hneg]; exact habs_nonneg
    linarith

/-- **Λ-level susceptibility under `h → -h`**:
`χ_Λ(J, -h, β; i) = χ_Λ(J, h, β; i) - 2·M_Λ(J, h, β; i)`.
Direct lift of `IsingModel.susceptibility_neg_h` through
`susceptibilityΛ := IsingModel.susceptibility (inducedGraph G Λ)` and
`magnetizationΛ = IsingModel.magnetization (inducedGraph G Λ)`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityΛ_neg_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : (↑Λ : Type _)) :
    susceptibilityΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i
      = susceptibilityΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i
          - 2 * magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.susceptibility_neg_h (inducedGraph G Λ) J h β i

/-- **Λ-level susceptibility closed form at `|h|`** (A-4, capstone):
`χ_Λ(J, |h|, β; i) = χ_Λ(J, h, β; i) + M_Λ(J, |h|, β; i) - M_Λ(J, h, β; i)`,
unconditionally (no ferromagnetic hypothesis required).

Direct lift of `IsingModel.susceptibility_eq_abs_h` (PR #771) through
`susceptibilityΛ := IsingModel.susceptibility (inducedGraph G Λ)` and
`magnetizationΛ = IsingModel.magnetization (inducedGraph G Λ)`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityΛ_eq_abs_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : (↑Λ : Type _)) :
    susceptibilityΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i
      = susceptibilityΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i
          + magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i
          - magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.susceptibility_eq_abs_h (inducedGraph G Λ) J h β i

/-- **Λ-level correlation closed form at `J = 0`**:
`correlationΛ G Λ ⟨0, h, β⟩ A = tanh(β·h)^A.card`. Direct lift of
`IsingModel.correlation_J_zero` through
`correlationΛ := correlation (inducedGraph G Λ)`. Unconditional. -/
theorem correlationΛ_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  IsingModel.correlation_J_zero (inducedGraph G Λ) h β A

/-- **Λ-level lower bound `correlationΛ ≥ tanh(β·h)^|A|`** (ferromagnetic,
sharp): by J-monotonicity from `J = 0` (where `correlationΛ = tanh(β·h)^|A|`)
up to any `J ≥ 0`. -/
theorem correlationΛ_ge_tanh_pow_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) A := by
  have h_zero : correlationΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card := correlationΛ_J_zero G Λ h β A
  rw [← h_zero]
  exact correlationΛ_monotone_J G Λ hh hβ A
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hJ) hJ

/-- **Λ-level lower bound `magnetizationΛ ≥ tanh(β·h)`** (ferromagnetic):
specialization of `correlationΛ_ge_tanh_pow_card` at `A = {i}` where
`|A|^1 = |A|.card = 1`. -/
theorem magnetizationΛ_ge_tanh
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : ↑Λ) :
    Real.tanh (β * h)
      ≤ magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
  have := correlationΛ_ge_tanh_pow_card G Λ hJ hh hβ ({i} : Finset (↑Λ : Type _))
  simpa [Finset.card_singleton] using this

/-- **Z₂ symmetry at `h = 0` for `correlationAlongExhaustion`**:
pointwise zero at every `n`.  Either `A ⊄ Λ.volume n` (both branches
of the dite give `0`) or `A ⊆ Λ.volume n` and the lifted correlation
vanishes by `correlationΛ_odd_vanish_h_zero`. -/
theorem correlationAlongExhaustion_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hodd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n = 0 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hAn]
    refine correlationΛ_odd_vanish_h_zero G (Λ.volume n) J β _ ?_
    rw [liftFinset_card hAn]
    exact hodd
  · exact correlationAlongExhaustion_of_not_subset G Λ ⟨J, 0, β⟩ hAn

/-- **Z₂ odd-symmetry under `h → -h` for `correlationAlongExhaustion`**:
at every stage `n`,
`corrAlongExh G Λ ⟨J,-h,β⟩ A n = (-1)^|A| · corrAlongExh G Λ ⟨J,h,β⟩ A n`
(Z₂ odd-symmetry under `h → -h`).

Case split on `A ⊆ Λ.volume n`: the else branch is `0`, and
`(-1)^|A| · 0 = 0`. Subset branch uses `correlationΛ_neg_h` +
`liftFinset_card` (preservation of cardinality under the lift).

Generalizes `correlationAlongExhaustion_h_zero` from `h = 0` (where
both sides are `0` at odd `|A|`) to arbitrary `h`. -/
theorem correlationAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) A n
      = (-1) ^ A.card * correlationAlongExhaustion G Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ (⟨J, -h, β⟩ : IsingParams ℝ) hAn,
        correlationAlongExhaustion_of_subset G Λ (⟨J, h, β⟩ : IsingParams ℝ) hAn,
        correlationΛ_neg_h, liftFinset_card hAn]
  · rw [correlationAlongExhaustion_of_not_subset G Λ (⟨J, -h, β⟩ : IsingParams ℝ) hAn,
        correlationAlongExhaustion_of_not_subset G Λ (⟨J, h, β⟩ : IsingParams ℝ) hAn]
    ring

/-- **∞-volume `correlationInfinite` invariance under `h → -h`**
(for even `|A|`):
`correlationInfinite G Λ ⟨J, -h, β⟩ A = correlationInfinite G Λ ⟨J, h, β⟩ A`.

At even `|A|`, the pointwise `correlationAlongExhaustion_neg_h`
sign is `(-1)^|A| = 1`, so the sequence is unchanged and the
`ciSup` agrees. For odd `|A|` the sign flips, turning `ciSup` into
`-ciInf` (harder to analyze); deferred. -/
theorem correlationInfinite_neg_h_of_even_card
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (heven : Even A.card) :
    correlationInfinite G Λ (⟨J, -h, β⟩ : IsingParams ℝ) A
      = correlationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) A := by
  unfold correlationInfinite
  refine iSup_congr ?_
  intro n
  rw [correlationAlongExhaustion_neg_h]
  obtain ⟨k, hk⟩ := heven
  rw [hk]
  have h2k : (-1 : ℝ) ^ (k + k) = 1 := by
    rw [show k + k = 2 * k from by omega, pow_mul]
    simp
  rw [h2k, one_mul]

/-- **∞-volume `correlationInfinite` equals value at `|h|`**
(for even `|A|`): direct consequence of
`correlationInfinite_neg_h_of_even_card` via `abs_choice`. -/
theorem correlationInfinite_eq_abs_h_of_even_card
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (heven : Even A.card) :
    correlationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) A
      = correlationInfinite G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) A := by
  rcases abs_choice h with habs | habs
  · rw [habs]
  · rw [habs, correlationInfinite_neg_h_of_even_card G Λ J h β A heven]

/-- **Z₂ odd-symmetry for `magnetizationAlongExhaustion` under `h → -h`**:
at each stage `n`,
`magnetizationAlongExhaustion ⟨J,-h,β⟩ i n = -magnetizationAlongExhaustion ⟨J,h,β⟩ i n`.
Specialization of `correlationAlongExhaustion_neg_h` at `A = {i}`
(`|A| = 1`, `(-1)^1 = -1`). -/
theorem magnetizationAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i n
      = -magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
  change correlationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) {i} n
    = -correlationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) {i} n
  rw [correlationAlongExhaustion_neg_h, Finset.card_singleton, pow_one]
  ring

/-- **Pointwise along-exhaustion `|M_along(h) n| = M_along(|h|) n`**
under ferromagnetism at `|h|` (`0 ≤ J`, `0 < β`). Along-exhaustion
counterpart of the Λ-layer `abs_magnetizationΛ_eq_magnetizationΛ_abs_h`
(PR #772); uses `magnetizationAlongExhaustion_nonneg` and
`magnetizationAlongExhaustion_neg_h` via `abs_choice`. -/
theorem abs_magnetizationAlongExhaustion_eq_magnetizationAlongExhaustion_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : V) (n : ℕ) :
    |magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n|
      = magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n := by
  have hf_abs : Ferromagnetic (⟨J, |h|, β⟩ : IsingParams ℝ) :=
    ⟨hJ, abs_nonneg _, hβ⟩
  have habs_nonneg :
      0 ≤ magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n :=
    magnetizationAlongExhaustion_nonneg G Λ _ hf_abs i n
  rcases abs_choice h with habs | habs
  · -- |h| = h (h ≥ 0)
    have heq :
        magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          = magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
      rw [habs]
    rw [heq]
    apply abs_of_nonneg
    have h_ge : 0 ≤ h := by rw [← habs]; exact abs_nonneg h
    exact magnetizationAlongExhaustion_nonneg G Λ _ ⟨hJ, h_ge, hβ⟩ i n
  · -- |h| = -h (h ≤ 0)
    have hneg :
        magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          = -magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
      rw [habs]; exact magnetizationAlongExhaustion_neg_h G Λ J h β i n
    rw [hneg]
    apply abs_of_nonpos
    have hne :
        0 ≤ -magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
      rw [← hneg]; exact habs_nonneg
    linarith

/-- **Along-exhaustion susceptibility under `h → -h`**:
`χ_along(⟨J, -h, β⟩; i, n) = χ_along(⟨J, h, β⟩; i, n) - 2·M_along(⟨J, h, β⟩; i, n)`.

Case split on `i ∈ Λ.volume n`:
- Covered stage: reduce to `susceptibilityΛ_neg_h` (PR #776) at the
  lifted subtype site via
  `susceptibilityAlongExhaustion_of_mem` and
  `magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ`.
- Uncovered stage: all three terms are `0`, so the identity is trivial.

Along-exhaustion counterpart of `susceptibilityΛ_neg_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    susceptibilityAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i n
      = susceptibilityAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
          - 2 * magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
  by_cases hi : i ∈ Λ.volume n
  · rw [susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ G Λ _ hi]
    exact susceptibilityΛ_neg_h G (Λ.volume n) J h β ⟨i, hi⟩
  · rw [susceptibilityAlongExhaustion_of_not_mem G Λ _ hi,
        susceptibilityAlongExhaustion_of_not_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_not_mem G Λ _ hi]
    ring

/-- **Along-exhaustion susceptibility at `|h|`** (capstone,
along-exhaustion layer, no ferromagnetic hypothesis):
`χ_along(⟨J, |h|, β⟩; i, n) = χ_along(⟨J, h, β⟩; i, n)
 + M_along(⟨J, |h|, β⟩; i, n) - M_along(⟨J, h, β⟩; i, n)`.

Case split on `i ∈ Λ.volume n`: covered stage reduces to
`susceptibilityΛ_eq_abs_h` (PR #776) at the lifted subtype site;
uncovered stage is trivial (all four terms `0`).

Along-exhaustion counterpart of PR #776's `susceptibilityΛ_eq_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    susceptibilityAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
      = susceptibilityAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
          + magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          - magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
  by_cases hi : i ∈ Λ.volume n
  · rw [susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ G Λ _ hi,
        magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ G Λ _ hi]
    exact susceptibilityΛ_eq_abs_h G (Λ.volume n) J h β ⟨i, hi⟩
  · rw [susceptibilityAlongExhaustion_of_not_mem G Λ _ hi,
        susceptibilityAlongExhaustion_of_not_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_not_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_not_mem G Λ _ hi]
    ring

/-- **Along-exhaustion pointwise `χ_along(h) ≤ χ_along(|h|)`** (A-4c)
under `0 ≤ J`, `0 < β`, at every stage `n` and any site `i : V`:
`χ_along(⟨J, h, β⟩; i, n) ≤ χ_along(⟨J, |h|, β⟩; i, n)`.

Proof by `abs_choice h`:
- `|h| = h` (`h ≥ 0`): the two sides are equal, so `≤` is reflexive.
- `|h| = -h` (`h ≤ 0`): starting from
  `susceptibilityAlongExhaustion_eq_abs_h` at `h`, we have
  `χ_along(|h|) = χ_along(h) + M_along(|h|) - M_along(h)`. Under
  ferromagnetism at `|h|` (i.e. `0 ≤ J, 0 ≤ |h|, 0 < β`, the first and
  last from hypotheses, the middle from `abs_nonneg`),
  `M_along(|h|) ≥ 0` by `magnetizationAlongExhaustion_nonneg`. Using
  `magnetizationAlongExhaustion_neg_h` at `|h| = -h` inverted:
  `M_along(h) = -M_along(|h|) ≤ 0`. Hence the correction
  `M_along(|h|) - M_along(h) = M_along(|h|) + |M_along(|h|)| ≥ 0`, so
  `χ_along(h) ≤ χ_along(|h|)`.

No ferromagnetic hypothesis at `h` is needed; only at `|h|`
(where it is automatic given `0 ≤ J, 0 < β`).

Prereq for the `BddAbove`-conditional ∞-volume lift A-5'
(`susceptibilityInfinite_le_abs_h`).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_le_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : V) (n : ℕ) :
    susceptibilityAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
      ≤ susceptibilityAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n := by
  rcases abs_choice h with habs | habs
  · -- |h| = h, equality of the two sides
    rw [habs]
  · -- |h| = -h, use the eq_abs_h + sign of M_along(h)
    have heq := susceptibilityAlongExhaustion_eq_abs_h G Λ J h β i n
    -- ferromagnetic at |h|
    have hf_abs : Ferromagnetic (⟨J, |h|, β⟩ : IsingParams ℝ) :=
      ⟨hJ, abs_nonneg _, hβ⟩
    -- M_along(|h|) ≥ 0
    have hM_abs_nonneg :
        0 ≤ magnetizationAlongExhaustion G Λ
              (⟨J, |h|, β⟩ : IsingParams ℝ) i n :=
      magnetizationAlongExhaustion_nonneg G Λ _ hf_abs i n
    -- M_along(|h|) = M_along(-h) = -M_along(h); hence M_along(h) ≤ 0
    have hM_neg :
        magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          = -magnetizationAlongExhaustion G Λ
              (⟨J, h, β⟩ : IsingParams ℝ) i n := by
      rw [habs]; exact magnetizationAlongExhaustion_neg_h G Λ J h β i n
    have hM_h_nonpos :
        magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n ≤ 0 :=
      by linarith
    linarith

/-- **Infinite-volume susceptibility** at site `i : V`:
`susceptibilityInfinite G Λ p i := ⨆ n, susceptibilityAlongExhaustion G Λ p i n`.

Analog of `magnetizationInfinite` / `correlationInfinite`, but for the
susceptibility χ. Unlike `correlation` (bounded by 1) or
`magnetization` (bounded by 1), susceptibility is *not automatically
bounded* as the exhaustion grows: `|χ_Λ(i)| ≤ 2·|Λ|`, which diverges
with `|Λ|`. Hence the `⨆` on `ℝ` may return the `ciSup` default `0`
when the along-exhaustion sequence is unbounded (physically: near or at
the critical point, where χ diverges in the genuine thermodynamic
limit). Theorems that compare `susceptibilityInfinite` values
typically require an explicit `BddAbove` hypothesis in the unbounded
case (see `susceptibilityInfinite_le_abs_h` below).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
noncomputable def susceptibilityInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) : ℝ :=
  ⨆ n, susceptibilityAlongExhaustion G Λ p i n

/-- **`susceptibilityInfinite` as `ciSup`**:
`susceptibilityInfinite G Λ p i = ⨆ n, susceptibilityAlongExhaustion G Λ p i n`
(named restatement of the definition for use in rewrites). -/
theorem susceptibilityInfinite_eq_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    susceptibilityInfinite G Λ p i
      = ⨆ n, susceptibilityAlongExhaustion G Λ p i n := rfl

/-- **Unfolding of `susceptibilityInfinite`**:
`susceptibilityInfinite G Λ p i = ⨆ n, susceptibilityAlongExhaustion G Λ p i n`,
by definition. (Alias of `susceptibilityInfinite_eq_ciSup` for uniformity
with `magnetizationInfinite_apply`.) -/
theorem susceptibilityInfinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    susceptibilityInfinite G Λ p i
      = ⨆ n, susceptibilityAlongExhaustion G Λ p i n := rfl

/-- **Nonnegativity of `susceptibilityInfinite`** under ferromagnetism:
`0 ≤ susceptibilityInfinite G Λ p i`.

Proof: each `susceptibilityAlongExhaustion … n` is `≥ 0` by
`susceptibilityAlongExhaustion_nonneg`; the `⨆` of a pointwise-nonneg
sequence on `ℝ` is `≥ 0` regardless of whether the sequence is
bounded above (if unbounded, `ciSup` defaults to `0`, which is still
`≥ 0`). -/
theorem susceptibilityInfinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    0 ≤ susceptibilityInfinite G Λ p i := by
  unfold susceptibilityInfinite
  by_cases hbd :
      BddAbove (Set.range fun n => susceptibilityAlongExhaustion G Λ p i n)
  · exact le_ciSup_of_le hbd 0
      (susceptibilityAlongExhaustion_nonneg G Λ p hf i 0)
  · rw [Real.iSup_of_not_bddAbove hbd]

/-- **∞-volume one-sided `χ_∞(h) ≤ χ_∞(|h|)`** (A-5′) under
`0 ≤ J`, `0 < β`, **assuming** `BddAbove` of the `|h|`-side
along-exhaustion sequence.

Stage-wise pointwise inequality `χ_along(h) ≤ χ_along(|h|)` at every
`n` (A-4c, PR #780) transfers to the `⨆` once the `|h|`-side is
known to be bounded above. Under the `BddAbove` hypothesis, the
pointwise comparison plus `ciSup_le_ciSup` gives the result.

**Necessity of `BddAbove`**: the susceptibility is unbounded at the
ferromagnetic critical point, where `⨆ χ_along(|h|)` would default to
`0` via the `ciSup` convention on unbounded sets. Away from the critical
line (high-temperature or deep ferromagnetic pure phases) the `BddAbove`
hypothesis is expected to hold.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityInfinite_le_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : V)
    (hbd : BddAbove (Set.range fun n =>
      susceptibilityAlongExhaustion G Λ
        (⟨J, |h|, β⟩ : IsingParams ℝ) i n)) :
    susceptibilityInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i
      ≤ susceptibilityInfinite G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i := by
  unfold susceptibilityInfinite
  refine ciSup_mono hbd ?_
  intro n
  exact susceptibilityAlongExhaustion_le_abs_h G Λ J h β hJ hβ i n

/-- **∞-volume one-sided `|M_∞(h)| ≤ M_∞(|h|)`** under ferromagnetism
at `|h|` (`0 ≤ J`, `0 < β`).

**Inequality rather than equality**: the natural equality
`|M_∞(h)| = M_∞(|h|)` (true in Glimm–Jaffe §5.3's standard
thermodynamic limit) **does not hold in general** under this repo's
sup-based `magnetizationInfinite := ⨆ n, magnetizationAlongExhaustion
…`. Concretely: at `h < 0` ferromagnetic, each covered stage gives
`M_along(n) ≤ 0` by `magnetizationAlongExhaustion_neg_h` plus
ferromagnetic nonnegativity at `|h|`; any stage with `i ∉ Λ.volume n`
contributes the forced value `0` (by the
`if A ⊆ Λ.volume n then … else 0` convention). Thus if there is even
one such "missed stage", `M_∞(h) = 0` while `M_∞(|h|) > 0`, breaking
equality. Since `Exhaustion` does not require a missed stage, this
is an obstruction/example rather than a universal consequence of
`h < 0` ferromagnetic alone — but it shows the equality cannot be
expected to hold in general. This is the same odd-`|A|` obstruction
already noted in `correlationInfinite_neg_h_of_even_card`.

The one-sided bound still holds unconditionally: at each stage
`|M_along(h) n| = M_along(|h|) n ≥ 0`, so both
`M_∞(h) ≤ M_∞(|h|)` (pointwise `f ≤ |f| = g`) and
`-M_∞(|h|) ≤ M_∞(h)` (via `a(0) ≤ ciSup a` and
`-|f(0)| ≤ f(0) ≤ ciSup f`).

Reference: Glimm–Jaffe §5.3 pp. 77–80 (background).  Part of the
§5.3 Z₂ h-symmetry series tracked in issue #770. -/
theorem abs_magnetizationInfinite_le_magnetizationInfinite_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : V) :
    |magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i|
      ≤ magnetizationInfinite G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i := by
  rw [magnetizationInfinite_eq_ciSup, magnetizationInfinite_eq_ciSup]
  set f : ℕ → ℝ :=
    fun n => magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
    with hf_def
  set a : ℕ → ℝ :=
    fun n => magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
    with ha_def
  have habs : ∀ n, |f n| = a n := fun n =>
    abs_magnetizationAlongExhaustion_eq_magnetizationAlongExhaustion_abs_h
      G Λ J h β hJ hβ i n
  have hf_bdd : BddAbove (Set.range f) :=
    correlationAlongExhaustion_bddAbove G Λ (⟨J, h, β⟩ : IsingParams ℝ) {i}
  have ha_bdd : BddAbove (Set.range a) :=
    correlationAlongExhaustion_bddAbove G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) {i}
  apply abs_le.mpr
  refine ⟨?_, ?_⟩
  · -- -⨆ a ≤ ⨆ f : pick n = 0 as witness
    have h1 : a 0 ≤ ⨆ n, a n := le_ciSup ha_bdd 0
    have h2 : -|f 0| ≤ f 0 := neg_abs_le _
    have h3 : f 0 ≤ ⨆ n, f n := le_ciSup hf_bdd 0
    have habs0 : |f 0| = a 0 := habs 0
    linarith
  · -- ⨆ f ≤ ⨆ a : pointwise f n ≤ |f n| = a n ≤ ⨆ a
    apply ciSup_le
    intro n
    calc f n ≤ |f n| := le_abs_self _
      _ = a n := habs n
      _ ≤ ⨆ n, a n := le_ciSup ha_bdd n

/-- **`magnetizationInfinite ≤ 0` at `h ≤ 0` under ferromagnetism**:
for `0 ≤ J`, `0 < β`, `h ≤ 0`, any exhaustion `Λ`, and any ambient
site `i`, `magnetizationInfinite G Λ ⟨J, h, β⟩ i ≤ 0`.

Sign-control companion to `magnetizationInfinite_nonneg` (which covers
the `h ≥ 0` side under ferromagnetism). Proof: rewrite `M_∞` as
`⨆ n, M_along n`, then show each stage value is `≤ 0`:

- covered stages (`i ∈ Λ.volume n`): `magnetizationAlongExhaustion_neg_h`
  rewrites `M_along ⟨J, h, β⟩ = -M_along ⟨J, -h, β⟩`, and
  `magnetizationAlongExhaustion_nonneg` at `⟨J, -h, β⟩` (ferromagnetic,
  since `0 ≤ -h`) gives `0 ≤ M_along ⟨J, -h, β⟩`, hence
  `M_along ⟨J, h, β⟩ ≤ 0`;
- uncovered stages (`i ∉ Λ.volume n`): `M_along = 0 ≤ 0`.

Close with `ciSup_le`.

Reference: Glimm–Jaffe §5.3 pp. 77–80 (background). Part of the §5.3
Z₂ h-symmetry series tracked in issue #770. -/
theorem magnetizationInfinite_nonpos_of_nonpos_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hh : h ≤ 0) (i : V) :
    magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i ≤ 0 := by
  rw [magnetizationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  by_cases hi : i ∈ Λ.volume n
  · have hneg :
        magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
          = -magnetizationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i n := by
      have := magnetizationAlongExhaustion_neg_h G Λ J (-h) β i n
      simpa using this
    rw [hneg]
    have hnonneg :
        0 ≤ magnetizationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i n :=
      magnetizationAlongExhaustion_nonneg G Λ _
        ⟨hJ, by linarith, hβ⟩ i n
    linarith
  · rw [magnetizationAlongExhaustion_of_not_mem G Λ _ hi]

/-- **`magnetizationInfinite = 0` at `h ≤ 0` when some stage misses `i`**:
under ferromagnetism at `|h|` (`0 ≤ J`, `0 < β`) and `h ≤ 0`, if there
exists a stage `n₀` with `i ∉ Λ.volume n₀`, then
`magnetizationInfinite G Λ ⟨J, h, β⟩ i = 0`.

Concretizes the obstruction noted in
`abs_magnetizationInfinite_le_magnetizationInfinite_abs_h`: at `h ≤ 0`,
missed stages contribute the forced value `0` and dominate the sup.

Proof: `magnetizationInfinite_nonpos_of_nonpos_h` gives the `≤ 0`
direction; for `0 ≤ M_∞`, the missed stage has
`M_along n₀ = 0 ≤ M_∞` via
`magnetizationAlongExhaustion_le_magnetizationInfinite`. Close with
`le_antisymm`.

Reference: Glimm–Jaffe §5.3 pp. 77–80 (background). Part of the §5.3
Z₂ h-symmetry series tracked in issue #770. -/
theorem magnetizationInfinite_eq_zero_of_exists_stage_not_mem
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hh : h ≤ 0) (i : V)
    (hmiss : ∃ n, i ∉ Λ.volume n) :
    magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i = 0 := by
  obtain ⟨n₀, hn₀⟩ := hmiss
  have hupper :
      magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i ≤ 0 :=
    magnetizationInfinite_nonpos_of_nonpos_h G Λ J h β hJ hβ hh i
  have hlower :
      0 ≤ magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
    have hzero :
        magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n₀ = 0 :=
      magnetizationAlongExhaustion_of_not_mem G Λ _ hn₀
    have :
        magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n₀
          ≤ magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i :=
      magnetizationAlongExhaustion_le_magnetizationInfinite G Λ _ i n₀
    linarith
  linarith

/-- **Z₂ symmetry at `h = 0` for `correlationInfinite`**: vanishes
for odd-cardinality sets.  Supremum of a constantly-zero sequence. -/
theorem correlationInfinite_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hodd : Odd A.card) :
    correlationInfinite G Λ ⟨J, 0, β⟩ A = 0 := by
  simp only [correlationInfinite,
    correlationAlongExhaustion_h_zero G Λ J β A hodd, ciSup_const]

/-- **Z₂ symmetry at `h = 0` for `magnetizationΛ`**: for any `J, β` and
any site `i : ↑Λ`, `magnetizationΛ G Λ ⟨J, 0, β⟩ i = 0`. Specialization
of `correlationΛ_odd_vanish_h_zero` at `A = {i}` using `Odd 1`. -/
theorem magnetizationΛ_h_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i = 0 :=
  correlationΛ_odd_vanish_h_zero G Λ J β {i}
    (by simp [Finset.card_singleton])

/-- **Z₂ symmetry at `h = 0` for `magnetizationAlongExhaustion`**
per stage: for any `J, β`, any site `i : V`, and any `n`,
`magnetizationAlongExhaustion G Λ ⟨J, 0, β⟩ i n = 0`.
Specialization of `correlationAlongExhaustion_h_zero` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  correlationAlongExhaustion_h_zero G Λ J β {i}
    (by simp [Finset.card_singleton]) n


/-- **`correlationAlongExhaustion` at `J = 0` (on-stage closed form)**:
whenever the test set `A` is contained in `Λ.volume n`,
`correlationAlongExhaustion G Λ ⟨0, h, β⟩ A n = tanh(β·h)^A.card`.

Specialization of `IsingModel.correlation_J_zero`
(`⟨σ^A⟩ = tanh(β·h)^{|A|}`) along the induced-subgraph coercion.
Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
(infinite-temperature slice of the correlation function). -/
theorem correlationAlongExhaustion_J_zero_of_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) {A : Finset V} {n : ℕ} (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) A n
      = Real.tanh (β * h) ^ A.card := by
  rw [correlationAlongExhaustion_of_subset G Λ (⟨0, h, β⟩ : IsingParams ℝ)
        hAn]
  change IsingModel.correlation (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) (liftFinset A hAn) = _
  rw [IsingModel.correlation_J_zero, liftFinset_card hAn]

/-- **`correlationAlongExhaustion` at `J = 0` is eventually constant**
at `tanh(β·h)^A.card`. Immediate consequence of `Exhaustion.exhaust`
(any finite `A` is eventually covered by `Λ.volume n`) and
`correlationAlongExhaustion_J_zero_of_subset`. -/
theorem correlationAlongExhaustion_J_zero_eventually_eq
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (A : Finset V) :
    ∀ᶠ n in Filter.atTop,
      correlationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) A n
        = Real.tanh (β * h) ^ A.card := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  exact correlationAlongExhaustion_J_zero_of_subset G Λ h β (hN n hn)

/-- **∞-volume correlation at `J = 0`** (ferromagnetic): for
`⟨0, h, β⟩` ferromagnetic (i.e. `h ≥ 0`, `0 < β`; the strict-`β`
condition comes from `Ferromagnetic.hβ`),
`correlationInfinite G Λ ⟨0, h, β⟩ A = tanh(β·h)^A.card`.

Proof: `correlationAlongExhaustion` at `J = 0` is eventually
constant at `tanh(β·h)^A.card`, so it tends to that value; by
`correlationAlongExhaustion_tendsto_ciSup` it also tends to
`correlationInfinite`, so the two limits coincide.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1 / §5.1
infinite-temperature slice. -/
theorem correlationInfinite_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (A : Finset V) :
    correlationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card := by
  have h_tendsto_ciSup := correlationAlongExhaustion_tendsto_ciSup G Λ
    (⟨0, h, β⟩ : IsingParams ℝ) hf A
  have h_event := correlationAlongExhaustion_J_zero_eventually_eq G Λ h β A
  have h_tendsto_const :
      Filter.Tendsto
        (correlationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) A)
        Filter.atTop (nhds (Real.tanh (β * h) ^ A.card)) :=
    tendsto_const_nhds.congr' (h_event.mono (fun _ heq => heq.symm))
  have h_unique :
      (⨆ n, correlationAlongExhaustion G Λ
          (⟨0, h, β⟩ : IsingParams ℝ) A n) = Real.tanh (β * h) ^ A.card :=
    tendsto_nhds_unique h_tendsto_ciSup h_tendsto_const
  simp only [correlationInfinite, h_unique]

/-- **∞-volume lower bound `correlationInfinite ≥ tanh(β·h)^|A|`**
(ferromagnetic): by J-monotonicity from `J = 0` where
`correlationInfinite = tanh(β·h)^|A|` (via `correlationInfinite_J_zero`). -/
theorem correlationInfinite_ge_tanh_pow_card
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset V) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) A := by
  have hf0 : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
    ⟨le_rfl, hh, hβ⟩
  have h_zero := correlationInfinite_J_zero G Λ h β hf0 A
  rw [← h_zero]
  exact correlationInfinite_monotone_J G Λ hh hβ A
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hJ) hJ

/-- **∞-volume lower bound `magnetizationInfinite ≥ tanh(β·h)`**
(ferromagnetic): specialization of `correlationInfinite_ge_tanh_pow_card`
at `A = {i}`. -/
theorem magnetizationInfinite_ge_tanh
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : V) :
    Real.tanh (β * h)
      ≤ magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
  have := correlationInfinite_ge_tanh_pow_card G Λ hJ hh hβ ({i} : Finset V)
  simpa [Finset.card_singleton] using this

/-- **Empty-set correlation on `Λ` is `1`** (normalization). -/
@[simp]
theorem correlationΛ_empty (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    correlationΛ G Λ p ∅ = 1 :=
  IsingModel.correlation_empty (inducedGraph G Λ) p

/-- **Empty-set correlation along exhaustion is `1`** for every `n`.
Empty set is always a subset of `Λ.volume n`, so the `dite` branch
always returns `correlationΛ G (Λ.volume n) p (liftFinset ∅ _) = 1`. -/
@[simp]
theorem correlationAlongExhaustion_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    correlationAlongExhaustion G Λ p ∅ n = 1 := by
  unfold correlationAlongExhaustion
  have hsub : (∅ : Finset V) ⊆ Λ.volume n := Finset.empty_subset _
  rw [dif_pos hsub]
  have hlift : liftFinset (∅ : Finset V) hsub = (∅ : Finset (↑(Λ.volume n) : Type _)) := by
    simp [liftFinset]
  rw [hlift, correlationΛ_empty]

/-- **Infinite-volume empty-set correlation is `1`**:
`ciSup` of the constantly-one sequence. -/
@[simp]
theorem correlationInfinite_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) :
    correlationInfinite G Λ p ∅ = 1 := by
  simp only [correlationInfinite, correlationAlongExhaustion_empty, ciSup_const]

/-- **β=0 correlation vanishes on `Λ`**: at `β = 0` every nonempty
`A : Finset (↑Λ)` gives `correlationΛ = 0`. Lift of PR #182
`correlation_beta_zero_vanish_of_nonempty_A`
(`Inequalities/NonnegCorrelations.lean`). -/
theorem correlationΛ_beta_zero_vanish_of_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ G Λ (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_beta_zero_vanish_of_nonempty_A
    (inducedGraph G Λ) J h A hA

/-- **β=0 correlation vanishes along exhaustion**: pointwise zero
at every `n` for nonempty `A : Finset V`. Either `A ⊄ Λ.volume n`
(dite gives 0) or `A ⊆ Λ.volume n` and the lifted correlation
vanishes via `correlationΛ_beta_zero_vanish_of_nonempty`. -/
theorem correlationAlongExhaustion_beta_zero_vanish
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (A : Finset V) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) A n = 0 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ (⟨J, h, 0⟩ : IsingParams ℝ) hAn]
    refine correlationΛ_beta_zero_vanish_of_nonempty G (Λ.volume n) J h _ ?_
    obtain ⟨a, haA⟩ := hA
    exact ⟨⟨a, hAn haA⟩, by simp [liftFinset, haA]⟩
  · exact correlationAlongExhaustion_of_not_subset G Λ (⟨J, h, 0⟩ : IsingParams ℝ) hAn

/-- **β=0 correlation vanishes at infinite volume**: the stagewise
zero sequence has supremum zero. -/
theorem correlationInfinite_beta_zero_vanish
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (A : Finset V) (hA : A.Nonempty) :
    correlationInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 := by
  simp only [correlationInfinite,
    correlationAlongExhaustion_beta_zero_vanish G Λ J h A hA, ciSup_const]

/-- **J=h=0 correlation vanishes on `Λ`**: at zero parameters every
nonempty `A : Finset (↑Λ)` gives `correlationΛ = 0`. Lift of PR #188
`correlation_zero_params_vanish_of_nonempty_A`. -/
theorem correlationΛ_zero_params_vanish_of_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β : ℝ) (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_zero_params_vanish_of_nonempty_A
    (inducedGraph G Λ) β A hA

/-- **J=h=0 correlation vanishes along exhaustion**: pointwise zero
at every `n` for nonempty `A`. `dite` branches reduce to either 0
(off branch) or the Λ lift with nonempty `liftFinset`. -/
theorem correlationAlongExhaustion_zero_params_vanish
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (A : Finset V) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) A n = 0 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ (⟨0, 0, β⟩ : IsingParams ℝ) hAn]
    refine correlationΛ_zero_params_vanish_of_nonempty G (Λ.volume n) β _ ?_
    obtain ⟨a, haA⟩ := hA
    exact ⟨⟨a, hAn haA⟩, by simp [liftFinset, haA]⟩
  · exact correlationAlongExhaustion_of_not_subset G Λ (⟨0, 0, β⟩ : IsingParams ℝ) hAn

/-- **J=h=0 correlation vanishes at infinite volume**: `ciSup` of
the constantly-zero sequence. -/
theorem correlationInfinite_zero_params_vanish
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (A : Finset V) (hA : A.Nonempty) :
    correlationInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 := by
  simp only [correlationInfinite,
    correlationAlongExhaustion_zero_params_vanish G Λ β A hA, ciSup_const]

/-- **`magnetizationΛ` vanishes at `β = 0`**: for any `J, h`, any site
`i : ↑Λ`, `magnetizationΛ G Λ ⟨J, h, 0⟩ i = 0`. Specialization of
`correlationΛ_beta_zero_vanish_of_nonempty` at the nonempty singleton
`{i}`. -/
theorem magnetizationΛ_beta_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  correlationΛ_beta_zero_vanish_of_nonempty G Λ J h {i}
    (Finset.singleton_nonempty i)

/-- **`magnetizationAlongExhaustion` vanishes at `β = 0`** per stage:
for any `J, h`, any site `i : V`, and any `n`,
`magnetizationAlongExhaustion G Λ ⟨J, h, 0⟩ i n = 0`. Specialization
of `correlationAlongExhaustion_beta_zero_vanish` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i n = 0 :=
  correlationAlongExhaustion_beta_zero_vanish G Λ J h {i}
    (Finset.singleton_nonempty i) n

/-- **`magnetizationΛ` vanishes at `J = h = 0`**: for any `β`, any site
`i : ↑Λ`, `magnetizationΛ G Λ ⟨0, 0, β⟩ i = 0`. Specialization of
`correlationΛ_zero_params_vanish_of_nonempty`. -/
theorem magnetizationΛ_zero_params (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) i = 0 :=
  correlationΛ_zero_params_vanish_of_nonempty G Λ β {i}
    (Finset.singleton_nonempty i)

/-- **`magnetizationAlongExhaustion` vanishes at `J = h = 0`** per stage. -/
theorem magnetizationAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  correlationAlongExhaustion_zero_params_vanish G Λ β {i}
    (Finset.singleton_nonempty i) n

/-- **`magnetizationΛ` closed form at `J = 0`**: for any `h, β` and any
site `i : ↑Λ`, `magnetizationΛ G Λ ⟨0, h, β⟩ i = tanh(β·h)`.
Direct lift of `IsingModel.correlation_J_zero` on the induced subgraph
at `A = {i}`, with `Finset.card_singleton` reducing `A.card = 1`. -/
theorem magnetizationΛ_J_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
  change IsingModel.correlation (inducedGraph G Λ)
      (⟨0, h, β⟩ : IsingParams ℝ) {i} = _
  rw [IsingModel.correlation_J_zero, Finset.card_singleton, pow_one]

/-- **`magnetizationAlongExhaustion` closed form at `J = 0`** per stage
(on-stage): if `i ∈ Λ.volume n`, then
`magnetizationAlongExhaustion G Λ ⟨0, h, β⟩ i n = tanh(β·h)`.
Specialization of `correlationAlongExhaustion_J_zero_of_subset` at
`A = {i}`, with `{i} ⊆ Λ.volume n ↔ i ∈ Λ.volume n`. -/
theorem magnetizationAlongExhaustion_J_zero_of_mem
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) {i : V} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) i n
      = Real.tanh (β * h) := by
  have : ({i} : Finset V) ⊆ Λ.volume n := Finset.singleton_subset_iff.mpr hi
  have := correlationAlongExhaustion_J_zero_of_subset G Λ h β this
  rw [magnetizationAlongExhaustion_apply, this, Finset.card_singleton, pow_one]

/-- **`magnetizationAlongExhaustion` is eventually `tanh(β·h)` at `J = 0`**.
Immediate from `Exhaustion.exhaust` applied to `{i}` and
`magnetizationAlongExhaustion_J_zero_of_mem`. -/
theorem magnetizationAlongExhaustion_J_zero_eventually_eq
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) :
    ∀ᶠ n in Filter.atTop,
      magnetizationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) i n
        = Real.tanh (β * h) := by
  obtain ⟨N, hN⟩ := Λ.exhaust {i}
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  exact magnetizationAlongExhaustion_J_zero_of_mem G Λ h β
    (Finset.singleton_subset_iff.mp (hN n hn))

/-- **β=0 infinite-volume magnetization vanishes**: at infinite
temperature (`β = 0`), spins are uniformly distributed and decoupled,
so the thermodynamic magnetization is `0` at every site.

Specialization of `correlationInfinite_beta_zero_vanish` at the
singleton `{i}` (automatically nonempty). -/
theorem magnetizationInfinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) :
    magnetizationInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  correlationInfinite_beta_zero_vanish G Λ J h {i} (by simp)

/-- **`magnetizationInfinite` closed form at `J = 0`** (ferromagnetic):
`magnetizationInfinite G Λ ⟨0, h, β⟩ i = tanh(β·h)`.

Specialization of `correlationInfinite_J_zero`
(`⟨σ^A⟩_∞ = tanh(β·h)^|A|`, PR #210) at the singleton `{i}`
(`A.card = 1`, so the power reduces to `tanh(β·h)`).

Complements `magnetizationInfinite_beta_zero` (β=0: vanishes) and
`magnetizationInfinite_zero_at_h_zero` (h=0: vanishes).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
(non-interacting `J = 0` slice; `β` is constrained only by
`Ferromagnetic.hβ : 0 < β`, not by the infinite-temperature
limit `β → 0`); §5.1 pp. 76–77 (magnetization). -/
theorem magnetizationInfinite_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : V) :
    magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i
      = Real.tanh (β * h) := by
  unfold magnetizationInfinite
  rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]

/-- **`magnetizationInfinite` at `h = 0` vanishes**: the Z₂ spin-flip
symmetry at zero external field forces the single-site thermodynamic
magnetization to be zero.

This gives the zero-field **symmetric** value, which is distinct from
the *spontaneous magnetization* $m^* := \lim_{h \to 0^+} M(h)$ studied
in Glimm–Jaffe §5.1 (p. 77): symmetry breaking is detected by the
one-sided limit $h \to 0^+$ (or boundary-condition selection), not by
evaluating at $h = 0$. -/
theorem magnetizationInfinite_zero_at_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    magnetizationInfinite G Λ ⟨J, 0, β⟩ i = 0 :=
  correlationInfinite_h_zero G Λ J β {i} (by simp)

/-! ## Spontaneous magnetization

Define the spontaneous magnetization
$m^*(G, \Lambda; J, \beta; i) := \lim_{h \to 0^+} M^{\mathrm{FM}}(J, h, \beta; i)$
as the infimum over `h > 0` of `magnetizationInfinite`.  Since
`magnetizationInfinite` is monotone in `h` on `Set.Ici 0` (PR #95) and
bounded below by `0` (ferromagnetic, PR #98), the right-limit at `h = 0`
equals this infimum.

Reference: Glimm–Jaffe §5.1 p. 77. Friedli–Velenik §3.10 (self-consistent
magnetization). -/

/-! ## Spontaneous correlation function (general `A`)

Generalize `spontaneousMagnetization` (single-site, `A = {i}`) to an
arbitrary finite set `A : Finset V`.  Same infimum-form over `h > 0`,
derived from PR #91–#100's `correlationInfinite` API. -/

/-- **Spontaneous correlation function** (infimum form):
`spontaneousCorrelation G Λ J β A := ⨅ h : ↥(Set.Ioi 0), correlationInfinite G Λ ⟨J, h, β⟩ A`.

Generalization of `spontaneousMagnetization` to arbitrary `A : Finset V`.
For $A = \{i\}$, coincides with `spontaneousMagnetization` by definition. -/
noncomputable def spontaneousCorrelation
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) : ℝ :=
  ⨅ h : ↥(Set.Ioi (0 : ℝ)), correlationInfinite G Λ ⟨J, h.val, β⟩ A

/-- **Unfolding of `spontaneousCorrelation`** as a named identity:
`spontaneousCorrelation G Λ J β A = ⨅ h ∈ Ioi 0, correlationInfinite G Λ ⟨J, h, β⟩ A`. -/
theorem spontaneousCorrelation_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) :
    spontaneousCorrelation G Λ J β A
      = ⨅ h : ↥(Set.Ioi (0 : ℝ)), correlationInfinite G Λ ⟨J, h.val, β⟩ A :=
  rfl

/-- **Bounded-below witness** for `spontaneousCorrelation`: the family
`h ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` over `Set.Ioi 0` is bounded
below by `0` (ferromagnetic). -/
private theorem correlationInfinite_bddBelow_on_Ioi
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    BddBelow (Set.range
      (fun h : ↥(Set.Ioi (0 : ℝ)) =>
        correlationInfinite G Λ ⟨J, h.val, β⟩ A)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact correlationInfinite_nonneg G Λ ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Nonnegativity** (ferromagnetic): $\langle \sigma^A \rangle^* \ge 0$. -/
theorem spontaneousCorrelation_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    0 ≤ spontaneousCorrelation G Λ J β A := by
  refine le_ciInf ?_
  rintro h
  exact correlationInfinite_nonneg G Λ ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Upper bound**: $\langle \sigma^A \rangle^* \le 1$. -/
theorem spontaneousCorrelation_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β A ≤ 1 := by
  refine ciInf_le_of_le
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ A)
    ⟨1, by norm_num⟩ ?_
  exact correlationInfinite_le_one G Λ ⟨J, 1, β⟩ A

/-- **`-1 ≤ spontaneousCorrelation`** (ferromagnetic). Follows from
`spontaneousCorrelation_nonneg`. -/
theorem neg_one_le_spontaneousCorrelation
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    -1 ≤ spontaneousCorrelation G Λ J β A := by
  have := spontaneousCorrelation_nonneg G Λ hJ hβ A
  linarith

/-- **`|spontaneousCorrelation| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousCorrelation_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    |spontaneousCorrelation G Λ J β A| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_spontaneousCorrelation G Λ hJ hβ A,
    spontaneousCorrelation_le_one G Λ hJ hβ A⟩

/-- **`spontaneousCorrelation² ≤ 1`** (ferromagnetic). -/
theorem spontaneousCorrelation_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β A ^ 2 ≤ 1 := by
  have h := abs_spontaneousCorrelation_le_one G Λ hJ hβ A
  have : |spontaneousCorrelation G Λ J β A| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Lower bound by `correlationInfinite` at positive `h`**: for any
`h > 0`, $\langle \sigma^A \rangle^* \le \langle \sigma^A \rangle(h)$. -/
theorem spontaneousCorrelation_le_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (A : Finset V) :
    spontaneousCorrelation G Λ J β A
      ≤ correlationInfinite G Λ ⟨J, h, β⟩ A :=
  ciInf_le
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ A)
    ⟨h, hh⟩

/-- **Exhaustion-independence**: $\langle \sigma^A \rangle^*$ does not
depend on the choice of exhaustion. -/
theorem spontaneousCorrelation_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β A
      = spontaneousCorrelation G Λ' J β A := by
  unfold spontaneousCorrelation
  congr 1
  funext h
  exact correlationInfinite_indep_exhaustion G Λ Λ' ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Right-limit Tendsto**: for ferromagnetic Ising, the general-`A`
`correlationInfinite ⟨J, h, β⟩ A` tends to `spontaneousCorrelation` as
`h → 0⁺`. Analogous to
`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`. -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation G Λ J β A)) := by
  set f : ℝ → ℝ := fun h => correlationInfinite G Λ ⟨J, h, β⟩ A with hf_def
  have hmono : MonotoneOn f (Set.Ioi 0) := by
    have hmono_Ici : MonotoneOn f (Set.Ici 0) :=
      correlationInfinite_monotone_h G Λ hJ hβ A
    exact hmono_Ici.mono Set.Ioi_subset_Ici_self
  have hbdd : BddBelow (f '' Set.Ioi 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    exact correlationInfinite_nonneg G Λ ⟨J, h, β⟩
      ⟨hJ, le_of_lt hh, hβ⟩ A
  have htendsto := hmono.tendsto_nhdsGT hbdd
  have hsInf : sInf (f '' Set.Ioi 0) = spontaneousCorrelation G Λ J β A := by
    unfold spontaneousCorrelation
    rw [← sInf_range, ← Set.image_univ]
    congr 1
    ext y
    simp [hf_def, Set.image_univ, Set.mem_image, Set.mem_Ioi, Subtype.exists]
  rw [← hsInf]
  exact htendsto

/-! ## Spontaneous magnetization (single-site specialization)

`spontaneousMagnetization` is the single-site case `A = {i}` of
`spontaneousCorrelation`.  All basic properties are one-line
specializations.

Reference: Glimm–Jaffe §5.1 p. 77 (the order parameter $m^*$
distinguishing ordered/disordered phases). -/

/-- **Spontaneous magnetization at infinite volume** (*infimum form*):
for ferromagnetic Ising on an ambient type `V`, exhaustion `Λ`, and
fixed `J, β`,
`spontaneousMagnetization G Λ J β i := spontaneousCorrelation G Λ J β {i}`.

This is the order parameter $m^*$.  Since `magnetizationInfinite` is
monotone in `h` on `Set.Ici 0` and bounded in `[0, 1]`, this infimum
coincides with $\lim_{h \to 0^+} M(h)$
(`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`). -/
noncomputable def spontaneousMagnetization
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) : ℝ :=
  spontaneousCorrelation G Λ J β {i}

/-- **Unfolding of `spontaneousMagnetization`**:
`spontaneousMagnetization G Λ J β i = spontaneousCorrelation G Λ J β {i}`. -/
theorem spontaneousMagnetization_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    spontaneousMagnetization G Λ J β i = spontaneousCorrelation G Λ J β {i} :=
  rfl

/-- **Agreement at singletons**: `spontaneousCorrelation` on `{i}`
equals `spontaneousMagnetization`. Holds by definition. -/
theorem spontaneousCorrelation_singleton_eq_spontaneousMagnetization
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    spontaneousCorrelation G Λ J β {i}
      = spontaneousMagnetization G Λ J β i :=
  rfl

/-- **Nonnegativity of `spontaneousMagnetization`** (ferromagnetic):
$m^* \ge 0$.  Specialization of `spontaneousCorrelation_nonneg` at
`A = {i}`. -/
theorem spontaneousMagnetization_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    0 ≤ spontaneousMagnetization G Λ J β i :=
  spontaneousCorrelation_nonneg G Λ hJ hβ {i}

/-- **Upper bound**: $m^* \le 1$.  Specialization of
`spontaneousCorrelation_le_one` at `A = {i}`. -/
theorem spontaneousMagnetization_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β i ≤ 1 :=
  spontaneousCorrelation_le_one G Λ hJ hβ {i}


/-- **`-1 ≤ spontaneousMagnetization`** (ferromagnetic).
Direct from `spontaneousMagnetization_nonneg`. -/
theorem neg_one_le_spontaneousMagnetization
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    -1 ≤ spontaneousMagnetization G Λ J β i := by
  have := spontaneousMagnetization_nonneg G Λ hJ hβ i
  linarith

/-- **`|spontaneousMagnetization| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousMagnetization_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    |spontaneousMagnetization G Λ J β i| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_spontaneousMagnetization G Λ hJ hβ i,
    spontaneousMagnetization_le_one G Λ hJ hβ i⟩

/-- **`spontaneousMagnetization² ≤ 1`** (ferromagnetic). -/
theorem spontaneousMagnetization_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β i ^ 2 ≤ 1 := by
  have h := abs_spontaneousMagnetization_le_one G Λ hJ hβ i
  have : |spontaneousMagnetization G Λ J β i| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Lower bound for `magnetizationInfinite` at positive `h`**:
$m^* \le M(h)$ for $h > 0$. Specialization of
`spontaneousCorrelation_le_correlationInfinite` at `A = {i}` (noting
`magnetizationInfinite = correlationInfinite ... {i}`). -/
theorem spontaneousMagnetization_le_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (i : V) :
    spontaneousMagnetization G Λ J β i
      ≤ magnetizationInfinite G Λ ⟨J, h, β⟩ i :=
  spontaneousCorrelation_le_correlationInfinite G Λ hJ hβ hh {i}

/-- **Exhaustion-independence of `spontaneousMagnetization`**:
the value does not depend on the choice of exhaustion.  Specialization
of `spontaneousCorrelation_indep_exhaustion` at `A = {i}`. -/
theorem spontaneousMagnetization_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β i
      = spontaneousMagnetization G Λ' J β i :=
  spontaneousCorrelation_indep_exhaustion G Λ Λ' hJ hβ {i}

/-- **Right-limit Tendsto**: for ferromagnetic Ising,
`magnetizationInfinite` tends to `spontaneousMagnetization` as
`h → 0⁺`.  Specialization of
`tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT` at
`A = {i}` (noting `magnetizationInfinite = correlationInfinite ... {i}`). -/
theorem tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    Filter.Tendsto
      (fun h : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousMagnetization G Λ J β i)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT G Λ hJ hβ {i}

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

/-! ## Parameter monotonicity of `spontaneous*`

Combine the parameter-direction monotonicity of `correlationInfinite`
(PR #95–#97) with the infimum definition of `spontaneousCorrelation`
to obtain monotonicity of the spontaneous correlation function in
`J` and `β`.  The `h`-direction is already collapsed by the infimum
over `h > 0`, so only `J` and `β` remain as free parameters. -/

/-- **J-direction monotonicity of `spontaneousCorrelation`**: for
fixed `β > 0`, $\langle \sigma^A \rangle^*(J, \beta)$ is monotone in
$J \in \mathrm{Ici}\,0$.

Since `correlationInfinite_monotone_J` gives pointwise monotonicity
for each `h ∈ Ioi 0`, the iInf over `h > 0` is also monotone in `J`.
Proof via `ciInf_mono` + `correlationInfinite_bddBelow_on_Ioi`. -/
theorem spontaneousCorrelation_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation G Λ J β A)
      (Set.Ici 0) := by
  intro J₁ hJ₁ J₂ _ hJ₁₂
  unfold spontaneousCorrelation
  refine ciInf_mono
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ₁ hβ A) ?_
  intro h
  exact correlationInfinite_monotone_J G Λ h.property.le hβ A
    hJ₁ (hJ₁.trans hJ₁₂) hJ₁₂

/-- **Ambient-subgraph monotonicity of `spontaneousCorrelation`**
(ferromagnetic): for `G₁ ≤ G₂`, `0 ≤ J`, `0 < β`,
`spontaneousCorrelation G₁ Λ J β A ≤ spontaneousCorrelation G₂ Λ J β A`.
Via `ciInf_mono` + `correlationInfinite_monotone_ambient_subgraph`. -/
theorem spontaneousCorrelation_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (hG : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G₁ Λ J β A
      ≤ spontaneousCorrelation G₂ Λ J β A := by
  unfold spontaneousCorrelation
  refine ciInf_mono
    (correlationInfinite_bddBelow_on_Ioi G₁ Λ hJ hβ A) ?_
  intro hpos
  have hf : Ferromagnetic (⟨J, hpos.val, β⟩ : IsingParams ℝ) :=
    ⟨hJ, hpos.property.le, hβ⟩
  exact correlationInfinite_monotone_ambient_subgraph hG Λ
    (⟨J, hpos.val, β⟩ : IsingParams ℝ) hf A

/-- **β-direction monotonicity of `spontaneousCorrelation`**: for
fixed `J ≥ 0`, the map `β ↦ spontaneousCorrelation G Λ J β A` is
monotone on `Set.Ioi 0`.

Companion to `spontaneousCorrelation_monotone_J`.  Since
`correlationInfinite_monotone_beta` gives pointwise monotonicity in
`β` for each `h ∈ Ioi 0` (with the remaining parameters bounded
below by `0`), the iInf over `h > 0` is also monotone in `β`.
Proof via `ciInf_mono` + `correlationInfinite_bddBelow_on_Ioi`. -/
theorem spontaneousCorrelation_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (A : Finset V) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation G Λ J β A)
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ₁₂
  unfold spontaneousCorrelation
  refine ciInf_mono
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ₁ A) ?_
  intro h
  exact correlationInfinite_monotone_beta G Λ hJ h.property.le A
    hβ₁ (lt_of_lt_of_le hβ₁ hβ₁₂) hβ₁₂

/-- **J-direction monotonicity of `spontaneousMagnetization`**:
specialization of `spontaneousCorrelation_monotone_J` at `A = {i}`. -/
theorem spontaneousMagnetization_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (i : V) :
    MonotoneOn
      (fun J : ℝ => spontaneousMagnetization G Λ J β i)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J G Λ hβ {i}

/-- **β-direction monotonicity of `spontaneousMagnetization`**:
specialization of `spontaneousCorrelation_monotone_beta` at `A = {i}`. -/
theorem spontaneousMagnetization_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (i : V) :
    MonotoneOn
      (fun β : ℝ => spontaneousMagnetization G Λ J β i)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta G Λ hJ {i}

/-- **Ambient-subgraph monotonicity of `spontaneousMagnetization`**
(ferromagnetic): `G₁ ≤ G₂` ⇒ `m*_G₁(i) ≤ m*_G₂(i)`. Specialization of
`spontaneousCorrelation_monotone_ambient_subgraph` at `A = {i}`. -/
theorem spontaneousMagnetization_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (hG : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G₁ Λ J β i
      ≤ spontaneousMagnetization G₂ Λ J β i :=
  spontaneousCorrelation_monotone_ambient_subgraph hG Λ hJ hβ {i}

/-! ## Cor 4.3.5 (inductive n-point at h=0) at infinite volume

Lift `IsingModel.cor_4_3_5_h0` to the thermodynamic limit using the
liftFinset infrastructure from PR #107 and `Finset.sum_bij` to reindex
the powerset sum.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.5, p. 62. -/

/-- **Cor 4.3.5 lifted to infinite volume**: the inductive (n+2)-point
bound holds for `correlationInfinite` at `h = 0`.  For ferromagnetic
Ising at zero external field, any finite set `S`, and distinct sites
`j, k ∉ S`, the infinite-volume correlation satisfies the same
inductive bound as the finite-volume version. -/
theorem correlationInfinite_cor_4_3_5_h0
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    (S : Finset V) {j k : V} (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlationInfinite G Λ ⟨J, 0, β⟩ (insert j (insert k S)) ≤
      correlationInfinite G Λ ⟨J, 0, β⟩ S *
        correlationInfinite G Λ ⟨J, 0, β⟩ {j, k} +
      ∑ T ∈ S.powerset,
        correlationInfinite G Λ ⟨J, 0, β⟩ (insert j T) *
          correlationInfinite G Λ ⟨J, 0, β⟩ (insert k (S \ T)) := by
  set p := (⟨J, 0, β⟩ : IsingParams ℝ)
  have hlhs_tendsto := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf (insert j (insert k S))
  have hrhs_main :=
    (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf S).mul
      (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j, k})
  have hrhs_sum : Filter.Tendsto
      (fun n => ∑ T ∈ S.powerset,
        correlationAlongExhaustion G Λ p (insert j T) n *
          correlationAlongExhaustion G Λ p (insert k (S \ T)) n)
      Filter.atTop
      (nhds (∑ T ∈ S.powerset,
        correlationInfinite G Λ p (insert j T) *
          correlationInfinite G Λ p (insert k (S \ T)))) := by
    refine tendsto_finset_sum _ (fun T _ => ?_)
    exact (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf _).mul
      (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf _)
  have hrhs_tendsto := hrhs_main.add hrhs_sum
  refine le_of_tendsto_of_tendsto' hlhs_tendsto hrhs_tendsto ?_
  intro n
  by_cases hall : (insert j (insert k S) : Finset V) ⊆ Λ.volume n
  · have hj_vol : j ∈ Λ.volume n := hall (Finset.mem_insert_self _ _)
    have hk_vol : k ∈ Λ.volume n :=
      hall (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hS_vol : S ⊆ Λ.volume n := fun x hx =>
      hall (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have hjk_vol : ({j, k} : Finset V) ⊆ Λ.volume n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hj_vol
      · exact hk_vol
    let j' : (↑(Λ.volume n) : Type _) := ⟨j, hj_vol⟩
    let k' : (↑(Λ.volume n) : Type _) := ⟨k, hk_vol⟩
    let S' : Finset (↑(Λ.volume n) : Type _) := liftFinset S hS_vol
    have hj'_notin : j' ∉ S' := fun h => hj ((mem_liftFinset _ _).mp h)
    have hk'_notin : k' ∉ S' := fun h => hk ((mem_liftFinset _ _).mp h)
    have hjk' : j' ≠ k' := fun h => hjk (Subtype.mk.inj h)
    have hfin := IsingModel.cor_4_3_5_h0
      (inducedGraph G (Λ.volume n)) J β hf S' j' k' hj'_notin hk'_notin hjk'
    rw [correlationAlongExhaustion_of_subset G Λ p hall,
        correlationAlongExhaustion_of_subset G Λ p hS_vol,
        correlationAlongExhaustion_of_subset G Λ p hjk_vol]
    have hlift_jkS :
        liftFinset (insert j (insert k S)) hall = insert j' (insert k' S') := by
      rw [← liftFinset_insert hj_vol (fun x hx =>
        hall (Finset.mem_insert_of_mem hx))]
      simp only [S', k']
      rw [← liftFinset_insert hk_vol hS_vol]
    have hlift_jk :
        liftFinset ({j, k} : Finset V) hjk_vol = ({j', k'} : Finset _) := by
      ext x
      simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton, j', k']
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl (by rfl)
        · exact Or.inr (by rfl)
      · rintro (h | h)
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (congrArg Subtype.val h)
    rw [hlift_jkS, hlift_jk]
    have hsum_eq :
        ∑ T ∈ S.powerset,
          correlationAlongExhaustion G Λ p (insert j T) n *
            correlationAlongExhaustion G Λ p (insert k (S \ T)) n
        = ∑ T' ∈ S'.powerset,
          correlationΛ G (Λ.volume n) p (insert j' T') *
            correlationΛ G (Λ.volume n) p (insert k' (S' \ T')) := by
      refine Finset.sum_bij
        (fun T hT => liftFinset T
          (fun x hx => hS_vol ((Finset.mem_powerset.mp hT) hx)))
        ?_ ?_ ?_ ?_
      · intro T hT
        simp only [S', Finset.mem_powerset]
        intro x hx
        simp only [mem_liftFinset] at hx ⊢
        exact (Finset.mem_powerset.mp hT) hx
      · intro T₁ hT₁ T₂ hT₂ heq
        have h₁ := Finset.mem_powerset.mp hT₁
        have h₂ := Finset.mem_powerset.mp hT₂
        -- Beta-reduce heq to pure liftFinset equality
        have heq' : liftFinset T₁ (fun x hx => hS_vol (h₁ hx))
            = liftFinset T₂ (fun x hx => hS_vol (h₂ hx)) := heq
        ext x
        by_cases hx_vol : x ∈ Λ.volume n
        · constructor
          · intro hxT₁
            have hlift : (⟨x, hx_vol⟩ : ↑(Λ.volume n))
                ∈ liftFinset T₁ (fun y hy => hS_vol (h₁ hy)) :=
              (mem_liftFinset _ _).mpr hxT₁
            rw [heq'] at hlift
            exact (mem_liftFinset _ _).mp hlift
          · intro hxT₂
            have hlift : (⟨x, hx_vol⟩ : ↑(Λ.volume n))
                ∈ liftFinset T₂ (fun y hy => hS_vol (h₂ hy)) :=
              (mem_liftFinset _ _).mpr hxT₂
            rw [← heq'] at hlift
            exact (mem_liftFinset _ _).mp hlift
        · exact ⟨fun h => absurd (hS_vol (h₁ h)) hx_vol,
                fun h => absurd (hS_vol (h₂ h)) hx_vol⟩
      · intro T' hT'
        simp only [S', Finset.mem_powerset] at hT'
        refine ⟨T'.image (fun x => x.val), ?_, ?_⟩
        · simp only [Finset.mem_powerset]
          intro x hx
          simp only [Finset.mem_image] at hx
          obtain ⟨y, hyT', rfl⟩ := hx
          have := hT' hyT'
          simpa only [mem_liftFinset] using this
        · ext x
          simp only [mem_liftFinset, Finset.mem_image]
          refine ⟨?_, ?_⟩
          · rintro ⟨y, hyT', hyx⟩
            have : y = x := Subtype.ext hyx
            exact this ▸ hyT'
          · intro h
            exact ⟨x, h, rfl⟩
      · intro T hT
        have hT_sub := Finset.mem_powerset.mp hT
        have hjT_vol : (insert j T : Finset V) ⊆ Λ.volume n := fun x hx => by
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact hj_vol
          · exact hS_vol (hT_sub hx)
        have hkST_vol : (insert k (S \ T) : Finset V) ⊆ Λ.volume n :=
          fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_sdiff] at hx
            rcases hx with rfl | ⟨hxS, _⟩
            · exact hk_vol
            · exact hS_vol hxS
        rw [correlationAlongExhaustion_of_subset G Λ p hjT_vol,
            correlationAlongExhaustion_of_subset G Λ p hkST_vol]
        have h_liftFinset_jT :
            liftFinset (insert j T) hjT_vol
            = insert j' (liftFinset T (fun x hx => hS_vol (hT_sub hx))) := by
          rw [← liftFinset_insert hj_vol (fun x hx => hS_vol (hT_sub hx))]
        have h_liftFinset_kST :
            liftFinset (insert k (S \ T)) hkST_vol
            = insert k' (S' \ liftFinset T (fun x hx => hS_vol (hT_sub hx))) := by
          rw [← liftFinset_insert hk_vol (fun x hx => hS_vol
            ((Finset.mem_sdiff.mp hx).1))]
          congr 1
          simp only [S']
          exact (liftFinset_sdiff hS_vol (fun x hx => hS_vol (hT_sub hx))).symm
        rw [h_liftFinset_jT, h_liftFinset_kST]
    rw [hsum_eq]
    unfold correlationΛ
    exact hfin
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hall]
    have h_main :
        0 ≤ correlationAlongExhaustion G Λ p S n *
          correlationAlongExhaustion G Λ p {j, k} n :=
      mul_nonneg
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
    have h_sum : 0 ≤ ∑ T ∈ S.powerset,
        correlationAlongExhaustion G Λ p (insert j T) n *
          correlationAlongExhaustion G Λ p (insert k (S \ T)) n := by
      refine Finset.sum_nonneg fun T _ => ?_
      exact mul_nonneg
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
    linarith

/-- **Infinite-volume free energy density** (limsup form).

Defined as the `Filter.limsup` of `freeEnergyAlongExhaustion`, which
is always well-defined for real sequences (even non-convergent ones).
Glimm–Jaffe Proposition 4.6.1 asserts that this limsup equals the
liminf (i.e., the sequence converges); the convergence theorem itself
is deferred pending partition function super-additivity + Fekete's
lemma machinery. -/
noncomputable def freeEnergyInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  Filter.limsup (freeEnergyAlongExhaustion G Λ p) Filter.atTop

/-- **Unfolding of `freeEnergyInfinite`**:
`freeEnergyInfinite G Λ p = limsup (freeEnergyAlongExhaustion G Λ p)`
at `atTop`, by definition. -/
theorem freeEnergyInfinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyInfinite G Λ p
      = Filter.limsup (freeEnergyAlongExhaustion G Λ p) Filter.atTop := rfl

/-- **Zero-params lower-bound comparison for `freeEnergyAlongExhaustion`**.

For ferromagnetic Ising parameters (`J ≥ 0`, `h ≥ 0`, `β > 0`), the
free energy along the exhaustion dominates the value at zero coupling
and zero external field:
`freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n
  ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`.

Proof: transitive composition of `_monotone_h` at `J = 0` (giving
`f(0, 0, β) ≤ f(0, h, β)`) with `_monotone_J` at fixed `h`
(giving `f(0, h, β) ≤ f(J, h, β)`). -/
theorem freeEnergyAlongExhaustion_ge_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n
      ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n := by
  have h1 : freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n
      ≤ freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n :=
    freeEnergyAlongExhaustion_monotone_h G Λ le_rfl hβ n
      (Set.self_mem_Ici) hh hh
  have h2 : freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n
      ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n :=
    freeEnergyAlongExhaustion_monotone_J G Λ hh hβ n
      (Set.self_mem_Ici) hJ hJ
  exact h1.trans h2

/-- **Zero-params lower-bound comparison for `partitionFunctionAlongExhaustion`**
(partition function analog of `freeEnergyAlongExhaustion_ge_zero_params`).
For ferromagnetic, `Z(0, 0, β) ≤ Z(J, h, β)`. -/
theorem partitionFunctionAlongExhaustion_ge_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n := by
  have h1 : partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n :=
    partitionFunctionAlongExhaustion_monotone_h G Λ 0 β le_rfl hβ le_rfl hh n
  have h2 : partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n :=
    partitionFunctionAlongExhaustion_monotone_J G Λ h β hh hβ le_rfl hJ n
  exact h1.trans h2

/-- **Uniform lower bound** `freeEnergyAlongExhaustion ≥ log 2` for
ferromagnetic parameters on a nonempty volume.

Combines the zero-params comparison
(`freeEnergyAlongExhaustion_ge_zero_params`, PR #117) with the
explicit value at zero parameters (`freeEnergy_zero_params = log 2`,
PR #120) via `IsingModel.freeEnergy` definitional unfolding.

This is half of the data needed for Glimm–Jaffe §4.6 Proposition 4.6.1
(convergence): the sequence is bounded below by `log 2`. -/
theorem freeEnergyAlongExhaustion_ge_log_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n := by
  have h_zero : freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n = Real.log 2 := by
    change freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2
    exact IsingModel.freeEnergy_zero_params _ β (Finset.Nonempty.fintype_card_coe_pos hne)
  calc Real.log 2
      = freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n := h_zero.symm
    _ ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n :=
        freeEnergyAlongExhaustion_ge_zero_params G Λ hJ hh hβ n

/-- **Sharp along-exhaustion lower bound**:
for ferromagnetic parameters and nonempty stage,
`log(2·cosh(β·h)) ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`.

Specialization of `IsingModel.freeEnergy_ge_log_two_cosh` (FreeEnergy.lean)
at the induced subgraph on `Λ.volume n`. Sharpens the `log 2` uniform
lower bound (`freeEnergyAlongExhaustion_ge_log_two`). -/
theorem freeEnergyAlongExhaustion_ge_log_two_cosh
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n := by
  change Real.log (2 * Real.cosh (β * h))
      ≤ IsingModel.freeEnergy (inducedGraph G (Λ.volume n)) ⟨J, h, β⟩
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Along-exhaustion upper bound for the free energy**:
for nonempty `Λ.volume n`,
`freeEnergyAlongExhaustion G Λ p n ≤
  log 2 + |β|·(|J|·|E_n| + |h|·|Λ_n|) / |Λ_n|`,
where `E_n` is the edge count of the induced subgraph on `Λ.volume n`
and `|Λ_n|` is its cardinality.

Specialization of `IsingModel.freeEnergy_upper_bound` (Conditioning.lean,
Cor. 10.3.2 divided by `|ι|`) to the exhaustion setting. -/
theorem freeEnergyAlongExhaustion_upper_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ p n ≤ Real.log 2 +
      |p.β| * (|p.J| * (inducedGraph G (Λ.volume n)).edgeFinset.card +
          |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
        / Fintype.card (↑(Λ.volume n) : Type _) := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n)) p ≤ _
  exact IsingModel.freeEnergy_upper_bound _ p (Finset.Nonempty.fintype_card_coe_pos hne)

/-! ## Uniform upper bound under bounded edge density

The per-stage upper bound `freeEnergyAlongExhaustion_upper_bound` depends
on `|E_n| / |Λ_n|`; this ratio can diverge for an arbitrary exhaustion.
Under the natural hypothesis `BoundedEdgeDensity`, the sequence is
uniformly bounded above — a step toward Glimm–Jaffe §4.6 Prop 4.6.1
convergence (which still needs super-additivity + Fekete). -/

/-- **Bounded edge density along an exhaustion**: there is `c : ℝ` such
that for every `n` with `Λ.volume n` nonempty,
`|E(G[Λ_n])| ≤ c · |Λ_n|`.

Example: bounded-degree ambient graphs with max degree `Δ` satisfy
this with `c = Δ / 2`. -/
def BoundedEdgeDensity (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] : Prop :=
  ∃ c : ℝ, ∀ n, (Λ.volume n).Nonempty →
    ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
      c * Fintype.card (↑(Λ.volume n) : Type _)

/-- **Uniform upper bound on `freeEnergyAlongExhaustion` under bounded
edge density**: if `BoundedEdgeDensity G Λ` with constant `c`, then for
every `n` with `Λ.volume n` nonempty and any Ising parameters `p`,
`freeEnergyAlongExhaustion G Λ p n ≤ log 2 + |β|·(|J|·c + |h|)`.

Direct consequence of `freeEnergyAlongExhaustion_upper_bound` (PR #122)
and the edge-density bound `|E_n|/|Λ_n| ≤ c`. -/
theorem freeEnergyAlongExhaustion_le_uniform_upper_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _))
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ p n ≤
      Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
  have hcard_pos : (0 : ℝ) < Fintype.card (↑(Λ.volume n) : Type _) := by
    rw [Fintype.card_coe]; exact_mod_cast Finset.card_pos.mpr hne
  have hratio :
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        Fintype.card (↑(Λ.volume n) : Type _) ≤ c :=
    (div_le_iff₀ hcard_pos).mpr (hc n hne)
  calc freeEnergyAlongExhaustion G Λ p n
      ≤ Real.log 2 +
          |p.β| * (|p.J| * (inducedGraph G (Λ.volume n)).edgeFinset.card +
              |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
            / Fintype.card (↑(Λ.volume n) : Type _) :=
        freeEnergyAlongExhaustion_upper_bound G Λ p n hne
    _ = Real.log 2 +
          |p.β| * (|p.J| *
              ((inducedGraph G (Λ.volume n)).edgeFinset.card /
                Fintype.card (↑(Λ.volume n) : Type _)) + |p.h|) := by
          field_simp
    _ ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
          gcongr

/-! ## β = 0 closed form along exhaustion -/

/-- **Along-exhaustion β=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ, J, h`,
`freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_beta_zero` (PR #131) via
`change` + definitional unfolding of `freeEnergyAlongExhaustion`
through `freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_beta_zero _ J h (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Infinite-volume β=0 closed form**:
under `∀ n, (Λ.volume n).Nonempty`, `freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2`
for any `J, h, G, Λ`.

The sequence `n ↦ freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n` is constantly
`log 2` by `freeEnergyAlongExhaustion_beta_zero`, so its `limsup` on
`atTop` is `log 2` by `Filter.limsup_const`.

Sanity check: the β = 0 slice of the §4.6 Prop 4.6.1 infinite-volume
free energy is trivially the maximum-entropy value.

A weakened version requiring only `∀ᶠ n in atTop, (Λ.volume n).Nonempty`
is provided as `freeEnergyInfinite_beta_zero_of_eventually_nonempty`
in `AmbientLatticeSum.lean`. -/
theorem freeEnergyInfinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergyInfinite
  have hconst : freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ)
      = fun _ : ℕ => Real.log 2 := by
    funext n
    exact freeEnergyAlongExhaustion_beta_zero G Λ J h n (hne n)
  rw [hconst]
  exact Filter.limsup_const (Real.log 2)

/-! ## J = h = 0 closed form along exhaustion -/

/-- **Along-exhaustion J=h=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `β`,
`freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_zero_params` via `change` +
definitional unfolding of `freeEnergyAlongExhaustion` through
`freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_zero_params _ β (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Infinite-volume J=h=0 closed form**:
under `∀ n, (Λ.volume n).Nonempty`, `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2`
for any `β, G, Λ`.

The sequence `n ↦ freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n` is constantly
`log 2` by `freeEnergyAlongExhaustion_zero_params`, so its `limsup` on
`atTop` is `log 2` by `Filter.limsup_const`.

Companion to `freeEnergyInfinite_beta_zero`: both give the
maximum-entropy value `log 2` from orthogonal degeneracies
(β=0 vs. H ≡ 0).

A weakened version requiring only `∀ᶠ n in atTop, (Λ.volume n).Nonempty`
is provided as `freeEnergyInfinite_zero_params_of_eventually_nonempty`
in `AmbientLatticeSum.lean`. -/
theorem freeEnergyInfinite_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergyInfinite
  have hconst : freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = fun _ : ℕ => Real.log 2 := by
    funext n
    exact freeEnergyAlongExhaustion_zero_params G Λ β n (hne n)
  rw [hconst]
  exact Filter.limsup_const (Real.log 2)

/-! ## J = 0 closed form along exhaustion (graph-independent) -/

/-- **Along-exhaustion J=0 graph-independence**:
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n
  = freeEnergyAlongExhaustion ⊥ Λ ⟨0, h, β⟩ n`
for any `n`, any `G, Λ`, any `h, β` (no nonempty hypothesis).

Lift of `IsingModel.freeEnergy_eq_bot_at_J_zero` (PR #175) through
the definitional unfolding
`freeEnergyAlongExhaustion = freeEnergy (inducedGraph …)`:
apply the base identity on both sides to reduce to the same
`freeEnergy_bot` expression. -/
theorem freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph V) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))
          (⟨0, h, β⟩ : IsingParams ℝ)
  rw [IsingModel.freeEnergy_eq_bot_at_J_zero (inducedGraph G (Λ.volume n)),
      IsingModel.freeEnergy_eq_bot_at_J_zero
        (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))]

/-- **Along-exhaustion J=0 closed form (graph-independent)**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `h, β`,
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n = log (2·cosh(β·h))`.

Specialization of `IsingModel.freeEnergy_J_zero` via `change` +
definitional unfolding. -/
theorem freeEnergyAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  exact IsingModel.freeEnergy_J_zero _ h β (Finset.Nonempty.fintype_card_coe_pos hne)

/-! ## β = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion β=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n = 2 ^ |Λ.volume n|`
for any `J, h` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_beta_zero` (every
Boltzmann weight collapses to `exp 0 = 1`) with
`card_config_eq_two_pow` and `Fintype.card_coe`. -/
theorem partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_beta_zero, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_beta_zero` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_beta_zero, Real.log_pow]

/-! ## J = h = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=h=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n = 2 ^ |Λ.volume n|`
for any ambient graph `G, Λ` and any `β`.

Specialization of `IsingModel.partitionFunction_zero_params`
(`Z_G ⟨0,0,β⟩ = Fintype.card (Config ι)`) with `card_config_eq_two_pow`
(`|Config ι| = 2^|ι|`) and `Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_zero_params, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_zero_params` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_zero_params, Real.log_pow]

/-! ## J = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n = (2·cosh(β·h))^|Λ.volume n|`
for any `h, β` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_J_zero`
(`Z_G ⟨0, h, β⟩ = (2·cosh(β·h))^|ι|`, graph-independent) with
`Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_J_zero, Fintype.card_coe]

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n)
= |Λ.volume n| · log (2·cosh(β·h))`. Follows from
`partitionFunctionAlongExhaustion_J_zero` via `Real.log_pow`
(`2·cosh(β·h) > 0`). -/
theorem log_partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) := by
  rw [partitionFunctionAlongExhaustion_J_zero, Real.log_pow]

/-! ## Free-spin identity for induced subgraph -/

omit [DecidableEq V] in
/-- **Induced subgraph of the empty graph is empty**:
`inducedGraph (⊥ : SimpleGraph V) Λ = ⊥`.

`inducedGraph = induce = comap` and `SimpleGraph.comap_bot`.
Useful rewrite when the ambient graph is `⊥` (free-spin limit). -/
@[simp]
theorem inducedGraph_bot (Λ : Finset V) :
    inducedGraph (⊥ : SimpleGraph V) Λ = (⊥ : SimpleGraph (↑Λ : Type _)) :=
  SimpleGraph.comap_bot _

/-! ## h-symmetry / `|h|`-monotonicity along exhaustion

Specializations of `IsingModel.freeEnergy_neg_h`, `freeEnergy_eq_abs_h`,
and `freeEnergy_monotone_abs_h` (PRs #126–#127) to each stage of the
exhaustion, via the `change` + definitional-unfolding pattern already
used in this file. -/

/-- **Along-exhaustion partition-function h-evenness**:
`partitionFunctionAlongExhaustion G Λ ⟨J, -h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n`. Per-stage lift of
`IsingModel.partitionFunction_neg_h` via the flip involution. -/
theorem partitionFunctionAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_neg_h G (Λ.volume n) J h β

/-- **Along-exhaustion partition-function `|h|`-rewrite**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_eq_abs_h G (Λ.volume n) J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity of partition
function**: for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`partitionFunctionAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤
partitionFunctionAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_monotone_abs_h G (Λ.volume n) J β hJ hβ hh

/-- **Along-exhaustion h-evenness**:
`freeEnergyAlongExhaustion G Λ ⟨J, -h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, -h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_neg_h _ J h β

/-- **Along-exhaustion `|h|`-rewrite**:
`freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, |h|, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_eq_abs_h _ J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and any real `h₁, h₂` with `|h₁| ≤ |h₂|`,
`freeEnergyAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤ freeEnergyAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h₁, β⟩ : IsingParams ℝ)
    ≤ IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h₂, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_monotone_abs_h _ J β hJ hβ hh

/-- **BddAbove for `freeEnergyAlongExhaustion` under bounded edge density**:
assuming `BoundedEdgeDensity G Λ`, the range of the exhaustion free energy
is bounded above.

For nonempty stages the bound is `log 2 + |β|·(|J|·c + |h|)` by the
uniform upper bound above; for empty stages the value is
`(Fintype.card ∅)⁻¹ · log 1 = 0`, which is at most the same constant
(after taking its `max` with `0`). -/
theorem BddAbove_freeEnergyAlongExhaustion_range
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p)) := by
  obtain ⟨c, hc⟩ := hBED
  refine ⟨max 0 (Real.log 2 + |p.β| * (|p.J| * c + |p.h|)), ?_⟩
  rintro y ⟨n, rfl⟩
  by_cases hne : (Λ.volume n).Nonempty
  · exact le_max_of_le_right
      (freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ p hc n hne)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hcard : Fintype.card (↑(Λ.volume n) : Type _) = 0 := by
      rw [Fintype.card_coe, hne]; rfl
    have hfe : freeEnergyAlongExhaustion G Λ p n = 0 := by
      change IsingModel.freeEnergy (inducedGraph G (Λ.volume n)) p = 0
      unfold IsingModel.freeEnergy
      rw [hcard, Nat.cast_zero, inv_zero, zero_mul]
    rw [hfe]; exact le_max_left _ _

/-! ## Critical exponents at ∞-volume (GJ §17.7 Thm 17.7.1)

Explicit ∞-vol named aliases for the critical-exponent bounds
`η ≥ 0` and `ζ ≥ 0`, matching the finite-volume
`IsingModel.eta_nonneg_finite_vol` / `zeta_nonneg_finite_vol`
pattern. Direct pass-throughs of `truncated2Infinite_nonneg` (GKS-II
at ∞-vol) and `truncated4Infinite_nonpos_h_zero` (Cor 4.3.3 at ∞-vol). -/

/-- **η ≥ 0 at ∞-volume** (GJ §17.7 Thm 17.7.1, ∞-vol lattice version).
Explicit alias of `truncated2Infinite_nonneg` matching the
`eta_nonneg_finite_vol` naming convention. -/
theorem eta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    0 ≤ truncated2Infinite G Λ p i j :=
  truncated2Infinite_nonneg G Λ p hf i j

/-- **ζ ≥ 0 at ∞-volume** (GJ §17.7 Thm 17.7.1, ∞-vol lattice version,
at `h = 0`). Explicit alias of `truncated4Infinite_nonpos_h_zero` —
`U₄^∞ ≤ 0` for pairwise-distinct sites at `h = 0`. -/
theorem zeta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

/-- **Absence of even bound states — ∞-volume lattice** (Glimm–Jaffe
§17.2, pp. 311–313). ∞-vol version of
`IsingModel.absence_of_even_bound_states_finite_vol`:
`U₄^∞(i,j,k,l) ≤ 0` for ferromagnetic `⟨J, 0, β⟩` and pairwise-distinct
sites. Explicit alias of `truncated4Infinite_nonpos_h_zero`. -/
theorem absence_of_even_bound_states_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

end Ambient
end IsingModel

