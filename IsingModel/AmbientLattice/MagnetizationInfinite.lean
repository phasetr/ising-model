import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Infinite-volume single-site magnetization

Definition and properties of `magnetizationInfinite` (the thermodynamic
limit of the per-site magnetization) and related objects.

Includes: monotonicity in `h`, `β`, `J`; h-symmetry; spontaneous
magnetization limit; susceptibilityInfinite; and various special cases.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2–4.4, §5.3.
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


end Ambient
end IsingModel
