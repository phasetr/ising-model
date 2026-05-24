import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteExhaustionHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteSusceptibility
import IsingModel.AmbientLattice.MagnetizationInfiniteHZeroJZero
import IsingModel.AmbientLattice.MagnetizationInfiniteEmptyTrivial
import IsingModel.AmbientLattice.MagnetizationInfiniteMagTrivial
import IsingModel.AmbientLattice.MagnetizationInfiniteSusceptibilityRegularity

/-!
# Infinite-volume single-site magnetization

Definition and basic properties of `magnetizationInfinite` (the thermodynamic
limit of the per-site magnetization).

Includes the definition, elementary bounds, exhaustion convergence,
exhaustion-independence, and monotonicity in `h`, `β`, and `J`.

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

end Ambient
end IsingModel
