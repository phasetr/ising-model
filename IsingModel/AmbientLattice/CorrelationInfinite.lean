import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.Monotonicity

/-!
# Infinite-volume correlation functions

Convergence of correlations along an exhaustion, definition of the
infinite-volume correlation `correlationInfinite`, and key properties.

## Definitions

* `IsingModel.Ambient.correlationInfinite` — `ciSup` of the along-exhaustion
  correlation sequence.
* `IsingModel.Ambient.magnetizationInfinite` — single-site limit.
* `IsingModel.Ambient.truncated2Infinite` — U₂ two-point truncated function.

## Main results

* `correlationAlongExhaustion_tendsto_ciSup` — convergence theorem.
* `correlationInfinite_indep_exhaustion` — independence of the exhaustion.
* `correlationInfinite_gks_second` — GKS-II at infinite volume.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2 Thm 4.2.3.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Convergence along an exhaustion

Apply `correlationΛ_monotone_volume` to show that the correlations
along an exhaustion converge. We use a shifted sequence
`n ↦ correlationΛ G (Λ.volume (n + N)) p (liftFinset A ...)` where
`N` is chosen so that `A ⊆ Λ.volume N` (from `Exhaustion.exhaust`).
Past `N`, `correlationAlongExhaustion` equals this shifted sequence. -/

/-- The shifted correlation sequence along an exhaustion: given
`N : ℕ` with `A ⊆ Λ.volume n` for `n ≥ N`, the sequence
`n ↦ correlationΛ G (Λ.volume (n + N)) p (liftFinset A ...)` is
monotone and bounded. -/
theorem correlationΛ_shifted_monotone_bounded
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Monotone (fun n : ℕ =>
      correlationΛ G (Λ.volume (n + N)) p
        (liftFinset A (hN (n + N) (Nat.le_add_left N n))))
    ∧ ∀ n : ℕ,
      correlationΛ G (Λ.volume (n + N)) p
        (liftFinset A (hN (n + N) (Nat.le_add_left N n))) ≤ 1 := by
  refine ⟨?_, ?_⟩
  · intro n m hnm
    have hΛmono : Λ.volume (n + N) ⊆ Λ.volume (m + N) :=
      Λ.mono (Nat.add_le_add_right hnm N)
    exact correlationΛ_monotone_volume G hΛmono p hf
      (hN (n + N) (Nat.le_add_left N n))
  · intro n
    exact correlationΛ_le_one _ _ _ _

/-- **Tendsto convergence of the shifted correlation sequence**:
the shifted sequence (monotone and bounded by PR #88) converges
to its supremum by `tendsto_atTop_ciSup`. -/
theorem correlationΛ_shifted_tendsto
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    ∃ L : ℝ, Filter.Tendsto
      (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
        (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds L) := by
  obtain ⟨hmono, hbdd⟩ := correlationΛ_shifted_monotone_bounded G Λ p hf hN
  exact ⟨_, tendsto_atTop_ciSup hmono ⟨1, fun _ ⟨m, hm⟩ => hm ▸ hbdd m⟩⟩

/-- **Global monotonicity of `correlationAlongExhaustion`**:
because (1) for `n` where `A ⊆ Λ.volume n` fails, it equals 0;
(2) when it holds, `correlationΛ ≥ 0` by GKS-I; and (3) when both
endpoints satisfy the inclusion, `correlationΛ_monotone_volume`
(PR #87) applies. -/
theorem correlationAlongExhaustion_monotone
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Monotone (correlationAlongExhaustion G Λ p A) := by
  intro n m hnm
  by_cases hAn : A ⊆ Λ.volume n
  · by_cases hAm : A ⊆ Λ.volume m
    · rw [correlationAlongExhaustion_of_subset G Λ p hAn,
          correlationAlongExhaustion_of_subset G Λ p hAm]
      exact correlationΛ_monotone_volume G (Λ.mono hnm) p hf hAn
    · exact absurd (hAn.trans (Λ.mono hnm)) hAm
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hAn]
    by_cases hAm : A ⊆ Λ.volume m
    · rw [correlationAlongExhaustion_of_subset G Λ p hAm]
      exact correlationΛ_nonneg G (Λ.volume m) p hf _
    · rw [correlationAlongExhaustion_of_not_subset G Λ p hAm]

/-- **Global upper bound of `correlationAlongExhaustion` by 1**:
either the value is 0 (when `A ⊄ Λ.volume n`) or it is bounded
by `correlationΛ_le_one`. -/
theorem correlationAlongExhaustion_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ p A n ≤ 1 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ p hAn]
    exact correlationΛ_le_one _ _ _ _
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hAn]
    norm_num

/-- **Range is bounded above by 1**: the range of the sequence
`correlationAlongExhaustion G Λ p A` is bounded above. Witness `1`
via `correlationAlongExhaustion_le_one`. -/
theorem correlationAlongExhaustion_bddAbove
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    BddAbove (Set.range (correlationAlongExhaustion G Λ p A)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact correlationAlongExhaustion_le_one G Λ p A n

/-- **Convergence of correlation along an exhaustion (explicit limit)**:
for a ferromagnetic Ising model and any exhaustion `Λₙ ↑ V` of an
ambient type `V`, the sequence `correlationAlongExhaustion` converges
to its supremum as `n → ∞`.

The limit is `⨆ n, correlationAlongExhaustion G Λ p A n`; this
exposes the limit's identity (as a supremum) so it can be related
to the thermodynamic-limit correlation once `Λ.exhaust` is used to
identify `A` with a subset of some `Λ.volume N`.

Note: this theorem itself only uses `Λ.mono` (monotonicity of the
exhaustion); `Λ.exhaust` is not required for convergence alone,
but is needed in downstream physical identifications of `L`. -/
theorem correlationAlongExhaustion_tendsto_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Filter.Tendsto (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds (⨆ n, correlationAlongExhaustion G Λ p A n)) := by
  exact tendsto_atTop_ciSup
    (correlationAlongExhaustion_monotone G Λ p hf A)
    (correlationAlongExhaustion_bddAbove G Λ p A)

/-- **Convergence of correlation along an exhaustion (existential form)**:
thin wrapper around `correlationAlongExhaustion_tendsto_ciSup`. Use
the `_tendsto_ciSup` form when the identity of `L` as a supremum is
needed (e.g. for physical identification with the thermodynamic limit). -/
theorem correlationAlongExhaustion_convergent
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    ∃ L : ℝ, Filter.Tendsto
      (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds L) :=
  ⟨_, correlationAlongExhaustion_tendsto_ciSup G Λ p hf A⟩

/-! ## Infinite-volume correlation function

The supremum exposed by `correlationAlongExhaustion_tendsto_ciSup`
is, by GKS-I and `Λ.exhaust`, the thermodynamic-limit correlation
for ferromagnetic Ising models on an ambient `V`.  We package it as
a `noncomputable def` and record its basic properties. -/

/-- **Infinite-volume correlation function**: for a ferromagnetic
Ising model on an ambient type `V` with an exhaustion `Λ` and a
finite `A : Finset V`,
`correlationInfinite G Λ p A := ⨆ n, correlationAlongExhaustion G Λ p A n`.
This is the thermodynamic-limit correlation identified via
`Λ.exhaust` (any finite `A` lies in some `Λ.volume N`). -/
noncomputable def correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) : ℝ :=
  ⨆ n, correlationAlongExhaustion G Λ p A n

/-- **`correlationInfinite` as `ciSup`**:
`correlationInfinite G Λ p A = ⨆ n, correlationAlongExhaustion G Λ p A n`
(named restatement of the definition for use in rewrites). -/
theorem correlationInfinite_eq_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A
      = ⨆ n, correlationAlongExhaustion G Λ p A n := rfl

/-- **Pointwise bound**: `correlationAlongExhaustion G Λ p A n ≤
correlationInfinite G Λ p A` at every `n`. Direct from `le_ciSup` +
`correlationAlongExhaustion_bddAbove`. -/
theorem correlationAlongExhaustion_le_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ p A n ≤ correlationInfinite G Λ p A :=
  le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) n

/-- **Tendsto to infinite-volume correlation** (primary form):
`correlationAlongExhaustion` converges to `correlationInfinite`.
Restatement of `correlationAlongExhaustion_tendsto_ciSup` in terms
of the canonical `correlationInfinite` name. -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Filter.Tendsto (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds (correlationInfinite G Λ p A)) :=
  correlationAlongExhaustion_tendsto_ciSup G Λ p hf A

/-- **Upper bound**: `correlationInfinite ≤ 1`. Pointwise bound from
`correlationAlongExhaustion_le_one` + `ciSup_le`. -/
theorem correlationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ≤ 1 := by
  refine ciSup_le ?_
  intro n
  exact correlationAlongExhaustion_le_one G Λ p A n

/-- **Pointwise `|correlationInfinite| ≤ 1`** (unconditional):
the infinite-volume correlation is bounded in absolute value by `1`
regardless of parameters. Upper side is `correlationInfinite_le_one`;
lower side uses `le_ciSup` with the stage-`0` pointwise bound
`correlationAlongExhaustion ≥ -1` (from `abs_correlationAlongExhaustion_le_one`). -/
theorem abs_correlationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    |correlationInfinite G Λ p A| ≤ 1 := by
  refine abs_le.mpr ⟨?_, correlationInfinite_le_one G Λ p A⟩
  have h0 : -1 ≤ correlationAlongExhaustion G Λ p A 0 :=
    (abs_le.mp (abs_correlationAlongExhaustion_le_one G Λ p A 0)).1
  exact h0.trans (le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) 0)

/-- **`-1 ≤ correlationInfinite`** (unconditional).
Lower side of `abs_correlationInfinite_le_one`. -/
theorem neg_one_le_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    -1 ≤ correlationInfinite G Λ p A :=
  (abs_le.mp (abs_correlationInfinite_le_one G Λ p A)).1

/-- **`correlationInfinite² ≤ 1`** (unconditional). -/
theorem correlationInfinite_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ^ 2 ≤ 1 := by
  have h := abs_correlationInfinite_le_one G Λ p A
  have : |correlationInfinite G Λ p A| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Nonnegativity** (ferromagnetic): `correlationInfinite ≥ 0`.
Uses `Λ.exhaust`: pick `N` with `A ⊆ Λ.volume N`; then
`correlationAlongExhaustion G Λ p A N ≥ 0` by GKS-I, and this is
a lower bound for the supremum (so the supremum is also `≥ 0`). -/
theorem correlationInfinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    0 ≤ correlationInfinite G Λ p A := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  have hA : A ⊆ Λ.volume N := hN N le_rfl
  have hval : 0 ≤ correlationAlongExhaustion G Λ p A N := by
    rw [correlationAlongExhaustion_of_subset G Λ p hA]
    exact correlationΛ_nonneg G (Λ.volume N) p hf _
  exact hval.trans (le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) N)

/-- **Tendsto of the lifted `correlationΛ` sequence (explicit form)**:
given an explicit `N` and a hypothesis `hN : ∀ n ≥ N, A ⊆ Λ.volume n`,
the sequence `m ↦ correlationΛ G (Λ.volume (m+N)) p (liftFinset A …)`
converges to `correlationInfinite G Λ p A`.

The shifted sequence coincides with `correlationAlongExhaustion` on
indices `≥ N` (both branches of the dite agree since `A ⊆ Λ.volume (m+N)`),
and the base sequence's limit is `correlationInfinite` by
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
theorem tendsto_correlationΛ_correlationInfinite_of_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Filter.Tendsto
      (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
        (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds (correlationInfinite G Λ p A)) := by
  have hbase := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf A
  have hshift :
      Filter.Tendsto (fun m : ℕ => correlationAlongExhaustion G Λ p A (m + N))
        Filter.atTop (nhds (correlationInfinite G Λ p A)) :=
    hbase.comp (Filter.tendsto_add_atTop_nat N)
  refine hshift.congr ?_
  intro m
  have hA : A ⊆ Λ.volume (m + N) := hN (m + N) (Nat.le_add_left N m)
  exact correlationAlongExhaustion_of_subset G Λ p hA

/-- **Tendsto of the lifted `correlationΛ` sequence (corollary)**:
using `Λ.exhaust` to produce an `N` with `A ⊆ Λ.volume n` for `n ≥ N`,
the sequence `m ↦ correlationΛ G (Λ.volume (m+N)) p (liftFinset A …)`
converges to `correlationInfinite G Λ p A`.

This is the physical statement: as the volume grows, the finite-volume
correlation converges to the thermodynamic-limit correlation. -/
theorem tendsto_correlationΛ_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ Λ.volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
          (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite G Λ p A)) := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  exact ⟨N, hN, tendsto_correlationΛ_correlationInfinite_of_subset G Λ p hf hN⟩

/-! ## Exhaustion-independence of `correlationInfinite`

Although `correlationInfinite` is defined as a supremum tied to a
specific `Λ`, the value does not depend on the choice of exhaustion:
any two exhaustions yield the same thermodynamic-limit correlation. -/

/-- **Key sandwich lemma**: every value of `correlationAlongExhaustion`
along one exhaustion is bounded above by `correlationInfinite` along
another exhaustion of the same ambient type.

Proof sketch: if `A ⊆ Λ'.volume n`, apply `Λ.exhaust` to the finite
set `Λ'.volume n` to get `m` with `Λ'.volume n ⊆ Λ.volume m`; then
`correlationΛ_monotone_volume` sandwiches the two finite-volume
correlations, and `le_ciSup` moves from `Λ.volume m` to the supremum.
Otherwise `correlationAlongExhaustion Λ' n = 0 ≤ correlationInfinite Λ`
via `correlationInfinite_nonneg`. -/
theorem correlationAlongExhaustion_le_correlationInfinite_of_other
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ' p A n ≤ correlationInfinite G Λ p A := by
  by_cases hAn : A ⊆ Λ'.volume n
  · -- A ⊆ Λ'.volume n: use Λ.exhaust on Λ'.volume n
    obtain ⟨m, hm⟩ := Λ.exhaust (Λ'.volume n)
    have hsubset : Λ'.volume n ⊆ Λ.volume m := hm m le_rfl
    have hAm : A ⊆ Λ.volume m := hAn.trans hsubset
    have hmono :
        correlationΛ G (Λ'.volume n) p (liftFinset A hAn) ≤
          correlationΛ G (Λ.volume m) p (liftFinset A hAm) :=
      correlationΛ_monotone_volume G hsubset p hf hAn
    calc correlationAlongExhaustion G Λ' p A n
        = correlationΛ G (Λ'.volume n) p (liftFinset A hAn) :=
          correlationAlongExhaustion_of_subset G Λ' p hAn
      _ ≤ correlationΛ G (Λ.volume m) p (liftFinset A hAm) := hmono
      _ = correlationAlongExhaustion G Λ p A m :=
          (correlationAlongExhaustion_of_subset G Λ p hAm).symm
      _ ≤ correlationInfinite G Λ p A :=
          le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) m
  · -- A ⊄ Λ'.volume n: LHS = 0 ≤ correlationInfinite (nonneg)
    rw [correlationAlongExhaustion_of_not_subset G Λ' p hAn]
    exact correlationInfinite_nonneg G Λ p hf A

/-- **Exhaustion-independence** of `correlationInfinite`: for any two
exhaustions `Λ, Λ'` of the same ambient type `V`, the thermodynamic-limit
correlation is the same:
`correlationInfinite G Λ p A = correlationInfinite G Λ' p A`.

Proof: both `≤` directions by `ciSup_le` applied to the sandwich
lemma `correlationAlongExhaustion_le_correlationInfinite_of_other`. -/
theorem correlationInfinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    correlationInfinite G Λ p A = correlationInfinite G Λ' p A := by
  refine le_antisymm ?_ ?_
  · refine ciSup_le ?_
    intro n
    exact correlationAlongExhaustion_le_correlationInfinite_of_other
      G Λ' Λ p hf A n
  · refine ciSup_le ?_
    intro n
    exact correlationAlongExhaustion_le_correlationInfinite_of_other
      G Λ Λ' p hf A n

/-! ## Ambient-subgraph monotonicity of infinite-volume correlation

Finite-volume monotonicity in the ambient subgraph
(`correlationΛ_monotone_ambient_subgraph`, PR #58) lifts to the
thermodynamic-limit correlation: for ferromagnetic Ising on an
ambient type `V` and exhaustion `Λ`, `G₁ ≤ G₂` implies
`correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A`. -/

/-- **Ambient-subgraph monotonicity of `correlationAlongExhaustion`**:
if `G₁ ≤ G₂` then the exhaustion sequence is pointwise monotone in
the ambient subgraph. -/
theorem correlationAlongExhaustion_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G₁ Λ p A n
      ≤ correlationAlongExhaustion G₂ Λ p A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G₁ Λ p hAn,
        correlationAlongExhaustion_of_subset G₂ Λ p hAn]
    exact correlationΛ_monotone_ambient_subgraph h (Λ.volume n) p hf _
  · rw [correlationAlongExhaustion_of_not_subset G₁ Λ p hAn,
        correlationAlongExhaustion_of_not_subset G₂ Λ p hAn]

/-- **Ambient-subgraph monotonicity of `correlationInfinite`**:
if `G₁ ≤ G₂` then
`correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A`.

Proof: pointwise monotonicity of the exhaustion sequence
(`correlationAlongExhaustion_monotone_ambient_subgraph`) combined
with `le_ciSup` and `ciSup_le`. -/
theorem correlationInfinite_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A := by
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_ambient_subgraph h Λ p hf A n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G₂ Λ p A) n)

/-- **Magnetization along-exhaustion ambient-subgraph monotonicity**:
per stage, for `G₁ ≤ G₂` and ferromagnetic `p`. Specialization of
`correlationAlongExhaustion_monotone_ambient_subgraph` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G₁ Λ p i n
      ≤ magnetizationAlongExhaustion G₂ Λ p i n :=
  correlationAlongExhaustion_monotone_ambient_subgraph h Λ p hf {i} n


/-! ## GKS-II (second Griffiths inequality) at infinite volume

Lift the finite-volume second Griffiths inequality (`gks_second`,
`Inequalities/GKS.lean`) to the thermodynamic limit. For ferromagnetic
Ising and any two finite subsets `A, B`,
`correlationInfinite A * correlationInfinite B ≤ correlationInfinite (A ∆ B)`.

Reference: Glimm-Jaffe, *Quantum Physics* §4.2 Theorem 4.2.3 (GKS-II
for the infinite-volume limit).  Friedli-Velenik Thm 3.49 for the
finite-volume version. -/

/-- Helper: if `A ⊆ Λ` and `B ⊆ Λ` then `A ∆ B ⊆ Λ`. -/
theorem symmDiff_subset_of_subset
    {A B Λ : Finset V} (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    A ∆ B ⊆ Λ :=
  fun _ hx => (Finset.mem_symmDiff.mp hx).elim (fun h => hA h.1) (fun h => hB h.1)

/-- `correlationAlongExhaustion` is always `≥ 0` for a ferromagnetic
Ising model: either the value is `0` (when `A ⊄ Λ.volume n`) or it is
`correlationΛ ≥ 0` by GKS-I (`correlationΛ_nonneg`). -/
theorem correlationAlongExhaustion_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ p A n := by
  by_cases hA : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ p hA]
    exact correlationΛ_nonneg G (Λ.volume n) p hf _
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hA]


end Ambient
end IsingModel
